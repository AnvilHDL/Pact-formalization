import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Anvilpp.Base
import Anvilpp.Proc
import Anvilpp.Types
import Anvilpp.Typing
import Anvilpp.Automata

/-- A type variable is absent from a process type. -/
inductive AbsentIn : String → ProcTy → Prop where
  | var (x x' : String) :
    x ≠ x' →
    AbsentIn x (ProcTy.var x')
  | message (x : String) (me : MessageExch) :
    AbsentIn x (ProcTy.message me)
  | cycle (x : String) :
    AbsentIn x ProcTy.cycle
  | skip (x : String) :
    AbsentIn x ProcTy.skip
  | dollar (x : String) (pid : ProcId) :
    AbsentIn x (ProcTy.dollar pid)
  | choice (x : String) (τ₁ τ₂ : ProcTy) :
    AbsentIn x τ₁ →
    AbsentIn x τ₂ →
    AbsentIn x (ProcTy.choice τ₁ τ₂)
  | choice_fair (x : String) (bid : BranchId) (τ₁ τ₂ : ProcTy) :
    AbsentIn x τ₁ →
    AbsentIn x τ₂ →
    AbsentIn x (ProcTy.choice_fair bid τ₁ τ₂)
  | par (x : String) (τ₁ τ₂ : ProcTy) :
    AbsentIn x τ₁ →
    AbsentIn x τ₂ →
    AbsentIn x (ProcTy.par τ₁ τ₂)
  | seq (x : String) (τ₁ τ₂ : ProcTy) :
    AbsentIn x τ₁ →
    AbsentIn x τ₂ →
    AbsentIn x (ProcTy.seq τ₁ τ₂)
  | xoffer (x : String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    AbsentIn x τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → AbsentIn x ty) →
    AbsentIn x (ProcTy.xoffer τ_else branch_tys)
  | offer (x : String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    AbsentIn x τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → AbsentIn x ty) →
    AbsentIn x (ProcTy.offer τ_else branch_tys)
  | recur (x x' : String) (body : ProcTy) :
    x ≠ x' →
    AbsentIn x body →
    AbsentIn x (ProcTy.recur x' body)

/-- A type variable appears only at tail locations or is absent. -/
inductive AtTail : String → ProcTy → Prop where
  -- For par we only allow absence
  | absent (x : String) (τ : ProcTy) :
    AbsentIn x τ →
    AtTail x τ
  | seq (x : String) (τ₁ τ₂ : ProcTy) :
    AbsentIn x τ₁ →
    AtTail x τ₂ →
    AtTail x (ProcTy.seq τ₁ τ₂)
  | choice (x : String) (τ₁ τ₂ : ProcTy) :
    AtTail x τ₁ →
    AtTail x τ₂ →
    AtTail x (ProcTy.choice τ₁ τ₂)
  | choice_fair (x : String) (bid : BranchId) (τ₁ τ₂ : ProcTy) :
    AtTail x τ₁ →
    AtTail x τ₂ →
    AtTail x (ProcTy.choice_fair bid τ₁ τ₂)
  | xoffer (x : String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    AtTail x τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → AtTail x ty) →
    AtTail x (ProcTy.xoffer τ_else branch_tys)
  | offer (x : String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    AtTail x τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → AtTail x ty) →
    AtTail x (ProcTy.offer τ_else branch_tys)
  | recur (x x' : String) (body : ProcTy) :
    x ≠ x' →
    AtTail x body →
    AtTail x (ProcTy.recur x' body)


/-- Well-formed process types. All recursion variables appear only at tail locations. -/
inductive WellformedTy : ProcTy → Prop where
  | message (me : MessageExch) :
    WellformedTy (ProcTy.message me)
  | cycle :
    WellformedTy ProcTy.cycle
  | skip :
    WellformedTy ProcTy.skip
  | dollar (pid : ProcId) :
    WellformedTy (ProcTy.dollar pid)
  | choice (τ₁ τ₂ : ProcTy) :
    WellformedTy τ₁ →
    WellformedTy τ₂ →
    WellformedTy (ProcTy.choice τ₁ τ₂)
  | choice_fair (bid : BranchId) (τ₁ τ₂ : ProcTy) :
    WellformedTy τ₁ →
    WellformedTy τ₂ →
    WellformedTy (ProcTy.choice_fair bid τ₁ τ₂)
  | par (τ₁ τ₂ : ProcTy) :
    WellformedTy τ₁ →
    WellformedTy τ₂ →
    WellformedTy (ProcTy.par τ₁ τ₂)
  | seq (τ₁ τ₂ : ProcTy) :
    WellformedTy τ₁ →
    WellformedTy τ₂ →
    WellformedTy (ProcTy.seq τ₁ τ₂)
  | xoffer (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    WellformedTy τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → WellformedTy ty) →
    WellformedTy (ProcTy.xoffer τ_else branch_tys)
  | offer (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    WellformedTy τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → WellformedTy ty) →
    WellformedTy (ProcTy.offer τ_else branch_tys)
  | var (x : String) :
    WellformedTy (ProcTy.var x)
  | recur (x : String) (body : ProcTy) :
    WellformedTy body →
    AtTail x body →
    WellformedTy (ProcTy.recur x body)

-- TODO: the most important proof
lemma type_emulates_proc : ∀ (comp comp' : Semantics.ProcComp)
                             (comp_ty : ProcTyComposition) (c_lbl : TransLabel),
    CompositionTyJudgement comp comp_ty →
    Semantics.CompReduces comp c_lbl comp' →
    ∃ comp_ty',
      CompositionTyJudgement comp' comp_ty' ∧
      ProcTyCompTransition comp_ty (AbstractTransLabel.fromConcrete c_lbl) comp_ty' := sorry

def reachableTySet (Γ : String → Option ProcTy) (τ : ProcTy) : Finset ProcTy :=
  match τ with
  | .message x => {ProcTy.message x, ProcTy.skip}
  | .cycle => {ProcTy.cycle} ∪ {ProcTy.skip}
  | .skip => {ProcTy.skip}
  | .dollar pid => {ProcTy.dollar pid, ProcTy.skip}
  | .seq τ₁ τ₂ =>
      let set₁ := reachableTySet Γ τ₁
      let set₂ := reachableTySet Γ τ₂
      set₁.image (fun τ'₁ => ProcTy.seq τ'₁ τ₂) ∪ set₂
  | .choice τ₁ τ₂ =>
      (reachableTySet Γ τ₁) ∪ (reachableTySet Γ τ₂)
  | .choice_fair bid τ₁ τ₂ =>
      (reachableTySet Γ τ₁) ∪ (reachableTySet Γ τ₂)
  | .par τ₁ τ₂ =>
      let set₁ := reachableTySet Γ τ₁
      let set₂ := reachableTySet Γ τ₂
      (set₁ ×ˢ set₂).image (fun (τ'₁, τ'₂) => ProcTy.par τ'₁ τ'₂) ∪ {ProcTy.skip}
  | .xoffer τ_else branch_tys =>
      let set_else := reachableTySet Γ τ_else
      let set_branches :=
        branch_tys.foldl (fun acc (_, ty) => acc ∪ reachableTySet Γ ty) ∅
      set_else ∪ set_branches ∪ {ProcTy.skip}
  | .offer τ_else branch_tys =>
      let set_else := reachableTySet Γ τ_else
      let set_branches :=
        branch_tys.foldl (fun acc (_, ty) => acc ∪ reachableTySet Γ ty) ∅
      set_else ∪ set_branches ∪ {ProcTy.skip}
  | .var x => (
    match Γ x with
    | some τ' => {τ'}
    | none => {τ}
  )
  | .recur x body =>
    {τ} ∪ (reachableTySet (fun x' => if x' = x then τ else Γ x') body)
decreasing_by
  all_goals sorry


/-
  Now we actually prove that this finite set includes all reachable types.
  TODO: do we need further assumptions, e.g., all variables are bound?
-/

lemma reachable_types_in_set :
  ∀ (τ τ' : ProcTy), ProcTyReachable τ τ' → τ' ∈ reachableTySet (fun _ => none) τ := sorry

/-
  Similarly for compositions.
-/

lemma reachable_comp_types_in_set :
  ∀ (comp comp' : ProcTyComposition),
    ProcTyCompReachable comp comp' →
    Multiset.Rel (fun τ τ' => τ' ∈ reachableTySet (fun _ => none) τ) comp comp' := sorry
