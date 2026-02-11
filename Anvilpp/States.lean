import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Anvilpp.Proc
import Anvilpp.Typing
import Anvilpp.Automata
import Anvilpp.Helpers

def reachableTySet (Γ : String → Option ProcTy) (τ : ProcTy) : Finset ProcTy :=
  match τ with
  | .message x => {ProcTy.message x, ProcTy.skip}
  | .cycle => {ProcTy.cycle, ProcTy.skip}
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
  -- FIXME: check if this is correct
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
  all_goals sorry -- FIXME: complete


/-
  Now we actually prove that this finite set includes all reachable types.
  TODO: do we need further assumptions, e.g., all variables are bound?
-/

-- lemma reachable_types_in_set :
--   ∀ (τ τ' : ProcTy), ProcTyReachable τ τ' → τ' ∈ reachableTySet (fun _ => none) τ := sorry
