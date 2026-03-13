import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Anvilpp.Proc
import Anvilpp.Types
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

/-- A process type where every recursion variable occurs only in tail position. -/
inductive TailRecProcTyJudgement : ProcTy → Prop where
  | var (x : String) :
    TailRecProcTyJudgement (ProcTy.var x)
  | message (me : MessageExch) :
    TailRecProcTyJudgement (ProcTy.message me)
  | cycle :
    TailRecProcTyJudgement ProcTy.cycle
  | skip :
    TailRecProcTyJudgement ProcTy.skip
  | dollar (pid : ProcId) :
    TailRecProcTyJudgement (ProcTy.dollar pid)
  | choice (τ₁ τ₂ : ProcTy) :
    TailRecProcTyJudgement τ₁ →
    TailRecProcTyJudgement τ₂ →
    TailRecProcTyJudgement (ProcTy.choice τ₁ τ₂)
  | choice_fair (bid : BranchId) (τ₁ τ₂ : ProcTy) :
    TailRecProcTyJudgement τ₁ →
    TailRecProcTyJudgement τ₂ →
    TailRecProcTyJudgement (ProcTy.choice_fair bid τ₁ τ₂)
  | par (τ₁ τ₂ : ProcTy) :
    TailRecProcTyJudgement τ₁ →
    TailRecProcTyJudgement τ₂ →
    TailRecProcTyJudgement (ProcTy.par τ₁ τ₂)
  | seq (τ₁ τ₂ : ProcTy) :
    TailRecProcTyJudgement τ₁ →
    TailRecProcTyJudgement τ₂ →
    TailRecProcTyJudgement (ProcTy.seq τ₁ τ₂)
  | xoffer (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    TailRecProcTyJudgement τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → TailRecProcTyJudgement ty) →
    TailRecProcTyJudgement (ProcTy.xoffer τ_else branch_tys)
  | offer (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    TailRecProcTyJudgement τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → TailRecProcTyJudgement ty) →
    TailRecProcTyJudgement (ProcTy.offer τ_else branch_tys)
  | recur (x : String) (body : ProcTy) :
    TailRecProcTyJudgement body →
    AtTail x body →
    TailRecProcTyJudgement (ProcTy.recur x body)

/-- One-step transition relation that forgets labels. -/
def ProcTyStep (τ τ' : ProcTy) : Prop :=
  ∃ lbl, ProcTyTransition τ lbl τ'

/-- Types reachable by zero or more transitions from `τ`. -/
def ReachableProcTys (τ : ProcTy) : Set ProcTy :=
  { τ' | Relation.ReflTransGen ProcTyStep τ τ' }

abbrev CarrierClosed (S : Finset ProcTy) : Prop :=
  ∀ {τ₁ τ₂ : ProcTy}, τ₁ ∈ S → ProcTyStep τ₁ τ₂ → τ₂ ∈ S

lemma carrierClosed_union
  [DecidableEq ProcTy]
  {S₁ S₂ : Finset ProcTy}
  (h₁ : CarrierClosed S₁)
  (h₂ : CarrierClosed S₂) :
  CarrierClosed (S₁ ∪ S₂) := by
  intro τ₁ τ₂ hmem hstep
  rcases Finset.mem_union.mp hmem with hIn₁ | hIn₂
  · exact Finset.mem_union.mpr (Or.inl (h₁ hIn₁ hstep))
  · exact Finset.mem_union.mpr (Or.inr (h₂ hIn₂ hstep))

lemma carrierClosed_insert
  [DecidableEq ProcTy]
  {S : Finset ProcTy}
  {root : ProcTy}
  (hRoot : ∀ {τ₂ : ProcTy}, ProcTyStep root τ₂ → τ₂ ∈ insert root S)
  (hS : CarrierClosed S) :
  CarrierClosed (insert root S) := by
  intro τ₁ τ₂ hmem hstep
  rcases Finset.mem_insert.mp hmem with hEq | hInS
  · subst hEq
    exact hRoot hstep
  · exact Finset.mem_insert.mpr (Or.inr (hS hInS hstep))

lemma combineBranchCarriers
  [DecidableEq ProcTy]
  (branch_tys : List (MessageExch × ProcTy))
  (hCarrier : ∀ m ty, (m, ty) ∈ branch_tys →
    ∃ S : Finset ProcTy, ty ∈ S ∧ CarrierClosed S) :
  ∃ S : Finset ProcTy,
    (∀ m ty, (m, ty) ∈ branch_tys → ty ∈ S) ∧ CarrierClosed S := by
  induction branch_tys with
  | nil =>
      refine ⟨∅, ?_, ?_⟩
      · intro m ty hmem
        cases hmem
      · intro τ₁ τ₂ hmem _
        cases hmem
  | cons hd tl ih =>
      rcases hd with ⟨m0, ty0⟩
      rcases hCarrier m0 ty0 (by simp) with ⟨S0, h0in, h0closed⟩
      have hTailCarrier : ∀ m ty, (m, ty) ∈ tl →
        ∃ S : Finset ProcTy, ty ∈ S ∧ CarrierClosed S := by
        intro m ty hmem
        exact hCarrier m ty (by simp [hmem])
      rcases ih hTailCarrier with ⟨Stl, htlMem, htlClosed⟩
      refine ⟨S0 ∪ Stl, ?_, carrierClosed_union h0closed htlClosed⟩
      intro m ty hmem
      rcases List.mem_cons.mp hmem with hHead | hTail
      · cases hHead
        exact Finset.mem_union.mpr (Or.inl h0in)
      · exact Finset.mem_union.mpr (Or.inr (htlMem m ty hTail))

lemma par_closed_carrier
  [DecidableEq ProcTy]
  {τ₁ τ₂ : ProcTy}
  (hC₁ : ∃ S₁ : Finset ProcTy, τ₁ ∈ S₁ ∧ CarrierClosed S₁)
  (hC₂ : ∃ S₂ : Finset ProcTy, τ₂ ∈ S₂ ∧ CarrierClosed S₂) :
  ∃ S : Finset ProcTy,
    ProcTy.par τ₁ τ₂ ∈ S ∧ CarrierClosed S := by
  rcases hC₁ with ⟨S₁, h₁in, h₁closed⟩
  rcases hC₂ with ⟨S₂, h₂in, h₂closed⟩
  let SPar : Finset ProcTy := (S₁.product S₂).image (fun p : ProcTy × ProcTy => ProcTy.par p.1 p.2)
  refine ⟨(SPar ∪ S₁) ∪ S₂, ?_, ?_⟩
  · refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ?_)))
    refine Finset.mem_image.mpr ?_
    exact ⟨(τ₁, τ₂), Finset.mem_product.mpr ⟨h₁in, h₂in⟩, rfl⟩
  · intro σ σ' hmem hstep
    rcases Finset.mem_union.mp hmem with hInLeft | hIn₂
    · rcases Finset.mem_union.mp hInLeft with hInPar | hIn₁
      · rcases Finset.mem_image.mp hInPar with ⟨p, hpProd, hpEq⟩
        rcases Finset.mem_product.mp hpProd with ⟨hIn₁, hIn₂⟩
        rcases p with ⟨a, b⟩
        simp at hpEq
        subst hpEq
        rcases hstep with ⟨lbl, htr⟩
        cases htr with
        | par_left _ a' _ _ _ _ hsub =>
            have hA' : a' ∈ S₁ := h₁closed hIn₁ ⟨_, hsub⟩
            refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ?_)))
            refine Finset.mem_image.mpr ?_
            exact ⟨(a', b), Finset.mem_product.mpr ⟨hA', hIn₂⟩, rfl⟩
        | par_right _ _ b' _ _ _ hsub =>
            have hB' : b' ∈ S₂ := h₂closed hIn₂ ⟨_, hsub⟩
            refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ?_)))
            refine Finset.mem_image.mpr ?_
            exact ⟨(a, b'), Finset.mem_product.mpr ⟨hIn₁, hB'⟩, rfl⟩
        | par_left_ex _ _ a' _ _ hsub =>
            have hA' : a' ∈ S₁ := h₁closed hIn₁ ⟨_, hsub⟩
            refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ?_)))
            refine Finset.mem_image.mpr ?_
            exact ⟨(a', b), Finset.mem_product.mpr ⟨hA', hIn₂⟩, rfl⟩
        | par_right_ex _ _ _ b' _ hsub =>
            have hB' : b' ∈ S₂ := h₂closed hIn₂ ⟨_, hsub⟩
            refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ?_)))
            refine Finset.mem_image.mpr ?_
            exact ⟨(a, b'), Finset.mem_product.mpr ⟨hIn₁, hB'⟩, rfl⟩
        | par_tock _ _ a' b' hsub₁ hsub₂ =>
            have hA' : a' ∈ S₁ := h₁closed hIn₁ ⟨_, hsub₁⟩
            have hB' : b' ∈ S₂ := h₂closed hIn₂ ⟨_, hsub₂⟩
            refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ?_)))
            refine Finset.mem_image.mpr ?_
            exact ⟨(a', b'), Finset.mem_product.mpr ⟨hA', hB'⟩, rfl⟩
        | par_message _ _ a' b' _ _ _ _ hsub₁ hsub₂ =>
            have hA' : a' ∈ S₁ := h₁closed hIn₁ ⟨_, hsub₁⟩
            have hB' : b' ∈ S₂ := h₂closed hIn₂ ⟨_, hsub₂⟩
            refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ?_)))
            refine Finset.mem_image.mpr ?_
            exact ⟨(a', b'), Finset.mem_product.mpr ⟨hA', hB'⟩, rfl⟩
        | par_skip_left _ =>
            exact Finset.mem_union.mpr (Or.inr hIn₂)
        | par_skip_right _ =>
            exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hIn₁)))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (h₁closed hIn₁ hstep))))
    · exact Finset.mem_union.mpr (Or.inr (h₂closed hIn₂ hstep))

lemma seq_closed_carrier
  [DecidableEq ProcTy]
  {τ₁ τ₂ : ProcTy}
  (hC₁ : ∃ S₁ : Finset ProcTy, τ₁ ∈ S₁ ∧ CarrierClosed S₁)
  (hC₂ : ∃ S₂ : Finset ProcTy, τ₂ ∈ S₂ ∧ CarrierClosed S₂) :
  ∃ S : Finset ProcTy,
    ProcTy.seq τ₁ τ₂ ∈ S ∧ CarrierClosed S := by
  rcases hC₁ with ⟨S₁, h₁in, h₁closed⟩
  rcases hC₂ with ⟨S₂, h₂in, h₂closed⟩
  let SSeq : Finset ProcTy := S₁.image (fun a : ProcTy => ProcTy.seq a τ₂)
  refine ⟨SSeq ∪ S₂, ?_, ?_⟩
  · refine Finset.mem_union.mpr (Or.inl ?_)
    refine Finset.mem_image.mpr ?_
    exact ⟨τ₁, h₁in, rfl⟩
  · intro σ σ' hmem hstep
    rcases Finset.mem_union.mp hmem with hInSeq | hIn₂
    · rcases Finset.mem_image.mp hInSeq with ⟨a, hIn₁, hEq⟩
      subst hEq
      rcases hstep with ⟨lbl, htr⟩
      cases htr with
      | seq_step _ a' _ _ hsub =>
          have hA' : a' ∈ S₁ := h₁closed hIn₁ ⟨_, hsub⟩
          refine Finset.mem_union.mpr (Or.inl ?_)
          refine Finset.mem_image.mpr ?_
          exact ⟨a', hA', rfl⟩
      | seq_done _ =>
          exact Finset.mem_union.mpr (Or.inr h₂in)
    · exact Finset.mem_union.mpr (Or.inr (h₂closed hIn₂ hstep))

lemma choice_closed_carrier
  [DecidableEq ProcTy]
  {τ₁ τ₂ : ProcTy}
  (hC₁ : ∃ S₁ : Finset ProcTy, τ₁ ∈ S₁ ∧ CarrierClosed S₁)
  (hC₂ : ∃ S₂ : Finset ProcTy, τ₂ ∈ S₂ ∧ CarrierClosed S₂) :
  ∃ S : Finset ProcTy,
    ProcTy.choice τ₁ τ₂ ∈ S ∧ CarrierClosed S := by
  rcases hC₁ with ⟨S₁, h₁in, h₁closed⟩
  rcases hC₂ with ⟨S₂, h₂in, h₂closed⟩
  refine ⟨insert (ProcTy.choice τ₁ τ₂) (S₁ ∪ S₂), by simp, ?_⟩
  apply carrierClosed_insert
  · intro τ' hstep
    rcases hstep with ⟨lbl, htr⟩
    cases htr with
    | choice_left =>
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inl h₁in)))
    | choice_right =>
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inr h₂in)))
  · exact carrierClosed_union h₁closed h₂closed

lemma choiceFair_closed_carrier
  [DecidableEq ProcTy]
  {bid : BranchId}
  {τ₁ τ₂ : ProcTy}
  (hC₁ : ∃ S₁ : Finset ProcTy, τ₁ ∈ S₁ ∧ CarrierClosed S₁)
  (hC₂ : ∃ S₂ : Finset ProcTy, τ₂ ∈ S₂ ∧ CarrierClosed S₂) :
  ∃ S : Finset ProcTy,
    ProcTy.choice_fair bid τ₁ τ₂ ∈ S ∧ CarrierClosed S := by
  rcases hC₁ with ⟨S₁, h₁in, h₁closed⟩
  rcases hC₂ with ⟨S₂, h₂in, h₂closed⟩
  refine ⟨insert (ProcTy.choice_fair bid τ₁ τ₂) (S₁ ∪ S₂), by simp, ?_⟩
  apply carrierClosed_insert
  · intro τ' hstep
    rcases hstep with ⟨lbl, htr⟩
    cases htr with
    | choice_fair_left =>
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inl h₁in)))
    | choice_fair_right =>
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inr h₂in)))
  · exact carrierClosed_union h₁closed h₂closed

lemma xoffer_closed_carrier
  [DecidableEq ProcTy]
  {τ_else : ProcTy}
  {branch_tys : List (MessageExch × ProcTy)}
  (hElse : ∃ Selse : Finset ProcTy, τ_else ∈ Selse ∧ CarrierClosed Selse)
  (hBranches : ∀ m ty, (m, ty) ∈ branch_tys →
    ∃ S : Finset ProcTy, ty ∈ S ∧ CarrierClosed S) :
  ∃ S : Finset ProcTy,
    ProcTy.xoffer τ_else branch_tys ∈ S ∧ CarrierClosed S := by
  rcases hElse with ⟨Selse, hElseIn, hElseClosed⟩
  rcases combineBranchCarriers branch_tys hBranches with ⟨Sbr, hBrIn, hBrClosed⟩
  refine ⟨insert (ProcTy.xoffer τ_else branch_tys) (Selse ∪ Sbr), by simp, ?_⟩
  apply carrierClosed_insert
  · intro τ' hstep
    rcases hstep with ⟨lbl, htr⟩
    cases htr <;> aesop
  · exact carrierClosed_union hElseClosed hBrClosed

lemma replaceBranches_eq_of
  {x : String}
  {τ' : ProcTy}
  {branch_tys : List (MessageExch × ProcTy)}
  (h : ∀ m ty, (m, ty) ∈ branch_tys → ty.replaceVar x τ' = ty) :
  ProcTy.replaceBranches branch_tys x τ' = branch_tys := by
  induction branch_tys with
  | nil =>
    simp [ProcTy.replaceBranches]
  | cons hd tl ih =>
    rcases hd with ⟨m0, ty0⟩
    have hHead : ty0.replaceVar x τ' = ty0 := h m0 ty0 (by simp)
    have hTail : ∀ m ty, (m, ty) ∈ tl → ty.replaceVar x τ' = ty := by
      intro m ty hmem
      exact h m ty (by simp [hmem])
    simp [ProcTy.replaceBranches, hHead, ih hTail]

lemma absent_replaceVar_eq
  {x : String}
  {τ : ProcTy}
  (hAbs : AbsentIn x τ)
  (τ' : ProcTy) :
  τ.replaceVar x τ' = τ := by
  induction hAbs generalizing τ' with
  | var x' hneq =>
    simp [ProcTy.replaceVar, if_neg hneq]
  | message =>
    simp [ProcTy.replaceVar]
  | cycle =>
    simp [ProcTy.replaceVar]
  | skip =>
    simp [ProcTy.replaceVar]
  | dollar =>
    simp [ProcTy.replaceVar]
  | choice τ₁ τ₂ h₁ h₂ ih₁ ih₂ =>
    simp [ProcTy.replaceVar, ih₁ τ', ih₂ τ']
  | choice_fair bid τ₁ τ₂ h₁ h₂ ih₁ ih₂ =>
    simp [ProcTy.replaceVar, ih₁ τ', ih₂ τ']
  | par τ₁ τ₂ h₁ h₂ ih₁ ih₂ =>
    simp [ProcTy.replaceVar, ih₁ τ', ih₂ τ']
  | seq τ₁ τ₂ h₁ h₂ ih₁ ih₂ =>
    simp [ProcTy.replaceVar, ih₁ τ', ih₂ τ']
  | xoffer τ_else branch_tys hElse hBr ihElse ihBr =>
    simp [ProcTy.replaceVar, ihElse τ', replaceBranches_eq_of (x := x) (τ' := τ')
      (fun m ty hmem => ihBr m ty hmem τ')]
  | offer τ_else branch_tys hElse hBr ihElse ihBr =>
    simp [ProcTy.replaceVar, ihElse τ', replaceBranches_eq_of (x := x) (τ' := τ')
      (fun m ty hmem => ihBr m ty hmem τ')]
  | recur x' body hneq hBody ihBody =>
    simp [ProcTy.replaceVar, ihBody τ']

lemma attail_replaceVar_eq
  {x : String}
  {τ : ProcTy}
  (hTail : AtTail x τ)
  (τ' : ProcTy) :
  τ.replaceVar x τ' = τ := by
  induction hTail generalizing τ' with
  | absent τ hAbs =>
    exact absent_replaceVar_eq hAbs τ'
  | seq τ₁ τ₂ hAbs hTail ihTail =>
    simp [ProcTy.replaceVar, absent_replaceVar_eq hAbs τ', ihTail τ']
  | choice τ₁ τ₂ h₁ h₂ ih₁ ih₂ =>
    simp [ProcTy.replaceVar, ih₁ τ', ih₂ τ']
  | choice_fair bid τ₁ τ₂ h₁ h₂ ih₁ ih₂ =>
    simp [ProcTy.replaceVar, ih₁ τ', ih₂ τ']
  | xoffer τ_else branch_tys hElse hBr ihElse ihBr =>
    simp [ProcTy.replaceVar, ihElse τ', replaceBranches_eq_of (x := x) (τ' := τ')
      (fun m ty hmem => ihBr m ty hmem τ')]
  | offer τ_else branch_tys hElse hBr ihElse ihBr =>
    simp [ProcTy.replaceVar, ihElse τ', replaceBranches_eq_of (x := x) (τ' := τ')
      (fun m ty hmem => ihBr m ty hmem τ')]
  | recur x' body hneq hBody ihBody =>
    simp [ProcTy.replaceVar, ihBody τ']

/--
Helper lemma (left unproved):
from a tail-recursive type, we can build a finite carrier closed under one-step transitions.
-/
axiom tailrec_closed_carrier
  (τ : ProcTy)
  (hTail : TailRecProcTyJudgement τ) :
  ∃ S : Finset ProcTy,
    τ ∈ S ∧
    (∀ {τ₁ τ₂ : ProcTy}, τ₁ ∈ S → ProcTyStep τ₁ τ₂ → τ₂ ∈ S)

/--
Helper lemma (left unproved):
if a finite set is closed under one-step transitions and contains the start,
then every reachable state is in that set.
-/
lemma reachable_subset_of_closed_carrier
  {τ : ProcTy}
  {S : Finset ProcTy}
  (hStart : τ ∈ S)
  (hClosed : ∀ {τ₁ τ₂ : ProcTy}, τ₁ ∈ S → ProcTyStep τ₁ τ₂ → τ₂ ∈ S) :
  ReachableProcTys τ ⊆ (↑S : Set ProcTy) := by
  intro τ' hReach
  induction hReach with
  | refl =>
      exact hStart
  | tail _ hStep hIH =>
    exact hClosed hIH hStep

/--
If a process type has only tail recursions, then its reachable set of process types is finite.
-/
theorem reachable_finite_of_tailrec
  (τ : ProcTy)
  (hTail : TailRecProcTyJudgement τ) :
  ∃ S : Finset ProcTy, ∀ τ', ReachableProcTys τ τ' → τ' ∈ S := by
  obtain ⟨S, hStart, hClosed⟩ := tailrec_closed_carrier τ hTail
  have hSubset : ReachableProcTys τ ⊆ (↑S : Set ProcTy) :=
    reachable_subset_of_closed_carrier hStart hClosed
  refine ⟨S, ?_⟩
  intro τ' hReach
  exact hSubset hReach
