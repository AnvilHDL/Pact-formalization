import Anvilpp.ProofHelpers.Inference.AlphabetInvariant

/-!
# The conjunctive commitment under abstraction

`abs(C^P_(B,a_j)) = C_(abs_B(B),Msg(a_j))`.  The paper's `C_(B,a_j)` commits at
the position of `a_j` and copies each continuation; the Lean builders locate the
committed branch by value and re-sign each continuation, so the equation reads
the two premises the paper carries on `B`: `conjunctCompatible` (every
continuation already carries the offer's alphabet) and `ConjMsgOwn` (the branch
heads are pairwise distinct).
-/

namespace Pact

noncomputable section

open Classical

/-- `ConjMsgOwn` reduced to what the commitment reads: distinct branch heads. -/
def BranchHeadsDistinct (branches : List ChoiceBranch) : Prop :=
  branches.Pairwise fun left right =>
    ChoiceBranch.action left ≠ ChoiceBranch.action right

theorem BranchHeadsDistinct.eq_of_action_eq :
    ∀ {branches : List ChoiceBranch}, BranchHeadsDistinct branches →
      ∀ {left right : ChoiceBranch}, left ∈ branches → right ∈ branches →
        ChoiceBranch.action left = ChoiceBranch.action right → left = right := by
  intro branches
  induction branches with
  | nil => intro _ _ _ hLeft; exact absurd hLeft (by simp)
  | cons head rest ih =>
      intro hDistinct left right hLeft hRight hAction
      rw [BranchHeadsDistinct, List.pairwise_cons] at hDistinct
      rcases List.mem_cons.1 hLeft with rfl | hLeft'
      · rcases List.mem_cons.1 hRight with rfl | hRight'
        · rfl
        · exact absurd hAction (hDistinct.1 right hRight')
      · rcases List.mem_cons.1 hRight with rfl | hRight'
        · exact absurd hAction.symm (hDistinct.1 left hLeft')
        · exact ih hDistinct.2 hLeft' hRight' hAction

theorem BranchHeadsDistinct.tail {branch : ChoiceBranch}
    {rest : List ChoiceBranch} (h : BranchHeadsDistinct (branch :: rest)) :
    BranchHeadsDistinct rest := (List.pairwise_cons.1 h).2

theorem BranchHeadsDistinct.head_ne {branch selected : ChoiceBranch}
    {rest : List ChoiceBranch} (h : BranchHeadsDistinct (branch :: rest))
    (hMem : selected ∈ rest) :
    ChoiceBranch.action branch ≠ ChoiceBranch.action selected :=
  (List.pairwise_cons.1 h).1 selected hMem

/-! ## The generated components -/

@[simp] theorem inferProcess_skip (alphabet : PactTypeAlphabet) :
    inferProcess (Proc.skip alphabet) = .skip alphabet := by rw [inferProcess]

theorem inferBranches_cons (branch : ChoiceBranch) (rest : List ChoiceBranch) :
    inferBranches (branch :: rest) = inferBranch branch :: inferBranches rest :=
  inferBranches_action branch rest

/-! ### Equations for the product builders -/

theorem parallelProcessBranchesWithin_cons_cons (alphabet : PactTypeAlphabet)
    (first second : ChoiceBranch) (rest : List ChoiceBranch) :
    parallelProcessBranchesWithin alphabet (first :: second :: rest) =
      Proc.par alphabet (ChoiceBranch.toXOffer alphabet first)
        (parallelProcessBranchesWithin alphabet (second :: rest)) ∅ := by
  rw [parallelProcessBranchesWithin]
  simp

theorem parallelTypeBranchesWithin_cons_cons (alphabet : PactTypeAlphabet)
    (first second : BareMessage × PactType) (rest : List (BareMessage × PactType)) :
    parallelTypeBranchesWithin alphabet (first :: second :: rest) =
      .par alphabet (singletonTypeXOfferAt alphabet first)
        (parallelTypeBranchesWithin alphabet (second :: rest)) ∅ := by
  rw [parallelTypeBranchesWithin]
  simp

theorem parallelProcessBranchesSelectingWithin_cons_cons
    (alphabet : PactTypeAlphabet) (selected first second : ChoiceBranch)
    (rest : List ChoiceBranch) :
    parallelProcessBranchesSelectingWithin alphabet selected
        (first :: second :: rest) =
      if first = selected then
        Proc.par alphabet (selectedProcessBranchAt alphabet first)
          (parallelProcessBranchesWithin alphabet (second :: rest)) ∅
      else
        Proc.par alphabet (ChoiceBranch.toXOffer alphabet first)
          (parallelProcessBranchesSelectingWithin alphabet selected
            (second :: rest)) ∅ := by
  rw [parallelProcessBranchesSelectingWithin]
  simp

theorem parallelTypeBranchesSelectingWithin_cons_cons
    (alphabet : PactTypeAlphabet) (selected first second : BareMessage × PactType)
    (rest : List (BareMessage × PactType)) :
    parallelTypeBranchesSelectingWithin alphabet selected
        (first :: second :: rest) =
      if first = selected then
        .par alphabet (selectedTypeBranchAt alphabet first)
          (parallelTypeBranchesWithin alphabet (second :: rest)) ∅
      else
        .par alphabet (singletonTypeXOfferAt alphabet first)
          (parallelTypeBranchesSelectingWithin alphabet selected
            (second :: rest)) ∅ := by
  rw [parallelTypeBranchesSelectingWithin]
  simp

theorem inferProcess_toXOffer {alphabet : PactTypeAlphabet}
    {branch : ChoiceBranch}
    (hAlpha : (ChoiceBranch.continuation branch).alphabet = alphabet)
    (hWF : Proc.AlphabetWellFormed (ChoiceBranch.continuation branch)) :
    inferProcess (ChoiceBranch.toXOffer alphabet branch) =
      singletonTypeXOfferAt alphabet (inferBranch branch) := by
  rw [ChoiceBranch.toXOffer, inferProcess, singletonTypeXOfferAt,
    inferBranches_cons, inferBranches, inferProcess_skip]
  simp only [inferBranch, PactType.reannotate_inferProcess_eq_self hWF hAlpha]

theorem inferProcess_selectedProcessBranchAt {alphabet : PactTypeAlphabet}
    {branch : ChoiceBranch}
    (hAlpha : (ChoiceBranch.continuation branch).alphabet = alphabet)
    (hWF : Proc.AlphabetWellFormed (ChoiceBranch.continuation branch)) :
    inferProcess (selectedProcessBranchAt alphabet branch) =
      selectedTypeBranchAt alphabet (inferBranch branch) := by
  cases branch with
  | send msg expr process =>
      simp only [ChoiceBranch.continuation] at hAlpha hWF
      rw [selectedProcessBranchAt, inferProcess, selectedTypeBranchAt]
      simp only [inferBranch, ChoiceBranch.action, ChoiceBranch.getMessageId,
        ChoiceBranch.getDir, ChoiceBranch.continuation,
        PactType.reannotate_inferProcess_eq_self hWF hAlpha]
  | recv msg varName process =>
      simp only [ChoiceBranch.continuation] at hAlpha hWF
      rw [selectedProcessBranchAt, inferProcess, selectedTypeBranchAt]
      simp only [inferBranch, ChoiceBranch.action, ChoiceBranch.getMessageId,
        ChoiceBranch.getDir, ChoiceBranch.continuation,
        PactType.reannotate_inferProcess_eq_self hWF hAlpha]

theorem inferProcess_parallelProcessBranchesWithin {alphabet : PactTypeAlphabet} :
    ∀ branches : List ChoiceBranch,
      Proc.BranchesAlphabetWellFormed alphabet branches →
      inferProcess (parallelProcessBranchesWithin alphabet branches) =
        parallelTypeBranchesWithin alphabet (inferBranches branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _
      rw [parallelProcessBranchesWithin, inferProcess_skip, inferBranches,
        parallelTypeBranchesWithin]
  | cons head rest ih =>
      intro hWF
      rw [Proc.BranchesAlphabetWellFormed] at hWF
      cases rest with
      | nil =>
          rw [parallelProcessBranchesWithin, inferProcess_toXOffer hWF.1 hWF.2.1,
            inferBranches_cons, inferBranches, parallelTypeBranchesWithin]
      | cons second tail =>
          rw [parallelProcessBranchesWithin_cons_cons, inferProcess,
            inferProcess_toXOffer hWF.1 hWF.2.1, ih hWF.2.2,
            inferBranches_cons head, inferBranches_cons second,
            parallelTypeBranchesWithin_cons_cons, ← inferBranches_cons second]

/-! ## The commitment -/

theorem inferProcess_parallelProcessBranchesSelectingWithin
    {alphabet : PactTypeAlphabet} {selected : ChoiceBranch} :
    ∀ branches : List ChoiceBranch,
      Proc.BranchesAlphabetWellFormed alphabet branches →
      BranchHeadsDistinct branches → selected ∈ branches →
      inferProcess
          (parallelProcessBranchesSelectingWithin alphabet selected branches) =
        parallelTypeBranchesSelectingWithin alphabet (inferBranch selected)
          (inferBranches branches) := by
  intro branches
  induction branches with
  | nil => intro _ _ hMem; exact absurd hMem (by simp)
  | cons head rest ih =>
      intro hWF hDistinct hMem
      rw [Proc.BranchesAlphabetWellFormed] at hWF
      by_cases hEq : head = selected
      · subst hEq
        cases rest with
        | nil =>
            rw [parallelProcessBranchesSelectingWithin, if_pos rfl,
              inferProcess_selectedProcessBranchAt hWF.1 hWF.2.1,
              inferBranches_cons, inferBranches,
              parallelTypeBranchesSelectingWithin, if_pos rfl]
        | cons second tail =>
            rw [parallelProcessBranchesSelectingWithin_cons_cons, if_pos rfl,
              inferProcess,
              inferProcess_selectedProcessBranchAt hWF.1 hWF.2.1,
              inferProcess_parallelProcessBranchesWithin _ hWF.2.2,
              inferBranches_cons head, inferBranches_cons second,
              parallelTypeBranchesSelectingWithin_cons_cons, if_pos rfl,
              ← inferBranches_cons second]
      · have hSelectedMem : selected ∈ rest := by
          rcases List.mem_cons.1 hMem with rfl | h
          · exact absurd rfl hEq
          · exact h
        have hHeadNe : inferBranch head ≠ inferBranch selected := by
          intro hAbsurd
          exact hDistinct.head_ne hSelectedMem (congrArg Prod.fst hAbsurd)
        cases rest with
        | nil => exact absurd hSelectedMem (by simp)
        | cons second tail =>
            rw [parallelProcessBranchesSelectingWithin_cons_cons, if_neg hEq,
              inferProcess, inferProcess_toXOffer hWF.1 hWF.2.1,
              ih hWF.2.2 hDistinct.tail hSelectedMem,
              inferBranches_cons head, inferBranches_cons second,
              parallelTypeBranchesSelectingWithin_cons_cons, if_neg hHeadNe,
              ← inferBranches_cons second]

/-- `abs(C^P_(B,a_j)) = C_(abs_B(B),Msg(a_j))`. -/
theorem inferProcess_parallelProcessBranchesSelecting
    {alphabet : PactTypeAlphabet} {selected : ChoiceBranch}
    {branches : List ChoiceBranch}
    (hWF : Proc.BranchesAlphabetWellFormed alphabet branches)
    (hDistinct : BranchHeadsDistinct branches) (hMem : selected ∈ branches) :
    inferProcess (parallelProcessBranchesSelecting alphabet selected branches) =
      parallelTypeBranchesSelecting alphabet (inferBranch selected)
        (inferBranches branches) := by
  cases branches with
  | nil => exact absurd hMem (by simp)
  | cons head rest =>
      rw [parallelProcessBranchesSelecting, inferBranches_cons,
        parallelTypeBranchesSelecting, ← inferBranches_cons]
      exact inferProcess_parallelProcessBranchesSelectingWithin _ hWF hDistinct hMem

/-! ## `ConjMsgOwn` as a structural side condition -/

mutual
  /-- Every conjunctive offer has pairwise distinct branch heads. -/
  def Proc.ConjunctRegular : Proc → Prop
    | .send _ _ _ p | .recv _ _ _ p | .letp _ _ _ p | .recur _ _ p =>
        Proc.ConjunctRegular p
    | .var _ _ | .skip _ | .endp _ _ | .cycle _ => True
    | .par _ left right _ | .seq _ left right | .ifunfair _ _ left right
    | .iffair _ _ _ left right =>
        Proc.ConjunctRegular left ∧ Proc.ConjunctRegular right
    | .xoffer _ elseProcess branches =>
        Proc.ConjunctRegular elseProcess ∧ Proc.ConjunctRegularBranches branches
    | .offer _ elseProcess branches =>
        BranchHeadsDistinct branches ∧ Proc.ConjunctRegular elseProcess ∧
          Proc.ConjunctRegularBranches branches
  termination_by process => sizeOf process

  def Proc.ConjunctRegularBranches : List ChoiceBranch → Prop
    | [] => True
    | branch :: rest =>
        Proc.ConjunctRegular (ChoiceBranch.continuation branch) ∧
          Proc.ConjunctRegularBranches rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    first
    | (simp_wf; omega)
    | (have hBranch := ChoiceBranch.continuation_sizeOf_lt branch
       simp_wf
       omega)
end

theorem Proc.conjunctRegular_of_mem_branches {branches : List ChoiceBranch}
    {branch : ChoiceBranch}
    (hRegular : Proc.ConjunctRegularBranches branches) (hMem : branch ∈ branches) :
    Proc.ConjunctRegular (ChoiceBranch.continuation branch) := by
  induction branches with
  | nil => exact absurd hMem (by simp)
  | cons head rest ih =>
      rw [Proc.ConjunctRegularBranches] at hRegular
      rcases List.mem_cons.1 hMem with rfl | hTail
      · exact hRegular.1
      · exact ih hRegular.2 hTail

end

end Pact
