import Anvilpp.PactTypes.Syntax.TypeErasure

/-!
# Type-level offer/branch helper definitions
-/

namespace Pact

noncomputable section

/-! ## Type dynamics and semantic correspondence -/

/-- The complementary environment action needed to fire a type action. -/
def typeNeed (action : BareMessage) : BareMessage :=
  (action.1, action.2.invert)

def typeBranchNeeds (branches : List (BareMessage × PactType)) :
    Finset BareMessage :=
  (branches.map fun branch => typeNeed branch.1).toFinset

def TypeResolved (env : TypeEnvironment)
    (branches : List (BareMessage × PactType)) : Prop :=
  typeBranchNeeds branches ∩ env.future = ∅

def TypeNoImmediateBranch (env : TypeEnvironment)
    (branches : List (BareMessage × PactType)) : Prop :=
  typeBranchNeeds branches ∩ env.immediate = ∅

def TypeBranchEnabled (env : TypeEnvironment)
    (branch : BareMessage × PactType) : Prop :=
  typeNeed branch.1 ∈ env.immediate

end
end Pact

-- Declared outside `namespace Pact` so these land on the global
-- `PactTypeAlphabet` (`Proc.lean`), not a separate `Pact.PactTypeAlphabet`.
noncomputable section
namespace PactTypeAlphabet

  /-- The part of `parent` used by one conjunctive-offer branch. -/
  def branchPart (parent : PactTypeAlphabet)
      (branch : Pact.BareMessage × Pact.PactType) : PactTypeAlphabet :=
    { actions := parent.actions ∩
        ({branch.1} ∪ Pact.PactType.MessageActions branch.2)
      progress := parent.progress ∩ Pact.PactType.ProgressIds branch.2
      fair := parent.fair ∩ Pact.PactType.FairChoiceIds branch.2 }

  /-- The declarations left after assigning one component of an internal
  parallel product. -/
  def remove (parent assigned : PactTypeAlphabet) : PactTypeAlphabet :=
    { actions := parent.actions \ assigned.actions
      progress := parent.progress \ assigned.progress
      fair := parent.fair \ assigned.fair }

  /-- Assigning one branch its part and the tail the remainder reconstructs
  the enclosing alphabet.  The generated product has an empty interface, so
  no action is hidden at this internal parallel node. -/
  theorem mergeHidden_branchPart_remove_empty
      (parent : PactTypeAlphabet) (branch : Pact.BareMessage × Pact.PactType) :
      parent = mergeHidden (branchPart parent branch)
        (remove parent (branchPart parent branch)) ∅ := by
    rcases parent with ⟨actions, progress, fair⟩
    simp [mergeHidden, branchPart, remove]
    constructor
    · calc
        actions = actions \ (insert branch.1 branch.2.MessageActions) ∪
            actions ∩ (insert branch.1 branch.2.MessageActions) :=
          (Finset.sdiff_union_inter actions
            (insert branch.1 branch.2.MessageActions)).symm
        _ = actions ∩ (insert branch.1 branch.2.MessageActions) ∪
            actions \ (insert branch.1 branch.2.MessageActions) :=
          Finset.union_comm _ _
    constructor
    · calc
        progress = progress \ branch.2.ProgressIds ∪
            progress ∩ branch.2.ProgressIds :=
          (Finset.sdiff_union_inter progress branch.2.ProgressIds).symm
        _ = progress ∩ branch.2.ProgressIds ∪
            progress \ branch.2.ProgressIds := Finset.union_comm _ _
    · calc
        fair = fair \ branch.2.FairChoiceIds ∪
            fair ∩ branch.2.FairChoiceIds :=
          (Finset.sdiff_union_inter fair branch.2.FairChoiceIds).symm
        _ = fair ∩ branch.2.FairChoiceIds ∪
            fair \ branch.2.FairChoiceIds := Finset.union_comm _ _

  /-- Splitting `parent` into one branch's part and the remainder gives two
  parallel-compatible alphabets, with the empty interface (no synchronization
  at this internal, compiler-generated parallel node). -/
  theorem branchPart_remove_parallelCompatible
      (parent : PactTypeAlphabet) (hParentWF : parent.WellFormed)
      (branch : Pact.BareMessage × Pact.PactType) :
      ParallelCompatible parent (branchPart parent branch)
        (remove parent (branchPart parent branch)) ∅ := by
    have hActionsDisjoint : Disjoint (branchPart parent branch).actions
        (remove parent (branchPart parent branch)).actions := by
      simp only [branchPart, remove]
      exact (Finset.disjoint_sdiff_inter _ _).symm.mono_right (by simp)
    have hMessageIdsDisjoint : Disjoint (branchPart parent branch).messageIds
        (remove parent (branchPart parent branch)).messageIds := by
      rw [Finset.disjoint_left]
      rintro msgId hLeft hRight
      simp only [PactTypeAlphabet.messageIds, Finset.mem_image] at hLeft hRight
      obtain ⟨⟨lMsg, lDir⟩, hLeftAction, hLeftEq⟩ := hLeft
      obtain ⟨⟨rMsg, rDir⟩, hRightAction, hRightEq⟩ := hRight
      simp only at hLeftEq hRightEq
      rw [← hLeftEq] at hRightEq
      simp only [branchPart, remove, Finset.mem_inter, Finset.mem_sdiff]
        at hLeftAction hRightAction
      rw [hRightEq] at hRightAction
      rcases lDir with _ | _ <;> rcases rDir with _ | _
      · exact hRightAction.2 hLeftAction
      · exact hParentWF lMsg ⟨hLeftAction.1, hRightAction.1⟩
      · exact hParentWF lMsg ⟨hRightAction.1, hLeftAction.1⟩
      · exact hRightAction.2 hLeftAction
    exact
      { parent_eq := mergeHidden_branchPart_remove_empty parent branch
        shared_messageIds := by
          rw [Finset.disjoint_iff_inter_eq_empty] at hMessageIdsDisjoint
          simpa using hMessageIdsDisjoint
        boundary_messageIds_disjoint := by
          simpa [BoundaryMessageIdsDisjoint] using hMessageIdsDisjoint
        actions_disjoint := hActionsDisjoint
        complementary := by simp [ComplementaryOn]
        progress_disjoint := by
          simp only [branchPart, remove]
          exact (Finset.disjoint_sdiff_inter _ _).symm.mono_right (by simp)
        fair_disjoint := by
          simp only [branchPart, remove]
          exact (Finset.disjoint_sdiff_inter _ _).symm.mono_right (by simp) }

  /-- Project a new parallel boundary alphabet to one of the old children.
  Interface actions remain local to the child even though they are hidden at
  the parent boundary. -/
  def projectParallelChild (parent child : PactTypeAlphabet)
      (interface : Pact.Interface) : PactTypeAlphabet :=
    { actions := child.actions.filter fun action =>
        action.1 ∈ interface ∨ action ∈ parent.actions
      progress := child.progress ∩ parent.progress
      fair := child.fair ∩ parent.fair }

  /-- Project a new parallel alphabet to the left child.  Declarations that
  are new to the reannotated parallel node are assigned to the left child, so
  the two projected children still reconstruct the whole parent alphabet. -/
  def projectParallelLeft (parent left right : PactTypeAlphabet)
      (interface : Pact.Interface) : PactTypeAlphabet :=
    let rightPart := projectParallelChild parent right interface
    { actions :=
        (left.actions.filter fun action => action.1 ∈ interface) ∪
          (parent.actions \ rightPart.actions)
      progress := parent.progress \ rightPart.progress
      fair := parent.fair \ rightPart.fair }

end PactTypeAlphabet
end

namespace Pact
noncomputable section

namespace PactType

  /- Change the fixed alphabet of a type without changing its type
  operators.  Non-parallel descendants receive the same alphabet.  At a
  parallel node, the new boundary alphabet is projected to the two children;
  their interface actions are retained. -/
  mutual
    def reannotate (alphabet : PactTypeAlphabet) : PactType → PactType
      | .message _ msg dir => .message alphabet msg dir
      | .progress _ pid => .progress alphabet pid
      | .tock _ => .tock alphabet
      | .skip _ => .skip alphabet
      | .choice _ left right =>
          .choice alphabet (reannotate alphabet left)
            (reannotate alphabet right)
      | .seq _ left right =>
          .seq alphabet (reannotate alphabet left)
            (reannotate alphabet right)
      | .par _ left right interface =>
          let leftAlphabet := PactTypeAlphabet.projectParallelLeft alphabet
            left.alphabet right.alphabet interface
          let rightAlphabet := PactTypeAlphabet.projectParallelChild alphabet
            right.alphabet interface
          .par alphabet (reannotate leftAlphabet left)
            (reannotate rightAlphabet right) interface
      | .var _ name => .var alphabet name
      | .recur _ name body => .recur alphabet name (reannotate alphabet body)
      | .fairChoice _ bid left right =>
          .fairChoice alphabet bid (reannotate alphabet left)
            (reannotate alphabet right)
      | .xoffer _ elseType branches =>
          .xoffer alphabet (reannotate alphabet elseType)
            (reannotateBranches alphabet branches)
      | .offer _ elseType branches =>
          .offer alphabet (reannotate alphabet elseType)
            (reannotateBranches alphabet branches)
    termination_by processType => sizeOf processType

    def reannotateBranches (alphabet : PactTypeAlphabet) :
        List (BareMessage × PactType) → List (BareMessage × PactType)
      | [] => []
      | (action, processType) :: rest =>
          (action, reannotate alphabet processType) ::
            reannotateBranches alphabet rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  @[simp] theorem reannotate_alphabet
      (alphabet : PactTypeAlphabet) (processType : PactType) :
      (reannotate alphabet processType).alphabet = alphabet := by
    cases processType <;> simp [reannotate, PactType.alphabet]

  @[simp] theorem reannotateBranches_nil
      (alphabet : PactTypeAlphabet) :
      reannotateBranches alphabet [] = [] := by
    rw [reannotateBranches.eq_def]

  @[simp] theorem reannotateBranches_cons
      (alphabet : PactTypeAlphabet) (action : BareMessage)
      (processType : PactType) (rest : List (BareMessage × PactType)) :
      reannotateBranches alphabet ((action, processType) :: rest) =
        (action, reannotate alphabet processType) ::
          reannotateBranches alphabet rest := by
    rw [reannotateBranches.eq_def]

end PactType

def singletonTypeXOfferAt (alphabet : PactTypeAlphabet)
    (branch : BareMessage × PactType) : PactType :=
  let branch := (branch.1, branch.2.reannotate alphabet)
  .xoffer alphabet (.skip alphabet) [branch]

def singletonTypeXOffer (branch : BareMessage × PactType) : PactType :=
  singletonTypeXOfferAt branch.2.alphabet branch

/-- A selected conjunctive-offer branch has no synthetic else alternative:
its head action is now mandatory, followed by its continuation. -/
def selectedTypeBranchAt (alphabet : PactTypeAlphabet)
    (branch : BareMessage × PactType) : PactType :=
  .seq alphabet (.message alphabet branch.1.1 branch.1.2)
    (branch.2.reannotate alphabet)

def selectedTypeBranch (branch : BareMessage × PactType) : PactType :=
  selectedTypeBranchAt branch.2.alphabet branch

@[simp] theorem singletonTypeXOffer_alphabet
    (branch : BareMessage × PactType) :
    (singletonTypeXOffer branch).alphabet = branch.2.alphabet := by
  rcases branch with ⟨action, processType⟩
  simp [singletonTypeXOffer, singletonTypeXOfferAt, PactType.alphabet]

@[simp] theorem selectedTypeBranch_alphabet
    (branch : BareMessage × PactType) :
    (selectedTypeBranch branch).alphabet = branch.2.alphabet := by
  rcases branch with ⟨action, processType⟩
  simp [selectedTypeBranch, selectedTypeBranchAt, PactType.alphabet]

def parallelType (left right : PactType) (interface : Interface) : PactType :=
  .par (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet interface)
    left right interface

/- The worker partitions `alphabet` from left to right.  Each non-final branch
receives exactly the declarations it uses.  The final branch receives the
remainder, so the product retains the enclosing offer's fixed alphabet. -/
def parallelTypeBranchesWithin (alphabet : PactTypeAlphabet) :
    List (BareMessage × PactType) → PactType
  | [] => .skip alphabet
  | [branch] => singletonTypeXOfferAt alphabet branch
  | branch :: rest =>
      let leftAlphabet := alphabet.branchPart branch
      let rightAlphabet := alphabet.remove leftAlphabet
      .par alphabet (singletonTypeXOfferAt leftAlphabet branch)
        (parallelTypeBranchesWithin rightAlphabet rest) ∅

/-- Rewrite a conjunctive type offer into parallel singleton exclusive offers
whose component alphabets partition the enclosing offer alphabet. -/
def parallelTypeBranches : List (BareMessage × PactType) → PactType
  | [] => .skip PactTypeAlphabet.empty
  | branch :: rest => parallelTypeBranchesWithin branch.2.alphabet (branch :: rest)

/-- Post-process the singleton-`xoffer` product after `selected` witnesses that
the conjunctive offer fired.  Exactly that singleton loses its synthetic
`skip` else-arm; all other singleton offers are retained.  Consequently the
single outcome in which every singleton selects else is absent. -/
def parallelTypeBranchesSelectingWithin (alphabet : PactTypeAlphabet)
    (selected : BareMessage × PactType) :
    List (BareMessage × PactType) → PactType
  | [] => .skip alphabet
  | [branch] =>
      if branch = selected then selectedTypeBranchAt alphabet branch
      else singletonTypeXOfferAt alphabet branch
  | branch :: rest =>
      let leftAlphabet := alphabet.branchPart branch
      let rightAlphabet := alphabet.remove leftAlphabet
      if branch = selected then
        .par alphabet (selectedTypeBranchAt leftAlphabet branch)
          (parallelTypeBranchesWithin rightAlphabet rest) ∅
      else
        .par alphabet (singletonTypeXOfferAt leftAlphabet branch)
          (parallelTypeBranchesSelectingWithin rightAlphabet selected rest) ∅

def parallelTypeBranchesSelecting
    (selected : BareMessage × PactType) :
    List (BareMessage × PactType) → PactType
  | [] => .skip PactTypeAlphabet.empty
  | branch :: rest =>
      parallelTypeBranchesSelectingWithin branch.2.alphabet selected
        (branch :: rest)

@[simp] theorem parallelTypeBranchesSelecting_singleton_self
    (branch : BareMessage × PactType) :
    parallelTypeBranchesSelecting branch [branch] =
      selectedTypeBranch branch := by
  simp [parallelTypeBranchesSelecting, parallelTypeBranchesSelectingWithin,
    selectedTypeBranch]

theorem parallelTypeBranches_alphabet_eq_of_nonempty
    {alphabet : PactTypeAlphabet} :
    ∀ {branches : List (BareMessage × PactType)},
      branches ≠ [] →
      PactType.BranchesAlphabetWellFormed alphabet branches →
      (parallelTypeBranches branches).alphabet = alphabet
  | [], hNonempty, _ => False.elim (hNonempty rfl)
  | [branch], _, hBranches => by
      rcases branch with ⟨action, processType⟩
      simp only [PactType.BranchesAlphabetWellFormed] at hBranches
      simp [parallelTypeBranches, parallelTypeBranchesWithin,
        singletonTypeXOfferAt, PactType.alphabet]
      exact hBranches.2.1
  | branch :: next :: rest, _, hBranches => by
      rcases branch with ⟨action, processType⟩
      simp only [PactType.BranchesAlphabetWellFormed] at hBranches
      change processType.alphabet = alphabet
      exact hBranches.2.1

theorem parallelTypeBranchesSelecting_alphabet_eq_of_mem
    {alphabet : PactTypeAlphabet} {selected : BareMessage × PactType} :
    ∀ {branches : List (BareMessage × PactType)},
      selected ∈ branches →
      PactType.BranchesAlphabetWellFormed alphabet branches →
      (parallelTypeBranchesSelecting selected branches).alphabet = alphabet
  | [], hMem, _ => by
      cases hMem
  | [branch], hMem, hBranches => by
      have hSelected : selected = branch := by simpa using hMem
      subst selected
      rcases branch with ⟨action, processType⟩
      simp only [PactType.BranchesAlphabetWellFormed] at hBranches
      simpa [parallelTypeBranchesSelecting,
        parallelTypeBranchesSelectingWithin, selectedTypeBranchAt,
        PactType.alphabet] using hBranches.2.1
  | branch :: next :: rest, hMem, hBranches => by
      by_cases hSelected : branch = selected
      · subst selected
        rcases branch with ⟨action, processType⟩
        simp only [PactType.BranchesAlphabetWellFormed] at hBranches
        simpa [parallelTypeBranchesSelecting,
          parallelTypeBranchesSelectingWithin, PactType.alphabet] using
            hBranches.2.1
      · have hMemTail : selected ∈ next :: rest := by
          simp only [List.mem_cons] at hMem
          rcases hMem with hHead | hTail
          · exact False.elim (hSelected hHead.symm)
          · simpa [List.mem_cons] using hTail
        rcases branch with ⟨action, processType⟩
        simp only [PactType.BranchesAlphabetWellFormed] at hBranches
        simpa [parallelTypeBranchesSelecting,
          parallelTypeBranchesSelectingWithin, PactType.alphabet, hSelected]
          using hBranches.2.1

/-- Reannotation rewrites only alphabets, so it leaves every tail-occurrence
judgement of the underlying term unchanged. -/
theorem PactType.reannotate_tailOccurrences (name : String) :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet) (tail : Prop),
      processType.TailOccurrences name tail →
        (processType.reannotate alphabet).TailOccurrences name tail := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet tail hTail
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (branchTail : Prop),
          sizeOf branches < n →
          PactType.TailBranchOccurrences name branchTail branches →
          PactType.TailBranchOccurrences name branchTail
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet branchTail hBranchesSize hBranchesTail
        induction branches with
        | nil =>
            rw [PactType.reannotateBranches_nil]
            simp [PactType.TailBranchOccurrences]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hFields : branchType.TailOccurrences name branchTail ∧
                PactType.TailBranchOccurrences name branchTail rest := by
              simpa only [PactType.TailBranchOccurrences] using hBranchesTail
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simpa only [PactType.reannotateBranches,
              PactType.TailBranchOccurrences] using
              And.intro (ih (sizeOf branchType) hBranchSize branchType rfl
                  branchAlphabet branchTail hFields.1)
                (restIH hRestSize hFields.2)
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ =>
          simp [PactType.reannotate, PactType.TailOccurrences]
      | var _ other =>
          simpa only [PactType.reannotate, PactType.TailOccurrences] using hTail
      | recur _ binder body =>
          by_cases hBinder : binder = name
          · simp [PactType.reannotate, PactType.TailOccurrences, hBinder]
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]; simp_wf; omega
            simpa only [PactType.reannotate, PactType.TailOccurrences,
              if_neg hBinder] using
              ih (sizeOf body) hBodySize body rfl alphabet tail
                (by simpa only [PactType.TailOccurrences, if_neg hBinder]
                  using hTail)
      | choice _ left right | fairChoice _ _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.TailOccurrences name tail ∧
              right.TailOccurrences name tail := by
            simpa only [PactType.TailOccurrences] using hTail
          simpa only [PactType.reannotate, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl alphabet tail
                hFields.1)
              (ih (sizeOf right) hRightSize right rfl alphabet tail hFields.2)
      | seq _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name tail := by
            simpa only [PactType.TailOccurrences] using hTail
          simpa only [PactType.reannotate, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl alphabet False
                hFields.1)
              (ih (sizeOf right) hRightSize right rfl alphabet tail hFields.2)
      | par _ left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          simpa only [PactType.reannotate, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl _ False hFields.1)
              (ih (sizeOf right) hRightSize right rfl _ False hFields.2)
      | xoffer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFields : elseType.TailOccurrences name tail ∧
              PactType.TailBranchOccurrences name tail branches := by
            simpa only [PactType.TailOccurrences] using hTail
          simpa only [PactType.reannotate, PactType.TailOccurrences] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl alphabet tail
                hFields.1)
              (hBranches branches alphabet tail hBranchesSize hFields.2)
      | offer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFields : elseType.TailOccurrences name tail ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          simpa only [PactType.reannotate, PactType.TailOccurrences] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl alphabet tail
                hFields.1)
              (hBranches branches alphabet False hBranchesSize hFields.2)

/-- Reannotation preserves tail recursion for the same structural reason. -/
theorem PactType.reannotate_tailRecursive :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      processType.TailRecursive →
        (processType.reannotate alphabet).TailRecursive := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet hRec
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.TailRecursiveBranches branches →
          PactType.TailRecursiveBranches
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet hBranchesSize hBranchesRec
        induction branches with
        | nil =>
            simp [PactType.reannotateBranches, PactType.TailRecursiveBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hFields : branchType.TailRecursive ∧
                PactType.TailRecursiveBranches rest := by
              simpa only [PactType.TailRecursiveBranches] using hBranchesRec
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simpa only [PactType.reannotateBranches,
              PactType.TailRecursiveBranches] using
              And.intro (ih (sizeOf branchType) hBranchSize branchType rfl
                  branchAlphabet hFields.1)
                (restIH hRestSize hFields.2)
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
          simp [PactType.reannotate, PactType.TailRecursive]
      | recur _ binder body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          have hFields : body.TailOccurrences binder True ∧ body.TailRecursive := by
            simpa only [PactType.TailRecursive] using hRec
          simpa only [PactType.reannotate, PactType.TailRecursive] using
            And.intro (PactType.reannotate_tailOccurrences binder body alphabet
                True hFields.1)
              (ih (sizeOf body) hBodySize body rfl alphabet hFields.2)
      | choice _ left right | fairChoice _ _ left right | seq _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hRec
          simpa only [PactType.reannotate, PactType.TailRecursive] using
            And.intro (ih (sizeOf left) hLeftSize left rfl alphabet hFields.1)
              (ih (sizeOf right) hRightSize right rfl alphabet hFields.2)
      | par _ left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hRec
          simpa only [PactType.reannotate, PactType.TailRecursive] using
            And.intro (ih (sizeOf left) hLeftSize left rfl _ hFields.1)
              (ih (sizeOf right) hRightSize right rfl _ hFields.2)
      | xoffer _ elseType branches | offer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFields : elseType.TailRecursive ∧
              PactType.TailRecursiveBranches branches := by
            simpa only [PactType.TailRecursive] using hRec
          simpa only [PactType.reannotate, PactType.TailRecursive] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl alphabet
                hFields.1)
              (hBranches branches alphabet hBranchesSize hFields.2)

/-- A generated singleton offer inherits its branch body's tail properties. -/
theorem singletonTypeXOfferAt_tailOccurrences (name : String)
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (tail : Prop) (hBranch : branch.2.TailOccurrences name False) :
    (singletonTypeXOfferAt alphabet branch).TailOccurrences name tail := by
  simp only [singletonTypeXOfferAt, PactType.TailOccurrences,
    PactType.TailBranchOccurrences]
  refine ⟨trivial, ?_, trivial⟩
  exact PactType.reannotate_tailOccurrences name branch.2 alphabet tail
    (PactType.tailOccurrences_mono name False.elim branch.2 hBranch)

theorem singletonTypeXOfferAt_tailRecursive
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hBranch : branch.2.TailRecursive) :
    (singletonTypeXOfferAt alphabet branch).TailRecursive := by
  simp only [singletonTypeXOfferAt, PactType.TailRecursive,
    PactType.TailRecursiveBranches]
  exact ⟨trivial, PactType.reannotate_tailRecursive branch.2 alphabet hBranch,
    trivial⟩

/-- The selected branch's commit form inherits its body's tail properties. -/
theorem selectedTypeBranchAt_tailOccurrences (name : String)
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (tail : Prop) (hBranch : branch.2.TailOccurrences name False) :
    (selectedTypeBranchAt alphabet branch).TailOccurrences name tail := by
  simp only [selectedTypeBranchAt, PactType.TailOccurrences]
  exact ⟨trivial, PactType.reannotate_tailOccurrences name branch.2 alphabet
    tail (PactType.tailOccurrences_mono name False.elim branch.2 hBranch)⟩

theorem selectedTypeBranchAt_tailRecursive
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hBranch : branch.2.TailRecursive) :
    (selectedTypeBranchAt alphabet branch).TailRecursive := by
  simp only [selectedTypeBranchAt, PactType.TailRecursive]
  exact ⟨trivial, PactType.reannotate_tailRecursive branch.2 alphabet hBranch⟩

/-- The generated parallel product of an offer's branches has no free tail
occurrence of any name absent from every branch body. -/
theorem parallelTypeBranchesWithin_tailOccurrences (name : String) :
    ∀ (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet) (tail : Prop),
      (∀ branch ∈ branches, branch.2.TailOccurrences name False) →
        (parallelTypeBranchesWithin alphabet branches).TailOccurrences
          name tail := by
  intro branches
  induction branches with
  | nil => intro _ _ _; simp [parallelTypeBranchesWithin, PactType.TailOccurrences]
  | cons branch rest ih =>
      intro alphabet tail hBranches
      cases rest with
      | nil =>
          exact singletonTypeXOfferAt_tailOccurrences name alphabet branch tail
            (hBranches branch (by simp))
      | cons next tail' =>
          simp only [parallelTypeBranchesWithin, PactType.TailOccurrences]
          exact ⟨singletonTypeXOfferAt_tailOccurrences name _ branch False
              (hBranches branch (by simp)),
            ih _ False (fun item hItem =>
              hBranches item (List.mem_cons_of_mem branch hItem))⟩

theorem parallelTypeBranchesWithin_tailRecursive :
    ∀ (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet),
      (∀ branch ∈ branches, branch.2.TailRecursive) →
        (parallelTypeBranchesWithin alphabet branches).TailRecursive := by
  intro branches
  induction branches with
  | nil => intro _ _; simp [parallelTypeBranchesWithin, PactType.TailRecursive]
  | cons branch rest ih =>
      intro alphabet hBranches
      cases rest with
      | nil =>
          exact singletonTypeXOfferAt_tailRecursive alphabet branch
            (hBranches branch (by simp))
      | cons next tail' =>
          simp only [parallelTypeBranchesWithin, PactType.TailRecursive]
          exact ⟨singletonTypeXOfferAt_tailRecursive _ branch
              (hBranches branch (by simp)),
            ih _ (fun item hItem =>
              hBranches item (List.mem_cons_of_mem branch hItem))⟩

theorem parallelTypeBranchesSelectingWithin_tailOccurrences (name : String)
    (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet) (tail : Prop),
      (∀ branch ∈ branches, branch.2.TailOccurrences name False) →
      selected.2.TailOccurrences name False →
        (parallelTypeBranchesSelectingWithin alphabet selected
          branches).TailOccurrences name tail := by
  intro branches
  induction branches with
  | nil =>
      intro _ _ _ _
      simp [parallelTypeBranchesSelectingWithin, PactType.TailOccurrences]
  | cons branch rest ih =>
      intro alphabet tail hBranches hSelected
      cases rest with
      | nil =>
          by_cases hEq : branch = selected
          · simpa only [parallelTypeBranchesSelectingWithin, if_pos hEq] using
              selectedTypeBranchAt_tailOccurrences name alphabet branch tail
                (hBranches branch (by simp))
          · simpa only [parallelTypeBranchesSelectingWithin, if_neg hEq] using
              singletonTypeXOfferAt_tailOccurrences name alphabet branch tail
                (hBranches branch (by simp))
      | cons next tail' =>
          by_cases hEq : branch = selected
          · simp only [parallelTypeBranchesSelectingWithin, if_pos hEq,
              PactType.TailOccurrences]
            exact ⟨selectedTypeBranchAt_tailOccurrences name _ branch False
                (hBranches branch (by simp)),
              parallelTypeBranchesWithin_tailOccurrences name _ _ False
                (fun item hItem =>
                  hBranches item (List.mem_cons_of_mem branch hItem))⟩
          · simp only [parallelTypeBranchesSelectingWithin, if_neg hEq,
              PactType.TailOccurrences]
            exact ⟨singletonTypeXOfferAt_tailOccurrences name _ branch False
                (hBranches branch (by simp)),
              ih _ False (fun item hItem =>
                hBranches item (List.mem_cons_of_mem branch hItem)) hSelected⟩

theorem parallelTypeBranchesSelectingWithin_tailRecursive
    (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet),
      (∀ branch ∈ branches, branch.2.TailRecursive) →
      selected.2.TailRecursive →
        (parallelTypeBranchesSelectingWithin alphabet selected
          branches).TailRecursive := by
  intro branches
  induction branches with
  | nil =>
      intro _ _ _
      simp [parallelTypeBranchesSelectingWithin, PactType.TailRecursive]
  | cons branch rest ih =>
      intro alphabet hBranches hSelected
      cases rest with
      | nil =>
          by_cases hEq : branch = selected
          · simpa only [parallelTypeBranchesSelectingWithin, if_pos hEq] using
              selectedTypeBranchAt_tailRecursive alphabet branch
                (hBranches branch (by simp))
          · simpa only [parallelTypeBranchesSelectingWithin, if_neg hEq] using
              singletonTypeXOfferAt_tailRecursive alphabet branch
                (hBranches branch (by simp))
      | cons next tail' =>
          by_cases hEq : branch = selected
          · simp only [parallelTypeBranchesSelectingWithin, if_pos hEq,
              PactType.TailRecursive]
            exact ⟨selectedTypeBranchAt_tailRecursive _ branch
                (hBranches branch (by simp)),
              parallelTypeBranchesWithin_tailRecursive _ _
                (fun item hItem =>
                  hBranches item (List.mem_cons_of_mem branch hItem))⟩
          · simp only [parallelTypeBranchesSelectingWithin, if_neg hEq,
              PactType.TailRecursive]
            exact ⟨singletonTypeXOfferAt_tailRecursive _ branch
                (hBranches branch (by simp)),
              ih _ (fun item hItem =>
                hBranches item (List.mem_cons_of_mem branch hItem)) hSelected⟩

/-- Committing a conjunctive offer produces a term with no free occurrence of
any name that the offer's branch bodies do not mention. -/
theorem parallelTypeBranchesSelecting_tailOccurrences (name : String)
    (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType)) (tail : Prop)
    (hBranches : ∀ branch ∈ branches, branch.2.TailOccurrences name False)
    (hSelected : selected.2.TailOccurrences name False) :
    (parallelTypeBranchesSelecting selected branches).TailOccurrences
      name tail := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.TailOccurrences]
  | cons branch rest =>
      exact parallelTypeBranchesSelectingWithin_tailOccurrences name selected
        (branch :: rest) branch.2.alphabet tail hBranches hSelected

theorem parallelTypeBranchesSelecting_tailRecursive
    (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hBranches : ∀ branch ∈ branches, branch.2.TailRecursive)
    (hSelected : selected.2.TailRecursive) :
    (parallelTypeBranchesSelecting selected branches).TailRecursive := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.TailRecursive]
  | cons branch rest =>
      exact parallelTypeBranchesSelectingWithin_tailRecursive selected
        (branch :: rest) branch.2.alphabet hBranches hSelected

/-- Actions appearing at the heads of an offer's branches. -/
def typeBranchActions
    (branches : List (BareMessage × PactType)) : Finset BareMessage :=
  (branches.map Prod.fst).toFinset

/-- Keep only offers whose message identifier belongs to `interface`. -/
def restrictTypeOffers (interface : Interface) (offers : Finset BareMessage) :
    Finset BareMessage :=
  offers.filter fun offer => offer.1 ∈ interface

/-- Remove offers hidden by a parallel interface. -/
def hideTypeOffers (interface : Interface) (offers : Finset BareMessage) :
    Finset BareMessage :=
  offers.filter fun offer => offer.1 ∉ interface

end

end Pact
