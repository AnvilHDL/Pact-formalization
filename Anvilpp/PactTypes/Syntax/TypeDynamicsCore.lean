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

namespace PactTypeAlphabet

  /-- The part of `parent` used by one conjunctive-offer branch. -/
  def branchPart (parent : PactTypeAlphabet)
      (branch : BareMessage × PactType) : PactTypeAlphabet :=
    { actions := parent.actions ∩
        ({branch.1} ∪ PactType.MessageActions branch.2)
      progress := parent.progress ∩ PactType.ProgressIds branch.2
      fair := parent.fair ∩ PactType.FairChoiceIds branch.2 }

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
      (parent : PactTypeAlphabet) (branch : BareMessage × PactType) :
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
      (branch : BareMessage × PactType) :
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
      (interface : Interface) : PactTypeAlphabet :=
    { actions := child.actions.filter fun action =>
        action.1 ∈ interface ∨ action ∈ parent.actions
      progress := child.progress ∩ parent.progress
      fair := child.fair ∩ parent.fair }

  /-- Project a new parallel alphabet to the left child.  Declarations that
  are new to the reannotated parallel node are assigned to the left child, so
  the two projected children still reconstruct the whole parent alphabet. -/
  def projectParallelLeft (parent left right : PactTypeAlphabet)
      (interface : Interface) : PactTypeAlphabet :=
    let rightPart := projectParallelChild parent right interface
    { actions :=
        (left.actions.filter fun action => action.1 ∈ interface) ∪
          (parent.actions \ rightPart.actions)
      progress := parent.progress \ rightPart.progress
      fair := parent.fair \ rightPart.fair }

end PactTypeAlphabet

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
