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

def singletonTypeXOffer (branch : BareMessage × PactType) : PactType :=
  .xoffer branch.2.alphabet (.skip branch.2.alphabet) [branch]

/-- A selected conjunctive-offer branch has no synthetic else alternative:
its head action is now mandatory, followed by its continuation. -/
def selectedTypeBranch (branch : BareMessage × PactType) : PactType :=
  .seq branch.2.alphabet (.message branch.2.alphabet branch.1.1 branch.1.2)
    branch.2

@[simp] theorem singletonTypeXOffer_alphabet
    (branch : BareMessage × PactType) :
    (singletonTypeXOffer branch).alphabet = branch.2.alphabet := by
  simp [singletonTypeXOffer, PactType.alphabet]

@[simp] theorem selectedTypeBranch_alphabet
    (branch : BareMessage × PactType) :
    (selectedTypeBranch branch).alphabet = branch.2.alphabet := by
  simp [selectedTypeBranch, PactType.alphabet]

def parallelType (left right : PactType) (interface : Interface) : PactType :=
  .par (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet interface)
    left right interface

/-- Rewrite a conjunctive type offer into parallel singleton exclusive offers. -/
def parallelTypeBranches : List (BareMessage × PactType) → PactType
  | [] => .skip PactTypeAlphabet.empty
  | [branch] => singletonTypeXOffer branch
  | branch :: rest =>
      parallelType (singletonTypeXOffer branch) (parallelTypeBranches rest) ∅

/-- Post-process the singleton-`xoffer` product after `selected` witnesses that
the conjunctive offer fired.  Exactly that singleton loses its synthetic
`skip` else-arm; all other singleton offers are retained.  Consequently the
single outcome in which every singleton selects else is absent. -/
def parallelTypeBranchesSelecting
    (selected : BareMessage × PactType) :
    List (BareMessage × PactType) → PactType
  | [] => .skip PactTypeAlphabet.empty
  | [branch] =>
      if branch = selected then selectedTypeBranch branch
      else singletonTypeXOffer branch
  | branch :: rest =>
      if branch = selected then
        parallelType (selectedTypeBranch branch) (parallelTypeBranches rest) ∅
      else
        parallelType (singletonTypeXOffer branch)
          (parallelTypeBranchesSelecting selected rest) ∅

@[simp] theorem parallelTypeBranchesSelecting_singleton_self
    (branch : BareMessage × PactType) :
    parallelTypeBranchesSelecting branch [branch] =
      selectedTypeBranch branch := by
  simp [parallelTypeBranchesSelecting]

/-- Even duplicate branches force only one occurrence: the second singleton
retains its synthetic else arm. -/
@[simp] theorem parallelTypeBranchesSelecting_duplicate_pair
    (branch : BareMessage × PactType) :
    parallelTypeBranchesSelecting branch [branch, branch] =
      parallelType (selectedTypeBranch branch) (singletonTypeXOffer branch) ∅ := by
  simp [parallelTypeBranchesSelecting, parallelTypeBranches]

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
      change processType.alphabet = alphabet
      exact hBranches.2.1
  | branch :: next :: rest, _, hBranches => by
      rcases branch with ⟨action, processType⟩
      simp only [PactType.BranchesAlphabetWellFormed] at hBranches
      have hHead : processType.alphabet = alphabet := hBranches.2.1
      have hTail :
          (parallelTypeBranches (next :: rest)).alphabet = alphabet :=
        parallelTypeBranches_alphabet_eq_of_nonempty (by simp)
          hBranches.2.2.2
      change PactTypeAlphabet.mergeHidden processType.alphabet
          (parallelTypeBranches (next :: rest)).alphabet ∅ = alphabet
      rw [hHead, hTail]
      simp

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
      rw [parallelTypeBranchesSelecting_singleton_self]
      change processType.alphabet = alphabet
      exact hBranches.2.1
  | branch :: next :: rest, hMem, hBranches => by
      by_cases hSelected : branch = selected
      · subst selected
        rcases branch with ⟨action, processType⟩
        simp only [PactType.BranchesAlphabetWellFormed] at hBranches
        have hBranch : processType.alphabet = alphabet := hBranches.2.1
        have hTail :
            (parallelTypeBranches (next :: rest)).alphabet = alphabet :=
          parallelTypeBranches_alphabet_eq_of_nonempty (by simp)
            hBranches.2.2.2
        simp only [parallelTypeBranchesSelecting, if_true, parallelType,
          PactType.alphabet]
        change PactTypeAlphabet.mergeHidden processType.alphabet
            (parallelTypeBranches (next :: rest)).alphabet ∅ = alphabet
        rw [hBranch, hTail]
        simp
      · have hMemTail : selected ∈ next :: rest := by
          simp only [List.mem_cons] at hMem
          rcases hMem with hHead | hTail
          · exact False.elim (hSelected hHead.symm)
          · simpa [List.mem_cons] using hTail
        rcases branch with ⟨action, processType⟩
        simp only [PactType.BranchesAlphabetWellFormed] at hBranches
        have hBranch : processType.alphabet = alphabet := hBranches.2.1
        have hTail :
            (parallelTypeBranchesSelecting selected (next :: rest)).alphabet =
              alphabet :=
          parallelTypeBranchesSelecting_alphabet_eq_of_mem hMemTail
            hBranches.2.2.2
        simp only [parallelTypeBranchesSelecting, hSelected, if_false,
          parallelType, PactType.alphabet]
        change PactTypeAlphabet.mergeHidden processType.alphabet
            (parallelTypeBranchesSelecting selected (next :: rest)).alphabet
            ∅ = alphabet
        rw [hBranch, hTail]
        simp

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
