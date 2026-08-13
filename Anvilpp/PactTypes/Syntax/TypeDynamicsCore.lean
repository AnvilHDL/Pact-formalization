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
  .xoffer .skip [branch]

/-- A selected conjunctive-offer branch has no synthetic else alternative:
its head action is now mandatory, followed by its continuation. -/
def selectedTypeBranch (branch : BareMessage × PactType) : PactType :=
  .seq (.message branch.1.1 branch.1.2) branch.2

/-- Rewrite a conjunctive type offer into parallel singleton exclusive offers. -/
def parallelTypeBranches : List (BareMessage × PactType) → PactType
  | [] => .skip
  | [branch] => singletonTypeXOffer branch
  | branch :: rest =>
      .par (singletonTypeXOffer branch) (parallelTypeBranches rest) ∅

/-- Post-process the singleton-`xoffer` product after `selected` witnesses that
the conjunctive offer fired.  Exactly that singleton loses its synthetic
`skip` else-arm; all other singleton offers are retained.  Consequently the
single outcome in which every singleton selects else is absent. -/
def parallelTypeBranchesSelecting
    (selected : BareMessage × PactType) :
    List (BareMessage × PactType) → PactType
  | [] => .skip
  | [branch] =>
      if branch = selected then selectedTypeBranch branch
      else singletonTypeXOffer branch
  | branch :: rest =>
      if branch = selected then
        .par (selectedTypeBranch branch) (parallelTypeBranches rest) ∅
      else
        .par (singletonTypeXOffer branch)
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
      .par (selectedTypeBranch branch) (singletonTypeXOffer branch) ∅ := by
  simp [parallelTypeBranchesSelecting, parallelTypeBranches]

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
