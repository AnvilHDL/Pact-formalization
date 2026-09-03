import Anvilpp.PactTypes.Syntax.TypeErasure

namespace Pact

noncomputable section

/-! ## Type dynamics and semantic correspondence -/

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
        ({branch.1} ∪ PactType.MessageActions branch.2) }

  /-- The declarations left after assigning one component of an internal
  parallel product. -/
  def remove (parent assigned : PactTypeAlphabet) : PactTypeAlphabet :=
    { actions := parent.actions \ assigned.actions }

  /-- Project a new parallel alphabet onto a child: the child keeps its own
  interface actions and receives the whole new parent alphabet. -/
  def projectParallel (parent child : PactTypeAlphabet)
      (interface : Interface) : PactTypeAlphabet :=
    { actions :=
        (child.actions.filter fun action => action.1 ∈ interface) ∪
          parent.actions }

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
          let leftAlphabet :=
            PactTypeAlphabet.projectParallel alphabet left.alphabet interface
          let rightAlphabet :=
            PactTypeAlphabet.projectParallel alphabet right.alphabet interface
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
            (reannotateOfferBranches alphabet ∅ branches)
    termination_by processType => sizeOf processType

    def reannotateBranches (alphabet : PactTypeAlphabet) :
        List (BareMessage × PactType) → List (BareMessage × PactType)
      | [] => []
      | (action, processType) :: rest =>
          (action, reannotate alphabet processType) ::
            reannotateBranches alphabet rest
    termination_by branches => sizeOf branches

    /-- Conjunctive-offer branches run concurrently, so each carries the part of
    the alphabet no other branch claims. -/
    def reannotateOfferBranches (alphabet : PactTypeAlphabet)
        (seen : Finset BareMessage) :
        List (BareMessage × PactType) → List (BareMessage × PactType)
      | [] => []
      | (action, processType) :: rest =>
          (action,
            reannotate
              { actions :=
                  alphabet.actions \ (seen ∪ PactType.BranchMessageActions rest) }
              processType) ::
            reannotateOfferBranches alphabet
              (seen ∪ ({action} ∪ PactType.MessageActions processType)) rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

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

def parallelType (left right : PactType) (interface : Interface) : PactType :=
  .par (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet interface)
    left right interface

/- The worker partitions `alphabet` from left to right.  Each non-final branch
receives its own declared alphabet.  The final branch receives the remainder,
so the product retains the enclosing offer's fixed alphabet. -/
def parallelTypeBranchesWithin (alphabet : PactTypeAlphabet) :
    List (BareMessage × PactType) → PactType
  | [] => .skip alphabet
  | [branch] => singletonTypeXOfferAt alphabet branch
  | branch :: rest =>
      .par alphabet (singletonTypeXOfferAt alphabet branch)
        (parallelTypeBranchesWithin alphabet rest) ∅

/-- Rewrite a conjunctive type offer into parallel singleton exclusive offers.
Commitment places the branches in parallel with an empty interface, so every
component carries the complete enclosing alphabet. -/
def parallelTypeBranches (alphabet : PactTypeAlphabet) :
    List (BareMessage × PactType) → PactType
  | [] => .skip PactTypeAlphabet.empty
  | branch :: rest => parallelTypeBranchesWithin alphabet (branch :: rest)

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
      if branch = selected then
        .par alphabet (selectedTypeBranchAt alphabet branch)
          (parallelTypeBranchesWithin alphabet rest) ∅
      else
        .par alphabet (singletonTypeXOfferAt alphabet branch)
          (parallelTypeBranchesSelectingWithin alphabet selected rest) ∅

def parallelTypeBranchesSelecting (alphabet : PactTypeAlphabet)
    (selected : BareMessage × PactType) :
    List (BareMessage × PactType) → PactType
  | [] => .skip PactTypeAlphabet.empty
  | branch :: rest =>
      parallelTypeBranchesSelectingWithin alphabet selected (branch :: rest)

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
