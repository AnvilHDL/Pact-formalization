import Anvilpp.PactTypes.Proofs.Automata.BuildChoiceAutomatonLemmas

namespace Pact

noncomputable section

/-! ### Sequential composition: the left, redirect, and right clauses. -/

/-- The left states the sequence construction drops: every accepting state of
`left` other than its own entry.  The entry is kept even when it is accepting
itself, so the sequence still has an initial state. -/
def sequenceDeleted (left : AutomatonFragment) : Finset TypeAutomatonState :=
  left.accepting \ {left.initial}

/-- Where a left-child edge target lands in the sequence carrier: accepting
targets enter `right`, while non-accepting targets keep their `0`-tag. -/
def sequenceRedirect (left right : AutomatonFragment)
    (state : TypeAutomatonState) : TypeAutomatonState :=
  if state ∈ left.accepting then childState 1 right.initial
  else childState 0 state

/-- Legacy target-only field helper, unused by the sequence construction. -/
def sequenceRedirectFutureSpec (label : AutomatonConstructionLabel)
    (target : TypeAutomatonState) (removed : Finset BareMessage) :
    FutureSpec :=
  if label.semantic = TypeLabel.tock then .explicit ∅
  else .at target removed

/-- `Fut_τ(q,α,O_C,O_F)`: a clock edge exposes nothing; otherwise the copied
left field is combined with the right-entry menu exactly when the left source
passes the optimistic completion test, and the published current offer is
removed. -/
def sequenceLeftFutureSpec (label : AutomatonConstructionLabel)
    (rightEntry : TypeAutomatonState) (childFuture removed : Finset BareMessage)
    (completes : Bool) : FutureSpec :=
  if label.semantic = TypeLabel.tock then .explicit ∅
  else if completes then .atUnion childFuture rightEntry removed
  else .explicit (childFuture \ removed)

/-- The image of a left edge whose target is not final.

The edge stays in the left copy. Its resolved child future is combined with
the right-entry menu when the left source can complete this cycle. -/
def sequenceKeptLeftEdge (_left right : AutomatonFragment)
    (leftFuture : TypeAutomatonState → Finset BareMessage)
    (leftCompletes : TypeAutomatonState → Bool)
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  { source := childState 0 edge.source
    environment := edge.environment
    label := edge.label
    current := edge.current
    future := sequenceLeftFutureSpec edge.label
      (childState 1 right.initial) (resolveFutureSpec leftFuture edge.future)
      edge.current (leftCompletes edge.source)
    target := childState 0 edge.target }

/-- The image of a left edge whose target is final.

The target becomes the right entry. The future field is computed exactly as
for a retained edge, using the original child witness and left source. -/
def sequenceRedirectEdge (_left right : AutomatonFragment)
    (leftFuture : TypeAutomatonState → Finset BareMessage)
    (leftCompletes : TypeAutomatonState → Bool)
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  { source := childState 0 edge.source
    environment := edge.environment
    label := edge.label
    current := edge.current
    future := sequenceLeftFutureSpec edge.label
      (childState 1 right.initial) (resolveFutureSpec leftFuture edge.future)
      edge.current (leftCompletes edge.source)
    target := childState 1 right.initial }

/-- `δ_seq^left`: keep exactly the left edges whose target is not accepting. -/
def sequenceLeftEdges (left right : AutomatonFragment)
    (leftFuture : TypeAutomatonState → Finset BareMessage)
    (leftCompletes : TypeAutomatonState → Bool) :
    Finset PendingAutomatonEdge :=
  (left.edges.filter fun edge =>
    edge.source ∉ sequenceDeleted left ∧
      edge.target ∉ left.accepting).image
    (sequenceKeptLeftEdge left right leftFuture leftCompletes)

/-- `δ_seq^right`: copy all right edges into the right component. -/
def sequenceRightEdges (right : AutomatonFragment) :
    Finset PendingAutomatonEdge :=
  childPendingEdges 1 right

/-- `δ_seq^redirect`: redirect exactly the left edges whose target is accepting. -/
def sequenceRedirectEdges (left right : AutomatonFragment)
    (leftFuture : TypeAutomatonState → Finset BareMessage)
    (leftCompletes : TypeAutomatonState → Bool) :
    Finset PendingAutomatonEdge :=
  (left.edges.filter fun edge =>
    edge.source ∉ sequenceDeleted left ∧
      edge.target ∈ left.accepting).image
    (sequenceRedirectEdge left right leftFuture leftCompletes)

/-- Compatibility helper for older correspondence proofs.

The construction below does not use this combined helper.  It is just the case
split between `δ_seq^left` and `δ_seq^redirect`. -/
def sequenceLeftEdge (left right : AutomatonFragment)
    (leftFuture : TypeAutomatonState → Finset BareMessage)
    (leftCompletes : TypeAutomatonState → Bool)
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  if edge.target ∈ left.accepting then
    sequenceRedirectEdge left right leftFuture leftCompletes edge
  else
    sequenceKeptLeftEdge left right leftFuture leftCompletes edge

def buildSequenceAutomaton (left right : AutomatonFragment)
    (leftFuture : TypeAutomatonState → Finset BareMessage)
    (leftCompletes : TypeAutomatonState → Bool) : AutomatonFragment :=
  let states := (left.states \ sequenceDeleted left).image (childState 0) ∪
    childStates 1 right
  let accepting := childAccepting 1 right
  let completes :=
    (if right.initial ∈ right.completes then
      ((left.completes \ sequenceDeleted left).image (childState 0)) else ∅) ∪
      childCompletes 1 right
  finishAutomatonFragment states (childState 0 left.initial) accepting completes
    ((sequenceLeftEdges left right leftFuture leftCompletes ∪
        sequenceRightEdges right) ∪
      sequenceRedirectEdges left right leftFuture leftCompletes)

end

end Pact
