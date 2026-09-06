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

/-- Future spec used by sequence edges, kept and redirected alike.

A clock edge ends the current cycle, so it must not expose any same-cycle
future menu — neither the right entry's (on a redirect) nor the retagged
left target's (on a kept edge).  Non-clock edges keep the usual symbolic
reference to the target state's `OF` equation. -/
def sequenceRedirectFutureSpec (label : AutomatonConstructionLabel)
    (target : TypeAutomatonState) (removed : Finset BareMessage) :
    FutureSpec :=
  if label.semantic = TypeLabel.tock then .explicit ∅
  else .at target removed

/-- The image of a left edge whose target is not final.

The edge stays in the left copy, retagged.  The future field is rebuilt as a fresh `OF(q')` reference at the
retagged target — never the original edge's own `.future` retargeted in
place, since that original reference was resolved against `left` alone and
may carry an unrelated `removed` set.  `edge.current` is always a safe
choice of `removed`: it is exactly what a same-cycle self-loop needs
(`OF` of the loop's own state would otherwise double-count the offer this
edge already reports as current), and a no-op everywhere else, since
`edge.current` then generally is not present in the target's own menu
anyway.  A clock edge is the exception: it ends the cycle, so it exposes no
future menu at all, exactly as on the redirect clause. -/
def sequenceKeptLeftEdge (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  { source := childState 0 edge.source
    environment := edge.environment
    label := edge.label
    current := edge.current
    future := sequenceRedirectFutureSpec edge.label
      (sequenceRedirect left right edge.target) edge.current
    target := childState 0 edge.target }

/-- The image of a left edge whose target is final.

The source, environment, label, and current offers are copied from the left
edge.  The target becomes the
right entry, and the future field is `OF(i₂)` — with `removed := edge.current`
for the same self-loop-safety reason as `sequenceKeptLeftEdge`. -/
def sequenceRedirectEdge (_left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  { source := childState 0 edge.source
    environment := edge.environment
    label := edge.label
    current := edge.current
    future := sequenceRedirectFutureSpec edge.label (childState 1 right.initial)
      edge.current
    target := childState 1 right.initial }

/-- `δ_seq^left`: keep exactly the left edges whose target is not accepting. -/
def sequenceLeftEdges (left right : AutomatonFragment) :
    Finset PendingAutomatonEdge :=
  (left.edges.filter fun edge =>
    edge.source ∉ sequenceDeleted left ∧
      edge.target ∉ left.accepting).image
    (sequenceKeptLeftEdge left right)

/-- `δ_seq^right`: copy all right edges into the right component. -/
def sequenceRightEdges (right : AutomatonFragment) :
    Finset PendingAutomatonEdge :=
  childPendingEdges 1 right

/-- `δ_seq^redirect`: redirect exactly the left edges whose target is accepting. -/
def sequenceRedirectEdges (left right : AutomatonFragment) :
    Finset PendingAutomatonEdge :=
  (left.edges.filter fun edge =>
    edge.source ∉ sequenceDeleted left ∧
      edge.target ∈ left.accepting).image
    (sequenceRedirectEdge left right)

/-- Compatibility helper for older correspondence proofs.

The construction below does not use this combined helper.  It is just the case
split between `δ_seq^left` and `δ_seq^redirect`. -/
def sequenceLeftEdge (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  if edge.target ∈ left.accepting then
    sequenceRedirectEdge left right edge
  else
    sequenceKeptLeftEdge left right edge

def buildSequenceAutomaton (left right : AutomatonFragment) : AutomatonFragment :=
  let states := (left.states \ sequenceDeleted left).image (childState 0) ∪
    childStates 1 right
  let accepting := childAccepting 1 right
  finishAutomatonFragment states (childState 0 left.initial) accepting
    ((sequenceLeftEdges left right ∪ sequenceRightEdges right) ∪
      sequenceRedirectEdges left right)

end

end Pact
