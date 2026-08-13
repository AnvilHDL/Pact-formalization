import Anvilpp.PactTypes.Automata.TypeAlphabet

/-!
# Automaton state/edge/fragment representation used by every constructor
-/

namespace Pact

noncomputable section

/-! ### Construction representation -/

/--
Tagged States

* `root` and `final` are the two distinguished states used by atomic types.
* `child i q` injects state `q` into child automaton `i` of a sum/sequence.
* `pair q₁ q₂` is a state of a synchronized parallel product.
-/
inductive TypeAutomatonState : Type where
  /-- Fresh entry state introduced by a constructor. -/
  | root
  /-- Completed state used by atomic constructors. -/
  | final
  /-- State `state` embedded into child automaton `index`. -/
  | child : Nat → TypeAutomatonState → TypeAutomatonState
  /-- Product state containing one state from each parallel component. -/
  | pair : TypeAutomatonState → TypeAutomatonState → TypeAutomatonState
  deriving DecidableEq

/--
Visible labels become part of the final automaton. Variable labels are
temporary back-edge markers consumed when compiling the matching binder.
Future-observation labels are internal edges used only by `computeFuture`;
they retain optimistic component offers without becoming semantic steps.
-/
inductive AutomatonConstructionLabel : Type where
  | visible : TypeLabel → AutomatonConstructionLabel
  | variable : String → AutomatonConstructionLabel
  | future : AutomatonConstructionLabel
  deriving DecidableEq

/--
How to fill an edge's future-offer field.

* `explicit offers` copies a future set already computed by a child.
* `at state removed` computes `OF(state) \ removed` after the parent graph is
  complete. This is what prevents a constructor from inspecting a partial
  automaton during recursive construction.
-/
inductive FutureSpec : Type where
  | explicit : Finset BareMessage → FutureSpec
  | at : TypeAutomatonState → Finset BareMessage → FutureSpec
  deriving DecidableEq

/-- An edge whose future-offer field has not necessarily been resolved yet. -/
structure PendingAutomatonEdge : Type where
  source : TypeAutomatonState
  environment : TypeEnvironment
  label : AutomatonConstructionLabel
  current : Finset BareMessage
  future : FutureSpec
  target : TypeAutomatonState
  deriving DecidableEq

/--
A constructor fragment whose future references remain symbolic.

Keeping `FutureSpec.at` references unresolved is essential for recursion:
an enclosing binder can add a back-edge, changing the future offers reachable
from a child state.  Resolution therefore happens only when an operation
actually needs decorated edges, and once more for the final automaton.
-/
structure AutomatonFragment : Type where
  states : Finset TypeAutomatonState
  initial : TypeAutomatonState
  accepting : Finset TypeAutomatonState
  /-- States whose represented semantic residual is literally `skip`. -/
  skipping : Finset TypeAutomatonState
  /-- States whose represented residual may optimistically finish before the
  next clock.  Unlike `skipping`, this is analysis metadata rather than a
  source of semantic administrative transitions. -/
  completing : Finset TypeAutomatonState
  edges : Finset PendingAutomatonEdge

/-- Every symbolic future reference in a fragment points to a declared state. -/
def AutomatonFragment.FutureTargetsInStates
    (fragment : AutomatonFragment) : Prop :=
  ∀ edge ∈ fragment.edges, ∀ target removed,
    edge.future = .at target removed → target ∈ fragment.states

/-- A constructor edge after its future-offer field has been computed. -/
structure AutomatonFragmentEdge : Type where
  source : TypeAutomatonState
  environment : TypeEnvironment
  label : AutomatonConstructionLabel
  current : Finset BareMessage
  future : Finset BareMessage
  target : TypeAutomatonState
  deriving DecidableEq

/-- Complete state/edge graph used while resolving pending future fields. -/
structure PendingAutomaton : Type where
  states : Finset TypeAutomatonState
  edges : Finset PendingAutomatonEdge

namespace AutomatonConstructionLabel

  /-- Treat a temporary recursion edge as silent for local synchronization. -/
  def semantic : AutomatonConstructionLabel → TypeLabel
    | .visible label => label
    | .variable _ => TypeLabel.silent
    | .future => TypeLabel.silent

  /-- Combine product labels while preserving an unresolved recursion marker. -/
  def combine (interface : Interface)
      (left right : AutomatonConstructionLabel) : AutomatonConstructionLabel :=
    match left, right with
    | .future, _ => .future
    | _, .future => .future
    | .variable name, _ => .variable name
    | _, .variable name => .variable name
    | .visible leftLabel, .visible rightLabel =>
        .visible (TypeLabel.combine interface leftLabel rightLabel)

  /-- A synchronized non-clock product edge cannot hide a clock edge in
  either component. -/
  theorem component_nonclock_of_sync
      (interface : Interface) (left right : AutomatonConstructionLabel)
      (hSync : TypeLabel.Sync interface left.semantic right.semantic)
      (hCombined : (combine interface left right).semantic ≠ TypeLabel.tock) :
      left.semantic ≠ TypeLabel.tock ∧ right.semantic ≠ TypeLabel.tock := by
    have hClockIff : left.semantic = TypeLabel.tock ↔
        right.semantic = TypeLabel.tock := by
      have hIsTock := hSync.2.2
      cases hLeft : left.semantic <;> cases hRight : right.semantic <;>
        simp [TypeLabel.isTock, hLeft, hRight] at hIsTock ⊢
    constructor
    · intro hLeft
      have hRight := hClockIff.mp hLeft
      cases left with
      | visible leftLabel =>
          simp only [semantic] at hLeft
          subst leftLabel
          cases right with
          | visible rightLabel =>
              simp only [semantic] at hRight
              subst rightLabel
              exact hCombined rfl
          | «variable» name => simp [semantic, TypeLabel.silent] at hRight
          | future => simp [semantic, TypeLabel.silent] at hRight
      | «variable» name => simp [semantic, TypeLabel.silent] at hLeft
      | future => simp [semantic, TypeLabel.silent] at hLeft
    · intro hRight
      have hLeft := hClockIff.mpr hRight
      cases left with
      | visible leftLabel =>
          simp only [semantic] at hLeft
          subst leftLabel
          cases right with
          | visible rightLabel =>
              simp only [semantic] at hRight
              subst rightLabel
              exact hCombined rfl
          | «variable» name => simp [semantic, TypeLabel.silent] at hRight
          | future => simp [semantic, TypeLabel.silent] at hRight
      | «variable» name => simp [semantic, TypeLabel.silent] at hLeft
      | future => simp [semantic, TypeLabel.silent] at hLeft

end AutomatonConstructionLabel

end

end Pact
