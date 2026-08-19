import Anvilpp.PactTypes.Automata.CompileType

namespace Pact

open Classical

noncomputable section

/-- Candidate relation successors generated from one related residual/state
pair.  A successor is kept exactly when the automaton has an outgoing edge with
the same decoration as some semantic type step from the residual. -/
def relationSuccessors
    (auto : TypeAutomaton)
    (entry : PactType × TypeAutomatonState) :
    Finset (PactType × TypeAutomatonState) :=
  auto.edges.biUnion fun edge =>
    if edge.source = entry.2 then
      if hStep : ∃ residual',
          DecoratedTypeTransition
            edge.symbol.environment entry.1 edge.symbol.label edge.symbol.offers
            residual' then
        {(Classical.choose hStep, edge.target)}
      else
        ∅
    else
      ∅

/-- Fuel-bounded worklist saturation for the type/automaton relation. -/
def auxRelBuilderFuel (auto : TypeAutomaton) :
    Nat → Finset (PactType × TypeAutomatonState) →
      Finset (PactType × TypeAutomatonState) →
      Finset (PactType × TypeAutomatonState)
  | 0, rel_set, _ => rel_set
  | fuel + 1, rel_set, worklist =>
      match worklist.toList with
      | [] => rel_set
      | entry :: _ =>
          let worklist' := worklist.erase entry
          let newEntries := relationSuccessors auto entry \ rel_set
          auxRelBuilderFuel auto fuel
            (rel_set ∪ newEntries)
            (worklist' ∪ newEntries)


/-- The finite budget used by the executable relation builder. -/
def relationBuilderFuelBound (auto : TypeAutomaton)
    (rel_set worklist : Finset (PactType × TypeAutomatonState)) : Nat :=
  auto.states.card + auto.edges.card + rel_set.card + worklist.card + 1


/-- Saturate the paper's correspondence relation from the current worklist.

The first argument names the original residual whose relation is being built;
the current worklist already carries the concrete residual/state entries to
process. -/
def auxRelBuilder (_residual_ty : PactType) (auto : TypeAutomaton)
    (rel_set : Finset (PactType × TypeAutomatonState))
    (worklist : Finset (PactType × TypeAutomatonState)) :
    Finset (PactType × TypeAutomatonState) :=
  let fuel := relationBuilderFuelBound auto rel_set worklist
  auxRelBuilderFuel auto fuel rel_set worklist

def buildRelationSet (ty : PactType) (auto : TypeAutomaton) :
    Finset (PactType × TypeAutomatonState) :=
  let relation_set : Finset (PactType × TypeAutomatonState) := {(ty, auto.initial)}
  auxRelBuilder ty auto relation_set relation_set

def relationMembership
    (relation_set : Finset (PactType × TypeAutomatonState))
    (processType : PactType) (state : TypeAutomatonState) : Prop :=
  (processType, state) ∈ relation_set






-- Some Trivial Theorems for construction of relation

/-- The relation is closed under every one-step matched semantic/automaton
successor. -/
def RelationBuilderSaturated (auto : TypeAutomaton)
    (rel_set : Finset (PactType × TypeAutomatonState)) : Prop :=
  ∀ entry ∈ rel_set, relationSuccessors auto entry ⊆ rel_set


/-- Worklist saturation only adds relation entries; it never removes entries
already present in the accumulated relation. -/
theorem rel_set_subset_auxRelBuilderFuel (auto : TypeAutomaton) :
    ∀ fuel (rel_set worklist : Finset (PactType × TypeAutomatonState)),
      rel_set ⊆ auxRelBuilderFuel auto fuel rel_set worklist := by
  intro fuel
  induction fuel with
  | zero =>
      intro rel_set worklist
      simp [auxRelBuilderFuel]
  | succ fuel ih =>
      intro rel_set worklist
      simp only [auxRelBuilderFuel]
      cases hWorklist : worklist.toList with
      | nil =>
          simp
      | cons entry rest =>
          intro pair hPair
          apply ih
          exact Finset.mem_union_left _ hPair

/-- The relation builder contains its seed pair. -/
theorem buildRelationSet_initial (ty : PactType) (auto : TypeAutomaton)  :
    relationMembership (buildRelationSet ty auto) ty auto.initial := by
  simp [relationMembership, buildRelationSet, auxRelBuilder]
  apply rel_set_subset_auxRelBuilderFuel
  simp
end

/-- The chosen worklist fuel is enough to reach a saturated relation; in
particular the fuel-bounded recursion never stops just because fuel ran out.

TODO(redevelopment): prove this from the finite-state/residual uniqueness
invariants for admissible constructor automata. -/
theorem auxRelBuilderFuel_bound_saturated
    (auto : TypeAutomaton)
    (rel_set worklist : Finset (PactType × TypeAutomatonState)) :
    RelationBuilderSaturated auto
      (auxRelBuilderFuel auto
        (relationBuilderFuelBound auto rel_set worklist) rel_set worklist) := by
  sorry

/-- The public relation builder returns a saturated relation.

TODO(redevelopment): discharge from `auxRelBuilderFuel_bound_saturated` once
the public wrapper is normalized for `simp`. -/
theorem buildRelationSet_saturated (ty : PactType) (auto : TypeAutomaton) :
    RelationBuilderSaturated auto (buildRelationSet ty auto) := by
  sorry
end Pact
