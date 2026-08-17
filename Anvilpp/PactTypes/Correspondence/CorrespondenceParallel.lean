import Anvilpp.PactTypes.Correspondence.CorrespondenceVisibility

/-!
# Parallel-product correspondence

Only the top-level, documented leaves survive here
(`CORRESPONDENCE_THEOREMS.md` §10: "Forward step direction", "Reverse step
direction", "Target preservation", "Bridge from child bundles to product
reconstruction"). Their statements are general — they describe what must
hold of *any* correct product construction — and remain meaningful
independent of the exact future-offer mechanism.

Everything else previously in this file (the `buildParallelAutomaton`-specific
edge classifiers, `syncAutomatonEdgeWitnesses`/`localEnvironment` reconstruction
plumbing, `semanticResolvedAutomatonEdges`, etc., ~1600 lines) was deleted: it
was proof infrastructure built around the *current* `BuildParallelAutomaton.lean`
construction, which fakes the parallel product's future-offer menu with
synthetic `AutomatonConstructionLabel.future` edges resolved by
`computeFuture`'s local graph closure. `pactautomatonconstruction.typ`'s `OF`
is instead a single global least fixed point over the whole compiled
automaton, with the product-state contribution `hide_I(OF(q₁)∪OF(q₂))` built
into that fixed point directly ("without inventing any new kind of edge") —
i.e. the current construction's synthetic-edge mechanism is exactly the kind
of thing the current spec rules out. Once `computeFuture`/`buildParallelAutomaton`
are reworked to match, this deleted content would not transfer over (it was
keyed to the exact synthetic-edge shape) and would need to be re-derived
against the new construction.
-/

namespace Pact

noncomputable section

/-- Every semantic parallel step yields a matching resolved product edge
(forward step direction). -/
theorem parallel_semantic_step_to_resolved_edge
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hInterface : interface ⊆ signature.interface)
    (hScoped : PactType.InterfaceScoped (.par left right interface))
    (hLeftStep : CompilationScopedFragmentStepCorrect signature left)
    (hRightStep : CompilationScopedFragmentStepCorrect signature right)
    (hLeftCanonical : left.EntryCanonical)
    (hRightCanonical : right.EntryCanonical)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation (.par left right interface) state
      residual)
    (hOuterEnvironment : environment ∈ signature.localEnvironments)
    (hOuterAvoids : environment.AvoidsInterface
      (PactType.ParallelInterfaces (PactType.par left right interface)))
    (hStep : DecoratedTypeTransition environment residual label offers
      residual') :
    ∃ target,
      (compileTypeFuel signature
        (typeCompilationFuel (.par left right interface))
        (.par left right interface)).HasResolvedEdge signature
          (.par left right interface) state environment label
          offers target ∧
      TypeCompilationRelation (.par left right interface) target residual' := by
  sorry -- TODO(redevelopment): needs re-deriving against the reworked
  -- `buildParallelAutomaton`/`computeFuture`; .

/-- Every resolved product edge yields the corresponding semantic parallel
step (reverse step direction). -/
theorem parallel_resolved_edge_to_semantic_step
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hInterface : interface ⊆ signature.interface)
    (hScoped : PactType.InterfaceScoped (.par left right interface))
    (hLeftStep : CompilationScopedFragmentStepCorrect signature left)
    (hRightStep : CompilationScopedFragmentStepCorrect signature right)
    (hLeftWitness :
      CompilationScopedResolvedOfferWitnessCorrect signature left)
    (hRightWitness :
      CompilationScopedResolvedOfferWitnessCorrect signature right)
    (hLeftCanonical : left.EntryCanonical)
    (hRightCanonical : right.EntryCanonical)
    {residual residual' : PactType} {state target : TypeAutomatonState}
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation (.par left right interface) state
      residual)
    (hOuterEnvironment : environment ∈ signature.localEnvironments)
    (hOuterAvoids : environment.AvoidsInterface
      (PactType.par left right interface).ParallelInterfaces)
    (hEdge : (compileTypeFuel signature
      (typeCompilationFuel (.par left right interface))
      (.par left right interface)).HasResolvedEdge signature
        (.par left right interface) state environment label
        offers target)
    (hTargetRelated : TypeCompilationRelation (.par left right interface)
      target residual') :
    DecoratedTypeTransition environment residual label offers residual' := by
  sorry -- TODO(redevelopment): needs re-deriving against the reworked
  -- `buildParallelAutomaton`/`computeFuture`; .

/-- Every resolved product edge reaches a state representing the semantic
targets (target preservation). -/
theorem compilationResolvedEdgeTargetsRelated_parallel
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hLeftTargets : CompilationResolvedEdgeTargetsRelated signature left)
    (hRightTargets : CompilationResolvedEdgeTargetsRelated signature right) :
    CompilationResolvedEdgeTargetsRelated signature
      (.par left right interface) := by
  sorry -- TODO(redevelopment): needs re-deriving against the reworked
  -- `buildParallelAutomaton`/`computeFuture`; .

/-- Scoped child step correctness plus target visibility gives the semantic
offer witness needed by synchronization (bridge from child bundles to
product reconstruction). -/
theorem compilationScopedResolvedOfferWitnessCorrect_of_step_targets_visible
    (signature : TypeAlphabet) (processType : PactType)
    (hStep : CompilationScopedFragmentStepCorrect signature processType)
    (hTargets : CompilationResolvedEdgeTargetsRelated signature processType)
    (hVisible : CompilationPendingEdgesVisible signature processType)
    (hCanonical : processType.EntryCanonical) :
    CompilationScopedResolvedOfferWitnessCorrect signature processType := by
  sorry -- TODO(redevelopment): needs re-deriving against the reworked
  -- `buildParallelAutomaton`/`computeFuture`; .

end

end Pact
