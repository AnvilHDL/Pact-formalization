import Anvilpp.PactTypes.Correspondence.CorrespondenceSequenceGraph

/-!
# Sequence correspondence: future, step, completing
-/

namespace Pact

noncomputable section

/-- Canonical raw-fragment form of a lifted left sequence edge.  The parent
recomputes the future at the represented target, while preserving the child's
current offer set. -/
theorem compileTypeFuel_sequence_left_child_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hNotDeleted : target ∉ sequenceDeleted
      (compileTypeFuel signature (typeCompilationFuel left) left)) :
    (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right)).HasResolvedEdge signature (.seq left right)
        (.child 0 source) env label offers (.child 0 target) ↔
      ∃ childFuture,
        (compileTypeFuel signature (typeCompilationFuel left) left).HasResolvedEdge signature left
            source env label
              { current := offers.current, future := childFuture } target ∧
          computeFuture
              { states :=
                  (compileTypeFuel signature
                    (typeCompilationFuel (.seq left right))
                    (.seq left right)).states
                edges :=
                  (compileTypeFuel signature
                    (typeCompilationFuel (.seq left right))
                    (.seq left right)).edges }
              (.child 0 target) \ offers.current = offers.future := by
  sorry -- TODO(redevelopment): body relied on old computeFuture-based
  -- HasResolvedEdge classifiers deleted from CorrespondenceSequenceGraph.lean;
  -- .
theorem compileTypeFuel_sequence_right_child_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right)).HasResolvedEdge signature (.seq left right)
        (.child 1 source) env label offers (.child 1 target) ↔
      (compileTypeFuel signature (typeCompilationFuel right) right).HasResolvedEdge signature right
        source env label offers target := by
  sorry -- TODO(redevelopment): body relied on old computeFuture-based
  -- HasResolvedEdge classifiers deleted from CorrespondenceSequenceGraph.lean;
  -- .
theorem compileTypeFuel_sequence_bridge_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right)).HasResolvedEdge signature (.seq left right)
        (.child 0 source) env label offers
        (.child 1 (compileTypeFuel signature
          (typeCompilationFuel right) right).initial) ↔
      ((∃ childFuture deletedTarget,
          deletedTarget ∈ sequenceDeleted (compileTypeFuel signature
              (typeCompilationFuel left) left) ∧
          (compileTypeFuel signature (typeCompilationFuel left) left).HasResolvedEdge signature left
              source env label
                { current := offers.current, future := childFuture }
                deletedTarget ∧
          computeFuture
              { states :=
                  (compileTypeFuel signature
                    (typeCompilationFuel (.seq left right))
                    (.seq left right)).states
                edges :=
                  (compileTypeFuel signature
                    (typeCompilationFuel (.seq left right))
                    (.seq left right)).edges }
              (.child 1 (compileTypeFuel signature
                (typeCompilationFuel right) right).initial) \ offers.current =
            offers.future) ∨
        (source = (compileTypeFuel signature
            (typeCompilationFuel left) left).initial ∧
          (compileTypeFuel signature (typeCompilationFuel left) left).initial ∈
            (compileTypeFuel signature (typeCompilationFuel left) left).accepting ∧
          env ∈ signature.localEnvironments ∧
          label = TypeLabel.silent ∧ offers.current = ∅ ∧
          computeFuture
              { states :=
                  (compileTypeFuel signature
                    (typeCompilationFuel (.seq left right))
                    (.seq left right)).states
                edges :=
                  (compileTypeFuel signature
                    (typeCompilationFuel (.seq left right))
                    (.seq left right)).edges }
              (.child 1 (compileTypeFuel signature
                (typeCompilationFuel right) right).initial) = offers.future)) := by
  sorry -- TODO(redevelopment): body relied on old computeFuture-based
  -- HasResolvedEdge classifiers deleted from CorrespondenceSequenceGraph.lean;
  -- .
theorem compileTypeFuel_sequence_left_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileTypeFuel signature (typeCompilationFuel (.seq left right))
        (.seq left right)).HasResolvedEdge signature (.seq left right)
      (.child 0 source) env label offers target) :
    (∃ childTarget childFuture,
        target = .child 0 childTarget ∧
        childTarget ∉ sequenceDeleted (compileTypeFuel signature
          (typeCompilationFuel left) left) ∧
        (compileTypeFuel signature (typeCompilationFuel left) left).HasResolvedEdge signature left
            source env label
              { current := offers.current, future := childFuture }
              childTarget ∧
        computeFuture
            { states :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).states
              edges :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).edges }
            (.child 0 childTarget) \ offers.current = offers.future) ∨
      (target = .child 1 (compileTypeFuel signature
          (typeCompilationFuel right) right).initial ∧
        ((∃ childFuture deletedTarget,
            deletedTarget ∈ sequenceDeleted (compileTypeFuel signature
                (typeCompilationFuel left) left) ∧
            (compileTypeFuel signature (typeCompilationFuel left) left).HasResolvedEdge signature left
                source env label
                  { current := offers.current, future := childFuture }
                  deletedTarget ∧
            computeFuture
                { states :=
                    (compileTypeFuel signature
                      (typeCompilationFuel (.seq left right))
                      (.seq left right)).states
                  edges :=
                    (compileTypeFuel signature
                      (typeCompilationFuel (.seq left right))
                      (.seq left right)).edges }
                (.child 1 (compileTypeFuel signature
                  (typeCompilationFuel right) right).initial) \
                    offers.current = offers.future) ∨
          (source = (compileTypeFuel signature
              (typeCompilationFuel left) left).initial ∧
            (compileTypeFuel signature (typeCompilationFuel left) left).initial ∈
              (compileTypeFuel signature (typeCompilationFuel left) left).accepting ∧
            env ∈ signature.localEnvironments ∧
            label = TypeLabel.silent ∧ offers.current = ∅ ∧
            computeFuture
                { states :=
                    (compileTypeFuel signature
                      (typeCompilationFuel (.seq left right))
                      (.seq left right)).states
                  edges :=
                    (compileTypeFuel signature
                      (typeCompilationFuel (.seq left right))
                      (.seq left right)).edges }
                (.child 1 (compileTypeFuel signature
                  (typeCompilationFuel right) right).initial) =
              offers.future))) := by
  sorry -- TODO(redevelopment): body relied on old computeFuture-based
  -- HasResolvedEdge classifiers deleted from CorrespondenceSequenceGraph.lean;
  -- .
theorem compileTypeFuel_sequence_right_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileTypeFuel signature (typeCompilationFuel (.seq left right))
        (.seq left right)).HasResolvedEdge signature (.seq left right)
      (.child 1 source) env label offers target) :
    ∃ childTarget,
      target = .child 1 childTarget ∧
      (compileTypeFuel signature (typeCompilationFuel right) right).HasResolvedEdge signature right
        source env label offers childTarget := by
  sorry -- TODO(redevelopment): body relied on old computeFuture-based
  -- HasResolvedEdge classifiers deleted from CorrespondenceSequenceGraph.lean;
  -- .
theorem TypeOffers.skip_sequence_fields
    {env : TypeEnvironment} {right : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.seq .skip right) TypeLabel.silent right
      current future) :
    current = ∅ ∧ future = typeFutureOffers right := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers with
  | seq_fuse _ _ _ _ _ _ hInner => cases hInner <;> simp_all
  | _ => simp_all

theorem TypeOffers.sequence_fields
    {env : TypeEnvironment} {left left' right : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.seq left right) label (.seq left' right)
      current future) :
    ∃ childFuture,
      TypeOffers env left label left' current childFuture ∧
        future = typeFutureOffers (.seq left' right) \ current := by
  generalize hLabel : label = actualLabel at hOffers
  cases hOffers with
  | seq _ _ _ _ _ _ childFuture hChild =>
      subst actualLabel
      exact ⟨childFuture, hChild, rfl⟩
  | _ => simp_all

/-- Optimistic completion metadata composes pointwise through sequencing.
The left tagged state completes exactly when both its represented residual and
the right entry complete; a right tagged state simply inherits the right
child's predicate. -/
theorem compilationCompletingCorrect_sequence
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationCompletingCorrect signature left)
    (hRight : CompilationCompletingCorrect signature right)
    (hRightCanonical : right.EntryCanonical) :
    CompilationCompletingCorrect signature (.seq left right) := by
  intro state residual hRelated
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment = compileTypeFuel signature
      (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment = compileTypeFuel signature
      (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hRightInitial : rightFragment.initial ∈ rightFragment.completing ↔
      right.CanCompleteBeforeTock = true := by
    have hInitialRelation :=
      compileType_initial_relation_of_canonical signature right
        (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
          hRightCanonical)
    have hCanonical := hRight _ right hInitialRelation
    simpa [rightFragment, hRightStable, compileType] using hCanonical
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) =
        buildSequenceAutomaton signature leftFragment rightFragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  cases hRelated with
  | sequence_left_entry _ _ childResidual childQ _ hChildRelated =>
      have hLeftChild : childQ ∈ leftFragment.completing ↔
          childResidual.CanCompleteBeforeTock = true := by
        have hCanonical := hLeft childQ childResidual hChildRelated
        simpa [leftFragment, hLeftStable] using hCanonical
      change childState 0 childQ ∈
          (buildSequenceAutomaton signature leftFragment rightFragment).completing ↔
        (PactType.seq childResidual right).CanCompleteBeforeTock = true
      by_cases hRightComplete : right.CanCompleteBeforeTock = true
      · simp [buildSequenceAutomaton, finishAutomatonFragment, childCompleting,
          childState, hLeftChild, hRightInitial, hRightComplete,
          PactType.CanCompleteBeforeTock]
      · simp [buildSequenceAutomaton, finishAutomatonFragment, childCompleting,
          childState, hRightInitial, hRightComplete,
          PactType.CanCompleteBeforeTock]
  | sequence_left_progressed _ _ childResidual childQ hChildRelated _ =>
      have hLeftChild : childQ ∈ leftFragment.completing ↔
          childResidual.CanCompleteBeforeTock = true := by
        have hCanonical := hLeft childQ childResidual hChildRelated
        simpa [leftFragment, hLeftStable] using hCanonical
      change childState 0 childQ ∈
          (buildSequenceAutomaton signature leftFragment rightFragment).completing ↔
        (PactType.seq childResidual right).CanCompleteBeforeTock = true
      by_cases hRightComplete : right.CanCompleteBeforeTock = true
      · simp [buildSequenceAutomaton, finishAutomatonFragment, childCompleting,
          childState, hLeftChild, hRightInitial, hRightComplete,
          PactType.CanCompleteBeforeTock]
      · simp [buildSequenceAutomaton, finishAutomatonFragment, childCompleting,
          childState, hRightInitial, hRightComplete,
          PactType.CanCompleteBeforeTock]
  | sequence_right _ _ _ childQ hChildRelated =>
      have hNotLeft : childState 1 childQ ∉
          (if rightFragment.initial ∈ rightFragment.completing then
            childCompleting 0 leftFragment
          else ∅) := by
        split <;> simp [childCompleting, childState]
      have hCanonical := hRight childQ _ hChildRelated
      constructor
      · intro hCompleting
        simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union] at hCompleting
        rcases hCompleting with hImpossible | hChild
        · exact (hNotLeft hImpossible).elim
        · apply hCanonical.mp
          simpa [childCompleting, childState, rightFragment,
            hRightStable] using hChild
      · intro hResidual
        simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union]
        right
        have hChild := hCanonical.mpr hResidual
        simpa [childCompleting, childState, rightFragment,
          hRightStable] using hChild

end

end Pact
