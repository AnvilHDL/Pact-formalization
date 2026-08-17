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
    AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right))
        (.child 0 source) env label offers (.child 0 target) ↔
      ∃ childFuture,
        AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature (typeCompilationFuel left) left)
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
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  have hNotDeleted' : target ∉ sequenceDeleted leftFragment := by
    rwa [hLeftStable]
  have hCore :=
    buildSequenceAutomaton_hasResolvedEdge_left_iff signature leftFragment
      rightFragment source target env label offers hNotDeleted'
  simpa only [fragment, hLeftStable, hFragment] using hCore

/-- Canonical raw-fragment form of an embedded right sequence edge. -/
theorem compileTypeFuel_sequence_right_child_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right))
        (.child 1 source) env label offers (.child 1 target) ↔
      AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel right) right)
        source env label offers target := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  have hCore :=
    buildSequenceAutomaton_hasResolvedEdge_right_iff signature leftFragment
      rightFragment source target env label offers hRightTargets
  simpa only [fragment, hRightStable] using hCore

/-- Canonical raw-fragment classification of every edge reaching the right
entry from a tagged left state: either an ordinary left edge whose own target
is deleted by the redirect (*fused* with the administrative step, keeping its
own label — see `sequenceLeftEdge`), or the literal entry bridge firing at
`left`'s own accepting entry (`sequenceEntryBridgeEdges`). -/
theorem compileTypeFuel_sequence_bridge_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right))
        (.child 0 source) env label offers
        (.child 1 (compileTypeFuel signature
          (typeCompilationFuel right) right).initial) ↔
      ((∃ childFuture deletedTarget,
          deletedTarget ∈ sequenceDeleted (compileTypeFuel signature
              (typeCompilationFuel left) left) ∧
          AutomatonFragment.HasResolvedEdge
              (compileTypeFuel signature (typeCompilationFuel left) left)
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
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment, ← hRightStable]
  have hCore :=
    buildSequenceAutomaton_hasResolvedEdge_bridge_iff signature leftFragment
      rightFragment source env label offers
  simpa only [fragment, hFragment, hLeftStable, hRightStable] using hCore

/-- Exact target-shape classification for every raw edge leaving a tagged left
sequence state: either an ordinary kept continuation (`.child 0 childTarget`,
`childTarget` not deleted by the redirect), or an edge landing on `right`'s
entry — either a fused ordinary left edge whose own target *is* deleted
(`seq_fuse`-shaped), or the literal entry bridge (`skip_seq`-shaped); see
`compileTypeFuel_sequence_bridge_edge_iff`. -/
theorem compileTypeFuel_sequence_left_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : AutomatonFragment.HasResolvedEdge
      (compileTypeFuel signature (typeCompilationFuel (.seq left right))
        (.seq left right))
      (.child 0 source) env label offers target) :
    (∃ childTarget childFuture,
        target = .child 0 childTarget ∧
        childTarget ∉ sequenceDeleted (compileTypeFuel signature
          (typeCompilationFuel left) left) ∧
        AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature (typeCompilationFuel left) left)
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
            AutomatonFragment.HasResolvedEdge
                (compileTypeFuel signature (typeCompilationFuel left) left)
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
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment] at hEdge
  rcases hEdge with ⟨pendingEdge, hPendingEdge, hSource, hEnvironment,
    hLabel, hCurrent, hResolvedFuture, hTarget⟩
  have hOutgoing :=
    (buildSequenceAutomaton_outgoing_left signature leftFragment rightFragment
      source pendingEdge).mp ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with hChild | hBridge | hFutureBridge
  · rcases hChild with ⟨childEdge, _, _, hPending⟩
    by_cases hDel : childEdge.target ∈ sequenceDeleted leftFragment
    · have hTargetEq : target = .child 1 rightFragment.initial := by
        rw [hPending, sequenceLeftEdge_target, sequenceRedirect_of_mem hDel]
          at hTarget
        simpa [childState] using hTarget.symm
      have hFixed : AutomatonFragment.HasResolvedEdge
          (compileTypeFuel signature (typeCompilationFuel (.seq left right))
            (.seq left right))
          (.child 0 source) env label offers
            (.child 1 (compileTypeFuel signature
              (typeCompilationFuel right) right).initial) := by
        rw [hFragment]
        simpa [hTargetEq, hRightStable] using (show fragment.HasResolvedEdge
          (.child 0 source) env label offers target from
            ⟨pendingEdge, hPendingEdge, hSource, hEnvironment, hLabel,
              hCurrent, hResolvedFuture, hTarget⟩)
      have hFields :=
        (compileTypeFuel_sequence_bridge_edge_iff signature left right source
          env label offers).mp hFixed
      right
      exact ⟨by simpa [hRightStable] using hTargetEq, hFields⟩
    · have hTargetEq : target = .child 0 childEdge.target := by
        rw [hPending, sequenceLeftEdge_target, sequenceRedirect_of_not_mem hDel]
          at hTarget
        simpa [childState] using hTarget.symm
      have hFixed : AutomatonFragment.HasResolvedEdge
          (compileTypeFuel signature (typeCompilationFuel (.seq left right))
            (.seq left right))
          (.child 0 source) env label offers (.child 0 childEdge.target) := by
        rw [hFragment]
        simpa [hTargetEq] using (show fragment.HasResolvedEdge
          (.child 0 source) env label offers target from
            ⟨pendingEdge, hPendingEdge, hSource, hEnvironment, hLabel,
              hCurrent, hResolvedFuture, hTarget⟩)
      have hDel' : childEdge.target ∉ sequenceDeleted
          (compileTypeFuel signature (typeCompilationFuel left) left) := by
        rwa [hLeftStable] at hDel
      rcases (compileTypeFuel_sequence_left_child_edge_iff signature left right
        source childEdge.target env label offers hDel').mp hFixed with
        ⟨childFuture, hChildResolved, hFuture⟩
      left
      exact ⟨childEdge.target, childFuture, hTargetEq, hDel', hChildResolved,
        hFuture⟩
  · rcases hBridge with ⟨_, _, _, _, hPending⟩
    have hTargetEq : target = .child 1 rightFragment.initial := by
      rw [hPending] at hTarget
      simpa [childState] using hTarget.symm
    have hFixed : AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right))
        (.child 0 source) env label offers
          (.child 1 (compileTypeFuel signature
            (typeCompilationFuel right) right).initial) := by
      rw [hFragment]
      simpa [hTargetEq, hRightStable] using (show fragment.HasResolvedEdge
        (.child 0 source) env label offers target from
          ⟨pendingEdge, hPendingEdge, hSource, hEnvironment, hLabel,
            hCurrent, hResolvedFuture, hTarget⟩)
    have hFields :=
      (compileTypeFuel_sequence_bridge_edge_iff signature left right source env
        label offers).mp hFixed
    right
    exact ⟨by simpa [hRightStable] using hTargetEq, hFields⟩
  · rcases hFutureBridge with ⟨_, hPending⟩
    rw [hPending] at hLabel
    simp at hLabel

/-- Exact target-shape classification for every raw edge leaving a tagged right
sequence state. -/
theorem compileTypeFuel_sequence_right_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : AutomatonFragment.HasResolvedEdge
      (compileTypeFuel signature (typeCompilationFuel (.seq left right))
        (.seq left right))
      (.child 1 source) env label offers target) :
    ∃ childTarget,
      target = .child 1 childTarget ∧
      AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel right) right)
        source env label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment] at hEdge
  rcases hEdge with ⟨pendingEdge, hPendingEdge, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  have hOutgoing :=
    (buildSequenceAutomaton_outgoing_right signature leftFragment rightFragment
      source pendingEdge).mp ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPending⟩
  have hTargetEq : target = .child 1 childEdge.target := by
    rw [hPending] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEq, ?_⟩
  apply (compileTypeFuel_sequence_right_child_edge_iff signature left right
    source childEdge.target env label offers).mp
  rw [hFragment]
  simpa [hTargetEq] using (show fragment.HasResolvedEdge
    (.child 1 source) env label offers target from
      ⟨pendingEdge, hPendingEdge, hSource, hEnvironment, hLabel, hCurrent,
        hFuture, hTarget⟩)


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
