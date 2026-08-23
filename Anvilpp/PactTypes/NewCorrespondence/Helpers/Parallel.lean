import Anvilpp.PactTypes.NewCorrespondence.Helpers.Sequence

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-- Describes the two semantic forms of a decorated parallel step. -/
inductive ParDecoratedStepCase
    (left right : PactType) (interface : Interface) (target : PactType)
    (env : TypeEnvironment) (label : TypeLabel)
    (current future : Finset BareMessage) : Prop where
  | step (leftEnv rightEnv : TypeEnvironment) (leftLabel rightLabel : TypeLabel)
      (leftTarget rightTarget : PactType)
      (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
      target = .par leftTarget rightTarget interface →
      ¬ (leftTarget = .skip ∧ rightTarget = .skip) →
      DecoratedTypeTransition leftEnv left leftLabel
        (TypeOfferSummary.mk leftCurrent leftFuture) leftTarget →
      DecoratedTypeTransition rightEnv right rightLabel
        (TypeOfferSummary.mk rightCurrent rightFuture) rightTarget →
      env.WellFormed →
      LocalTypeEnvironment env interface rightEnv right rightLabel leftEnv →
      LocalTypeEnvironment env interface leftEnv left leftLabel rightEnv →
      TypeLabel.Sync interface leftLabel rightLabel →
      label = TypeLabel.combine interface leftLabel rightLabel →
      current = hideTypeOffers interface (leftCurrent ∪ rightCurrent) →
      future = hideTypeOffers interface (leftFuture ∪ rightFuture) →
      ParDecoratedStepCase left right interface target env label current future
  | fuse (leftEnv rightEnv : TypeEnvironment) (leftLabel rightLabel : TypeLabel)
      (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
      target = .skip →
      DecoratedTypeTransition leftEnv left leftLabel
        (TypeOfferSummary.mk leftCurrent leftFuture) .skip →
      DecoratedTypeTransition rightEnv right rightLabel
        (TypeOfferSummary.mk rightCurrent rightFuture) .skip →
      env.WellFormed →
      LocalTypeEnvironment env interface rightEnv right rightLabel leftEnv →
      LocalTypeEnvironment env interface leftEnv left leftLabel rightEnv →
      TypeLabel.Sync interface leftLabel rightLabel →
      label = TypeLabel.combine interface leftLabel rightLabel →
      current = hideTypeOffers interface (leftCurrent ∪ rightCurrent) →
      future = hideTypeOffers interface (leftFuture ∪ rightFuture) →
      ParDecoratedStepCase left right interface target env label current future

theorem par_witnesses_agree
    {env : TypeEnvironment} {left right leftTarget rightTarget : PactType}
    {interface : Interface} {leftEnv rightEnv leftEnv' rightEnv' : TypeEnvironment}
    {leftLabel rightLabel leftLabel' rightLabel' : TypeLabel}
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    (hLeftTrans : TypeTransition leftEnv left leftLabel leftTarget)
    (hRightTrans : TypeTransition rightEnv right rightLabel rightTarget)
    (hWF : env.WellFormed)
    (hLocal1 : LocalTypeEnvironment env interface rightEnv right rightLabel leftEnv)
    (hLocal2 : LocalTypeEnvironment env interface leftEnv left leftLabel rightEnv)
    (hSync : TypeLabel.Sync interface leftLabel rightLabel)
    (hLeftOffers : TypeOffers leftEnv' left leftLabel' leftTarget leftCurrent leftFuture)
    (hRightOffers : TypeOffers rightEnv' right rightLabel' rightTarget rightCurrent rightFuture)
    (hWF' : env.WellFormed)
    (hLocal1' : LocalTypeEnvironment env interface rightEnv' right rightLabel' leftEnv')
    (hLocal2' : LocalTypeEnvironment env interface leftEnv' left leftLabel' rightEnv')
    (hSync' : TypeLabel.Sync interface leftLabel' rightLabel')
    (hCombineEq :
      TypeLabel.combine interface leftLabel rightLabel =
        TypeLabel.combine interface leftLabel' rightLabel') :
    leftEnv = leftEnv' ∧ rightEnv = rightEnv' ∧ leftLabel = leftLabel' ∧
      rightLabel = rightLabel' := by
    sorry

/-- Proves that every decorated parallel step either retains both components or fuses them once both complete. -/
theorem decoratedTypeTransition_par_cases
    {env : TypeEnvironment} {label : TypeLabel}
    {left right target : PactType} {interface : Interface}
    {current future : Finset BareMessage}
    (hStep :
      DecoratedTypeTransition env (.par left right interface) label
        (TypeOfferSummary.mk current future) target) :
    ParDecoratedStepCase left right interface target env label current future := by
  rcases hStep with ⟨hTransition, hOffers⟩
  cases hTransition with
  | par _ leftEnv rightEnv _ _ leftTarget _ rightTarget leftLabel rightLabel
      hLeftTrans hRightTrans hNonFinal hSide =>
      obtain ⟨hWF, hLocal1, hLocal2, hSync⟩ := hSide
      change TypeOffers env (.par left right interface)
        (TypeLabel.combine interface leftLabel rightLabel)
        (.par leftTarget rightTarget interface) current future at hOffers
      generalize hCombineEq :
        TypeLabel.combine interface leftLabel rightLabel = actualLabel at hOffers
      cases hOffers with
      | par _ leftEnv' rightEnv' _ _ _ _ _ leftLabel' rightLabel'
          leftCurrent leftFuture rightCurrent rightFuture
          hLeftOffers hRightOffers _hNonFinal' hLocal1' hLocal2' hWFSync' =>
          obtain ⟨hWF', hSync'⟩ := hWFSync'
          obtain ⟨hEnvEq1, hEnvEq2, hLabelEq1, hLabelEq2⟩ :=
            par_witnesses_agree hLeftTrans hRightTrans hWF hLocal1 hLocal2 hSync
              hLeftOffers hRightOffers hWF' hLocal1' hLocal2' hSync' hCombineEq
          subst hEnvEq1; subst hEnvEq2; subst hLabelEq1; subst hLabelEq2
          exact ParDecoratedStepCase.step leftEnv rightEnv leftLabel rightLabel leftTarget
            rightTarget leftCurrent leftFuture rightCurrent rightFuture rfl hNonFinal
            ⟨hLeftTrans, hLeftOffers⟩ ⟨hRightTrans, hRightOffers⟩ hWF hLocal1 hLocal2 hSync
            hCombineEq rfl rfl
  | par_fuse _ leftEnv rightEnv _ _ _ leftLabel rightLabel
      hLeftTrans hRightTrans hSide =>
      obtain ⟨hWF, hLocal1, hLocal2, hSync⟩ := hSide
      change TypeOffers env (.par left right interface)
        (TypeLabel.combine interface leftLabel rightLabel) .skip current future at hOffers
      generalize hCombineEq :
        TypeLabel.combine interface leftLabel rightLabel = actualLabel at hOffers
      cases hOffers with
      | par_fuse _ leftEnv' rightEnv' _ _ _ leftLabel' rightLabel'
          leftCurrent leftFuture rightCurrent rightFuture
          hLeftOffers hRightOffers hLocal1' hLocal2' hWFSync' =>
          obtain ⟨hWF', hSync'⟩ := hWFSync'
          obtain ⟨hEnvEq1, hEnvEq2, hLabelEq1, hLabelEq2⟩ :=
            par_witnesses_agree hLeftTrans hRightTrans hWF hLocal1 hLocal2 hSync
              hLeftOffers hRightOffers hWF' hLocal1' hLocal2' hSync' hCombineEq
          subst hEnvEq1; subst hEnvEq2; subst hLabelEq1; subst hLabelEq2
          exact ParDecoratedStepCase.fuse leftEnv rightEnv leftLabel rightLabel leftCurrent
            leftFuture rightCurrent rightFuture rfl ⟨hLeftTrans, hLeftOffers⟩
            ⟨hRightTrans, hRightOffers⟩ hWF hLocal1 hLocal2 hSync hCombineEq rfl rfl

/-- Automaton-level counterpart of `T-Par`/`T-Par-Fuse`: a compiled edge out
of a product state exists exactly when the two components admit synchronized
decorated steps under the shared interface, using the semantic rule's own
`LocalTypeEnvironment`/`Sync` side conditions verbatim. Packages the whole
gap between `buildParallelAutomaton`'s locally-resolved synchronized-edge
construction and the native (`computeFutureOf`-based) `HasEdge` view
`StepIffStatement`'s goals are stated in, mirroring `T-Par` directly rather
than exposing `syncAutomatonEdges`'s internal witness machinery. Note that the `LocalTypeEnvironment` side conditions are stated over
whatever sibling `PactType` (`childLeft`/`childRight`) the caller's
residuals happen to be, not over the outer, fixed `left`/`right` the
automaton was compiled for — `T-Par` is a rule about the *current* residual
at every step, not only the initial one, and the compiled child automata
`compileType signature left`/`compileType signature right` are shared
across every residual reachable inside them. `childLeft`/`childRight` come
bundled with a relation-membership witness at `q1`/`q2` precisely so a
caller who already knows some other residual relates to `q1`/`q2` can pin
`childLeft`/`childRight` down via `relationMembership_functional`, rather
than being stuck comparing two independently-existentially-chosen
`PactType`s. -/
theorem buildParallelAutomaton_pair_hasEdge_iff
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    (q1 q2 target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileType signature (.par left right interface)).HasEdge
        (.pair q1 q2) env label offers target ↔
      ∃ (childLeft childRight : PactType)
        (leftEnv rightEnv : TypeEnvironment) (leftLabel rightLabel : TypeLabel)
        (leftOffers rightOffers : TypeOfferSummary) (q1' q2' : TypeAutomatonState),
        (compileType signature left).HasEdge q1 leftEnv leftLabel leftOffers q1' ∧
        (compileType signature right).HasEdge q2 rightEnv rightLabel rightOffers q2' ∧
        relationMembership (buildRelationSet left (compileType signature left))
          childLeft q1 ∧
        relationMembership (buildRelationSet right (compileType signature right))
          childRight q2 ∧
        env.WellFormed ∧
        LocalTypeEnvironment env interface rightEnv childRight rightLabel leftEnv ∧
        LocalTypeEnvironment env interface leftEnv childLeft leftLabel rightEnv ∧
        TypeLabel.Sync interface leftLabel rightLabel ∧
        label = TypeLabel.combine interface leftLabel rightLabel ∧
        offers.current =
          hideTypeOffers interface (leftOffers.current ∪ rightOffers.current) ∧
        offers.future =
          hideTypeOffers interface (leftOffers.future ∪ rightOffers.future) ∧
        -- Mirrors the compiler's own redirect: a raw target whose both sides
        -- are accepting (H13: exactly when both children finish) is placed
        -- in `q_done`, never left as its own separate `.pair` state.
        (if q1' ∈ (compileType signature left).accepting ∧
            q2' ∈ (compileType signature right).accepting then
          target = TypeAutomatonState.final
        else target = .pair q1' q2') := by
  sorry

/-- The `q_done` state's own outgoing edges are exactly the non-clock silent
idle self-loop, mirroring `.final`'s identical role in every atomic base
case (`.message`, `.tock`, `.progress`). -/
theorem buildParallelAutomaton_final_hasEdge_iff
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    (env : TypeEnvironment) (label : TypeLabel) (offers : TypeOfferSummary)
    (target : TypeAutomatonState) :
    (compileType signature (.par left right interface)).HasEdge
        TypeAutomatonState.final env label offers target ↔
      env.WellFormed ∧ env.clock = false ∧ label = TypeLabel.silent ∧
      offers = TypeOfferSummary.mk ∅ ∅ ∧ target = TypeAutomatonState.final := by
  sorry

/-- Proves each parallel component's own offer pair remains in its own
transition alphabet whenever the combined, interface-hidden parent symbol
is in the fixed alphabet, mirroring `transitionAlphabet_of_typeOffers_target_subset`
for `.par`'s two-sided hiding pattern (which changes both the current and
future components, unlike `.seq`'s future-only pattern that lemma covers). -/
theorem transitionAlphabet_of_par_component
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    {leftEnv rightEnv : TypeEnvironment} {leftLabel rightLabel : TypeLabel}
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    {env : TypeEnvironment} {label : TypeLabel}
    (hWF : env.WellFormed)
    (hLocal1 : LocalTypeEnvironment env interface rightEnv right rightLabel leftEnv)
    (hLocal2 : LocalTypeEnvironment env interface leftEnv left leftLabel rightEnv)
    (hSync : TypeLabel.Sync interface leftLabel rightLabel)
    (hLabelEq : label = TypeLabel.combine interface leftLabel rightLabel)
    (hSymbol :
      TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
          (hideTypeOffers interface (leftFuture ∪ rightFuture))) ∈
        signature.transitionAlphabet) :
    TypeAutomatonSymbol.mk leftEnv leftLabel
        (TypeOfferSummary.mk leftCurrent leftFuture) ∈
      signature.transitionAlphabet ∧
    TypeAutomatonSymbol.mk rightEnv rightLabel
        (TypeOfferSummary.mk rightCurrent rightFuture) ∈
      signature.transitionAlphabet := by
  sorry

/-- Every accepting state of a compiled fragment is related to `skip` — the
converse direction of H13's characterization. Needed when a `.par` redirect
edge's target is already pinned (by the compiler's own construction) to a
pair of accepting states, without any pre-existing `relationMembership`
witness at that specific pair to read H13 off of directly. -/
theorem relationMembership_of_accepting
    (signature : TypeAlphabet) (processType : PactType) {state : TypeAutomatonState}
    (hAccept : state ∈ (compileType signature processType).accepting) :
    relationMembership (buildRelationSet processType (compileType signature processType))
      PactType.skip state := by
  sorry

/-- Defines the related-state shape for a compiled parallel product,
mirroring `pactproofs.typ`'s own "Related states" bullets verbatim: a
product state represents the pointwise composition, or the dedicated
`q_done` state (`.final`) represents `skip` once both components finish. -/
def parRelationShape
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    (entry : PactType × TypeAutomatonState) : Prop :=
  (∃ q1 q2 residualLeft residualRight,
      entry = (.par residualLeft residualRight interface, .pair q1 q2) ∧
      relationMembership (buildRelationSet left (compileType signature left))
        residualLeft q1 ∧
      relationMembership (buildRelationSet right (compileType signature right))
        residualRight q2) ∨
    entry = (PactType.skip, TypeAutomatonState.final)

/-- Proves every related parallel pair has the parallel shape. -/
lemma relationMembership_par_cases
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    (hLeftForward :
      ∀ {residual' : PactType} {q1 : TypeAutomatonState} {env : TypeEnvironment}
        {label : TypeLabel} {offers : TypeOfferSummary} {target : PactType},
        relationMembership (buildRelationSet left (compileType signature left))
          residual' q1 →
        (TypeAutomatonSymbol.mk env label offers ∈
          (compileType signature left).alphabet) →
        DecoratedTypeTransition env residual' label offers target →
        ∃ q1', (compileType signature left).HasEdge q1 env label offers q1' ∧
          relationMembership (buildRelationSet left (compileType signature left))
            target q1')
    (hRightForward :
      ∀ {residual' : PactType} {q2 : TypeAutomatonState} {env : TypeEnvironment}
        {label : TypeLabel} {offers : TypeOfferSummary} {target : PactType},
        relationMembership (buildRelationSet right (compileType signature right))
          residual' q2 →
        (TypeAutomatonSymbol.mk env label offers ∈
          (compileType signature right).alphabet) →
        DecoratedTypeTransition env residual' label offers target →
        ∃ q2', (compileType signature right).HasEdge q2 env label offers q2' ∧
          relationMembership (buildRelationSet right (compileType signature right))
            target q2')
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.par left right interface)
          (compileType signature (.par left right interface)))
        residual state) :
    parRelationShape signature left right interface (residual, state) := by
  sorry
  -- have hFuelEq : typeCompilationFuel (.par left right interface) =
  --     max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
  --   simp only [typeCompilationFuel]; omega
  -- have hWhole :
  --     compileTypeFuel signature (typeCompilationFuel (.par left right interface))
  --       (.par left right interface) =
  --       buildParallelAutomaton signature interface
  --         (compileTypeFuel signature (typeCompilationFuel left) left)
  --         (compileTypeFuel signature (typeCompilationFuel right) right) := by
  --   rw [hFuelEq]
  --   show buildParallelAutomaton signature interface
  --       (compileTypeFuel signature
  --         (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
  --       (compileTypeFuel signature
  --         (max (typeCompilationFuel left) (typeCompilationFuel right)) right) =
  --     buildParallelAutomaton signature interface
  --       (compileTypeFuel signature (typeCompilationFuel left) left)
  --       (compileTypeFuel signature (typeCompilationFuel right) right)
  --   congr 1
  --   · exact compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl
  --   · exact compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl
  -- have hInit : (compileType signature (.par left right interface)).initial =
  --     .pair (compileType signature left).initial (compileType signature right).initial := by
  --   show (compileTypeFuel signature (typeCompilationFuel (.par left right interface))
  --     (.par left right interface)).initial = _
  --   rw [hWhole]
  --   simp only [buildParallelAutomaton, finishAutomatonFragment]
  --   rfl
  -- have hResult :=
  --   buildRelationSet_preserves (.par left right interface)
  --   (compileType signature (.par left right interface))
  --   (fun entry =>
  --     relationMembership
  --       (buildRelationSet (.par left right interface)
  --         (compileType signature (.par left right interface)))
  --       entry.1 entry.2 ∧
  --     parRelationShape signature left right interface entry)
  --   (by
  --     refine ⟨buildRelationSet_initial (.par left right interface)
  --       (compileType signature (.par left right interface)), ?_⟩
  --     show parRelationShape signature left right interface
  --       (.par left right interface,
  --         (compileType signature (.par left right interface)).initial)
  --     rw [hInit]
  --     exact Or.inl ⟨(compileType signature left).initial,
  --       (compileType signature right).initial, left, right, rfl,
  --       buildRelationSet_initial left (compileType signature left),
  --       buildRelationSet_initial right (compileType signature right)⟩)
  --   (by
  --     intro entry hEntryAnd successor hSuccessor
  --     obtain ⟨hEntryMem, hEntry⟩ := hEntryAnd
  --     have hSuccessorMem :
  --         relationMembership
  --           (buildRelationSet (.par left right interface)
  --             (compileType signature (.par left right interface)))
  --           successor.1 successor.2 :=
  --       buildRelationSet_saturated (.par left right interface)
  --         (compileType signature (.par left right interface)) entry hEntryMem hSuccessor
  --     refine ⟨hSuccessorMem, ?_⟩
  --     rcases relationSuccessors_mem_cases (compileType signature (.par left right interface))
  --       entry successor hSuccessor with ⟨edge, hEdgeMem, hSource, hTarget, hStep⟩
  --     have hSymbolMem := compileType_hasEdge_symbol_mem signature (.par left right interface)
  --       (show (compileType signature (.par left right interface)).HasEdge edge.source
  --         edge.symbol.environment edge.symbol.label edge.symbol.offers edge.target
  --         from hEdgeMem)
  --     have hOuterMem :
  --         TypeAutomatonSymbol.mk edge.symbol.environment edge.symbol.label
  --             edge.symbol.offers ∈ signature.transitionAlphabet := by
  --       simpa [compileType] using hSymbolMem
  --     have hOuterEdge :
  --         (compileType signature (.par left right interface)).HasEdge entry.2
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers successor.2 := by
  --       rw [← hSource, hTarget]; exact hEdgeMem
  --     rw [show edge.symbol.offers = TypeOfferSummary.mk edge.symbol.offers.current
  --       edge.symbol.offers.future from rfl] at hStep hOuterMem hOuterEdge
  --     rcases hEntry with
  --       ⟨q1, q2, residualLeft, residualRight, hEntryEq, hLeftRelated, hRightRelated⟩ | hEntryEq
  --     · -- general product case: `entry` represents `.par residualLeft residualRight interface`
  --       have hEntry1 : entry.1 = .par residualLeft residualRight interface := by rw [hEntryEq]
  --       have hEntry2 : entry.2 = .pair q1 q2 := by rw [hEntryEq]
  --       rw [hEntry1] at hStep
  --       rw [hEntry2] at hOuterEdge
  --       cases decoratedTypeTransition_par_cases hStep with
  --       | step leftEnv rightEnv leftLabel rightLabel leftTarget rightTarget
  --           leftCurrent leftFuture rightCurrent rightFuture hTargetEq hNonFinal
  --           hLeftStep hRightStep hWF hLocal1 hLocal2 hSync hLabelEq hCurrentEq hFutureEq =>
  --           obtain ⟨hLeftSymbolMem0, hRightSymbolMem0⟩ :=
  --             transitionAlphabet_of_par_component signature residualLeft residualRight
  --               interface hWF hLocal1 hLocal2 hSync hLabelEq
  --               (hCurrentEq ▸ hFutureEq ▸ hOuterMem)
  --           have hLeftSymbolMem :
  --               TypeAutomatonSymbol.mk leftEnv leftLabel
  --                 (TypeOfferSummary.mk leftCurrent leftFuture) ∈
  --                 (compileType signature left).alphabet := by
  --             simpa [compileType] using hLeftSymbolMem0
  --           have hRightSymbolMem :
  --               TypeAutomatonSymbol.mk rightEnv rightLabel
  --                 (TypeOfferSummary.mk rightCurrent rightFuture) ∈
  --                 (compileType signature right).alphabet := by
  --             simpa [compileType] using hRightSymbolMem0
  --           obtain ⟨q1', hLeftEdge, hLeftTargetRelated⟩ :=
  --             hLeftForward hLeftRelated hLeftSymbolMem hLeftStep
  --           obtain ⟨q2', hRightEdge, hRightTargetRelated⟩ :=
  --             hRightForward hRightRelated hRightSymbolMem hRightStep
  --           -- H13: at least one of `q1'`/`q2'` is not accepting, since a
  --           -- child remains (`hNonFinal`), so the compiler does not redirect.
  --           have hNotBothAccept :
  --               ¬ (q1' ∈ (compileType signature left).accepting ∧
  --                  q2' ∈ (compileType signature right).accepting) := by
  --             rintro ⟨hAccept1, hAccept2⟩
  --             exact hNonFinal
  --               ⟨(helper_h13_final_states_represent_completion signature
  --                   hLeftTargetRelated).mp hAccept1,
  --                 (helper_h13_final_states_represent_completion signature
  --                   hRightTargetRelated).mp hAccept2⟩
  --           have hConstructedEdge :
  --               (compileType signature (.par left right interface)).HasEdge
  --                 (.pair q1 q2) edge.symbol.environment edge.symbol.label
  --                 (TypeOfferSummary.mk edge.symbol.offers.current
  --                   edge.symbol.offers.future) (.pair q1' q2') := by
  --             rw [buildParallelAutomaton_pair_hasEdge_iff]
  --             refine ⟨residualLeft, residualRight, leftEnv, rightEnv, leftLabel, rightLabel,
  --               TypeOfferSummary.mk leftCurrent leftFuture,
  --               TypeOfferSummary.mk rightCurrent rightFuture, q1', q2',
  --               hLeftEdge, hRightEdge, hLeftRelated, hRightRelated, hWF, hLocal1, hLocal2,
  --               hSync, hLabelEq, hCurrentEq, hFutureEq, ?_⟩
  --             simp [hNotBothAccept]
  --           have hSuccessorEq : successor.2 = .pair q1' q2' :=
  --             compileType_hasEdge_target_unique signature (.par left right interface)
  --               hOuterEdge hConstructedEdge
  --           exact Or.inl ⟨q1', q2', leftTarget, rightTarget, Prod.ext hTargetEq hSuccessorEq,
  --             hLeftTargetRelated, hRightTargetRelated⟩
  --       | fuse leftEnv rightEnv leftLabel rightLabel leftCurrent leftFuture rightCurrent
  --           rightFuture hTargetEq hLeftStep hRightStep hWF hLocal1 hLocal2 hSync hLabelEq
  --           hCurrentEq hFutureEq =>
  --           obtain ⟨hLeftSymbolMem0, hRightSymbolMem0⟩ :=
  --             transitionAlphabet_of_par_component signature residualLeft residualRight
  --               interface hWF hLocal1 hLocal2 hSync hLabelEq
  --               (hCurrentEq ▸ hFutureEq ▸ hOuterMem)
  --           have hLeftSymbolMem :
  --               TypeAutomatonSymbol.mk leftEnv leftLabel
  --                 (TypeOfferSummary.mk leftCurrent leftFuture) ∈
  --                 (compileType signature left).alphabet := by
  --             simpa [compileType] using hLeftSymbolMem0
  --           have hRightSymbolMem :
  --               TypeAutomatonSymbol.mk rightEnv rightLabel
  --                 (TypeOfferSummary.mk rightCurrent rightFuture) ∈
  --                 (compileType signature right).alphabet := by
  --             simpa [compileType] using hRightSymbolMem0
  --           obtain ⟨q1', hLeftEdge, hLeftTargetRelated⟩ :=
  --             hLeftForward hLeftRelated hLeftSymbolMem hLeftStep
  --           obtain ⟨q2', hRightEdge, hRightTargetRelated⟩ :=
  --             hRightForward hRightRelated hRightSymbolMem hRightStep
  --           -- H13: both children finish here, so the compiler redirects to `q_done`.
  --           have hBothAccept :
  --               q1' ∈ (compileType signature left).accepting ∧
  --               q2' ∈ (compileType signature right).accepting :=
  --             ⟨(helper_h13_final_states_represent_completion signature
  --                 hLeftTargetRelated).mpr rfl,
  --               (helper_h13_final_states_represent_completion signature
  --                 hRightTargetRelated).mpr rfl⟩
  --           have hConstructedEdge :
  --               (compileType signature (.par left right interface)).HasEdge
  --                 (.pair q1 q2) edge.symbol.environment edge.symbol.label
  --                 (TypeOfferSummary.mk edge.symbol.offers.current
  --                   edge.symbol.offers.future) TypeAutomatonState.final := by
  --             rw [buildParallelAutomaton_pair_hasEdge_iff]
  --             refine ⟨residualLeft, residualRight, leftEnv, rightEnv, leftLabel, rightLabel,
  --               TypeOfferSummary.mk leftCurrent leftFuture,
  --               TypeOfferSummary.mk rightCurrent rightFuture, q1', q2',
  --               hLeftEdge, hRightEdge, hLeftRelated, hRightRelated, hWF, hLocal1, hLocal2,
  --               hSync, hLabelEq, hCurrentEq, hFutureEq, ?_⟩
  --             simp [hBothAccept]
  --           have hSuccessorEq : successor.2 = TypeAutomatonState.final :=
  --             compileType_hasEdge_target_unique signature (.par left right interface)
  --               hOuterEdge hConstructedEdge
  --           exact Or.inr (Prod.ext hTargetEq hSuccessorEq)
  --     · -- `q_done` case: `entry` already represents `skip` at the dedicated
  --       -- done state; its only public edge is the non-clock silent idle
  --       -- self-loop, which the atomic `skip` step matches directly
  --       -- (paper's "Forward direction at the done state").
  --       have hEntry1 : entry.1 = PactType.skip := by rw [hEntryEq]
  --       have hEntry2 : entry.2 = TypeAutomatonState.final := by rw [hEntryEq]
  --       rw [hEntry1] at hStep
  --       rw [hEntry2] at hOuterEdge
  --       rw [buildParallelAutomaton_final_hasEdge_iff] at hOuterEdge
  --       obtain ⟨hWF, hClock, hLabelEqDone, hOffersEqDone, hSuccessorEq⟩ := hOuterEdge
  --       rw [hLabelEqDone, hOffersEqDone] at hStep
  --       have hSkipStep : DecoratedTypeTransition edge.symbol.environment .skip
  --           TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) PactType.skip :=
  --         ⟨TypeTransition.skip edge.symbol.environment ⟨hWF, hClock⟩,
  --           TypeOffers.skip edge.symbol.environment ⟨hWF, hClock⟩⟩
  --       have hSuccessor1Eq : successor.1 = PactType.skip :=
  --         decoratedTypeTransition_target_unique hStep hSkipStep
  --       exact Or.inr (Prod.ext hSuccessor1Eq hSuccessorEq))
  --   (residual, state) hRelated
  -- exact hResult.2


end

end Pact
