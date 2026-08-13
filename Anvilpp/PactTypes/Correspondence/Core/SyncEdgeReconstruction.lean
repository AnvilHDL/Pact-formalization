import Anvilpp.PactTypes.Correspondence.Core.ParallelEnvironment

/-!
# Reconstructing a synchronized parallel edge from its two LocalTypeEnvironment components
-/

namespace Pact

noncomputable section

private theorem hideOffers_partition (interface : Interface)
    (offers : Finset BareMessage) :
    hideOffers interface offers ∪ interfaceOffers interface offers = offers := by
  ext action
  simp [hideOffers, interfaceOffers]
  tauto

private theorem hideOffers_disjoint_interfaceOffers (interface : Interface)
    (offers : Finset BareMessage) :
    Disjoint (hideOffers interface offers) (interfaceOffers interface offers) := by
  rw [Finset.disjoint_left]
  intro action hHidden hInterface
  exact (Finset.mem_filter.mp hHidden).2
    (Finset.mem_filter.mp hInterface).2

private theorem finset_eq_of_hideOffers_eq_of_interfaceOffers_eq
    (interface : Interface) {left right : Finset BareMessage}
    (hHidden : hideOffers interface left = hideOffers interface right)
    (hInterface : interfaceOffers interface left =
      interfaceOffers interface right) :
    left = right := by
  rw [← hideOffers_partition interface left,
    ← hideOffers_partition interface right, hHidden, hInterface]

private theorem hideOffers_union (interface : Interface)
    (left right : Finset BareMessage) :
    hideOffers interface (left ∪ right) =
      hideOffers interface left ∪ hideOffers interface right := by
  ext action
  simp [hideOffers]
  tauto

private theorem interfaceOffers_union (interface : Interface)
    (left right : Finset BareMessage) :
    interfaceOffers interface (left ∪ right) =
      interfaceOffers interface left ∪ interfaceOffers interface right := by
  ext action
  simp [interfaceOffers]
  tauto

private theorem hideOffers_restrictTypeOffers (interface : Interface)
    (offers : Finset BareMessage) :
    hideOffers interface (restrictTypeOffers interface offers) = ∅ := by
  ext action
  simp [hideOffers, restrictTypeOffers]

private theorem interfaceOffers_restrictTypeOffers (interface : Interface)
    (offers : Finset BareMessage) :
    interfaceOffers interface (restrictTypeOffers interface offers) =
      restrictTypeOffers interface offers := by
  ext action
  simp [interfaceOffers, restrictTypeOffers]

private theorem hideOffers_sdiff (interface : Interface)
    (left right : Finset BareMessage) :
    hideOffers interface (left \ right) =
      hideOffers interface left \ hideOffers interface right := by
  ext action
  simp [hideOffers]
  tauto

private theorem interfaceOffers_sdiff (interface : Interface)
    (left right : Finset BareMessage) :
    interfaceOffers interface (left \ right) =
      interfaceOffers interface left \ interfaceOffers interface right := by
  ext action
  simp [interfaceOffers]
  tauto

private theorem finset_sdiff_eq_self_of_disjoint {left right : Finset BareMessage}
    (hDisjoint : Disjoint left right) : left \ right = left := by
  ext action
  simp only [Finset.mem_sdiff]
  constructor
  · exact fun h => h.1
  · intro hLeft
    exact ⟨hLeft, fun hRight => Finset.disjoint_left.mp hDisjoint hLeft hRight⟩

private theorem hideOffers_eq_self_of_avoids
    (interface : Interface) (offers : Finset BareMessage)
    (hAvoids : ∀ action ∈ offers, action.1 ∉ interface) :
    hideOffers interface offers = offers := by
  ext action
  constructor
  · exact fun h => (Finset.mem_filter.mp h).1
  · intro hAction
    exact Finset.mem_filter.mpr ⟨hAction, hAvoids action hAction⟩

private theorem interfaceOffers_eq_empty_of_avoids
    (interface : Interface) (offers : Finset BareMessage)
    (hAvoids : ∀ action ∈ offers, action.1 ∉ interface) :
    interfaceOffers interface offers = ∅ := by
  ext action
  simp only [interfaceOffers, Finset.mem_filter]
  constructor
  · rintro ⟨hOffers, hInterface⟩
    exact (hAvoids action hOffers hInterface).elim
  · intro hEmpty
    simpa using hEmpty

/- The exact ordinary local-environment equations reconstruct the original
outer environment after hiding the interface.  No offer-summary disjointness
is needed: the semantic future subtraction is retained verbatim. -/
/-- The product environment reconstruction uses only well-formedness and
avoidance of the current interface; exportedness is one sufficient way to
obtain those facts, but nested products use this more general form. -/
private theorem combineAutomatonEnvironment_eq_of_ordinaryLocalFields_of_avoids
    (interface : Interface)
    {outer leftEnvironment rightEnvironment : TypeEnvironment}
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    (hOuterWellFormed : outer.WellFormed)
    (hOuterAvoids : outer.AvoidsInterface interface)
    (hOuterClock : outer.clock = false)
    (hLeftClock : leftEnvironment.clock = false)
    (hRightClock : rightEnvironment.clock = false)
    (hLeftImmediate : leftEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface rightCurrent)
    (hLeftFuture : leftEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface rightFuture) \
        leftEnvironment.immediate)
    (hRightImmediate : rightEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface leftCurrent)
    (hRightFuture : rightEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface leftFuture) \
        rightEnvironment.immediate) :
    combineAutomatonEnvironment interface leftEnvironment rightEnvironment =
      outer := by
  have hOuterDisjoint : Disjoint outer.future outer.immediate := by
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm]
    exact hOuterWellFormed.2 hOuterClock
  have hHideOuterImmediate :=
    hideOffers_eq_self_of_avoids interface outer.immediate hOuterAvoids.1
  have hHideOuterFuture :=
    hideOffers_eq_self_of_avoids interface outer.future hOuterAvoids.2
  have hHideLeftImmediate :
      hideOffers interface leftEnvironment.immediate = outer.immediate := by
    rw [hLeftImmediate, hideOffers_union, hHideOuterImmediate,
      hideOffers_restrictTypeOffers, Finset.union_empty]
  have hHideRightImmediate :
      hideOffers interface rightEnvironment.immediate = outer.immediate := by
    rw [hRightImmediate, hideOffers_union, hHideOuterImmediate,
      hideOffers_restrictTypeOffers, Finset.union_empty]
  have hHideLeftFuture :
      hideOffers interface leftEnvironment.future = outer.future := by
    rw [hLeftFuture, hideOffers_sdiff, hideOffers_union, hHideOuterFuture,
      hideOffers_restrictTypeOffers, Finset.union_empty, hHideLeftImmediate]
    exact finset_sdiff_eq_self_of_disjoint hOuterDisjoint
  have hHideRightFuture :
      hideOffers interface rightEnvironment.future = outer.future := by
    rw [hRightFuture, hideOffers_sdiff, hideOffers_union, hHideOuterFuture,
      hideOffers_restrictTypeOffers, Finset.union_empty, hHideRightImmediate]
    exact finset_sdiff_eq_self_of_disjoint hOuterDisjoint
  have hCombinedImmediate :
        hideOffers interface
            (leftEnvironment.immediate ∪ rightEnvironment.immediate) =
          outer.immediate := by
    rw [hideOffers_union, hHideLeftImmediate, hHideRightImmediate,
      Finset.union_self]
  have hCombinedFuture :
        hideOffers interface
            (leftEnvironment.future ∪ rightEnvironment.future) =
          outer.future := by
    rw [hideOffers_union, hHideLeftFuture, hHideRightFuture,
      Finset.union_self]
  cases outer with
  | mk immediate future clock =>
      cases clock
      · simp [combineAutomatonEnvironment, hLeftClock, hRightClock,
          hCombinedImmediate, hCombinedFuture]
      · simp at hOuterClock

/-- The exact ordinary local-environment equations reconstruct the original
outer environment after hiding the interface.  No offer-summary disjointness
is needed: the semantic future subtraction is retained verbatim. -/

private theorem combineAutomatonEnvironment_eq_of_ordinaryLocalFields
    (signature : TypeAlphabet) (interface : Interface)
    {outer leftEnvironment rightEnvironment : TypeEnvironment}
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    (hAlphabet : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hOuterEnvironment : outer ∈ signature.environments)
    (hOuterClock : outer.clock = false)
    (hLeftClock : leftEnvironment.clock = false)
    (hRightClock : rightEnvironment.clock = false)
    (hLeftImmediate : leftEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface rightCurrent)
    (hLeftFuture : leftEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface rightFuture) \
        leftEnvironment.immediate)
    (hRightImmediate : rightEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface leftCurrent)
    (hRightFuture : rightEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface leftFuture) \
        rightEnvironment.immediate) :
    combineAutomatonEnvironment interface leftEnvironment rightEnvironment =
      outer := by
  have hOuterWellFormed :=
    TypeAlphabet.environment_wellFormed hOuterEnvironment
  have hOuterDisjoint : Disjoint outer.future outer.immediate := by
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm]
    exact hOuterWellFormed.2 hOuterClock
  have hImmediateAvoids :
      ∀ action ∈ outer.immediate, action.1 ∉ interface := by
    intro action hAction hInternal
    exact TypeAlphabet.environment_immediate_avoids_interface
      hAlphabet hOuterEnvironment action hAction (hInterface hInternal)
  have hFutureAvoids :
      ∀ action ∈ outer.future, action.1 ∉ interface := by
    intro action hAction hInternal
    exact TypeAlphabet.environment_future_avoids_interface
      hAlphabet hOuterEnvironment action hAction (hInterface hInternal)
  have hHideOuterImmediate :=
    hideOffers_eq_self_of_avoids interface outer.immediate hImmediateAvoids
  have hInterfaceOuterImmediate :=
    interfaceOffers_eq_empty_of_avoids interface outer.immediate hImmediateAvoids
  have hHideOuterFuture :=
    hideOffers_eq_self_of_avoids interface outer.future hFutureAvoids
  have hHideLeftImmediate :
      hideOffers interface leftEnvironment.immediate = outer.immediate := by
    rw [hLeftImmediate, hideOffers_union, hHideOuterImmediate,
      hideOffers_restrictTypeOffers, Finset.union_empty]
  have hHideRightImmediate :
      hideOffers interface rightEnvironment.immediate = outer.immediate := by
    rw [hRightImmediate, hideOffers_union, hHideOuterImmediate,
      hideOffers_restrictTypeOffers, Finset.union_empty]
  have hHideLeftFuture :
      hideOffers interface leftEnvironment.future = outer.future := by
    rw [hLeftFuture, hideOffers_sdiff, hideOffers_union, hHideOuterFuture,
      hideOffers_restrictTypeOffers, Finset.union_empty, hHideLeftImmediate]
    exact finset_sdiff_eq_self_of_disjoint hOuterDisjoint
  have hHideRightFuture :
      hideOffers interface rightEnvironment.future = outer.future := by
    rw [hRightFuture, hideOffers_sdiff, hideOffers_union, hHideOuterFuture,
      hideOffers_restrictTypeOffers, Finset.union_empty, hHideRightImmediate]
    exact finset_sdiff_eq_self_of_disjoint hOuterDisjoint
  have hCombinedImmediate :
        hideOffers interface
            (leftEnvironment.immediate ∪ rightEnvironment.immediate) =
          outer.immediate := by
    rw [hideOffers_union, hHideLeftImmediate, hHideRightImmediate,
      Finset.union_self]
  have hCombinedFuture :
        hideOffers interface
            (leftEnvironment.future ∪ rightEnvironment.future) =
          outer.future := by
    rw [hideOffers_union, hHideLeftFuture, hHideRightFuture,
      Finset.union_self]
  cases outer with
  | mk immediate future clock =>
      cases clock
      · simp [combineAutomatonEnvironment, hLeftClock, hRightClock,
          hCombinedImmediate, hCombinedFuture]
      · simp at hOuterClock

/-- Elimination form of `LocalTypeEnvironment` exposing the exact ordinary
environment equations without losing the clock alternative. -/
private theorem LocalTypeEnvironment.clock_or_ordinary
    {outer siblingEnvironment localEnvironment : TypeEnvironment}
    {interface : Interface} {sibling : PactType} {label : TypeLabel}
    (hLocal : LocalTypeEnvironment outer interface siblingEnvironment sibling
      label localEnvironment) :
    (outer.clock = true ∧
        siblingEnvironment = TypeEnvironment.tock ∧
        localEnvironment = TypeEnvironment.tock) ∨
      ∃ siblingTarget current future,
        outer.clock = false ∧
        siblingEnvironment.clock = false ∧
        TypeOffers siblingEnvironment sibling label siblingTarget
          current future ∧
        localEnvironment.clock = false ∧
        localEnvironment.immediate =
          outer.immediate ∪ restrictTypeOffers interface current ∧
        localEnvironment.future =
          (outer.future ∪ restrictTypeOffers interface future) \
            localEnvironment.immediate := by
  cases hLocal with
  | clock outer interface sibling label hClock =>
      exact Or.inl ⟨hClock, rfl, rfl⟩
  | ordinary outer siblingEnvironment localEnvironment interface sibling
      siblingTarget label current future hOuterClock hSiblingClock hOffers
      hLocalClock hImmediate hFuture =>
      exact Or.inr ⟨siblingTarget, current, future, hOuterClock,
        hSiblingClock, hOffers, hLocalClock, hImmediate, hFuture⟩

/-- Regression: the current syntactic linearity check does not yet imply
disjoint current/future decorations.  An `offer` may expose a branch head as
current while its else continuation immediately re-offers the same message. -/
theorem sameCycleMessageLinear_offer_else_current_future_overlap :
    let action : BareMessage := ("same", .send)
    let elseType : PactType := .message action.1 action.2
    let processType : PactType := .offer elseType [(action, .skip)]
    processType.SameCycleMessageLinear ∧
      TypeOffers TypeEnvironment.empty processType TypeLabel.silent elseType
        {action} {action} ∧
      ¬ Disjoint ({action} : Finset BareMessage) {action} := by
  dsimp
  constructor
  · simp [PactType.SameCycleMessageLinear,
      PactType.SameCycleMessageLinearBranches, PactType.PrefixMessageIds]
  · constructor
    · have hOffers := TypeOffers.offer_else TypeEnvironment.empty
          (.message "same" .send) [(("same", .send), .skip)] (by
            simp [TypeEnvironment.empty, TypeEnvironment.WellFormed,
              TypeNoImmediateBranch, TypeResolved, typeBranchNeeds, typeNeed])
      simpa [typeBranchActions, typeFutureOffers, typeFutureOffersFuel] using
        hOffers
    · intro hDisjoint
      have hMember : (("same", .send) : BareMessage) ∈
          ({("same", .send)} : Finset BareMessage) := by simp
      exact Finset.disjoint_left.mp hDisjoint hMember hMember

/-- Every operational offer decoration is an exact decomposition of the
syntax-derived future menu of its target, modulo offers already current on the
edge.  This theorem is intentionally syntax-side: constructor automata use it
only to justify following an execution target when placed under sequencing. -/
theorem TypeOffers.current_union_future_eq_targetFuture :
    ∀ source environment target label current future,
      TypeOffers environment source label target current future →
        current ∪ future = current ∪ typeFutureOffers target := by
  intro source
  induction hSize : sizeOf source using Nat.strong_induction_on
      generalizing source with
  | h n ih =>
      intro environment target label current future hOffers
      cases source with
      | par left right interface =>
          cases hOffers with
          | par outer leftEnvironment rightEnvironment interface left
              leftTarget right rightTarget leftLabel rightLabel leftCurrent
              leftFuture rightCurrent rightFuture hLeftOffers hRightOffers
              _ _ _ =>
              have hLeft := ih (sizeOf left) (by
                rw [← hSize]
                simp_wf
                omega) left rfl _ _ _ _ _ hLeftOffers
              have hRight := ih (sizeOf right) (by
                rw [← hSize]
                simp_wf
                omega) right rfl _ _ _ _ _ hRightOffers
              rw [typeFutureOffers_parallel]
              ext action
              simp only [hideTypeOffers, Finset.mem_filter,
                Finset.mem_union]
              constructor
              · rintro (⟨hCurrent, hOutside⟩ | ⟨hFuture, hOutside⟩)
                · exact Or.inl ⟨hCurrent, hOutside⟩
                · rcases hFuture with hLeftFuture | hRightFuture
                  · have hMember : action ∈ leftCurrent ∪
                        typeFutureOffers leftTarget := by
                      rw [← hLeft]
                      exact Finset.mem_union_right _ hLeftFuture
                    rcases Finset.mem_union.mp hMember with hCurrent | hTarget
                    · exact Or.inl ⟨Or.inl hCurrent, hOutside⟩
                    · exact Or.inr ⟨Or.inl hTarget, hOutside⟩
                  · have hMember : action ∈ rightCurrent ∪
                        typeFutureOffers rightTarget := by
                      rw [← hRight]
                      exact Finset.mem_union_right _ hRightFuture
                    rcases Finset.mem_union.mp hMember with hCurrent | hTarget
                    · exact Or.inl ⟨Or.inr hCurrent, hOutside⟩
                    · exact Or.inr ⟨Or.inr hTarget, hOutside⟩
              · rintro (⟨hCurrent, hOutside⟩ | ⟨hTarget, hOutside⟩)
                · exact Or.inl ⟨hCurrent, hOutside⟩
                · rcases hTarget with hLeftTarget | hRightTarget
                  · have hMember : action ∈ leftCurrent ∪ leftFuture := by
                      rw [hLeft]
                      exact Finset.mem_union_right _ hLeftTarget
                    rcases Finset.mem_union.mp hMember with hCurrent | hFuture
                    · exact Or.inl ⟨Or.inl hCurrent, hOutside⟩
                    · exact Or.inr ⟨Or.inl hFuture, hOutside⟩
                  · have hMember : action ∈ rightCurrent ∪ rightFuture := by
                      rw [hRight]
                      exact Finset.mem_union_right _ hRightTarget
                    rcases Finset.mem_union.mp hMember with hCurrent | hFuture
                    · exact Or.inl ⟨Or.inr hCurrent, hOutside⟩
                    · exact Or.inr ⟨Or.inr hFuture, hOutside⟩
      | message msg dir =>
          cases hOffers <;> simp [typeFutureOffers, typeFutureOffersFuel]
      | progress pid =>
          cases hOffers <;> simp [typeFutureOffers, typeFutureOffersFuel]
      | tock =>
          cases hOffers <;> simp [typeFutureOffers, typeFutureOffersFuel]
      | skip =>
          cases hOffers <;> simp [typeFutureOffers, typeFutureOffersFuel]
      | var name => cases hOffers
      | recur name body => cases hOffers <;> simp
      | choice left right => cases hOffers <;> simp
      | fairChoice bid left right => cases hOffers <;> simp
      | seq left right =>
          cases hOffers <;> simp [typeFutureOffers_sequence]
      | xoffer elseType branches =>
          cases hOffers <;> simp [typeFutureOffers, typeFutureOffersFuel]
      | offer elseType branches =>
          cases hOffers <;> simp [typeFutureOffers, typeFutureOffersFuel]

/-- Package explicitly chosen witness edges into the existential product test. -/
private theorem syncAutomatonEdges_of_witnesses
    (interface : Interface) {leftEdges rightEdges : Finset AutomatonFragmentEdge}
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    (hLeftWitness : leftWitness ∈ leftEdges)
    (hRightWitness : rightWitness ∈ rightEdges)
    (hSync : syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness) :
    syncAutomatonEdges interface leftEdges rightEdges left right := by
  exact ⟨leftWitness, hLeftWitness, rightWitness, hRightWitness, hSync⟩

/-- The ordinary local-environment fields, using independent witness offer
summaries, are exactly the strict witness synchronization predicate. -/
private theorem syncAutomatonEdgeWitnesses_of_ordinaryLocalFields
    (interface : Interface)
    {outer : TypeEnvironment}
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    (hOuter : combineAutomatonEnvironment interface left.environment
      right.environment = outer)
    (hLeftMatch : matchesAutomatonOfferWitness left leftWitness)
    (hRightMatch : matchesAutomatonOfferWitness right rightWitness)
    (hLeftClock : left.environment.clock = false)
    (hRightClock : right.environment.clock = false)
    (hLeftImmediate : left.environment.immediate =
      outer.immediate ∪ restrictTypeOffers interface rightWitness.current)
    (hLeftFuture : left.environment.future =
      (outer.future ∪ restrictTypeOffers interface rightWitness.future) \
        left.environment.immediate)
    (hRightImmediate : right.environment.immediate =
      outer.immediate ∪ restrictTypeOffers interface leftWitness.current)
    (hRightFuture : right.environment.future =
      (outer.future ∪ restrictTypeOffers interface leftWitness.future) \
        right.environment.immediate)
    (hLabelSync : TypeLabel.Sync interface left.label.semantic
      right.label.semantic) :
    syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness := by
  unfold syncAutomatonEdgeWitnesses
  simp only [hLeftClock, if_false]
  rw [hOuter]
  exact ⟨hLeftMatch, hRightMatch,
    ⟨True.intro, hRightClock, hLeftImmediate, hLeftFuture,
      hRightImmediate, hRightFuture⟩, hLabelSync⟩

/-- Realizing the offer summaries existentially stored in two semantic local
judgments as resolved witness edges yields the compiler's existential product
test.  Actual edges are used as witnesses in the clock case. -/
private theorem localTypeEnvironments_to_syncAutomatonEdges
    (signature : TypeAlphabet) (interface : Interface)
    {leftEdges rightEdges : Finset AutomatonFragmentEdge}
    {outer : TypeEnvironment} {leftEdge rightEdge : AutomatonFragmentEdge}
    {left right : PactType}
    (hAlphabet : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hOuterEnvironment : outer ∈ signature.environments)
    (hLeftEdge : leftEdge ∈ leftEdges)
    (hRightEdge : rightEdge ∈ rightEdges)
    (hLeftLocal : LocalTypeEnvironment outer interface
      rightEdge.environment right rightEdge.label.semantic
      leftEdge.environment)
    (hRightLocal : LocalTypeEnvironment outer interface
      leftEdge.environment left leftEdge.label.semantic
      rightEdge.environment)
    (hLeftRealizes :
      ∀ {target current future},
        TypeOffers leftEdge.environment left leftEdge.label.semantic target
          current future →
        ∃ witness ∈ leftEdges,
          matchesAutomatonOfferWitness leftEdge witness ∧
            witness.current = current ∧ witness.future = future)
    (hRightRealizes :
      ∀ {target current future},
        TypeOffers rightEdge.environment right rightEdge.label.semantic target
          current future →
        ∃ witness ∈ rightEdges,
          matchesAutomatonOfferWitness rightEdge witness ∧
            witness.current = current ∧ witness.future = future)
    (hLabelSync : TypeLabel.Sync interface leftEdge.label.semantic
      rightEdge.label.semantic) :
    syncAutomatonEdges interface leftEdges rightEdges leftEdge rightEdge ∧
      combineAutomatonEnvironment interface leftEdge.environment
        rightEdge.environment = outer := by
  have hLeftCases := LocalTypeEnvironment.clock_or_ordinary hLeftLocal
  have hRightCases := LocalTypeEnvironment.clock_or_ordinary hRightLocal
  rcases hLeftCases with hClock | hOrdinary
  · rcases hClock with ⟨hOuterClock, hRightTock, hLeftTock⟩
    have hOuterLocal : outer ∈ signature.localEnvironments :=
      signature.environments_subset_localEnvironments hOuterEnvironment
    have hOuterTock := TypeAlphabet.localEnvironment_eq_tock_of_clock
      hOuterLocal hOuterClock
    have hCombined : combineAutomatonEnvironment interface
        leftEdge.environment rightEdge.environment = outer := by
      rw [hLeftTock, hRightTock, hOuterTock]
      simp [combineAutomatonEnvironment, TypeEnvironment.tock]
    constructor
    · apply syncAutomatonEdges_of_witnesses interface hLeftEdge hRightEdge
      unfold syncAutomatonEdgeWitnesses
      simp [matchesAutomatonOfferWitness, hLeftTock, hRightTock,
        hLabelSync]
      intro hFalse
      simp [TypeEnvironment.tock] at hFalse
    · exact hCombined
  · rcases hOrdinary with
      ⟨rightTarget, rightCurrent, rightFuture, hOuterClock,
        hRightClock, hRightOffers, hLeftClock, hLeftImmediate, hLeftFuture⟩
    rcases hRightCases with hClock | hOrdinary
    · rcases hClock with ⟨_, hLeftTock, hRightTock⟩
      rw [hRightTock] at hRightClock
      simp [TypeEnvironment.tock] at hRightClock
    · rcases hOrdinary with
        ⟨leftTarget, leftCurrent, leftFuture, _, hLeftClock',
          hLeftOffers, hRightClock', hRightImmediate, hRightFuture⟩
      obtain ⟨leftWitness, hLeftWitness, hLeftMatch,
          hLeftCurrent, hLeftFutureSummary⟩ := hLeftRealizes hLeftOffers
      obtain ⟨rightWitness, hRightWitness, hRightMatch,
          hRightCurrent, hRightFutureSummary⟩ := hRightRealizes hRightOffers
      rw [← hLeftCurrent] at hRightImmediate
      rw [← hLeftFutureSummary] at hRightFuture
      rw [← hRightCurrent] at hLeftImmediate
      rw [← hRightFutureSummary] at hLeftFuture
      have hCombined :=
        combineAutomatonEnvironment_eq_of_ordinaryLocalFields
          signature interface hAlphabet hInterface hOuterEnvironment
          hOuterClock hLeftClock hRightClock hLeftImmediate hLeftFuture
          hRightImmediate hRightFuture
      constructor
      · apply syncAutomatonEdges_of_witnesses interface
          hLeftWitness hRightWitness
        exact syncAutomatonEdgeWitnesses_of_ordinaryLocalFields interface
          hCombined hLeftMatch hRightMatch hLeftClock hRightClock
          hLeftImmediate hLeftFuture hRightImmediate hRightFuture hLabelSync
      · exact hCombined

/-- Local-domain form of sibling-environment reconstruction.  Avoidance of
the current interface replaces exportedness/signature well-formedness. -/
theorem localTypeEnvironments_to_syncAutomatonEdges_local
    (signature : TypeAlphabet) (interface : Interface)
    {leftEdges rightEdges : Finset AutomatonFragmentEdge}
    {outer : TypeEnvironment} {leftEdge rightEdge : AutomatonFragmentEdge}
    {left right : PactType}
    (hInterface : interface ⊆ signature.interface)
    (hOuterEnvironment : outer ∈ signature.localEnvironments)
    (hOuterAvoids : outer.AvoidsInterface interface)
    (hLeftEdge : leftEdge ∈ leftEdges)
    (hRightEdge : rightEdge ∈ rightEdges)
    (hLeftLocal : LocalTypeEnvironment outer interface
      rightEdge.environment right rightEdge.label.semantic
      leftEdge.environment)
    (hRightLocal : LocalTypeEnvironment outer interface
      leftEdge.environment left leftEdge.label.semantic
      rightEdge.environment)
    (hLeftRealizes :
      ∀ {target current future},
        TypeOffers leftEdge.environment left leftEdge.label.semantic target
          current future →
        ∃ witness ∈ leftEdges,
          matchesAutomatonOfferWitness leftEdge witness ∧
            witness.current = current ∧ witness.future = future)
    (hRightRealizes :
      ∀ {target current future},
        TypeOffers rightEdge.environment right rightEdge.label.semantic target
          current future →
        ∃ witness ∈ rightEdges,
          matchesAutomatonOfferWitness rightEdge witness ∧
            witness.current = current ∧ witness.future = future)
    (hLabelSync : TypeLabel.Sync interface leftEdge.label.semantic
      rightEdge.label.semantic) :
    syncAutomatonEdges interface leftEdges rightEdges leftEdge rightEdge ∧
      combineAutomatonEnvironment interface leftEdge.environment
        rightEdge.environment = outer := by
  have hLeftCases := LocalTypeEnvironment.clock_or_ordinary hLeftLocal
  have hRightCases := LocalTypeEnvironment.clock_or_ordinary hRightLocal
  rcases hLeftCases with hClock | hOrdinary
  · rcases hClock with ⟨hOuterClock, hRightTock, hLeftTock⟩
    have hOuterTock := TypeAlphabet.localEnvironment_eq_tock_of_clock
      hOuterEnvironment hOuterClock
    have hCombined : combineAutomatonEnvironment interface
        leftEdge.environment rightEdge.environment = outer := by
      rw [hLeftTock, hRightTock, hOuterTock]
      simp [combineAutomatonEnvironment, TypeEnvironment.tock]
    constructor
    · apply syncAutomatonEdges_of_witnesses interface hLeftEdge hRightEdge
      unfold syncAutomatonEdgeWitnesses
      simp [matchesAutomatonOfferWitness, hLeftTock, hRightTock,
        hLabelSync]
      intro hFalse
      simp [TypeEnvironment.tock] at hFalse
    · exact hCombined
  · rcases hOrdinary with
      ⟨rightTarget, rightCurrent, rightFuture, hOuterClock,
        hRightClock, hRightOffers, hLeftClock, hLeftImmediate, hLeftFuture⟩
    rcases hRightCases with hClock | hOrdinary
    · rcases hClock with ⟨_, hLeftTock, hRightTock⟩
      rw [hRightTock] at hRightClock
      simp [TypeEnvironment.tock] at hRightClock
    · rcases hOrdinary with
        ⟨leftTarget, leftCurrent, leftFuture, _, hLeftClock',
          hLeftOffers, hRightClock', hRightImmediate, hRightFuture⟩
      obtain ⟨leftWitness, hLeftWitness, hLeftMatch,
          hLeftCurrent, hLeftFutureSummary⟩ := hLeftRealizes hLeftOffers
      obtain ⟨rightWitness, hRightWitness, hRightMatch,
          hRightCurrent, hRightFutureSummary⟩ := hRightRealizes hRightOffers
      rw [← hLeftCurrent] at hRightImmediate
      rw [← hLeftFutureSummary] at hRightFuture
      rw [← hRightCurrent] at hLeftImmediate
      rw [← hRightFutureSummary] at hLeftFuture
      have hCombined :=
        combineAutomatonEnvironment_eq_of_ordinaryLocalFields_of_avoids
          interface
          (TypeAlphabet.localEnvironment_wellFormed hOuterEnvironment)
          hOuterAvoids hOuterClock hLeftClock hRightClock hLeftImmediate
          hLeftFuture hRightImmediate hRightFuture
      constructor
      · apply syncAutomatonEdges_of_witnesses interface
          hLeftWitness hRightWitness
        exact syncAutomatonEdgeWitnesses_of_ordinaryLocalFields interface
          hCombined hLeftMatch hRightMatch hLeftClock hRightClock
          hLeftImmediate hLeftFuture hRightImmediate hRightFuture hLabelSync
      · exact hCombined

/-- Strict witness synchronization reconstructs the two semantic
sibling-local environments using the witness summaries, while the actual
edges retain the product target and exposed offer summary. -/
theorem syncAutomatonEdgeWitnesses_to_localTypeEnvironments
    (interface : Interface)
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    {leftType leftTarget rightType rightTarget : PactType}
    (hLeftOffers : TypeOffers leftWitness.environment leftType
      leftWitness.label.semantic leftTarget leftWitness.current
      leftWitness.future)
    (hRightOffers : TypeOffers rightWitness.environment rightType
      rightWitness.label.semantic rightTarget rightWitness.current
      rightWitness.future)
    (hSync : syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness) :
    let outer := combineAutomatonEnvironment interface
      left.environment right.environment
    LocalTypeEnvironment outer interface right.environment rightType
        right.label.semantic left.environment ∧
      LocalTypeEnvironment outer interface left.environment leftType
        left.label.semantic right.environment := by
  unfold syncAutomatonEdgeWitnesses at hSync
  rcases hSync with ⟨hLeftMatch, hRightMatch, hFields, hLabelSync⟩
  rcases hLeftMatch with ⟨hLeftSource, hLeftEnvironment, hLeftLabel⟩
  rcases hRightMatch with ⟨hRightSource, hRightEnvironment, hRightLabel⟩
  rw [hLeftEnvironment, hLeftLabel] at hLeftOffers
  rw [hRightEnvironment, hRightLabel] at hRightOffers
  cases hLeftClock : left.environment.clock with
  | true =>
      simp only [hLeftClock, if_true] at hFields
      rcases hFields with ⟨hLeftTock, hRightTock⟩
      rw [hLeftTock, hRightTock]
      simp only [combineAutomatonEnvironment, TypeEnvironment.tock]
      exact ⟨LocalTypeEnvironment.clock TypeEnvironment.tock interface
          rightType right.label.semantic rfl,
        LocalTypeEnvironment.clock TypeEnvironment.tock interface
          leftType left.label.semantic rfl⟩
  | false =>
      simp only [hLeftClock, if_false] at hFields
      rcases hFields with ⟨hLeftClock', hRightClock, hLeftImmediate,
        hLeftFuture, hRightImmediate, hRightFuture⟩
      let outer := combineAutomatonEnvironment interface
        left.environment right.environment
      have hOuterClock : outer.clock = false := by
        simp [outer, combineAutomatonEnvironment, hLeftClock, hRightClock]
      change LocalTypeEnvironment outer interface right.environment rightType
          right.label.semantic left.environment ∧
        LocalTypeEnvironment outer interface left.environment leftType
          left.label.semantic right.environment
      exact ⟨
        LocalTypeEnvironment.ordinary outer right.environment left.environment
          interface rightType rightTarget right.label.semantic
          rightWitness.current rightWitness.future hOuterClock hRightClock
          hRightOffers hLeftClock hLeftImmediate hLeftFuture,
        LocalTypeEnvironment.ordinary outer left.environment right.environment
          interface leftType leftTarget left.label.semantic
          leftWitness.current leftWitness.future hOuterClock hLeftClock
          hLeftOffers hRightClock hRightImmediate hRightFuture⟩

end

end Pact
