import Anvilpp.PactTypes.Automata.AutomatonFragment

/-!
# Finite same-cycle reference closure over a pending automaton
-/

namespace Pact

noncomputable section

/-! ### Future-offer computation -/

namespace PendingAutomaton

  /-- States whose offers are referenced by outgoing edges from `state`. -/
  def referencedStates (automaton : PendingAutomaton)
      (state : TypeAutomatonState) : Finset TypeAutomatonState :=
    (automaton.edges.filter fun edge => edge.source = state).biUnion fun edge =>
      -- A clock transition ends the current cycle.  Its decorated `future`
      -- field describes the offers after taking that transition, but those
      -- offers must not be used while computing the menu still reachable
      -- from `state` in the current cycle.
      if edge.label.semantic = TypeLabel.tock then ∅
      else
        match edge.future with
        | .explicit _ => ∅
        | .at target _ => {target}

  /-- Offers already visible directly on outgoing edges from `state`. -/
  def offersAt (automaton : PendingAutomaton)
      (state : TypeAutomatonState) : Finset BareMessage :=
    (automaton.edges.filter fun edge => edge.source = state).biUnion fun edge =>
      if edge.label.semantic = TypeLabel.tock then ∅
      else
        edge.current ∪
          match edge.future with
          | .explicit offers => offers
          | .at _ _ => ∅

  def futureStep (automaton : PendingAutomaton)
      (reached : Finset TypeAutomatonState) : Finset TypeAutomatonState :=
    reached ∪ reached.biUnion automaton.referencedStates

  def futureReachableAux (automaton : PendingAutomaton) :
      Nat → Finset TypeAutomatonState → Finset TypeAutomatonState
    | 0, reached => reached
    | fuel + 1, reached =>
        futureReachableAux automaton fuel (futureStep automaton reached)

  /-- Every symbolic reference in the graph points to a declared state. -/
  def ReferencesClosed (automaton : PendingAutomaton) : Prop :=
    ∀ state ∈ automaton.states,
      automaton.referencedStates state ⊆ automaton.states

  theorem referencesClosed_of_futureTargetsInStates
      (fragment : AutomatonFragment)
      (hTargets : fragment.FutureTargetsInStates) :
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).ReferencesClosed := by
    intro state _ target hTarget
    simp only [referencedStates, Finset.mem_biUnion, Finset.mem_filter]
      at hTarget
    rcases hTarget with ⟨edge, ⟨hEdge, _⟩, hFuture⟩
    by_cases hClock : edge.label.semantic = TypeLabel.tock
    · simp [hClock] at hFuture
    · simp only [hClock, if_false] at hFuture
      cases hSpec : edge.future with
      | explicit offers => simp [hSpec] at hFuture
      | «at» referenced removed =>
          simp only [hSpec, Finset.mem_singleton] at hFuture
          subst target
          exact hTargets edge hEdge referenced removed hSpec

  private theorem subset_futureStep (automaton : PendingAutomaton)
      (reached : Finset TypeAutomatonState) :
      reached ⊆ automaton.futureStep reached := by
    exact Finset.subset_union_left

  private theorem futureStep_subset_states
      (automaton : PendingAutomaton) (reached : Finset TypeAutomatonState)
      (hClosed : automaton.ReferencesClosed)
      (hReached : reached ⊆ automaton.states) :
      automaton.futureStep reached ⊆ automaton.states := by
    intro state hState
    simp only [futureStep, Finset.mem_union, Finset.mem_biUnion] at hState
    rcases hState with hState | ⟨source, hSource, hReference⟩
    · exact hReached hState
    · exact hClosed source (hReached hSource) hReference

  private theorem futureReachableAux_fixed_of_futureStep_eq
      (automaton : PendingAutomaton) (reached : Finset TypeAutomatonState)
      (hFixed : automaton.futureStep reached = reached) :
      ∀ fuel, futureReachableAux automaton fuel reached = reached := by
    intro fuel
    induction fuel with
    | zero => rfl
    | succ fuel ih =>
        simp only [futureReachableAux, hFixed]
        exact ih

  private theorem futureStep_futureReachableAux
      (automaton : PendingAutomaton) : ∀ fuel reached,
      automaton.futureStep (futureReachableAux automaton fuel reached) =
        futureReachableAux automaton fuel (automaton.futureStep reached) := by
    intro fuel
    induction fuel with
    | zero => intro reached; rfl
    | succ fuel ih =>
        intro reached
        simp only [futureReachableAux]
        exact ih (automaton.futureStep reached)

  private theorem futureReachableAux_succ
      (automaton : PendingAutomaton) (fuel : Nat)
      (reached : Finset TypeAutomatonState) :
      futureReachableAux automaton (fuel + 1) reached =
        automaton.futureStep (futureReachableAux automaton fuel reached) := by
    simp only [futureReachableAux]
    exact (futureStep_futureReachableAux automaton fuel reached).symm

  /-- If `k` is at least the number of states still missing from `reached`,
  `k` saturation rounds reach a fixed point. -/
  private theorem futureReachableAux_fixed_after_missing
      (automaton : PendingAutomaton) (hClosed : automaton.ReferencesClosed) :
      ∀ k reached,
        reached ⊆ automaton.states →
        automaton.states.card ≤ reached.card + k →
        automaton.futureStep (futureReachableAux automaton k reached) =
          futureReachableAux automaton k reached := by
    intro k
    induction k with
    | zero =>
        intro reached hReached hCard
        have hEqual : reached = automaton.states := by
          exact Finset.eq_of_subset_of_card_le hReached (by simpa using hCard)
        rw [hEqual]
        apply Finset.Subset.antisymm
        · exact futureStep_subset_states automaton automaton.states hClosed
            (fun _ h => h)
        · exact subset_futureStep automaton automaton.states
    | succ k ih =>
        intro reached hReached hCard
        let next := automaton.futureStep reached
        have hNextSubset : next ⊆ automaton.states :=
          futureStep_subset_states automaton reached hClosed hReached
        by_cases hFixed : next = reached
        · have hStepFixed : automaton.futureStep reached = reached := by
            simpa [next] using hFixed
          have hAux : futureReachableAux automaton (k + 1) reached = reached := by
            simp only [futureReachableAux]
            rw [hStepFixed]
            exact futureReachableAux_fixed_of_futureStep_eq
              automaton reached hStepFixed k
          rw [hAux]
          exact hStepFixed
        · have hStrict : reached.card < next.card := by
            apply Finset.card_lt_card
            exact Finset.ssubset_iff_subset_ne.mpr
              ⟨subset_futureStep automaton reached, Ne.symm hFixed⟩
          have hNextCard : automaton.states.card ≤ next.card + k := by
            omega
          simpa only [futureReachableAux, next] using
            ih next hNextSubset hNextCard

  /-- Saturation is stable after `|states|` rounds; running any additional
  number of rounds does not change the reached set. -/
  theorem futureReachableAux_add_card_stable
      (automaton : PendingAutomaton) (hClosed : automaton.ReferencesClosed)
      (reached : Finset TypeAutomatonState)
      (hReached : reached ⊆ automaton.states) (extra : Nat) :
      futureReachableAux automaton (automaton.states.card + extra) reached =
        futureReachableAux automaton automaton.states.card reached := by
    have hFixed : automaton.futureStep
          (futureReachableAux automaton automaton.states.card reached) =
        futureReachableAux automaton automaton.states.card reached := by
      apply futureReachableAux_fixed_after_missing automaton hClosed
      · exact hReached
      · omega
    induction extra with
    | zero => simp
    | succ extra ih =>
        rw [Nat.add_succ,
          futureReachableAux_succ automaton (automaton.states.card + extra),
          ih, hFixed]

  /-- Pointwise preservation of references lifts to every finite saturation
  depth.  This is the graph-theoretic core used by constructor state tags. -/
  theorem futureReachableAux_image_of_embedding
      (child parent : PendingAutomaton)
      (embed : TypeAutomatonState → TypeAutomatonState)
      (hReferences : ∀ state,
        parent.referencedStates (embed state) =
          (child.referencedStates state).image embed) :
      ∀ fuel reached,
        parent.futureReachableAux fuel (reached.image embed) =
          (child.futureReachableAux fuel reached).image embed := by
    intro fuel
    induction fuel with
    | zero => intro reached; rfl
    | succ fuel ih =>
        intro reached
        simp only [futureReachableAux]
        have hStep : parent.futureStep (reached.image embed) =
            (child.futureStep reached).image embed := by
          apply Finset.Subset.antisymm
          · intro target hTarget
            simp only [futureStep, Finset.mem_union, Finset.mem_biUnion]
              at hTarget
            rcases hTarget with hDirect | ⟨source, hSource, hTarget⟩
            · rcases Finset.mem_image.mp hDirect with ⟨state, hState, rfl⟩
              apply Finset.mem_image.mpr
              exact ⟨state, Finset.mem_union_left _ hState, rfl⟩
            · rcases Finset.mem_image.mp hSource with ⟨state, hState, rfl⟩
              rw [hReferences] at hTarget
              rcases Finset.mem_image.mp hTarget with
                ⟨referenced, hReferenced, rfl⟩
              apply Finset.mem_image.mpr
              exact ⟨referenced, Finset.mem_union_right _
                (Finset.mem_biUnion.mpr ⟨state, hState, hReferenced⟩), rfl⟩
          · intro target hTarget
            rcases Finset.mem_image.mp hTarget with ⟨state, hState, rfl⟩
            simp only [futureStep, Finset.mem_union, Finset.mem_biUnion]
              at hState ⊢
            rcases hState with hDirect | ⟨source, hSource, hReferenced⟩
            · exact Or.inl (Finset.mem_image.mpr ⟨state, hDirect, rfl⟩)
            · right
              refine ⟨embed source,
                Finset.mem_image.mpr ⟨source, hSource, rfl⟩, ?_⟩
              rw [hReferences]
              exact Finset.mem_image.mpr ⟨state, hReferenced, rfl⟩
        rw [hStep]
        exact ih (child.futureStep reached)

  /-- Offers unioned over an embedded reached set are preserved whenever
  `offersAt` is preserved pointwise by the embedding. -/
  theorem biUnion_offersAt_image_of_embedding
      (child parent : PendingAutomaton)
      (embed : TypeAutomatonState → TypeAutomatonState)
      (hOffers : ∀ state,
        parent.offersAt (embed state) = child.offersAt state)
      (reached : Finset TypeAutomatonState) :
      (reached.image embed).biUnion parent.offersAt =
        reached.biUnion child.offersAt := by
    ext action
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨state, hState, rfl⟩, hAction⟩
      rw [hOffers] at hAction
      exact ⟨state, hState, hAction⟩
    · rintro ⟨state, hState, hAction⟩
      refine ⟨embed state, ⟨state, hState, rfl⟩, ?_⟩
      rw [hOffers]
      exact hAction

  /-- Saturate references for at most `|Q|` rounds. -/
  def futureReachable (automaton : PendingAutomaton)
      (state : TypeAutomatonState) : Finset TypeAutomatonState :=
    futureReachableAux automaton automaton.states.card {state}

  /-- An exact reference-preserving state embedding preserves the saturated
  same-cycle reachable set.  A larger parent carrier only adds redundant
  saturation rounds. -/
  theorem futureReachable_eq_of_embedding
      (child parent : PendingAutomaton)
      (embed : TypeAutomatonState → TypeAutomatonState)
      (hReferences : ∀ state,
        parent.referencedStates (embed state) =
          (child.referencedStates state).image embed)
      (hClosed : child.ReferencesClosed)
      (state : TypeAutomatonState) (hState : state ∈ child.states)
      (hCard : child.states.card ≤ parent.states.card) :
      parent.futureReachable (embed state) =
        (child.futureReachable state).image embed := by
    obtain ⟨extra, hExtra⟩ := Nat.exists_eq_add_of_le hCard
    unfold futureReachable
    rw [show ({embed state} : Finset TypeAutomatonState) =
        ({state} : Finset TypeAutomatonState).image embed by simp]
    rw [futureReachableAux_image_of_embedding child parent embed hReferences]
    rw [hExtra,
      child.futureReachableAux_add_card_stable hClosed {state} (by
        simpa using hState) extra]

  /-- Two closed pending graphs with the same edge set have the same
  same-cycle reachability from any state carried by both graphs.  Their state
  carriers may differ because constructor views retain different bookkeeping
  states; only the finite saturation bound changes, and closure makes those
  extra rounds redundant. -/
  theorem futureReachable_eq_of_same_edges
      (first second : PendingAutomaton)
      (hEdges : first.edges = second.edges)
      (hFirstClosed : first.ReferencesClosed)
      (hSecondClosed : second.ReferencesClosed)
      (state : TypeAutomatonState)
      (hFirstState : state ∈ first.states)
      (hSecondState : state ∈ second.states) :
      first.futureReachable state = second.futureReachable state := by
    let shared : PendingAutomaton :=
      { states := first.states ∪ second.states, edges := first.edges }
    have hFirstCard : first.states.card ≤ shared.states.card :=
      Finset.card_le_card Finset.subset_union_left
    have hSecondCard : second.states.card ≤ shared.states.card :=
      Finset.card_le_card Finset.subset_union_right
    have hFirst := futureReachable_eq_of_embedding first shared id
      (fun current => by
        change first.referencedStates current =
          (first.referencedStates current).image id
        ext target
        simp) hFirstClosed state hFirstState hFirstCard
    have hSecondReferences : ∀ current,
        shared.referencedStates (id current) =
          (second.referencedStates current).image id := by
      intro current
      unfold referencedStates
      rw [hEdges]
      ext target
      simp
    have hSecond := futureReachable_eq_of_embedding second shared id
      hSecondReferences hSecondClosed state hSecondState hSecondCard
    have hFirst' : shared.futureReachable state =
        first.futureReachable state := by simpa using hFirst
    have hSecond' : shared.futureReachable state =
        second.futureReachable state := by simpa using hSecond
    exact hFirst'.symm.trans hSecond'

  /-- If a state has no same-cycle future references, saturation cannot leave
  that state. -/
  theorem futureReachable_eq_singleton_of_referencedStates_eq_empty
      (automaton : PendingAutomaton) (state : TypeAutomatonState)
      (hReferences : automaton.referencedStates state = ∅) :
      automaton.futureReachable state = {state} := by
    unfold futureReachable
    have hAux : ∀ fuel,
        futureReachableAux automaton fuel {state} = {state} := by
      intro fuel
      induction fuel with
      | zero => rfl
      | succ fuel ih =>
          change futureReachableAux automaton fuel
            (({state} : Finset TypeAutomatonState) ∪
              ({state} : Finset TypeAutomatonState).biUnion
                automaton.referencedStates) = {state}
          simp [hReferences, ih]
    exact hAux automaton.states.card

  private theorem futureStep_mono (automaton : PendingAutomaton)
      {smaller larger : Finset TypeAutomatonState}
      (hSubset : smaller ⊆ larger) :
      automaton.futureStep smaller ⊆ automaton.futureStep larger := by
    intro state hState
    simp only [futureStep, Finset.mem_union, Finset.mem_biUnion] at hState ⊢
    rcases hState with hDirect | ⟨source, hSource, hReference⟩
    · exact Or.inl (hSubset hDirect)
    · exact Or.inr ⟨source, hSubset hSource, hReference⟩

  private theorem futureReachableAux_mono (automaton : PendingAutomaton)
      (fuel : Nat) {smaller larger : Finset TypeAutomatonState}
      (hSubset : smaller ⊆ larger) :
      automaton.futureReachableAux fuel smaller ⊆
        automaton.futureReachableAux fuel larger := by
    induction fuel generalizing smaller larger with
    | zero => exact hSubset
    | succ fuel ih =>
        exact ih (futureStep_mono automaton hSubset)

  private theorem subset_futureReachableAux (automaton : PendingAutomaton)
      (fuel : Nat) (reached : Finset TypeAutomatonState) :
      reached ⊆ automaton.futureReachableAux fuel reached := by
    induction fuel generalizing reached with
    | zero => exact fun _ h => h
    | succ fuel ih =>
        exact (subset_futureStep automaton reached).trans
          (ih (automaton.futureStep reached))

  /-- Saturated same-cycle reachability unfolds by one symbolic-reference
  step.  This is the finite-graph fixed-point equation behind constructor
  roots: a state reaches itself and everything reachable from each of its
  immediate same-cycle references. -/
  theorem futureReachable_unfold (automaton : PendingAutomaton)
      (state : TypeAutomatonState) (hClosed : automaton.ReferencesClosed)
      (hState : state ∈ automaton.states) :
      automaton.futureReachable state =
        {state} ∪ (automaton.referencedStates state).biUnion
          automaton.futureReachable := by
    let closure := automaton.futureReachable state
    let unfolded := ({state} : Finset TypeAutomatonState) ∪
      (automaton.referencedStates state).biUnion automaton.futureReachable
    have hClosureFixed : automaton.futureStep closure = closure := by
      apply futureReachableAux_fixed_after_missing automaton hClosed
      · simpa [closure, futureReachable] using hState
      · omega
    have hStateClosure : state ∈ closure := by
      apply subset_futureReachableAux automaton automaton.states.card {state}
      simp [closure, futureReachable]
    have hReferenceClosure : ∀ reference,
        reference ∈ automaton.referencedStates state →
          automaton.futureReachable reference ⊆ closure := by
      intro reference hReference target hTarget
      have hReferenceState : reference ∈ automaton.states :=
        hClosed state hState hReference
      have hReferenceInClosure : reference ∈ closure := by
        rw [← hClosureFixed]
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨state, hStateClosure, hReference⟩)
      have hSingletonSubset : ({reference} : Finset TypeAutomatonState) ⊆
          closure := by
        simpa using hReferenceInClosure
      have hMonotone := futureReachableAux_mono automaton
        automaton.states.card hSingletonSubset
      have hClosureStable : automaton.futureReachableAux
          automaton.states.card closure = closure := by
        exact futureReachableAux_fixed_of_futureStep_eq automaton closure
          hClosureFixed automaton.states.card
      rw [hClosureStable] at hMonotone
      exact hMonotone hTarget
    have hUnfoldedSubset : unfolded ⊆ closure := by
      intro target hTarget
      simp only [unfolded, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_biUnion] at hTarget
      rcases hTarget with rfl | ⟨reference, hReference, hReachable⟩
      · exact hStateClosure
      · exact hReferenceClosure reference hReference hReachable
    have hUnfoldedFixed : automaton.futureStep unfolded = unfolded := by
      apply Finset.Subset.antisymm
      · intro target hTarget
        simp only [futureStep, Finset.mem_union, Finset.mem_biUnion] at hTarget
        rcases hTarget with hDirect | ⟨source, hSource, hReference⟩
        · exact hDirect
        · simp only [unfolded, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_biUnion] at hSource ⊢
          rcases hSource with rfl | ⟨first, hFirst, hSourceReachable⟩
          · exact Or.inr ⟨target, hReference,
              subset_futureReachableAux automaton automaton.states.card
                {target} (by simpa)⟩
          · have hFirstState : first ∈ automaton.states :=
              hClosed state hState hFirst
            have hFirstFixed : automaton.futureStep
                (automaton.futureReachable first) =
                automaton.futureReachable first := by
              apply futureReachableAux_fixed_after_missing automaton hClosed
              · simpa [futureReachable] using hFirstState
              · omega
            have hTargetReachable : target ∈
                automaton.futureReachable first := by
              rw [← hFirstFixed]
              exact Finset.mem_union_right _
                (Finset.mem_biUnion.mpr
                  ⟨source, hSourceReachable, hReference⟩)
            exact Or.inr ⟨first, hFirst, hTargetReachable⟩
      · exact subset_futureStep automaton unfolded
    apply Finset.Subset.antisymm
    · have hStart : ({state} : Finset TypeAutomatonState) ⊆ unfolded := by
        exact Finset.subset_union_left
      have hMonotone := futureReachableAux_mono automaton
        automaton.states.card hStart
      have hUnfoldedStable : automaton.futureReachableAux
          automaton.states.card unfolded = unfolded :=
        futureReachableAux_fixed_of_futureStep_eq automaton unfolded
          hUnfoldedFixed automaton.states.card
      simpa [closure, futureReachable, hUnfoldedStable] using hMonotone
    · exact hUnfoldedSubset

  /-- If an embedding preserves every child reference as a parent reference,
  every state reachable in the child maps to a state reachable in the parent.
  This one-sided form permits the parent to add references, as sequence does
  when it installs continuation bridges. -/
  theorem futureReachable_image_subset_of_embedding
      (child parent : PendingAutomaton)
      (embed : TypeAutomatonState → TypeAutomatonState)
      (hReferences : ∀ state,
        (child.referencedStates state).image embed ⊆
          parent.referencedStates (embed state))
      (hParentClosed : parent.ReferencesClosed)
      (state : TypeAutomatonState) (hParentState : embed state ∈ parent.states) :
      (child.futureReachable state).image embed ⊆
        parent.futureReachable (embed state) := by
    let parentReach := parent.futureReachable (embed state)
    have hParentFixed : parent.futureStep parentReach = parentReach := by
      apply futureReachableAux_fixed_after_missing parent hParentClosed
      · simpa [parentReach, futureReachable] using hParentState
      · omega
    have hLiftAux : ∀ fuel reached,
        reached.image embed ⊆ parentReach →
          (child.futureReachableAux fuel reached).image embed ⊆
            parentReach := by
      intro fuel
      induction fuel with
      | zero =>
          intro reached hReached
          exact hReached
      | succ fuel ih =>
          intro reached hReached
          apply ih (child.futureStep reached)
          intro target hTarget
          rcases Finset.mem_image.mp hTarget with
            ⟨childTarget, hChildTarget, rfl⟩
          simp only [futureStep, Finset.mem_union, Finset.mem_biUnion]
            at hChildTarget
          rcases hChildTarget with hDirect |
              ⟨childSource, hSource, hReference⟩
          · exact hReached (Finset.mem_image.mpr
              ⟨childTarget, hDirect, rfl⟩)
          · have hMappedSource : embed childSource ∈ parentReach :=
              hReached (Finset.mem_image.mpr
                ⟨childSource, hSource, rfl⟩)
            have hMappedReference : embed childTarget ∈
                parent.referencedStates (embed childSource) :=
              hReferences childSource
                (Finset.mem_image.mpr ⟨childTarget, hReference, rfl⟩)
            rw [← hParentFixed]
            exact Finset.mem_union_right _
              (Finset.mem_biUnion.mpr
                ⟨embed childSource, hMappedSource, hMappedReference⟩)
    unfold futureReachable
    apply hLiftAux child.states.card {state}
    intro target hTarget
    rcases Finset.mem_image.mp hTarget with ⟨source, hSource, rfl⟩
    simp only [Finset.mem_singleton] at hSource
    subst source
    exact subset_futureReachableAux parent parent.states.card {embed state}
      (by simp)

  /-- The starting state is always contained in its finite reference closure. -/
  theorem mem_futureReachable_self (automaton : PendingAutomaton)
      (state : TypeAutomatonState) :
      state ∈ automaton.futureReachable state := by
    apply subset_futureReachableAux automaton automaton.states.card {state}
    simp [futureReachable]

  /-- Every immediate same-cycle reference is contained in the finite
  reference closure of its source. -/
  theorem referencedStates_subset_futureReachable
      (automaton : PendingAutomaton) (source : TypeAutomatonState)
      (hClosed : automaton.ReferencesClosed)
      (hSource : source ∈ automaton.states) :
      automaton.referencedStates source ⊆
        automaton.futureReachable source := by
    rw [automaton.futureReachable_unfold source hClosed hSource]
    intro target hTarget
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨target, hTarget, automaton.mem_futureReachable_self target⟩)

  /-- Reference closure is transitive: the closure of any already reached
  state is contained in the original closure. -/
  theorem futureReachable_subset_of_mem
      (automaton : PendingAutomaton) {source target : TypeAutomatonState}
      (hClosed : automaton.ReferencesClosed)
      (hSource : source ∈ automaton.states)
      (hTarget : target ∈ automaton.futureReachable source) :
      automaton.futureReachable target ⊆
        automaton.futureReachable source := by
    let closure := automaton.futureReachable source
    have hClosureFixed : automaton.futureStep closure = closure := by
      apply futureReachableAux_fixed_after_missing automaton hClosed
      · simpa [closure, futureReachable] using hSource
      · omega
    have hSingletonSubset : ({target} : Finset TypeAutomatonState) ⊆
        closure := by
      simpa [closure] using hTarget
    have hMonotone := futureReachableAux_mono automaton
      automaton.states.card hSingletonSubset
    have hClosureStable : automaton.futureReachableAux
        automaton.states.card closure = closure :=
      futureReachableAux_fixed_of_futureStep_eq automaton closure
        hClosureFixed automaton.states.card
    change automaton.futureReachableAux automaton.states.card {target} ⊆
      closure
    rw [← hClosureStable]
    exact hMonotone

  /-- A finite reference closure is contained in any set which contains its
  source and is closed under immediate references. -/
  theorem futureReachable_subset_of_reference_closed
      (automaton : PendingAutomaton) (source : TypeAutomatonState)
      (allowed : Finset TypeAutomatonState)
      (hSource : source ∈ allowed)
      (hAllowed : ∀ state ∈ allowed,
        automaton.referencedStates state ⊆ allowed) :
      automaton.futureReachable source ⊆ allowed := by
    unfold futureReachable
    have hAux : ∀ fuel reached, reached ⊆ allowed →
        automaton.futureReachableAux fuel reached ⊆ allowed := by
      intro fuel
      induction fuel with
      | zero =>
          intro reached hReached
          exact hReached
      | succ fuel ih =>
          intro reached hReached
          apply ih
          intro state hState
          simp only [futureStep, Finset.mem_union,
            Finset.mem_biUnion] at hState
          rcases hState with hState | ⟨parent, hParent, hReference⟩
          · exact hReached hState
          · exact hAllowed parent (hReached hParent) hReference
    apply hAux
    simpa using hSource

  /-- A root whose immediate references are exactly a set of child entries,
  possibly together with a self-reference, reaches precisely itself and the
  complete closures of those child entries.  This packages the harmless
  self-loop pattern used by the offer constructors. -/
  theorem futureReachable_eq_self_union_biUnion
      (automaton : PendingAutomaton) (source : TypeAutomatonState)
      (entries : Finset TypeAutomatonState)
      (hClosed : automaton.ReferencesClosed)
      (hSource : source ∈ automaton.states)
      (hReferencesUpper : automaton.referencedStates source ⊆
        insert source entries)
      (hEntries : entries ⊆ automaton.referencedStates source) :
      automaton.futureReachable source =
        {source} ∪ entries.biUnion automaton.futureReachable := by
    apply Finset.Subset.antisymm
    · apply automaton.futureReachable_subset_of_reference_closed source
        ({source} ∪ entries.biUnion automaton.futureReachable)
      · simp
      · intro state hState reference hReference
        simp only [Finset.mem_union, Finset.mem_singleton,
          Finset.mem_biUnion] at hState ⊢
        rcases hState with rfl | ⟨entry, hEntry, hReachable⟩
        · have hClassified := hReferencesUpper hReference
          simp only [Finset.mem_insert] at hClassified
          rcases hClassified with rfl | hEntry
          · exact Or.inl rfl
          · exact Or.inr ⟨reference, hEntry,
              automaton.mem_futureReachable_self reference⟩
        · have hEntryState : entry ∈ automaton.states :=
            hClosed source hSource (hEntries hEntry)
          have hReferenceReachable : reference ∈
              automaton.futureReachable entry := by
            have hStateInStates : state ∈ automaton.states :=
              (automaton.futureReachable_subset_of_reference_closed
                entry automaton.states hEntryState
                  (fun current hCurrent => hClosed current hCurrent))
                hReachable
            have hReferenceAtState :=
              automaton.referencedStates_subset_futureReachable state
                hClosed hStateInStates
            have hStateClosure := automaton.futureReachable_subset_of_mem
              hClosed hEntryState hReachable
            exact hStateClosure (hReferenceAtState hReference)
          exact Or.inr ⟨entry, hEntry, hReferenceReachable⟩
    · intro state hState
      simp only [Finset.mem_union, Finset.mem_singleton,
        Finset.mem_biUnion] at hState
      rcases hState with rfl | ⟨entry, hEntry, hReachable⟩
      · exact automaton.mem_futureReachable_self _
      · have hEntryReachable :=
          automaton.referencedStates_subset_futureReachable source hClosed
            hSource (hEntries hEntry)
        exact (automaton.futureReachable_subset_of_mem hClosed hSource
          hEntryReachable) hReachable

end PendingAutomaton

/-- A graph containing only explicit future fields has no symbolic future
references.  Parallel products have this form after their child decorations
have been resolved. -/
theorem PendingAutomaton.referencedStates_eq_empty_of_all_explicit
    (automaton : PendingAutomaton)
    (hExplicit : ∀ edge ∈ automaton.edges,
      ∃ offers, edge.future = .explicit offers)
    (state : TypeAutomatonState) :
    automaton.referencedStates state = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro target hTarget
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter] at hTarget
  rcases hTarget with ⟨edge, ⟨hEdge, _⟩, hFuture⟩
  obtain ⟨offers, hOffers⟩ := hExplicit edge hEdge
  simp [hOffers] at hFuture


end

end Pact
