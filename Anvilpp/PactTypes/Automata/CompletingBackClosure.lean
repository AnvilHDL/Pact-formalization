import Anvilpp.PactTypes.Automata.SyncEdgesLemmas

/-!
# Backward completion closure used to seed recursion-body completing sets
-/

namespace Pact

noncomputable section

/-! ### Reusable constructor combinators -/

/-- One step of backward closure for completion: add every state with a
non-clock outgoing edge into an already-completing state.  Message, progress,
and administrative edges may all occur before the next clock, so completion
at their target transports backward to their source. -/
private def completingBackStep (body : AutomatonFragment)
    (reached : Finset TypeAutomatonState) : Finset TypeAutomatonState :=
  reached ∪
    (body.edges.filter fun edge =>
      edge.label.semantic ≠ TypeLabel.tock ∧ edge.target ∈ reached).image
      fun edge => edge.source

private def completingBackClosureAux (body : AutomatonFragment) :
    Nat → Finset TypeAutomatonState → Finset TypeAutomatonState
  | 0, reached => reached
  | fuel + 1, reached =>
      completingBackClosureAux body fuel (completingBackStep body reached)

/-- Saturate backward closure for `|E|` rounds.  Every state a round can add
is the source of some edge, so after `body.edges.card` rounds no new source
remains available and the operator has reached its fixed point.  Using the
edge count rather than the state count makes saturation provable with no
well-formedness side condition on the fragment. -/
def completingBackClosure (body : AutomatonFragment)
    (seed : Finset TypeAutomatonState) : Finset TypeAutomatonState :=
  completingBackClosureAux body body.edges.card seed

/-! #### Hypothesis-free saturation

`completingBackStep` is extensive and monotone, and everything it can add
lies in `body.edges.image (·.source)`.  A strictly growing chain inside that
finite set therefore stabilizes within `body.edges.card` rounds. -/

private theorem completingBackStep_subset (body : AutomatonFragment)
    (reached : Finset TypeAutomatonState) :
    reached ⊆ completingBackStep body reached :=
  Finset.subset_union_left

private theorem completingBackStep_mono (body : AutomatonFragment)
    {left right : Finset TypeAutomatonState} (hSubset : left ⊆ right) :
    completingBackStep body left ⊆ completingBackStep body right := by
  classical
  intro state hState
  simp only [completingBackStep, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hState ⊢
  rcases hState with hState | ⟨edge, ⟨hEdge, hLabel, hTarget⟩, hSource⟩
  · exact Or.inl (hSubset hState)
  · exact Or.inr ⟨edge, ⟨hEdge, hLabel, hSubset hTarget⟩, hSource⟩

/-- Anything a round adds is the source of an edge of `body`. -/
private theorem completingBackStep_subset_union_sources
    (body : AutomatonFragment) (reached : Finset TypeAutomatonState) :
    completingBackStep body reached ⊆
      reached ∪ body.edges.image (fun edge => edge.source) := by
  classical
  intro state hState
  simp only [completingBackStep, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hState ⊢
  rcases hState with hState | ⟨edge, ⟨hEdge, _, _⟩, hSource⟩
  · exact Or.inl hState
  · exact Or.inr ⟨edge, hEdge, hSource⟩

/-- The recursion unrolls on the left; this is the matching right-hand step. -/
private theorem completingBackClosureAux_succ_right
    (body : AutomatonFragment) :
    ∀ fuel reached,
      completingBackClosureAux body (fuel + 1) reached =
        completingBackStep body
          (completingBackClosureAux body fuel reached) := by
  intro fuel
  induction fuel with
  | zero => intro reached; rfl
  | succ fuel ih =>
      intro reached
      show completingBackClosureAux body (fuel + 1)
          (completingBackStep body reached) = _
      rw [ih (completingBackStep body reached)]
      rfl

private theorem subset_completingBackClosureAux (body : AutomatonFragment) :
    ∀ fuel reached, reached ⊆ completingBackClosureAux body fuel reached := by
  intro fuel
  induction fuel with
  | zero => intro reached; exact Finset.Subset.refl _
  | succ fuel ih =>
      intro reached
      exact (completingBackStep_subset body reached).trans
        (ih (completingBackStep body reached))

/-- Once a round changes nothing, no later round changes anything either. -/
private theorem completingBackClosureAux_stable
    (body : AutomatonFragment) (seed : Finset TypeAutomatonState) :
    ∀ extra fuel,
      completingBackStep body (completingBackClosureAux body fuel seed) =
          completingBackClosureAux body fuel seed →
        completingBackClosureAux body (fuel + extra) seed =
          completingBackClosureAux body fuel seed := by
  intro extra
  induction extra with
  | zero => intro fuel _; rfl
  | succ extra ih =>
      intro fuel hStable
      have hPrevious : completingBackClosureAux body (fuel + extra) seed =
          completingBackClosureAux body fuel seed := ih fuel hStable
      show completingBackClosureAux body (fuel + extra + 1) seed = _
      rw [completingBackClosureAux_succ_right, hPrevious, hStable]

/-- Either the chain has already stabilized, or it has consumed at least
`fuel` distinct edge sources. -/
private theorem completingBackClosureAux_stable_or_card
    (body : AutomatonFragment) (seed : Finset TypeAutomatonState) :
    ∀ fuel,
      completingBackStep body (completingBackClosureAux body fuel seed) =
          completingBackClosureAux body fuel seed ∨
        fuel ≤ ((completingBackClosureAux body fuel seed) ∩
          body.edges.image (fun edge => edge.source)).card := by
  classical
  intro fuel
  induction fuel with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ fuel ih =>
      by_cases hStable :
          completingBackStep body
              (completingBackClosureAux body (fuel + 1) seed) =
            completingBackClosureAux body (fuel + 1) seed
      · exact Or.inl hStable
      · refine Or.inr ?_
        have hStep : completingBackClosureAux body (fuel + 1) seed =
            completingBackStep body
              (completingBackClosureAux body fuel seed) :=
          completingBackClosureAux_succ_right body fuel seed
        have hPreviousNotStable :
            completingBackStep body
                (completingBackClosureAux body fuel seed) ≠
              completingBackClosureAux body fuel seed := by
          intro hEq
          apply hStable
          rw [hStep, hEq, hEq]
        have hCard : fuel ≤ ((completingBackClosureAux body fuel seed) ∩
            body.edges.image (fun edge => edge.source)).card := by
          rcases ih with hEq | hCard
          · exact absurd hEq hPreviousNotStable
          · exact hCard
        have hGrow : (completingBackClosureAux body fuel seed) ∩
              body.edges.image (fun edge => edge.source) ⊂
            (completingBackClosureAux body (fuel + 1) seed) ∩
              body.edges.image (fun edge => edge.source) := by
          constructor
          · intro state hState
            simp only [Finset.mem_inter] at hState ⊢
            exact ⟨(hStep ▸ completingBackStep_subset body _) hState.1,
              hState.2⟩
          · intro hSubset
            apply hPreviousNotStable
            apply Finset.Subset.antisymm _ (completingBackStep_subset body _)
            intro state hState
            rcases Finset.mem_union.mp
              (completingBackStep_subset_union_sources body
                (completingBackClosureAux body fuel seed) hState) with
              hOld | hSource
            · exact hOld
            · have hInter : state ∈
                  (completingBackClosureAux body (fuel + 1) seed) ∩
                    body.edges.image (fun edge => edge.source) :=
                Finset.mem_inter.mpr ⟨hStep ▸ hState, hSource⟩
              exact (Finset.mem_inter.mp (hSubset hInter)).1
        have := Finset.card_lt_card hGrow
        omega

/-- The saturated closure really is a fixed point of one more round. -/
private theorem completingBackClosure_fixed (body : AutomatonFragment)
    (seed : Finset TypeAutomatonState) :
    completingBackStep body (completingBackClosure body seed) =
      completingBackClosure body seed := by
  classical
  set sources := body.edges.image (fun edge => edge.source) with hSources
  have hSourcesCard : sources.card ≤ body.edges.card :=
    Finset.card_image_le
  have hAtSources :
      completingBackStep body
          (completingBackClosureAux body sources.card seed) =
        completingBackClosureAux body sources.card seed := by
    rcases completingBackClosureAux_stable_or_card body seed sources.card with
      hStable | hCard
    · exact hStable
    · have hFull : (completingBackClosureAux body sources.card seed) ∩
          sources = sources := by
        apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
        exact hCard
      have hContained : sources ⊆
          completingBackClosureAux body sources.card seed := by
        intro state hState
        have := hFull ▸ hState
        exact (Finset.mem_inter.mp this).1
      apply Finset.Subset.antisymm _ (completingBackStep_subset body _)
      intro state hState
      rcases Finset.mem_union.mp
        (completingBackStep_subset_union_sources body _ hState) with
        hOld | hSource
      · exact hOld
      · exact hContained hSource
  obtain ⟨extra, hExtra⟩ := Nat.exists_eq_add_of_le hSourcesCard
  unfold completingBackClosure
  rw [hExtra, completingBackClosureAux_stable body seed extra sources.card
    hAtSources, hAtSources]

/-! ### Backward-closure characterization

`completingBackClosure` is definitionally a forward `futureReachable`
saturation on the *reversed* non-clock graph: reverse every edge other than a
`tock` edge of `body`, encoding its (reversed) target as a `FutureSpec.at`
reference, and reuse the whole `PendingAutomaton.futureReachable` proof library
instead of redeveloping the fixed-point argument. -/

/-- One non-clock edge of `body`, reversed and repackaged as a `FutureSpec.at`
reference from its target back to its source. -/
private def nonClockBackEdge
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  { source := edge.target
    environment := TypeEnvironment.empty
    label := .visible TypeLabel.silent
    current := ∅
    future := .at edge.source ∅
    target := edge.target }

private def nonClockBackEdges (body : AutomatonFragment) :
    Finset PendingAutomatonEdge :=
  (body.edges.filter fun edge => edge.label.semantic != TypeLabel.tock).image
    nonClockBackEdge

/-- The pending automaton whose forward same-cycle reference closure from a
state computes exactly the states that reach it backward through non-clock
edges of `body`. -/
private def nonClockBackPending (body : AutomatonFragment) : PendingAutomaton :=
  { states := body.states, edges := nonClockBackEdges body }

private theorem nonClockBackPending_referencedStates
    (body : AutomatonFragment) (state : TypeAutomatonState) :
    (nonClockBackPending body).referencedStates state =
      (body.edges.filter fun edge =>
        edge.label.semantic ≠ TypeLabel.tock ∧ edge.target = state).image
        fun edge => edge.source := by
  classical
  ext source
  constructor
  · intro hMember
    simp only [PendingAutomaton.referencedStates, nonClockBackPending,
      Finset.mem_biUnion, Finset.mem_filter] at hMember
    obtain ⟨backEdge, ⟨hBackEdge, hSource⟩, hReference⟩ := hMember
    simp only [nonClockBackEdges, Finset.mem_image, Finset.mem_filter,
      bne_iff_ne] at hBackEdge
    obtain ⟨edge, ⟨hEdge, hLabel⟩, hBackEdgeEq⟩ := hBackEdge
    have hSourceEq : edge.target = state := by
      rw [← hBackEdgeEq] at hSource
      simpa [nonClockBackEdge] using hSource
    have hReferenceEq : source = edge.source := by
      rw [← hBackEdgeEq] at hReference
      simpa [nonClockBackEdge, AutomatonConstructionLabel.semantic,
        TypeLabel.silent] using hReference
    simp only [Finset.mem_image, Finset.mem_filter]
    exact ⟨edge, ⟨hEdge, hLabel, hSourceEq⟩, hReferenceEq.symm⟩
  · intro hMember
    simp only [Finset.mem_image, Finset.mem_filter] at hMember
    obtain ⟨edge, ⟨hEdge, hLabel, hTarget⟩, hSourceEq⟩ := hMember
    have hFilterMem : edge ∈ body.edges.filter fun edge =>
        edge.label.semantic != TypeLabel.tock := by
      simp [hEdge, hLabel]
    simp only [PendingAutomaton.referencedStates, nonClockBackPending,
      Finset.mem_biUnion, Finset.mem_filter]
    refine ⟨nonClockBackEdge edge, ⟨?_, ?_⟩, ?_⟩
    · simp only [nonClockBackEdges, Finset.mem_image]
      exact ⟨edge, hFilterMem, rfl⟩
    · simp [nonClockBackEdge, hTarget]
    · simp [nonClockBackEdge, AutomatonConstructionLabel.semantic,
        TypeLabel.silent, hSourceEq]

private theorem completingBackStep_eq_futureStep (body : AutomatonFragment)
    (reached : Finset TypeAutomatonState) :
    completingBackStep body reached =
      (nonClockBackPending body).futureStep reached := by
  classical
  simp only [completingBackStep, PendingAutomaton.futureStep]
  congr 1
  ext source
  simp only [Finset.mem_biUnion, nonClockBackPending_referencedStates,
    Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨edge, ⟨hEdge, hLabel, hTargetReached⟩, rfl⟩
    exact ⟨edge.target, hTargetReached, edge, ⟨hEdge, hLabel, rfl⟩, rfl⟩
  · rintro ⟨target, hTargetReached, edge, ⟨hEdge, hLabel, hTarget⟩, rfl⟩
    exact ⟨edge, ⟨hEdge, hLabel, hTarget ▸ hTargetReached⟩, rfl⟩

private theorem completingBackClosureAux_eq_futureReachableAux
    (body : AutomatonFragment) :
    ∀ fuel reached,
      completingBackClosureAux body fuel reached =
        (nonClockBackPending body).futureReachableAux fuel reached := by
  intro fuel
  induction fuel with
  | zero => intro reached; rfl
  | succ fuel ih =>
      intro reached
      simp only [completingBackClosureAux, PendingAutomaton.futureReachableAux]
      rw [completingBackStep_eq_futureStep]
      exact ih _

/-- `completingBackClosure` is exactly forward `futureReachable` saturation on
the reversed silent-edge graph, started from `seed` instead of a singleton.
This transports the entire proved `futureReachable` fixed-point theory
(closure, monotonicity, unfolding) to backward completion closure. -/
private theorem completingBackClosure_eq_futureReachableAux
    (body : AutomatonFragment) (seed : Finset TypeAutomatonState) :
    completingBackClosure body seed =
      (nonClockBackPending body).futureReachableAux body.edges.card seed := by
  simp only [completingBackClosure]
  exact completingBackClosureAux_eq_futureReachableAux body body.edges.card
    seed

/-- Two saturated iterates from the same seed agree: whichever stabilizes
first is propagated to the other by `completingBackClosureAux_stable`. -/
private theorem completingBackClosureAux_eq_of_fixed
    (body : AutomatonFragment) (seed : Finset TypeAutomatonState)
    {left right : Nat}
    (hLeft : completingBackStep body (completingBackClosureAux body left seed) =
      completingBackClosureAux body left seed)
    (hRight : completingBackStep body
        (completingBackClosureAux body right seed) =
      completingBackClosureAux body right seed) :
    completingBackClosureAux body left seed =
      completingBackClosureAux body right seed := by
  rcases Nat.le_total left right with hLe | hLe
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hLe
    exact (completingBackClosureAux_stable body seed extra left hLeft).symm
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hLe
    exact completingBackClosureAux_stable body seed extra right hRight

/-- The reversed non-clock graph is reference-closed whenever `body`'s
states already contain every edge endpoint (ordinary edge endpoints, not
symbolic future references, so no `FutureTargetsInStates` premise is needed
here). -/
private theorem nonClockBackPending_referencesClosed
    (body : AutomatonFragment)
    (hSources : ∀ edge ∈ body.edges, edge.source ∈ body.states) :
    (nonClockBackPending body).ReferencesClosed := by
  intro state _ target hTarget
  rw [nonClockBackPending_referencedStates] at hTarget
  simp only [Finset.mem_image, Finset.mem_filter] at hTarget
  rcases hTarget with ⟨edge, ⟨hEdge, _, _⟩, rfl⟩
  simpa [nonClockBackPending] using hSources edge hEdge

/-- Backward completion closure unfolds by one symbolic non-clock predecessor
step: a state is in the closure of `seed` exactly when it already belongs to
`seed`, or it has an outgoing silent edge into a state whose own backward
closure already contains `seed`-reachable material.  In practice this is used
through the two directional corollaries below. -/
theorem completingBackClosure_superset_seed
    (body : AutomatonFragment) (seed : Finset TypeAutomatonState) :
    seed ⊆ completingBackClosure body seed :=
  subset_completingBackClosureAux body body.edges.card seed

/-- If `source` has a non-clock edge into some state already in the closure of
`seed`, then `source` itself is in the closure of `seed`.  This is the
predecessor-step direction used to place the recursion root/backedge sources
into the closure.  It needs no well-formedness side condition: the closure is
a fixed point of `completingBackStep` by `completingBackClosure_fixed`. -/
theorem completingBackClosure_mem_of_nonClockEdge
    (body : AutomatonFragment) (seed : Finset TypeAutomatonState)
    (edge : PendingAutomatonEdge) (hEdge : edge ∈ body.edges)
    (hLabel : edge.label.semantic ≠ TypeLabel.tock)
    (hTarget : edge.target ∈ completingBackClosure body seed) :
    edge.source ∈ completingBackClosure body seed := by
  classical
  have hStepMem : edge.source ∈
      completingBackStep body (completingBackClosure body seed) := by
    simp only [completingBackStep, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter]
    exact Or.inr ⟨edge, ⟨hEdge, hLabel, hTarget⟩, rfl⟩
  rwa [completingBackClosure_fixed body seed] at hStepMem

/-- Backward completion closure is contained in any predecessor-closed set
containing `seed`: if a set contains `seed` and is closed under taking
non-clock
predecessors, the whole closure lands inside it.  This is the direction used
to bound the closure from above by a syntactic completion characterization. -/
theorem completingBackClosure_subset_of_predecessor_closed
    (body : AutomatonFragment) (seed allowed : Finset TypeAutomatonState)
    (hSeed : seed ⊆ allowed)
    (hAllowed : ∀ edge ∈ body.edges,
      edge.label.semantic ≠ TypeLabel.tock → edge.target ∈ allowed →
        edge.source ∈ allowed) :
    completingBackClosure body seed ⊆ allowed := by
  rw [completingBackClosure_eq_futureReachableAux]
  have hAux : ∀ fuel reached, reached ⊆ allowed →
      (nonClockBackPending body).futureReachableAux fuel reached ⊆ allowed := by
    intro fuel
    induction fuel with
    | zero => intro reached hReached; exact hReached
    | succ fuel ih =>
        intro reached hReached
        simp only [PendingAutomaton.futureReachableAux]
        apply ih
        intro state hState
        simp only [PendingAutomaton.futureStep, Finset.mem_union,
          Finset.mem_biUnion] at hState
        rcases hState with hState | ⟨source, hSource, hReference⟩
        · exact hReached hState
        · rw [nonClockBackPending_referencedStates] at hReference
          simp only [Finset.mem_image, Finset.mem_filter] at hReference
          rcases hReference with ⟨edge, ⟨hEdge, hLabel, hTarget⟩, rfl⟩
          apply hAllowed edge hEdge hLabel
          rw [hTarget]
          exact hReached hSource
  exact hAux body.edges.card seed hSeed

/-- Backward completion closure is monotone in the seed. -/
theorem completingBackClosure_mono
    (body : AutomatonFragment)
    {seed1 seed2 : Finset TypeAutomatonState} (hSubset : seed1 ⊆ seed2) :
    completingBackClosure body seed1 ⊆ completingBackClosure body seed2 := by
  apply completingBackClosure_subset_of_predecessor_closed
  · exact hSubset.trans (completingBackClosure_superset_seed body seed2)
  · intro edge hEdge hLabel hTarget
    exact completingBackClosure_mem_of_nonClockEdge body seed2
      edge hEdge hLabel hTarget

/-- Inserting a state with no incoming non-clock edges into the seed only adds
that state itself to the closure: it can never unlock a new predecessor,
since no edge targets it. -/
theorem completingBackClosure_union_isolated_target
    (body : AutomatonFragment) (isolated : TypeAutomatonState)
    (seed : Finset TypeAutomatonState)
    (hNoIncoming : ∀ edge ∈ body.edges, edge.target ≠ isolated) :
    completingBackClosure body ({isolated} ∪ seed) =
      {isolated} ∪ completingBackClosure body seed := by
  apply Finset.Subset.antisymm
  · apply completingBackClosure_subset_of_predecessor_closed
    · exact Finset.union_subset_union (Finset.Subset.refl _)
        (completingBackClosure_superset_seed body seed)
    · intro edge hEdge hLabel hTarget
      simp only [Finset.mem_union, Finset.mem_singleton] at hTarget ⊢
      rcases hTarget with hTarget | hTarget
      · exact absurd hTarget (hNoIncoming edge hEdge)
      · exact Or.inr (completingBackClosure_mem_of_nonClockEdge body seed
          edge hEdge hLabel hTarget)
  · apply Finset.union_subset
    · exact (Finset.subset_union_left).trans
        (completingBackClosure_superset_seed body ({isolated} ∪ seed))
    · exact completingBackClosure_mono body Finset.subset_union_right

/-- A carrier whose states and edges are `body`'s own states/edges, each
tagged by `childState index`, but whose completing/accepting/initial
bookkeeping is irrelevant to backward closure and is therefore left blank.
This is definitionally the state/edge shape shared by `buildRecursionAutomaton`'s
`taggedCarrier` (at `index = 0`) and by any other constructor that lifts a
child fragment's edges with `childPendingEdge`. -/
def taggedFragment (index : Nat) (body : AutomatonFragment) :
    AutomatonFragment :=
  { states := childStates index body
    initial := childState index body.initial
    accepting := ∅
    edges := body.edges.image fun edge =>
      { source := childState index edge.source
        environment := edge.environment
        label := edge.label
        current := edge.current
        future := edge.future
        target := childState index edge.target } }

/-- The reversed non-clock predecessor function commutes exactly with
`childState index`-tagging: predecessors of a tagged state in the tagged
carrier are exactly the tagged predecessors of the untagged state in `body`.
-/
private theorem nonClockBackPending_taggedFragment_referencedStates
    (index : Nat) (body : AutomatonFragment) (state : TypeAutomatonState) :
    (nonClockBackPending (taggedFragment index body)).referencedStates
        (childState index state) =
      ((nonClockBackPending body).referencedStates state).image
        (childState index) := by
  classical
  rw [nonClockBackPending_referencedStates,
    nonClockBackPending_referencedStates]
  ext source
  constructor
  · intro hMember
    simp only [taggedFragment, Finset.mem_image, Finset.mem_filter] at hMember
    obtain ⟨edge, ⟨⟨original, hOriginal, hEdgeEq⟩, hLabel, hTarget⟩, hSourceEq⟩ :=
      hMember
    subst hEdgeEq
    simp only at hLabel hTarget
    have hTargetEq : original.target = state := by injection hTarget
    simp only [Finset.mem_image, Finset.mem_filter]
    exact ⟨original.source, ⟨original, ⟨hOriginal, hLabel, hTargetEq⟩, rfl⟩,
      hSourceEq⟩
  · intro hMember
    simp only [Finset.mem_image, Finset.mem_filter] at hMember
    obtain ⟨candidate, ⟨original, ⟨hOriginal, hLabel, hTarget⟩, hSourceEq⟩, hEq⟩ :=
      hMember
    simp only [taggedFragment, Finset.mem_image, Finset.mem_filter]
    refine ⟨_, ⟨⟨original, hOriginal, rfl⟩, ?_, ?_⟩, ?_⟩
    · simpa using hLabel
    · simp [childState, hTarget]
    · simp only [childState, hSourceEq]; exact hEq

/-- Backward completion closure commutes with `childState`-tagging: computing
the closure in the tagged carrier and reading off tagged states is the same
as computing the closure directly in `body` and tagging the result.  This is
the single reusable embedding underlying every constructor's use of backward
completion closure over a tagged child. -/
theorem completingBackClosure_taggedFragment_image
    (index : Nat) (body : AutomatonFragment) (seed : Finset TypeAutomatonState) :
    completingBackClosure (taggedFragment index body) (seed.image (childState index)) =
      (completingBackClosure body seed).image (childState index) := by
  classical
  rw [completingBackClosure_eq_futureReachableAux,
    completingBackClosure_eq_futureReachableAux]
  have hEdgesCard : (taggedFragment index body).edges.card = body.edges.card := by
    simp only [taggedFragment]
    apply Finset.card_image_of_injective
    intro a b hEq
    simp only [PendingAutomatonEdge.mk.injEq, childState,
      TypeAutomatonState.child.injEq] at hEq
    cases a
    cases b
    simp_all
  rw [hEdgesCard]
  exact PendingAutomaton.futureReachableAux_image_of_embedding
    (nonClockBackPending body)
      (nonClockBackPending (taggedFragment index body))
    (childState index)
    (fun state =>
      nonClockBackPending_taggedFragment_referencedStates index body state)
    body.edges.card seed

/-- `completingBackStep`, hence the whole closure, depends only on the
`(source, label, target)` projection of each edge.  Two fragments whose edges
agree on that projection (in particular differing only in unused `future`
bookkeeping) and whose declared state sets both bound the true edge/seed
footprint compute the same backward completion closure regardless of their
raw `states.card` fuel bound.  This lets `buildRecursionAutomaton`'s literal
`taggedCarrier` be identified with the canonical `taggedFragment` used by the
embedding lemma above. -/
theorem completingBackClosure_eq_of_edges_agree
    (first second : AutomatonFragment)
    (hAgree : ∀ source label target,
        (∃ edge ∈ first.edges,
          edge.source = source ∧ edge.label = label ∧ edge.target = target) ↔
        (∃ edge ∈ second.edges,
          edge.source = source ∧ edge.label = label ∧ edge.target = target))
    (seed : Finset TypeAutomatonState) :
    completingBackClosure first seed = completingBackClosure second seed := by
  classical
  have hStep : ∀ reached, completingBackStep first reached =
      completingBackStep second reached := by
    intro reached
    simp only [completingBackStep]
    congr 1
    ext source
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨edge, ⟨hEdge, hLabel, hReached⟩, rfl⟩
      obtain ⟨edge', hEdge', hSourceEq, hLabelEq, hTargetEq⟩ :=
        (hAgree edge.source edge.label edge.target).mp ⟨edge, hEdge, rfl, rfl, rfl⟩
      exact ⟨edge', ⟨hEdge', hLabelEq ▸ hLabel, hTargetEq ▸ hReached⟩, hSourceEq⟩
    · rintro ⟨edge, ⟨hEdge, hLabel, hReached⟩, rfl⟩
      obtain ⟨edge', hEdge', hSourceEq, hLabelEq, hTargetEq⟩ :=
        (hAgree edge.source edge.label edge.target).mpr ⟨edge, hEdge, rfl, rfl, rfl⟩
      exact ⟨edge', ⟨hEdge', hLabelEq ▸ hLabel, hTargetEq ▸ hReached⟩, hSourceEq⟩
  have hAux : ∀ fuel reached, completingBackClosureAux first fuel reached =
      completingBackClosureAux second fuel reached := by
    intro fuel
    induction fuel with
    | zero => intro reached; rfl
    | succ fuel ih =>
        intro reached
        simp only [completingBackClosureAux, hStep]
        exact ih _
  -- Both fragments saturate; transport `second`'s fixed point along the
  -- shared step function, then match the two saturated iterates.
  have hFirstFixed : completingBackStep first
      (completingBackClosureAux first first.edges.card seed) =
      completingBackClosureAux first first.edges.card seed :=
    completingBackClosure_fixed first seed
  have hSecondFixed : completingBackStep first
      (completingBackClosureAux first second.edges.card seed) =
      completingBackClosureAux first second.edges.card seed := by
    rw [hAux second.edges.card seed, hStep]
    exact completingBackClosure_fixed second seed
  calc completingBackClosure first seed
      = completingBackClosureAux first second.edges.card seed :=
        completingBackClosureAux_eq_of_fixed first seed hFirstFixed hSecondFixed
    _ = completingBackClosureAux second second.edges.card seed :=
        hAux second.edges.card seed
    _ = completingBackClosure second seed := rfl

/-- Backward completion closure is monotone under edge-set growth: enlarging
the carrier's edges (any edge realized in `first`, as a `(source, label,
target)` triple, also realized in `second`) can only enlarge the closure.
Unlike `completingBackClosure_eq_of_edges_agree` this is one-directional and
needs no card/fuel matching argument at all -- it is a direct
predecessor-closure argument: `completingBackClosure second seed` is itself
predecessor-closed under `second`'s (hence, via `hSubset`, under `first`'s)
edges and contains `seed`, so it already bounds `first`'s closure from above. -/
theorem completingBackClosure_mono_edges
    (first second : AutomatonFragment)
    (hSubset : ∀ source label target,
        (∃ edge ∈ first.edges,
          edge.source = source ∧ edge.label = label ∧ edge.target = target) →
        (∃ edge ∈ second.edges,
          edge.source = source ∧ edge.label = label ∧ edge.target = target))
    (seed : Finset TypeAutomatonState) :
    completingBackClosure first seed ⊆ completingBackClosure second seed := by
  apply completingBackClosure_subset_of_predecessor_closed
  · exact completingBackClosure_superset_seed second seed
  · intro edge hEdge hLabel hTarget
    obtain ⟨edge', hEdge', hSourceEq, hLabelEq, hTargetEq⟩ :=
      hSubset edge.source edge.label edge.target ⟨edge, hEdge, rfl, rfl, rfl⟩
    have hLabel' : edge'.label.semantic ≠ TypeLabel.tock := by
      rw [hLabelEq]; exact hLabel
    have hTarget' : edge'.target ∈ completingBackClosure second seed := by
      rw [hTargetEq]; exact hTarget
    have hResult := completingBackClosure_mem_of_nonClockEdge second seed edge'
      hEdge' hLabel' hTarget'
    rwa [hSourceEq] at hResult

end

end Pact
