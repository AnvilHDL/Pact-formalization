import Anvilpp.PactTypes.Spec.Automata.BuildParallelAutomaton
import Anvilpp.PactTypes.Proofs.Automata.CompileTypeLemmas
import Anvilpp.PactTypes.Proofs.Syntax.TypeDynamicsCoreLemmas
import Anvilpp.PactTypes.Proofs.Automata.BuildOfferAutomataLemmas
import Anvilpp.PactTypes.Proofs.Automata.BuildChoiceAutomatonLemmas
import Anvilpp.PactTypes.Proofs.Automata.BuildRecursionAutomatonLemmas

/-!
Absence of marker edges for one recursion variable, constructor by constructor.
-/

namespace Pact

noncomputable section

/-- Tagging an edge for a child slot keeps its label. -/
theorem childPendingEdges_noMarkerFor
    (index : Nat) (fragment : AutomatonFragment) (name : String)
    (hChild : fragment.NoMarkerFor name) :
    ∀ edge ∈ childPendingEdges index fragment,
      edge.label ≠ AutomatonConstructionLabel.variable name := by
  classical
  intro edge hEdge
  simp only [childPendingEdges, Finset.mem_image] at hEdge
  obtain ⟨original, hOriginal, rfl⟩ := hEdge
  exact hChild original hOriginal

/-- The indexed branch edges of an offer keep their branch labels. -/
theorem indexedFragmentEdges_noMarkerFor
    (automata : List (BareMessage × AutomatonFragment)) (name : String)
    (hChildren : ∀ entry ∈ automata, entry.2.NoMarkerFor name) :
    ∀ edge ∈ indexedFragmentEdges automata,
      edge.label ≠ AutomatonConstructionLabel.variable name := by
  classical
  intro edge hEdge
  simp only [indexedFragmentEdges, mem_foldl_union_iff, Finset.notMem_empty,
    false_or] at hEdge
  obtain ⟨indexed, hIndexed, hMem⟩ := hEdge
  obtain ⟨entry, index⟩ := indexed
  rw [List.mk_mem_zipIdx_iff_getElem?] at hIndexed
  refine childPendingEdges_noMarkerFor (index + 1) entry.2 name ?_ edge hMem
  exact hChildren entry (List.mem_of_getElem? hIndexed)

theorem buildChoiceAutomaton_noMarkerFor
    (alphabet : PactTypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (name : String)
    (hLeft : left.NoMarkerFor name) (hRight : right.NoMarkerFor name) :
    (buildChoiceAutomaton alphabet left right selectionLeft
      selectionRight).NoMarkerFor name := by
  classical
  intro edge hEdge
  simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton] at hEdge
  rcases hEdge with (hLeftEdge | hRightEdge) | hSelection
  · exact childPendingEdges_noMarkerFor 0 left name hLeft edge hLeftEdge
  · exact childPendingEdges_noMarkerFor 1 right name hRight edge hRightEdge
  · obtain ⟨environment, -, hEq⟩ := hSelection
    rcases hEq with rfl | rfl <;> simp

theorem buildSequenceAutomaton_noMarkerFor
    (left right : AutomatonFragment)
    {leftFuture : TypeAutomatonState → Finset BareMessage}
    {leftCompletes : TypeAutomatonState → Bool} (name : String)
    (hLeft : left.NoMarkerFor name) (hRight : right.NoMarkerFor name) :
    (buildSequenceAutomaton left right leftFuture leftCompletes).NoMarkerFor name := by
  classical
  intro edge hEdge
  simp only [buildSequenceAutomaton, finishAutomatonFragment, Finset.mem_union,
    sequenceLeftEdges, sequenceRightEdges, sequenceRedirectEdges,
    Finset.mem_image, Finset.mem_filter] at hEdge
  rcases hEdge with (⟨original, ⟨hOriginal, -⟩, rfl⟩ | hRightEdge) |
    ⟨original, ⟨hOriginal, -⟩, rfl⟩
  · exact hLeft original hOriginal
  · exact childPendingEdges_noMarkerFor 1 right name hRight edge hRightEdge
  · exact hLeft original hOriginal

theorem buildExclusiveOfferAutomaton_noMarkerFor
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) (name : String)
    (hElse : elseAutomaton.NoMarkerFor name)
    (hBranches : ∀ entry ∈ branchAutomata, entry.2.NoMarkerFor name) :
    (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
      branchAutomata).NoMarkerFor name := by
  classical
  intro edge hEdge
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with (((hElseEdge | hBranchEdge) | hFire) | hWait) | hElseRoot
  · exact childPendingEdges_noMarkerFor 0 elseAutomaton name hElse edge hElseEdge
  · exact indexedFragmentEdges_noMarkerFor branchAutomata name hBranches edge
      hBranchEdge
  · rw [mem_foldl_union_iff] at hFire
    rcases hFire with hEmpty | ⟨indexed, hIndexed, hMem⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hMem
      obtain ⟨environment, -, rfl⟩ := hMem
      simp
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, -, rfl⟩ := hWait
    simp
  · simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
    obtain ⟨environment, -, rfl⟩ := hElseRoot
    simp

theorem buildSelectedConjunctiveOfferAutomaton_noMarkerFor
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (name : String)
    (hElse : elseAutomaton.NoMarkerFor name)
    (hBranches : ∀ entry ∈ selectedConjunctions, entry.2.NoMarkerFor name) :
    (buildSelectedConjunctiveOfferAutomaton alphabet branches elseAutomaton
      selectedConjunctions).NoMarkerFor name := by
  classical
  intro edge hEdge
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with (((hElseEdge | hBranchEdge) | hFire) | hWait) | hElseRoot
  · exact childPendingEdges_noMarkerFor 0 elseAutomaton name hElse edge hElseEdge
  · exact indexedFragmentEdges_noMarkerFor selectedConjunctions name hBranches
      edge hBranchEdge
  · rw [mem_foldl_union_iff] at hFire
    rcases hFire with hEmpty | ⟨indexed, hIndexed, hMem⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hMem
      obtain ⟨environment, -, rfl⟩ := hMem
      simp
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, -, rfl⟩ := hWait
    simp
  · simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
    obtain ⟨environment, -, rfl⟩ := hElseRoot
    simp

/-- The binder erases its own calls and copies every other body edge, so the
result calls `name` only where the body already did. -/
theorem buildRecursionAutomaton_noMarkerFor
    (alphabet : PactTypeAlphabet) (binder name : String)
    (body : AutomatonFragment)
    (hBody : binder = name ∨ body.NoMarkerFor name) :
    (buildRecursionAutomaton alphabet binder body).NoMarkerFor name := by
  classical
  intro edge hEdge
  simp only [buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter] at hEdge
  rcases hEdge with ⟨environment, -, rfl⟩ | ⟨original, hOriginal, rfl⟩
  · simp
  · by_cases hMarker : original.label = AutomatonConstructionLabel.variable binder
    · rw [if_pos hMarker]; simp
    · rw [if_neg hMarker]
      simp only
      rcases hBody with rfl | hNoMarker
      · exact hMarker
      · exact hNoMarker original hOriginal

/-- Resolving symbolic futures leaves labels alone. -/
theorem resolveAutomatonEdgesWith_noMarkerFor
    (fragment : AutomatonFragment)
    (futureAt : TypeAutomatonState → Finset BareMessage) (name : String)
    (hFragment : fragment.NoMarkerFor name) :
    ∀ edge ∈ resolveAutomatonEdgesWith fragment futureAt,
      edge.label ≠ AutomatonConstructionLabel.variable name := by
  classical
  intro edge hEdge
  simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hEdge
  obtain ⟨original, hOriginal, rfl⟩ := hEdge
  exact hFragment original hOriginal

/-- `combine` introduces no call of its own: a combined call comes from a
component. -/
theorem AutomatonConstructionLabel.combine_eq_variable
    {interface : Interface} {left right : AutomatonConstructionLabel}
    {name : String}
    (hCombine :
      AutomatonConstructionLabel.combine interface left right = .variable name) :
    left = .variable name ∨ right = .variable name := by
  cases left <;> cases right <;>
    simp_all [AutomatonConstructionLabel.combine]

/-- A product edge calls `name` only if one of the four component fragments
does: `combine` propagates a call from either side, and every completion or
survivor family copies its component's label verbatim. -/
theorem buildParallelAutomaton_noMarkerFor
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (name : String)
    (hLeft : left.NoMarkerFor name) (hRight : right.NoMarkerFor name)
    (hRestampedLeft : restampedLeft.NoMarkerFor name)
    (hRestampedRight : restampedRight.NoMarkerFor name) :
    (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
      interface left right restampedLeft restampedRight
      leftFuture rightFuture restampedLeftFuture
      restampedRightFuture).NoMarkerFor name := by
  classical
  intro edge hEdge
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    parallelRawTransitionEdges, parallelLeftCompleteEdges,
    parallelRightCompleteEdges, parallelLeftCompleteSurvivorEdges,
    parallelRightCompleteSurvivorEdges, parallelLeftCompleteDoneEdges,
    parallelRightCompleteDoneEdges, parallelDoneEdges, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Finset.mem_inter] at hEdge
  rcases hEdge with
      ((((((⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, -⟩, rfl⟩ |
        ⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, -⟩, rfl⟩) |
        ⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, -⟩, rfl⟩) |
        ⟨rightEdge, ⟨hRightEdge, -⟩, rfl⟩) |
        ⟨leftEdge, ⟨hLeftEdge, -⟩, rfl⟩) |
        ⟨rightEdge, ⟨hRightEdge, -⟩, rfl⟩) |
        ⟨leftEdge, ⟨hLeftEdge, -⟩, rfl⟩) |
      ⟨environment, -, rfl⟩
  · intro hEq
    simp only at hEq
    rcases AutomatonConstructionLabel.combine_eq_variable hEq with hL | hR
    · exact resolveAutomatonEdgesWith_noMarkerFor left leftFuture name hLeft
        leftEdge hLeftEdge hL
    · exact resolveAutomatonEdgesWith_noMarkerFor right rightFuture name hRight
        rightEdge hRightEdge hR
  · intro hEq
    simp only at hEq
    rcases AutomatonConstructionLabel.combine_eq_variable hEq with hL | hR
    · exact resolveAutomatonEdgesWith_noMarkerFor left leftFuture name hLeft
        leftEdge hLeftEdge hL
    · exact resolveAutomatonEdgesWith_noMarkerFor right rightFuture name hRight
        rightEdge hRightEdge hR
  · intro hEq
    simp only at hEq
    rcases AutomatonConstructionLabel.combine_eq_variable hEq with hL | hR
    · exact resolveAutomatonEdgesWith_noMarkerFor left leftFuture name hLeft
        leftEdge hLeftEdge hL
    · exact resolveAutomatonEdgesWith_noMarkerFor right rightFuture name hRight
        rightEdge hRightEdge hR
  · exact resolveAutomatonEdgesWith_noMarkerFor restampedRight
      restampedRightFuture name hRestampedRight rightEdge hRightEdge
  · exact resolveAutomatonEdgesWith_noMarkerFor restampedLeft
      restampedLeftFuture name hRestampedLeft leftEdge hLeftEdge
  · exact resolveAutomatonEdgesWith_noMarkerFor restampedRight
      restampedRightFuture name hRestampedRight rightEdge hRightEdge
  · exact resolveAutomatonEdgesWith_noMarkerFor restampedLeft
      restampedLeftFuture name hRestampedLeft leftEdge hLeftEdge
  · simp

/-- A compiled fragment calls `name` only where the type does.  This is the
absence half of the recursion-marker invariant: a name that occurs nowhere in
the type sources no marker edge anywhere in its automaton. -/
theorem compileTypeFuel_noMarkerFor (name : String) :
    ∀ fuel processType,
      PactType.TailOccurrences name False processType →
      (compileTypeFuel fuel processType).NoMarkerFor name := by
  intro fuel
  induction fuel with
  | zero => intro processType _ edge hEdge; simp [compileTypeFuel] at hEdge
  | succ fuel ih =>
      intro processType hTail
      cases processType with
      | skip alphabet =>
          intro edge hEdge
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image,
            Finset.mem_filter] at hEdge
          obtain ⟨environment, -, rfl⟩ := hEdge
          simp
      | message alphabet msg dir =>
          intro edge hEdge
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with (⟨environment, -, rfl⟩ | ⟨environment, -, rfl⟩) |
            ⟨environment, -, rfl⟩ <;> simp
      | tock alphabet =>
          intro edge hEdge
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with ⟨environment, -, rfl⟩ | ⟨environment, -, rfl⟩ <;>
            (by_cases hClock : environment.clock <;> simp [hClock])
      | progress alphabet pid =>
          intro edge hEdge
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with ⟨environment, -, rfl⟩ | ⟨environment, -, rfl⟩ <;> simp
      | var alphabet other =>
          have hNe : other ≠ name := by
            intro hEq
            rw [PactType.TailOccurrences] at hTail
            exact hTail hEq
          intro edge hEdge
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image,
            Finset.mem_filter] at hEdge
          obtain ⟨environment, -, rfl⟩ := hEdge
          simpa using hNe
      | recur alphabet binder body =>
          rw [compileTypeFuel.eq_def]
          refine buildRecursionAutomaton_noMarkerFor alphabet binder name
            (compileTypeFuel fuel body) ?_
          by_cases hBinder : binder = name
          · exact Or.inl hBinder
          · refine Or.inr (ih body ?_)
            simpa [PactType.TailOccurrences, hBinder] using hTail
      | choice alphabet left right =>
          rw [PactType.TailOccurrences] at hTail
          obtain ⟨hLeft, hRight⟩ := hTail
          rw [compileTypeFuel.eq_def]
          exact buildChoiceAutomaton_noMarkerFor alphabet _ _ _ _ name
            (ih left hLeft) (ih right hRight)
      | fairChoice alphabet bid left right =>
          rw [PactType.TailOccurrences] at hTail
          obtain ⟨hLeft, hRight⟩ := hTail
          rw [compileTypeFuel.eq_def]
          exact buildChoiceAutomaton_noMarkerFor alphabet _ _ _ _ name
            (ih left hLeft) (ih right hRight)
      | seq alphabet left right =>
          rw [PactType.TailOccurrences] at hTail
          obtain ⟨hLeft, hRight⟩ := hTail
          rw [compileTypeFuel.eq_def]
          exact buildSequenceAutomaton_noMarkerFor _ _ name
            (ih left hLeft) (ih right hRight)
      | par alphabet left right interface =>
          rw [PactType.TailOccurrences] at hTail
          obtain ⟨hLeft, hRight⟩ := hTail
          rw [compileTypeFuel.eq_def]
          exact buildParallelAutomaton_noMarkerFor alphabet _ _ interface
            _ _ _ _ _ _ _ _ name
            (ih left hLeft) (ih right hRight)
            (ih _ (PactType.reannotate_tailOccurrences name left alphabet False
              hLeft))
            (ih _ (PactType.reannotate_tailOccurrences name right alphabet False
              hRight))
      | xoffer alphabet elseType branches =>
          rw [PactType.TailOccurrences] at hTail
          obtain ⟨hElse, hBranches⟩ := hTail
          have hEach : ∀ branch ∈ branches,
              PactType.TailOccurrences name False branch.2 := by
            clear hElse
            induction branches with
            | nil => intro branch hMem; simp at hMem
            | cons head rest ihRest =>
                rw [PactType.TailBranchOccurrences] at hBranches
                obtain ⟨hHead, hRest⟩ := hBranches
                intro branch hMem
                rcases List.mem_cons.mp hMem with rfl | hTail'
                · exact hHead
                · exact ihRest hRest branch hTail'
          rw [compileTypeFuel.eq_def]
          refine buildExclusiveOfferAutomaton_noMarkerFor alphabet branches _ _
            name (ih elseType hElse) ?_
          intro entry hEntry
          simp only [List.mem_map] at hEntry
          obtain ⟨branch, hBranch, rfl⟩ := hEntry
          exact ih branch.2 (hEach branch hBranch)
      | offer alphabet elseType branches =>
          rw [PactType.TailOccurrences] at hTail
          obtain ⟨hElse, hBranches⟩ := hTail
          have hEach : ∀ branch ∈ branches,
              PactType.TailOccurrences name False branch.2 := by
            clear hElse
            induction branches with
            | nil => intro branch hMem; simp at hMem
            | cons head rest ihRest =>
                rw [PactType.TailBranchOccurrences] at hBranches
                obtain ⟨hHead, hRest⟩ := hBranches
                intro branch hMem
                rcases List.mem_cons.mp hMem with rfl | hTail'
                · exact hHead
                · exact ihRest hRest branch hTail'
          rw [compileTypeFuel.eq_def]
          refine buildSelectedConjunctiveOfferAutomaton_noMarkerFor alphabet
            branches _ _ name (ih elseType hElse) ?_
          intro entry hEntry
          simp only [List.mem_map] at hEntry
          obtain ⟨selected, hSelected, rfl⟩ := hEntry
          exact ih _ (parallelTypeBranchesSelecting_tailOccurrences name alphabet
            selected branches False hEach (hEach selected hSelected))

/-- A fragment with no marker at all is vacuously inert. -/
theorem AutomatonFragment.MarkerOffersInert.of_noMarkerFor
    {fragment : AutomatonFragment} {name : String}
    (hAbsent : fragment.NoMarkerFor name) :
    fragment.MarkerOffersInert name :=
  fun edge hEdge hLabel => absurd hLabel (hAbsent edge hEdge)

theorem childPendingEdges_markerOffersInert
    (index : Nat) (fragment : AutomatonFragment) (name : String)
    (hChild : fragment.MarkerOffersInert name) :
    ∀ edge ∈ childPendingEdges index fragment,
      edge.label = AutomatonConstructionLabel.variable name →
        edge.current = ∅ ∧ ∀ offers, edge.future = .explicit offers →
          offers = ∅ := by
  classical
  intro edge hEdge hLabel
  simp only [childPendingEdges, Finset.mem_image] at hEdge
  obtain ⟨original, hOriginal, rfl⟩ := hEdge
  obtain ⟨hCurrent, hFuture⟩ := hChild original hOriginal hLabel
  refine ⟨hCurrent, ?_⟩
  intro offers hOffers
  simp only [childPendingEdge] at hOffers
  cases hSpec : original.future with
  | explicit originalOffers =>
      rw [hSpec] at hOffers
      simp only [childFutureSpec, FutureSpec.explicit.injEq] at hOffers
      exact hFuture offers (by rw [hSpec, hOffers])
  | «at» target removed =>
      rw [hSpec] at hOffers
      simp [childFutureSpec] at hOffers
  | atUnion offers target removed =>
      simp [hSpec, childFutureSpec] at hOffers

theorem indexedFragmentEdges_markerOffersInert
    (automata : List (BareMessage × AutomatonFragment)) (name : String)
    (hChildren : ∀ entry ∈ automata, entry.2.MarkerOffersInert name) :
    ∀ edge ∈ indexedFragmentEdges automata,
      edge.label = AutomatonConstructionLabel.variable name →
        edge.current = ∅ ∧ ∀ offers, edge.future = .explicit offers →
          offers = ∅ := by
  classical
  intro edge hEdge
  simp only [indexedFragmentEdges, mem_foldl_union_iff, Finset.notMem_empty,
    false_or] at hEdge
  obtain ⟨indexed, hIndexed, hMem⟩ := hEdge
  obtain ⟨entry, index⟩ := indexed
  rw [List.mk_mem_zipIdx_iff_getElem?] at hIndexed
  exact childPendingEdges_markerOffersInert (index + 1) entry.2 name
    (hChildren entry (List.mem_of_getElem? hIndexed)) edge hMem

theorem buildChoiceAutomaton_markerOffersInert
    (alphabet : PactTypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (name : String)
    (hLeft : left.MarkerOffersInert name) (hRight : right.MarkerOffersInert name) :
    (buildChoiceAutomaton alphabet left right selectionLeft
      selectionRight).MarkerOffersInert name := by
  classical
  intro edge hEdge
  simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton] at hEdge
  rcases hEdge with (hLeftEdge | hRightEdge) | hSelection
  · exact childPendingEdges_markerOffersInert 0 left name hLeft edge hLeftEdge
  · exact childPendingEdges_markerOffersInert 1 right name hRight edge hRightEdge
  · obtain ⟨environment, -, hEq⟩ := hSelection
    rcases hEq with rfl | rfl <;> (intro hLabel; simp at hLabel)

theorem buildSequenceAutomaton_markerOffersInert
    (left right : AutomatonFragment)
    {leftFuture : TypeAutomatonState → Finset BareMessage}
    {leftCompletes : TypeAutomatonState → Bool} (name : String)
    (hLeft : left.NoMarkerFor name) (hRight : right.MarkerOffersInert name) :
    (buildSequenceAutomaton left right leftFuture leftCompletes).MarkerOffersInert name := by
  classical
  intro edge hEdge hLabel
  simp only [buildSequenceAutomaton, finishAutomatonFragment, Finset.mem_union,
    sequenceLeftEdges, sequenceRightEdges, sequenceRedirectEdges,
    Finset.mem_image, Finset.mem_filter] at hEdge
  rcases hEdge with (⟨original, ⟨hOriginal, -⟩, rfl⟩ | hRightEdge) |
    ⟨original, ⟨hOriginal, -⟩, rfl⟩
  · exact absurd hLabel (hLeft original hOriginal)
  · exact childPendingEdges_markerOffersInert 1 right name hRight edge hRightEdge
      hLabel
  · exact absurd hLabel (hLeft original hOriginal)

theorem buildExclusiveOfferAutomaton_markerOffersInert
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) (name : String)
    (hElse : elseAutomaton.MarkerOffersInert name)
    (hBranches : ∀ entry ∈ branchAutomata, entry.2.MarkerOffersInert name) :
    (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
      branchAutomata).MarkerOffersInert name := by
  classical
  intro edge hEdge
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with (((hElseEdge | hBranchEdge) | hFire) | hWait) | hElseRoot
  · exact childPendingEdges_markerOffersInert 0 elseAutomaton name hElse edge
      hElseEdge
  · exact indexedFragmentEdges_markerOffersInert branchAutomata name hBranches
      edge hBranchEdge
  · rw [mem_foldl_union_iff] at hFire
    rcases hFire with hEmpty | ⟨indexed, hIndexed, hMem⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hMem
      obtain ⟨environment, -, rfl⟩ := hMem
      intro hLabel; simp at hLabel
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, -, rfl⟩ := hWait
    intro hLabel; simp at hLabel
  · simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
    obtain ⟨environment, -, rfl⟩ := hElseRoot
    intro hLabel; simp at hLabel

theorem buildRecursionAutomaton_markerOffersInert
    (alphabet : PactTypeAlphabet) (binder name : String)
    (body : AutomatonFragment)
    (hBody : binder = name ∨ body.MarkerOffersInert name) :
    (buildRecursionAutomaton alphabet binder body).MarkerOffersInert name := by
  classical
  intro edge hEdge hLabel
  simp only [buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter] at hEdge
  rcases hEdge with ⟨environment, -, rfl⟩ | ⟨original, hOriginal, rfl⟩
  · simp at hLabel
  · by_cases hMarker : original.label = AutomatonConstructionLabel.variable binder
    · rw [if_pos hMarker] at hLabel; simp at hLabel
    · rw [if_neg hMarker] at hLabel ⊢
      simp only at hLabel ⊢
      rcases hBody with rfl | hInert
      · exact absurd hLabel hMarker
      · obtain ⟨hCurrent, hFuture⟩ := hInert original hOriginal hLabel
        refine ⟨hCurrent, ?_⟩
        intro offers hOffers
        cases hSpec : original.future with
        | explicit originalOffers =>
            rw [hSpec] at hOffers
            simp only [childFutureSpec, FutureSpec.explicit.injEq] at hOffers
            exact hFuture offers (by rw [hSpec, hOffers])
        | «at» target removed =>
            rw [hSpec] at hOffers
            simp [childFutureSpec] at hOffers
        | atUnion offers target removed =>
            simp [hSpec, childFutureSpec] at hOffers

theorem buildSelectedConjunctiveOfferAutomaton_markerOffersInert
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (name : String)
    (hElse : elseAutomaton.MarkerOffersInert name)
    (hBranches : ∀ entry ∈ selectedConjunctions, entry.2.MarkerOffersInert name) :
    (buildSelectedConjunctiveOfferAutomaton alphabet branches elseAutomaton
      selectedConjunctions).MarkerOffersInert name := by
  classical
  intro edge hEdge
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with (((hElseEdge | hBranchEdge) | hFire) | hWait) | hElseRoot
  · exact childPendingEdges_markerOffersInert 0 elseAutomaton name hElse edge
      hElseEdge
  · exact indexedFragmentEdges_markerOffersInert selectedConjunctions name
      hBranches edge hBranchEdge
  · rw [mem_foldl_union_iff] at hFire
    rcases hFire with hEmpty | ⟨indexed, hIndexed, hMem⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hMem
      obtain ⟨environment, -, rfl⟩ := hMem
      intro hLabel; simp at hLabel
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, -, rfl⟩ := hWait
    intro hLabel; simp at hLabel
  · simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
    obtain ⟨environment, -, rfl⟩ := hElseRoot
    intro hLabel; simp at hLabel

/-- Compiled marker edges are offer-inert.  `TailOccurrences name True` is the
paper's tail-recursion side condition: it puts every call of `name` where a
marker is allowed to appear, and rules calls out of the positions — a sequence's
left operand, either side of a parallel, a conjunctive branch — whose compilers
would fuse a marker with an offer-carrying edge. -/
theorem compileTypeFuel_markerOffersInert (name : String) :
    ∀ fuel processType,
      PactType.TailOccurrences name True processType →
      (compileTypeFuel fuel processType).MarkerOffersInert name := by
  intro fuel
  induction fuel with
  | zero => intro processType _ edge hEdge; simp [compileTypeFuel] at hEdge
  | succ fuel ih =>
      intro processType hTail
      cases processType with
      | skip alphabet =>
          exact AutomatonFragment.MarkerOffersInert.of_noMarkerFor
            (compileTypeFuel_noMarkerFor name (fuel + 1) _
              (by rw [PactType.TailOccurrences]; trivial))
      | message alphabet msg dir =>
          exact AutomatonFragment.MarkerOffersInert.of_noMarkerFor
            (compileTypeFuel_noMarkerFor name (fuel + 1) _
              (by rw [PactType.TailOccurrences]; trivial))
      | tock alphabet =>
          exact AutomatonFragment.MarkerOffersInert.of_noMarkerFor
            (compileTypeFuel_noMarkerFor name (fuel + 1) _
              (by rw [PactType.TailOccurrences]; trivial))
      | progress alphabet pid =>
          exact AutomatonFragment.MarkerOffersInert.of_noMarkerFor
            (compileTypeFuel_noMarkerFor name (fuel + 1) _
              (by rw [PactType.TailOccurrences]; trivial))
      | var alphabet other =>
          intro edge hEdge hLabel
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image,
            Finset.mem_filter] at hEdge
          obtain ⟨environment, -, rfl⟩ := hEdge
          exact ⟨rfl, by intro offers hOffers; simp at hOffers⟩
      | recur alphabet binder body =>
          rw [compileTypeFuel.eq_def]
          refine buildRecursionAutomaton_markerOffersInert alphabet binder name
            (compileTypeFuel fuel body) ?_
          by_cases hBinder : binder = name
          · exact Or.inl hBinder
          · refine Or.inr (ih body ?_)
            rw [PactType.TailOccurrences] at hTail
            simpa [hBinder] using hTail
      | choice alphabet left right =>
          rw [PactType.TailOccurrences] at hTail
          rw [compileTypeFuel.eq_def]
          exact buildChoiceAutomaton_markerOffersInert alphabet _ _ _ _ name
            (ih left hTail.1) (ih right hTail.2)
      | fairChoice alphabet bid left right =>
          rw [PactType.TailOccurrences] at hTail
          rw [compileTypeFuel.eq_def]
          exact buildChoiceAutomaton_markerOffersInert alphabet _ _ _ _ name
            (ih left hTail.1) (ih right hTail.2)
      | seq alphabet left right =>
          rw [PactType.TailOccurrences] at hTail
          rw [compileTypeFuel.eq_def]
          exact buildSequenceAutomaton_markerOffersInert _ _ name
            (compileTypeFuel_noMarkerFor name fuel left hTail.1)
            (ih right hTail.2)
      | par alphabet left right interface =>
          rw [PactType.TailOccurrences] at hTail
          refine AutomatonFragment.MarkerOffersInert.of_noMarkerFor ?_
          exact compileTypeFuel_noMarkerFor name (fuel + 1) _
            (by rw [PactType.TailOccurrences]; exact hTail)
      | xoffer alphabet elseType branches =>
          rw [PactType.TailOccurrences] at hTail
          obtain ⟨hElse, hBranches⟩ := hTail
          have hEach : ∀ branch ∈ branches,
              PactType.TailOccurrences name True branch.2 := by
            clear hElse
            induction branches with
            | nil => intro branch hMem; simp at hMem
            | cons head rest ihRest =>
                rw [PactType.TailBranchOccurrences] at hBranches
                obtain ⟨hHead, hRest⟩ := hBranches
                intro branch hMem
                rcases List.mem_cons.mp hMem with rfl | hTail'
                · exact hHead
                · exact ihRest hRest branch hTail'
          rw [compileTypeFuel.eq_def]
          refine buildExclusiveOfferAutomaton_markerOffersInert alphabet branches
            _ _ name (ih elseType hElse) ?_
          intro entry hEntry
          simp only [List.mem_map] at hEntry
          obtain ⟨branch, hBranch, rfl⟩ := hEntry
          exact ih branch.2 (hEach branch hBranch)
      | offer alphabet elseType branches =>
          rw [PactType.TailOccurrences] at hTail
          obtain ⟨hElse, hBranches⟩ := hTail
          have hEach : ∀ branch ∈ branches,
              PactType.TailOccurrences name False branch.2 := by
            clear hElse
            induction branches with
            | nil => intro branch hMem; simp at hMem
            | cons head rest ihRest =>
                rw [PactType.TailBranchOccurrences] at hBranches
                obtain ⟨hHead, hRest⟩ := hBranches
                intro branch hMem
                rcases List.mem_cons.mp hMem with rfl | hTail'
                · exact hHead
                · exact ihRest hRest branch hTail'
          rw [compileTypeFuel.eq_def]
          refine buildSelectedConjunctiveOfferAutomaton_markerOffersInert
            alphabet branches _ _ name (ih elseType hElse) ?_
          intro entry hEntry
          simp only [List.mem_map] at hEntry
          obtain ⟨selected, hSelected, rfl⟩ := hEntry
          refine AutomatonFragment.MarkerOffersInert.of_noMarkerFor
            (compileTypeFuel_noMarkerFor name fuel _ ?_)
          exact parallelTypeBranchesSelecting_tailOccurrences name alphabet
            selected branches False hEach (hEach selected hSelected)

/-! ### Marker sources travel with the child tag -/

theorem childPendingEdges_markerSource
    (index : Nat) (fragment : AutomatonFragment) (name : String)
    (q : TypeAutomatonState) :
    (∃ edge ∈ childPendingEdges index fragment,
        edge.source = childState index q ∧
        edge.label = AutomatonConstructionLabel.variable name) ↔
      MarkerSource fragment name q := by
  classical
  constructor
  · rintro ⟨edge, hEdge, hSource, hLabel⟩
    simp only [childPendingEdges, Finset.mem_image] at hEdge
    obtain ⟨original, hOriginal, rfl⟩ := hEdge
    refine ⟨original, hOriginal, ?_, hLabel⟩
    simpa [childPendingEdge, childState] using hSource
  · rintro ⟨original, hOriginal, hSource, hLabel⟩
    exact ⟨childPendingEdge index original,
      Finset.mem_image_of_mem _ hOriginal,
      by simp [childPendingEdge, childState, hSource], hLabel⟩

theorem buildChoiceAutomaton_markerSource_child0
    (alphabet : PactTypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (name : String)
    (q : TypeAutomatonState) :
    MarkerSource (buildChoiceAutomaton alphabet left right selectionLeft
        selectionRight) name (childState 0 q) ↔
      MarkerSource left name q := by
  classical
  constructor
  · rintro ⟨edge, hEdge, hSource, hLabel⟩
    simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton] at hEdge
    rcases hEdge with (hLeftEdge | hRightEdge) | hSelection
    · exact (childPendingEdges_markerSource 0 left name q).mp
        ⟨edge, hLeftEdge, hSource, hLabel⟩
    · exfalso
      simp only [childPendingEdges, Finset.mem_image] at hRightEdge
      obtain ⟨original, -, rfl⟩ := hRightEdge
      simp [childPendingEdge, childState] at hSource
    · obtain ⟨environment, -, hEq⟩ := hSelection
      rcases hEq with rfl | rfl <;> simp at hLabel
  · intro hChild
    obtain ⟨edge, hEdge, hSource, hLabel⟩ :=
      (childPendingEdges_markerSource 0 left name q).mpr hChild
    refine ⟨edge, ?_, hSource, hLabel⟩
    simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union]
    exact Or.inl (Or.inl hEdge)

theorem buildChoiceAutomaton_markerSource_child1
    (alphabet : PactTypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (name : String)
    (q : TypeAutomatonState) :
    MarkerSource (buildChoiceAutomaton alphabet left right selectionLeft
        selectionRight) name (childState 1 q) ↔
      MarkerSource right name q := by
  classical
  constructor
  · rintro ⟨edge, hEdge, hSource, hLabel⟩
    simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton] at hEdge
    rcases hEdge with (hLeftEdge | hRightEdge) | hSelection
    · exfalso
      simp only [childPendingEdges, Finset.mem_image] at hLeftEdge
      obtain ⟨original, -, rfl⟩ := hLeftEdge
      simp [childPendingEdge, childState] at hSource
    · exact (childPendingEdges_markerSource 1 right name q).mp
        ⟨edge, hRightEdge, hSource, hLabel⟩
    · obtain ⟨environment, -, hEq⟩ := hSelection
      rcases hEq with rfl | rfl <;> simp at hLabel
  · intro hChild
    obtain ⟨edge, hEdge, hSource, hLabel⟩ :=
      (childPendingEdges_markerSource 1 right name q).mpr hChild
    refine ⟨edge, ?_, hSource, hLabel⟩
    simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union]
    exact Or.inl (Or.inr hEdge)

theorem buildChoiceAutomaton_markerSource_root
    (alphabet : PactTypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (name : String) :
    ¬ MarkerSource (buildChoiceAutomaton alphabet left right selectionLeft
      selectionRight) name TypeAutomatonState.root := by
  classical
  rintro ⟨edge, hEdge, hSource, hLabel⟩
  simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton] at hEdge
  rcases hEdge with (hLeftEdge | hRightEdge) | hSelection
  · simp only [childPendingEdges, Finset.mem_image] at hLeftEdge
    obtain ⟨original, -, rfl⟩ := hLeftEdge
    simp [childPendingEdge, childState] at hSource
  · simp only [childPendingEdges, Finset.mem_image] at hRightEdge
    obtain ⟨original, -, rfl⟩ := hRightEdge
    simp [childPendingEdge, childState] at hSource
  · obtain ⟨environment, -, hEq⟩ := hSelection
    rcases hEq with rfl | rfl <;> simp at hLabel

theorem indexedFragmentEdges_markerSource
    (automata : List (BareMessage × AutomatonFragment)) (name : String)
    (i : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : automata[i]? = some entry) (q : TypeAutomatonState) :
    (∃ edge ∈ indexedFragmentEdges automata,
        edge.source = childState (i + 1) q ∧
        edge.label = AutomatonConstructionLabel.variable name) ↔
      MarkerSource entry.2 name q := by
  classical
  constructor
  · rintro ⟨edge, hEdge, hSource, hLabel⟩
    simp only [indexedFragmentEdges, mem_foldl_union_iff, Finset.notMem_empty,
      false_or] at hEdge
    obtain ⟨indexed, hIndexed, hMem⟩ := hEdge
    obtain ⟨other, j⟩ := indexed
    rw [List.mk_mem_zipIdx_iff_getElem?] at hIndexed
    simp only [childPendingEdges, Finset.mem_image] at hMem
    obtain ⟨original, hOriginal, rfl⟩ := hMem
    have hIndexEq : j = i := by
      have := hSource
      simp only [childPendingEdge, childState] at this
      exact (by injection this with h _; omega)
    subst hIndexEq
    have hOther : other = entry := by
      rw [hIndexed] at hEntry; exact Option.some.inj hEntry
    subst hOther
    refine ⟨original, hOriginal, ?_, hLabel⟩
    simpa [childPendingEdge, childState] using hSource
  · rintro ⟨original, hOriginal, hSource, hLabel⟩
    refine ⟨childPendingEdge (i + 1) original, ?_, ?_, hLabel⟩
    · simp only [indexedFragmentEdges, mem_foldl_union_iff]
      refine Or.inr ⟨(entry, i), ?_, ?_⟩
      · rw [List.mk_mem_zipIdx_iff_getElem?]; exact hEntry
      · exact Finset.mem_image_of_mem _ hOriginal
    · simp [childPendingEdge, childState, hSource]

theorem buildSequenceAutomaton_markerSource_child0
    (left right : AutomatonFragment)
    {leftFuture : TypeAutomatonState → Finset BareMessage}
    {leftCompletes : TypeAutomatonState → Bool} (name : String) (q : TypeAutomatonState)
    (hMarker : MarkerSource (buildSequenceAutomaton left right leftFuture leftCompletes) name
      (childState 0 q)) :
    MarkerSource left name q := by
  classical
  obtain ⟨edge, hEdge, hSource, hLabel⟩ := hMarker
  simp only [buildSequenceAutomaton, finishAutomatonFragment, Finset.mem_union,
    sequenceLeftEdges, sequenceRightEdges, sequenceRedirectEdges,
    Finset.mem_image, Finset.mem_filter] at hEdge
  rcases hEdge with (⟨original, ⟨hOriginal, -⟩, rfl⟩ | hRightEdge) |
    ⟨original, ⟨hOriginal, -⟩, rfl⟩
  · exact ⟨original, hOriginal, by simpa [sequenceKeptLeftEdge, childState]
      using hSource, hLabel⟩
  · exfalso
    simp only [childPendingEdges, Finset.mem_image] at hRightEdge
    obtain ⟨original, -, rfl⟩ := hRightEdge
    simp [childPendingEdge, childState] at hSource
  · exact ⟨original, hOriginal, by simpa [sequenceRedirectEdge, childState]
      using hSource, hLabel⟩

theorem buildSequenceAutomaton_markerSource_child1
    (left right : AutomatonFragment)
    {leftFuture : TypeAutomatonState → Finset BareMessage}
    {leftCompletes : TypeAutomatonState → Bool} (name : String) (q : TypeAutomatonState) :
    MarkerSource (buildSequenceAutomaton left right leftFuture leftCompletes) name (childState 1 q) ↔
      MarkerSource right name q := by
  classical
  constructor
  · rintro ⟨edge, hEdge, hSource, hLabel⟩
    simp only [buildSequenceAutomaton, finishAutomatonFragment,
      Finset.mem_union, sequenceLeftEdges, sequenceRightEdges,
      sequenceRedirectEdges, Finset.mem_image, Finset.mem_filter] at hEdge
    rcases hEdge with (⟨original, -, rfl⟩ | hRightEdge) | ⟨original, -, rfl⟩
    · exact absurd hSource (by simp [sequenceKeptLeftEdge, childState])
    · exact (childPendingEdges_markerSource 1 right name q).mp
        ⟨edge, hRightEdge, hSource, hLabel⟩
    · exact absurd hSource (by simp [sequenceRedirectEdge, childState])
  · intro hChild
    obtain ⟨edge, hEdge, hSource, hLabel⟩ :=
      (childPendingEdges_markerSource 1 right name q).mpr hChild
    refine ⟨edge, ?_, hSource, hLabel⟩
    simp only [buildSequenceAutomaton, finishAutomatonFragment,
      Finset.mem_union, sequenceRightEdges]
    exact Or.inl (Or.inr hEdge)

theorem buildExclusiveOfferAutomaton_markerSource_child0
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) (name : String)
    (q : TypeAutomatonState) :
    MarkerSource (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
        branchAutomata) name (childState 0 q) ↔
      MarkerSource elseAutomaton name q := by
  classical
  constructor
  · rintro ⟨edge, hEdge, hSource, hLabel⟩
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge
    rcases hEdge with (((hElse | hBranch) | hFire) | hWait) | hElseRoot
    · exact (childPendingEdges_markerSource 0 elseAutomaton name q).mp
        ⟨edge, hElse, hSource, hLabel⟩
    · exfalso
      simp only [indexedFragmentEdges, mem_foldl_union_iff,
        Finset.notMem_empty, false_or] at hBranch
      obtain ⟨indexed, -, hMem⟩ := hBranch
      simp only [childPendingEdges, Finset.mem_image] at hMem
      obtain ⟨original, -, rfl⟩ := hMem
      simp [childPendingEdge, childState] at hSource
    · exfalso
      rw [mem_foldl_union_iff] at hFire
      rcases hFire with hEmpty | ⟨indexed, hIndexed, hMem⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hMem
        obtain ⟨environment, -, rfl⟩ := hMem
        simp at hLabel
    · exfalso
      simp only [Finset.mem_image, Finset.mem_filter] at hWait
      obtain ⟨environment, -, rfl⟩ := hWait
      simp at hLabel
    · exfalso
      simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
      obtain ⟨environment, -, rfl⟩ := hElseRoot
      simp at hLabel
  · intro hChild
    obtain ⟨edge, hEdge, hSource, hLabel⟩ :=
      (childPendingEdges_markerSource 0 elseAutomaton name q).mpr hChild
    refine ⟨edge, ?_, hSource, hLabel⟩
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl hEdge)))

theorem buildExclusiveOfferAutomaton_markerSource_branch
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) (name : String)
    (i : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : branchAutomata[i]? = some entry) (q : TypeAutomatonState) :
    MarkerSource (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
        branchAutomata) name (childState (i + 1) q) ↔
      MarkerSource entry.2 name q := by
  classical
  constructor
  · rintro ⟨edge, hEdge, hSource, hLabel⟩
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge
    rcases hEdge with (((hElse | hBranch) | hFire) | hWait) | hElseRoot
    · exfalso
      simp only [childPendingEdges, Finset.mem_image] at hElse
      obtain ⟨original, -, rfl⟩ := hElse
      simp [childPendingEdge, childState] at hSource
    · exact (indexedFragmentEdges_markerSource branchAutomata name i entry
        hEntry q).mp ⟨edge, hBranch, hSource, hLabel⟩
    · exfalso
      rw [mem_foldl_union_iff] at hFire
      rcases hFire with hEmpty | ⟨indexed, hIndexed, hMem⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hMem
        obtain ⟨environment, -, rfl⟩ := hMem
        simp at hLabel
    · exfalso
      simp only [Finset.mem_image, Finset.mem_filter] at hWait
      obtain ⟨environment, -, rfl⟩ := hWait
      simp at hLabel
    · exfalso
      simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
      obtain ⟨environment, -, rfl⟩ := hElseRoot
      simp at hLabel
  · intro hChild
    obtain ⟨edge, hEdge, hSource, hLabel⟩ :=
      (indexedFragmentEdges_markerSource branchAutomata name i entry hEntry q).mpr
        hChild
    refine ⟨edge, ?_, hSource, hLabel⟩
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inr hEdge)))

theorem buildExclusiveOfferAutomaton_markerSource_root
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) (name : String) :
    ¬ MarkerSource (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
      branchAutomata) name TypeAutomatonState.root := by
  classical
  rintro ⟨edge, hEdge, hSource, hLabel⟩
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with (((hElse | hBranch) | hFire) | hWait) | hElseRoot
  · simp only [childPendingEdges, Finset.mem_image] at hElse
    obtain ⟨original, -, rfl⟩ := hElse
    simp [childPendingEdge, childState] at hSource
  · simp only [indexedFragmentEdges, mem_foldl_union_iff,
      Finset.notMem_empty, false_or] at hBranch
    obtain ⟨indexed, -, hMem⟩ := hBranch
    simp only [childPendingEdges, Finset.mem_image] at hMem
    obtain ⟨original, -, rfl⟩ := hMem
    simp [childPendingEdge, childState] at hSource
  · rw [mem_foldl_union_iff] at hFire
    rcases hFire with hEmpty | ⟨indexed, hIndexed, hMem⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hMem
      obtain ⟨environment, -, rfl⟩ := hMem
      simp at hLabel
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, -, rfl⟩ := hWait
    simp at hLabel
  · simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
    obtain ⟨environment, -, rfl⟩ := hElseRoot
    simp at hLabel

theorem buildSelectedConjunctiveOfferAutomaton_markerSource_child0
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment)) (name : String)
    (q : TypeAutomatonState) :
    MarkerSource (buildSelectedConjunctiveOfferAutomaton alphabet branches elseAutomaton
        selectedConjunctions) name (childState 0 q) ↔
      MarkerSource elseAutomaton name q := by
  classical
  constructor
  · rintro ⟨edge, hEdge, hSource, hLabel⟩
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge
    rcases hEdge with (((hElse | hBranch) | hFire) | hWait) | hElseRoot
    · exact (childPendingEdges_markerSource 0 elseAutomaton name q).mp
        ⟨edge, hElse, hSource, hLabel⟩
    · exfalso
      simp only [indexedFragmentEdges, mem_foldl_union_iff,
        Finset.notMem_empty, false_or] at hBranch
      obtain ⟨indexed, -, hMem⟩ := hBranch
      simp only [childPendingEdges, Finset.mem_image] at hMem
      obtain ⟨original, -, rfl⟩ := hMem
      simp [childPendingEdge, childState] at hSource
    · exfalso
      rw [mem_foldl_union_iff] at hFire
      rcases hFire with hEmpty | ⟨indexed, hIndexed, hMem⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hMem
        obtain ⟨environment, -, rfl⟩ := hMem
        simp at hLabel
    · exfalso
      simp only [Finset.mem_image, Finset.mem_filter] at hWait
      obtain ⟨environment, -, rfl⟩ := hWait
      simp at hLabel
    · exfalso
      simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
      obtain ⟨environment, -, rfl⟩ := hElseRoot
      simp at hLabel
  · intro hChild
    obtain ⟨edge, hEdge, hSource, hLabel⟩ :=
      (childPendingEdges_markerSource 0 elseAutomaton name q).mpr hChild
    refine ⟨edge, ?_, hSource, hLabel⟩
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl hEdge)))

theorem buildSelectedConjunctiveOfferAutomaton_markerSource_branch
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment)) (name : String)
    (i : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : selectedConjunctions[i]? = some entry) (q : TypeAutomatonState) :
    MarkerSource (buildSelectedConjunctiveOfferAutomaton alphabet branches elseAutomaton
        selectedConjunctions) name (childState (i + 1) q) ↔
      MarkerSource entry.2 name q := by
  classical
  constructor
  · rintro ⟨edge, hEdge, hSource, hLabel⟩
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge
    rcases hEdge with (((hElse | hBranch) | hFire) | hWait) | hElseRoot
    · exfalso
      simp only [childPendingEdges, Finset.mem_image] at hElse
      obtain ⟨original, -, rfl⟩ := hElse
      simp [childPendingEdge, childState] at hSource
    · exact (indexedFragmentEdges_markerSource selectedConjunctions name i entry
        hEntry q).mp ⟨edge, hBranch, hSource, hLabel⟩
    · exfalso
      rw [mem_foldl_union_iff] at hFire
      rcases hFire with hEmpty | ⟨indexed, hIndexed, hMem⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hMem
        obtain ⟨environment, -, rfl⟩ := hMem
        simp at hLabel
    · exfalso
      simp only [Finset.mem_image, Finset.mem_filter] at hWait
      obtain ⟨environment, -, rfl⟩ := hWait
      simp at hLabel
    · exfalso
      simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
      obtain ⟨environment, -, rfl⟩ := hElseRoot
      simp at hLabel
  · intro hChild
    obtain ⟨edge, hEdge, hSource, hLabel⟩ :=
      (indexedFragmentEdges_markerSource selectedConjunctions name i entry hEntry q).mpr
        hChild
    refine ⟨edge, ?_, hSource, hLabel⟩
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inr hEdge)))

theorem buildSelectedConjunctiveOfferAutomaton_markerSource_root
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment)) (name : String) :
    ¬ MarkerSource (buildSelectedConjunctiveOfferAutomaton alphabet branches elseAutomaton
      selectedConjunctions) name TypeAutomatonState.root := by
  classical
  rintro ⟨edge, hEdge, hSource, hLabel⟩
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with (((hElse | hBranch) | hFire) | hWait) | hElseRoot
  · simp only [childPendingEdges, Finset.mem_image] at hElse
    obtain ⟨original, -, rfl⟩ := hElse
    simp [childPendingEdge, childState] at hSource
  · simp only [indexedFragmentEdges, mem_foldl_union_iff,
      Finset.notMem_empty, false_or] at hBranch
    obtain ⟨indexed, -, hMem⟩ := hBranch
    simp only [childPendingEdges, Finset.mem_image] at hMem
    obtain ⟨original, -, rfl⟩ := hMem
    simp [childPendingEdge, childState] at hSource
  · rw [mem_foldl_union_iff] at hFire
    rcases hFire with hEmpty | ⟨indexed, hIndexed, hMem⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hMem
      obtain ⟨environment, -, rfl⟩ := hMem
      simp at hLabel
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, -, rfl⟩ := hWait
    simp at hLabel
  · simp only [Finset.mem_image, Finset.mem_filter] at hElseRoot
    obtain ⟨environment, -, rfl⟩ := hElseRoot
    simp at hLabel

/-- The branch-list form of `TailOccurrences` is a statement about every
branch body. -/
theorem tailBranchOccurrences_forall (name : String) (tail : Prop) :
    ∀ branches : List (BareMessage × PactType),
      PactType.TailBranchOccurrences name tail branches →
      ∀ branch ∈ branches, PactType.TailOccurrences name tail branch.2
  | [], _, branch, hMem => by simp at hMem
  | head :: rest, hBranches, branch, hMem => by
      rw [PactType.TailBranchOccurrences] at hBranches
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact hBranches.1
      · exact tailBranchOccurrences_forall name tail rest hBranches.2 branch
          hRest

/-! ### Marker edges keep their child's target under the child tag -/

end


end Pact
