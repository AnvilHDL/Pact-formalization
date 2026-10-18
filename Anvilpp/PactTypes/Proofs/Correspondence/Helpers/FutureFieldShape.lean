import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.MenuLinkCompletion

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-- A copied sequence field retains its stored operand and tags its menu reference. -/
theorem childFutureSpec_atUnion (index : Nat) (spec : FutureSpec)
    (stored removed : Finset BareMessage) (reference : TypeAutomatonState)
    (hSpec : childFutureSpec index spec = .atUnion stored reference removed) :
    ∃ child, spec = .atUnion stored child removed ∧ reference = .child index child := by
  cases spec with
  | explicit offers | «at» target mask => simp [childFutureSpec] at hSpec
  | atUnion offers target mask =>
    simp only [childFutureSpec, FutureSpec.atUnion.injEq] at hSpec
    obtain ⟨rfl, rfl, rfl⟩ := hSpec
    exact ⟨target, rfl, rfl⟩

private def SequenceFieldRepresented
    (relation : Finset (PactType × TypeAutomatonState))
    (edge : PendingAutomatonEdge) : Prop :=
  ∀ stored reference removed, edge.future = .atUnion stored reference removed →
    edge.label.semantic ≠ .tock ∧ removed = edge.current ∧ ∃ alphabet left right,
      (.seq alphabet left right, edge.source) ∈ relation ∧
      (right, reference) ∈ relation ∧ left.CanCompleteDeclared = true

private theorem sequenceFieldRepresented_child
    (relation childRelation : Finset (PactType × TypeAutomatonState))
    (index : Nat) (edge : PendingAutomatonEdge)
    (hEdge : SequenceFieldRepresented childRelation edge)
    (hLift : ∀ rho q, (rho, q) ∈ childRelation →
      (rho, TypeAutomatonState.child index q) ∈ relation) :
    SequenceFieldRepresented relation (childPendingEdge index edge) := by
  intro stored reference removed hFuture
  obtain ⟨child, hField, rfl⟩ := childFutureSpec_atUnion index edge.future
    stored removed reference hFuture
  obtain ⟨hNonClock, hRemoved, alphabet, left, right, hSource, hRight, hComplete⟩ :=
    hEdge stored child removed hField
  exact ⟨hNonClock, hRemoved, alphabet, left, right, hLift _ _ hSource,
    hLift _ _ hRight, hComplete⟩

private theorem compileTypeFuel_sequenceFieldRepresented :
    ∀ fuel ty, typeCompilationFuel ty ≤ fuel →
      ∀ edge ∈ (compileTypeFuel fuel ty).edges,
        SequenceFieldRepresented (buildRelationSetCoreFuel fuel ty) edge := by
  intro fuel
  induction fuel with
  | zero => intro ty _ edge hEdge; simp [compileTypeFuel] at hEdge
  | succ fuel ih =>
    intro ty hFuel edge hEdge
    have hCopy (child : PactType) (index : Nat)
        (hChildFuel : typeCompilationFuel child ≤ fuel)
        (hLift : ∀ rho q, (rho, q) ∈ buildRelationSetCoreFuel fuel child →
          (rho, TypeAutomatonState.child index q) ∈ buildRelationSetCoreFuel (fuel + 1) ty)
        (hCopied : edge ∈ childPendingEdges index (compileTypeFuel fuel child)) :
        SequenceFieldRepresented (buildRelationSetCoreFuel (fuel + 1) ty) edge := by
      obtain ⟨childEdge, hChild, rfl⟩ := Finset.mem_image.mp hCopied
      exact sequenceFieldRepresented_child _ _ index childEdge
        (ih child hChildFuel childEdge hChild) hLift
    cases ty with
    | skip a | var a name =>
      intro stored reference removed hFuture
      simp only [compileTypeFuel, finishAutomatonFragment,
        Finset.mem_image, Finset.mem_filter] at hEdge
      obtain ⟨env, _, rfl⟩ := hEdge
      simp at hFuture
    | message a msg dir =>
      intro stored reference removed hFuture
      simp only [compileTypeFuel, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with (⟨env, _, rfl⟩ | ⟨env, _, rfl⟩) | ⟨env, _, rfl⟩ <;>
        simp at hFuture
    | progress a pid =>
      intro stored reference removed hFuture
      simp only [compileTypeFuel, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with ⟨env, _, rfl⟩ | ⟨env, _, rfl⟩ <;> simp at hFuture
    | tock a =>
      intro stored reference removed hFuture
      simp only [compileTypeFuel, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with ⟨env, _, rfl⟩ | ⟨env, _, rfl⟩
      · split at hFuture <;> simp_all
      · simp at hFuture
    | choice a left right | fairChoice a bid left right =>
      have hLeft : typeCompilationFuel left ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      have hRight : typeCompilationFuel right ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      simp only [compileTypeFuel, buildChoiceAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with (hLeftEdge | hRightEdge) | hRoot
      · exact hCopy left 0 hLeft (by
          intro rho q hRelated
          simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          exact Or.inr (Or.inl ⟨(rho, q), hRelated, rfl⟩)) hLeftEdge
      · exact hCopy right 1 hRight (by
          intro rho q hRelated
          simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          exact Or.inr (Or.inr ⟨(rho, q), hRelated, rfl⟩)) hRightEdge
      · intro stored reference removed hFuture
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton] at hRoot
        obtain ⟨env, _, hCase⟩ := hRoot
        rcases hCase with rfl | rfl <;> simp at hFuture
    | recur a name body =>
      have hBody : typeCompilationFuel body ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      intro stored reference removed hFuture
      simp only [compileTypeFuel, buildRecursionAutomaton, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image] at hEdge
      rcases hEdge with ⟨env, _, rfl⟩ | ⟨child, hChild, rfl⟩
      · simp at hFuture
      · by_cases hMarker : child.label = .variable name
        · simp [hMarker] at hFuture
        · simp only [if_neg hMarker] at hFuture ⊢
          obtain ⟨q, hField, rfl⟩ := childFutureSpec_atUnion 0 child.future
            stored removed reference hFuture
          obtain ⟨hNonClock, hRemoved, alphabet, left, right, hSource, hRight, hComplete⟩ :=
            ih body hBody child hChild stored q removed hField
          refine ⟨hNonClock, hRemoved, alphabet, left.replaceVar name (.recur a name body),
            right.replaceVar name (.recur a name body), ?_, ?_,
            PactType.canCompleteDeclared_replaceVar_of_complete _ _ left hComplete⟩
          · rw [buildRelationSetCoreFuel]
            exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
              ⟨(.seq alphabet left right, child.source), hSource, by simp [PactType.replaceVar, childState]⟩)
          · rw [buildRelationSetCoreFuel]
            exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(right, q), hRight, rfl⟩)
    | seq a left right =>
      have hLeft : typeCompilationFuel left ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      have hRight : typeCompilationFuel right ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      have hLeftField (child : PendingAutomatonEdge)
          (hKeep : child.source ∉ sequenceDeleted (compileTypeFuel fuel left))
          (stored : Finset BareMessage) (reference : TypeAutomatonState)
          (removed : Finset BareMessage)
          (hField : sequenceLeftFutureSpec child.label
            (childState 1 (compileTypeFuel fuel right).initial)
            (resolveFutureSpec (computeFutureOfFuel (min fuel (typeCompilationFuel left)) left)
              child.future) child.current
            (decide (∃ entry ∈ buildRelationSetCoreFuel (min fuel (typeCompilationFuel left)) left,
              entry.2 = child.source ∧
                typeCanCompleteThisCycleFuel (sizeOf entry.1 + 1) entry.1 = true)) =
              .atUnion stored reference removed) :
          child.label.semantic ≠ .tock ∧ removed = child.current ∧ ∃ alphabet l r,
            (.seq alphabet l r, TypeAutomatonState.child 0 child.source) ∈
              buildRelationSetCoreFuel (fuel + 1) (.seq a left right) ∧
            (r, reference) ∈ buildRelationSetCoreFuel (fuel + 1) (.seq a left right) ∧
            l.CanCompleteDeclared = true := by
        simp only [sequenceLeftFutureSpec] at hField
        split_ifs at hField with hClock hComplete
        obtain ⟨_, rfl, rfl⟩ := hField
        obtain ⟨entry, hEntry, hSource, hFlag⟩ := of_decide_eq_true hComplete
        rw [Nat.min_eq_right hLeft] at hEntry
        rw [← buildRelationSetCoreFuel_eq_of_sufficient left hLeft le_rfl] at hEntry
        refine ⟨hClock, rfl, a, entry.1, right, ?_, ?_, ?_⟩
        · rw [buildRelationSetCoreFuel]
          exact Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨entry, Finset.mem_filter.mpr ⟨hEntry, by simpa only [hSource] using hKeep⟩,
              by simp only [hSource]⟩)
        · rw [buildRelationSetCoreFuel]
          exact Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨(right, (compileTypeFuel fuel right).initial),
              buildRelationSetCoreFuel_initial_mem fuel right hRight, rfl⟩)
        · simpa only [typeCanCompleteThisCycleFuel_eq_canCompleteDeclared
            (sizeOf entry.1 + 1) entry.1 (by omega)]
            using hFlag
      simp only [compileTypeFuel, buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with (hLeftEdge | hRightEdge) | hRedirect
      · simp only [sequenceLeftEdges, Finset.mem_image, Finset.mem_filter] at hLeftEdge
        obtain ⟨child, ⟨_, hKeep, _⟩, rfl⟩ := hLeftEdge
        exact hLeftField child hKeep
      · exact hCopy right 1 hRight (by
          intro rho q hRelated
          rw [buildRelationSetCoreFuel]
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(rho, q), hRelated, rfl⟩)) hRightEdge
      · simp only [sequenceRedirectEdges, Finset.mem_image, Finset.mem_filter] at hRedirect
        obtain ⟨child, ⟨_, hKeep, _⟩, rfl⟩ := hRedirect
        exact hLeftField child hKeep
    | par a left right interface =>
      intro stored reference removed hFuture
      simp only [compileTypeFuel, buildParallelAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with ((((((hRaw | hLC) | hRC) | hLS) | hRS) | hLD) | hRD) | hDone
      · simp only [parallelRawTransitionEdges, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image] at hRaw
        obtain ⟨le, _, re, _, rfl⟩ := hRaw
        simp only [parallelFutureSpec] at hFuture
        split_ifs at hFuture
      · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image] at hLC
        obtain ⟨q, _, re, _, env, _, rfl⟩ := hLC
        simp only [parallelFutureSpec] at hFuture
        split_ifs at hFuture
      · simp only [parallelRightCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image] at hRC
        obtain ⟨q, _, le, _, env, _, rfl⟩ := hRC
        simp only [parallelFutureSpec] at hFuture
        split_ifs at hFuture
      · simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter, Finset.mem_image] at hLS
        obtain ⟨e, _, rfl⟩ := hLS
        simp only [parallelFutureSpec] at hFuture
        split_ifs at hFuture
      · simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter, Finset.mem_image] at hRS
        obtain ⟨e, _, rfl⟩ := hRS
        simp only [parallelFutureSpec] at hFuture
        split_ifs at hFuture
      · simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter, Finset.mem_image] at hLD
        obtain ⟨e, _, rfl⟩ := hLD
        simp only [parallelFutureSpec] at hFuture
        split_ifs at hFuture
      · simp only [parallelRightCompleteDoneEdges, Finset.mem_filter, Finset.mem_image] at hRD
        obtain ⟨e, _, rfl⟩ := hRD
        simp only [parallelFutureSpec] at hFuture
        split_ifs at hFuture
      · simp only [parallelDoneEdges, Finset.mem_image, Finset.mem_filter] at hDone
        obtain ⟨env, _, rfl⟩ := hDone
        simp at hFuture
    | xoffer a other branches | offer a other branches =>
      have hElse : typeCompilationFuel other ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      simp only [compileTypeFuel, buildExclusiveOfferAutomaton, buildAtomicConjunctiveOfferAutomaton,
        conjunctiveFiringEdges,
        finishAutomatonFragment, Finset.mem_union] at hEdge
      rcases hEdge with (((hElseEdge | hIndexed) | hBranch) | hWait) | hDefault
      · exact hCopy other 0 hElse (by
          intro rho q hRelated
          rw [buildRelationSetCoreFuel]
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨(rho, q), hRelated, rfl⟩))) hElseEdge
      · simp only [indexedFragmentEdges, List.zipIdx_map, mem_foldl_union_iff] at hIndexed
        rcases hIndexed with hEmpty | ⟨item, hItem, hCopyEdge⟩
        · simp at hEmpty
        · obtain ⟨entry, hEntry, rfl⟩ := List.mem_map.mp hItem
          apply hCopy _ (entry.2 + 1) ?_ ?_ hCopyEdge
          · first
            | have := typeCompilationFuel_le_typeBranchCompilationFuel branches entry.1
                (List.fst_mem_of_mem_zipIdx hEntry)
              simp [typeCompilationFuel] at hFuel; omega
            | have := typeCompilationFuel_parallelTypeBranchesFiring a entry.1 branches
              simp [typeCompilationFuel] at hFuel; omega
          · intro rho q hRelated
            simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
              mem_foldl_union_iff, Finset.mem_image]
            exact Or.inr (Or.inr (Or.inr ⟨entry, hEntry, (rho, q), hRelated, rfl⟩))
      · intro stored reference removed hFuture
        rw [mem_foldl_union_iff] at hBranch
        rcases hBranch with hEmpty | ⟨entry, _, hNew⟩
        · simp at hEmpty
        · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hNew
          simp at hFuture
      · intro stored reference removed hFuture
        obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hWait
        simp at hFuture
      · intro stored reference removed hFuture
        obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hDefault
        simp at hFuture

/-- Paper: a sequence union field reads its represented right operand, under a true left flag. -/
theorem compileTypeFuel_atUnion_represented
    (fuel : Nat) (ty : PactType) (hFuel : typeCompilationFuel ty ≤ fuel)
    (edge : PendingAutomatonEdge) (hEdge : edge ∈ (compileTypeFuel fuel ty).edges)
    (stored removed : Finset BareMessage) (reference : TypeAutomatonState)
    (hField : edge.future = .atUnion stored reference removed) :
    edge.label.semantic ≠ .tock ∧ removed = edge.current ∧ ∃ alphabet left right,
      (.seq alphabet left right, edge.source) ∈ buildRelationSetCoreFuel fuel ty ∧
      (right, reference) ∈ buildRelationSetCoreFuel fuel ty ∧
      left.CanCompleteDeclared = true :=
  compileTypeFuel_sequenceFieldRepresented fuel ty hFuel edge hEdge stored reference removed hField

end

end Pact
