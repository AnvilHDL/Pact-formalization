import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.Recursion

namespace Pact

noncomputable section

open Classical Pact.NewCorrespondence

private def StoredMenuSource (source : PactType) : Prop :=
  (∀ name, source.TailOccurrences name False) ∨
    ∃ alphabet left right, source = .seq alphabet left right ∧ left.CanCompleteDeclared = false

private theorem storedMenuSource_replaceVar (name : String) (replacement source : PactType)
    (hSource : StoredMenuSource source) (hTail : source.TailOccurrences name True) :
    StoredMenuSource (source.replaceVar name replacement) := by
  rcases hSource with hClosed | ⟨alphabet, left, right, rfl, hIncomplete⟩
  · rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement source (hClosed name)]
    exact Or.inl hClosed
  · have hLeft : left.TailOccurrences name False := by
      simp only [PactType.TailOccurrences] at hTail
      exact hTail.1
    rw [PactType.replaceVar,
      PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement left hLeft]
    exact Or.inr ⟨alphabet, left, right.replaceVar name replacement, rfl, hIncomplete⟩

private theorem compileTypeFuel_storedMenuSource :
    ∀ fuel ty, typeCompilationFuel ty ≤ fuel →
      ∀ bound, TypeWellFormedIn bound ty →
      ∀ source edge, (source, edge.source) ∈ buildRelationSetCoreFuel fuel ty →
      edge ∈ (compileTypeFuel fuel ty).edges → edge.label.semantic ≠ .tock →
      ∀ stored, edge.future = .explicit stored → StoredMenuSource source := by
  intro fuel
  induction fuel with
  | zero => intro ty _ bound _ source edge _ hEdge; simp [compileTypeFuel] at hEdge
  | succ fuel ih =>
    intro ty hFuel bound hWF source edge hRelated hEdge hNonClock stored hField
    have hChild (child : PactType) (index : Nat) (childBound : List String)
        (hChildFuel : typeCompilationFuel child ≤ fuel)
        (hChildWF : TypeWellFormedIn childBound child)
        (hChildEdge : edge ∈ childPendingEdges index (compileTypeFuel fuel child))
        (hPull : ∀ q, (source, .child index q) ∈ buildRelationSetCoreFuel (fuel + 1) ty →
          (source, q) ∈ buildRelationSetCoreFuel fuel child) :
        StoredMenuSource source := by
      obtain ⟨inner, hInner, rfl⟩ := Finset.mem_image.mp hChildEdge
      cases hSpec : inner.future with
      | explicit offers =>
        simp only [childPendingEdge, hSpec, childFutureSpec, FutureSpec.explicit.injEq] at hField
        subst offers
        exact ih child hChildFuel childBound hChildWF source inner (hPull _ hRelated)
          hInner hNonClock stored hSpec
      | «at» q mask | atUnion offers q mask => simp [childPendingEdge, hSpec, childFutureSpec] at hField
    have hCanonical : relationMembership (buildRelationSet ty (compileType ty)) source edge.source := by
      rw [buildRelationSetCoreFuel_eq_of_sufficient ty hFuel le_rfl] at hRelated
      exact hRelated
    cases ty with
    | skip a | var a name =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image,
        Finset.mem_filter] at hEdge
      obtain ⟨env, _, rfl⟩ := hEdge
      simp at hField
    | message a m d =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with (⟨env, _, rfl⟩ | ⟨env, _, rfl⟩) | ⟨env, _, rfl⟩ <;> simp at hField
    | progress a p =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with ⟨env, _, rfl⟩ | ⟨env, _, rfl⟩ <;> simp at hField
    | tock a =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with ⟨env, _, rfl⟩ | ⟨env, _, rfl⟩
      · split_ifs at hField
        simp_all [AutomatonConstructionLabel.semantic]
      · simp at hField
    | choice a left right | fairChoice a bid left right =>
      have hLeft : typeCompilationFuel left ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      have hRight : typeCompilationFuel right ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      have hWFChildren : TypeWellFormedIn bound left ∧ TypeWellFormedIn bound right := by
        first | exact typeWellFormedIn_choice hWF | exact typeWellFormedIn_fairChoice hWF
      simp only [compileTypeFuel, buildChoiceAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with (hLeftEdge | hRightEdge) | hRoot
      · apply hChild left 0 bound hLeft hWFChildren.1 hLeftEdge
        intro q hRho
        simpa [buildRelationSetCoreFuel, Finset.mem_image, Prod.mk.injEq] using hRho
      · apply hChild right 1 bound hRight hWFChildren.2 hRightEdge
        intro q hRho
        simpa [buildRelationSetCoreFuel, Finset.mem_image, Prod.mk.injEq] using hRho
      · simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton] at hRoot
        obtain ⟨env, _, hCase⟩ := hRoot
        rcases hCase with rfl | rfl <;> simp at hField
    | seq a left right =>
      have hLeft : typeCompilationFuel left ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      have hRight : typeCompilationFuel right ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      have hLeftSource (child : PendingAutomatonEdge)
          (hR : (source, .child 0 child.source) ∈ buildRelationSetCoreFuel (fuel + 1) (.seq a left right))
          (hNC : child.label.semantic ≠ .tock)
          (hF : sequenceLeftFutureSpec child.label
            (childState 1 (compileTypeFuel fuel right).initial)
            (resolveFutureSpec (computeFutureOfFuel (min fuel (typeCompilationFuel left)) left) child.future)
            child.current
            (decide (∃ entry ∈ buildRelationSetCoreFuel (min fuel (typeCompilationFuel left)) left,
              entry.2 = child.source ∧
                typeCanCompleteThisCycleFuel (sizeOf entry.1 + 1) entry.1 = true)) = .explicit stored) :
          StoredMenuSource source := by
        simp only [sequenceLeftFutureSpec, if_neg hNC] at hF
        split_ifs at hF with hComplete
        simp only [buildRelationSetCoreFuel, Finset.mem_union, Finset.mem_image,
          Finset.mem_filter, Prod.mk.injEq, TypeAutomatonState.child.injEq] at hR
        rcases hR with ⟨entry, ⟨hEntry, _⟩, hSource, _, hState⟩ |
          ⟨entry, _, _, hImpossible⟩
        · refine Or.inr ⟨a, entry.1, right, hSource.symm, ?_⟩
          have hNotComplete : ¬ entry.1.CanCompleteDeclared = true := by
            intro hFlag
            apply hComplete
            apply decide_eq_true_eq.mpr
            refine ⟨entry, ?_, hState, ?_⟩
            · rw [Nat.min_eq_right hLeft]
              rwa [buildRelationSetCoreFuel_eq_of_sufficient left hLeft le_rfl] at hEntry
            · simpa only [typeCanCompleteThisCycleFuel_eq_canCompleteDeclared
                (sizeOf entry.1 + 1) entry.1 (by omega)] using hFlag
          cases hFlag : entry.1.CanCompleteDeclared <;> simp_all
        · simp at hImpossible
      simp only [compileTypeFuel, buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with (hLeftEdge | hRightEdge) | hRedirect
      · simp only [sequenceLeftEdges, Finset.mem_image, Finset.mem_filter] at hLeftEdge
        obtain ⟨child, _, rfl⟩ := hLeftEdge
        exact hLeftSource child hRelated hNonClock hField
      · apply hChild right 1 bound hRight (typeWellFormedIn_seq hWF).2 hRightEdge
        intro q hRho
        simpa [buildRelationSetCoreFuel, Finset.mem_image, Prod.mk.injEq] using hRho
      · simp only [sequenceRedirectEdges, Finset.mem_image, Finset.mem_filter] at hRedirect
        obtain ⟨child, _, rfl⟩ := hRedirect
        exact hLeftSource child hRelated hNonClock hField
    | par a left right interface =>
      left
      intro name
      apply relationMembership_tailOccurrences (.par a left right interface) source edge.source
        name False hWF.2.2.2.2.2.1 ?_ hCanonical
      simpa only [PactType.TailOccurrences] using hWF.2.2.2.1 name
    | recur a name body =>
      have hBody : typeCompilationFuel body ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      have hBodyWF := typeWellFormedIn_recur hWF
      simp only [compileTypeFuel, buildRecursionAutomaton, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image] at hEdge
      rcases hEdge with ⟨env, _, rfl⟩ | ⟨child, hChildEdge, rfl⟩
      · simp at hField
      · by_cases hMarker : child.label = .variable name
        · simp [hMarker] at hField
        · simp only [if_neg hMarker] at hRelated hNonClock hField
          simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_image,
            Prod.mk.injEq, childState, TypeAutomatonState.child.injEq] at hRelated
          rcases hRelated with ⟨_, hImpossible⟩ | ⟨entry, hEntry, hSource, _, hState⟩
          · simp at hImpossible
          change (entry.1, entry.2) ∈ _ at hEntry
          have hBodyRelated : relationMembership (buildRelationSet body (compileType body))
              entry.1 child.source := by
            rw [buildRelationSetCoreFuel_eq_of_sufficient body hBody le_rfl] at hEntry
            simpa only [hState] using hEntry
          cases hSpec : child.future with
          | explicit offers =>
            simp only [hSpec, childFutureSpec, FutureSpec.explicit.injEq] at hField
            subst offers
            have hStored := ih body hBody (name :: bound) hBodyWF entry.1 child
              (by simpa only [hState] using hEntry) hChildEdge hNonClock stored hSpec
            have hRec : body.TailOccurrences name True ∧ body.TailRecursive := by
              simpa only [PactType.TailRecursive] using hWF.2.2.2.2.2.1
            have hTail := relationMembership_tailOccurrences body entry.1 child.source name True
              hRec.2 hRec.1 hBodyRelated
            rw [← hSource]
            exact storedMenuSource_replaceVar name (.recur a name body) entry.1 hStored hTail
          | «at» q mask | atUnion offers q mask => simp [hSpec, childFutureSpec] at hField
    | xoffer a other branches | offer a other branches =>
      have hElse : typeCompilationFuel other ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      have hElseWF : TypeWellFormedIn bound other := by
        first | exact (typeWellFormedIn_xoffer hWF).1 | exact (typeWellFormedIn_offer hWF).1
      simp only [compileTypeFuel, buildExclusiveOfferAutomaton, buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, Finset.mem_union] at hEdge
      rcases hEdge with (((hElseEdge | hIndexed) | hBranch) | hWait) | hDefault
      · apply hChild other 0 bound hElse hElseWF hElseEdge
        intro q hRho
        simpa [buildRelationSetCoreFuel, Finset.mem_image, Prod.mk.injEq,
          mem_foldl_union_iff] using hRho
      · simp only [indexedFragmentEdges, List.zipIdx_map, mem_foldl_union_iff] at hIndexed
        rcases hIndexed with hEmpty | ⟨item, hItem, hCopyEdge⟩
        · simp at hEmpty
        · obtain ⟨entry, hEntry, rfl⟩ := List.mem_map.mp hItem
          have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hEntry
          have hMember : entry.1 ∈ branches := List.mem_of_getElem? hGet
          refine hChild _ (entry.2 + 1) bound ?_ ?_ hCopyEdge ?_
          · first
            | have := typeCompilationFuel_le_typeBranchCompilationFuel branches entry.1 hMember
              simp [typeCompilationFuel] at hFuel; omega
            | rw [typeCompilationFuel_parallelTypeBranchesSelecting]
              simp [typeCompilationFuel] at hFuel; omega
          · first
            | exact (typeWellFormedIn_xoffer hWF).2 entry.1 hMember
            | exact (typeWellFormedIn_offer hWF).2 entry.1 hMember
          · intro q hRho
            simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
              mem_foldl_union_iff, Finset.notMem_empty, false_or, Finset.mem_image,
              Prod.mk.injEq] at hRho
            rcases hRho with ⟨_, hRoot⟩ | ⟨pair, _, _, hElse⟩ |
              ⟨indexed, hIndexed, pair, hPair, hSource, hState⟩
            · simp at hRoot
            · simp only [TypeAutomatonState.child.injEq] at hElse
              omega
            · have hIndex : indexed.2 = entry.2 := by
                simp only [TypeAutomatonState.child.injEq] at hState
                omega
              have hSame : indexed = entry := by
                have hGet' := List.mk_mem_zipIdx_iff_getElem?.mp hIndexed
                rw [hIndex, hGet] at hGet'
                exact Prod.ext (Option.some.inj hGet'.symm) hIndex
              subst indexed
              simp only [TypeAutomatonState.child.injEq, true_and] at hState
              change (pair.1, pair.2) ∈ _ at hPair
              simpa only [hSource, hState] using hPair
      · rw [mem_foldl_union_iff] at hBranch
        rcases hBranch with hEmpty | ⟨entry, _, hNew⟩
        · simp at hEmpty
        · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hNew
          simp at hField
      · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hWait
        simp at hField
      · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hDefault
        simp at hField

/-- Stored non-clock fields have no substitution-dependent operand. -/
theorem compileTypeFuel_explicit_source
    (fuel : Nat) (ty : PactType) (hFuel : typeCompilationFuel ty ≤ fuel)
    {bound : List String} (hWF : TypeWellFormedIn bound ty)
    {source : PactType} (edge : PendingAutomatonEdge)
    (hRelated : (source, edge.source) ∈ buildRelationSetCoreFuel fuel ty)
    (hEdge : edge ∈ (compileTypeFuel fuel ty).edges) (hNonClock : edge.label.semantic ≠ .tock)
    (stored : Finset BareMessage) (hField : edge.future = .explicit stored) :
    (∀ name, source.TailOccurrences name False) ∨
      ∃ alphabet left right, source = .seq alphabet left right ∧ left.CanCompleteDeclared = false :=
  compileTypeFuel_storedMenuSource fuel ty hFuel bound hWF source edge hRelated hEdge
    hNonClock stored hField

end

end Pact
