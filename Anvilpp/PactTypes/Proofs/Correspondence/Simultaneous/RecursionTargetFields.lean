import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.Recursion
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.MenuReferenceShape

namespace Pact

noncomputable section

open Classical Pact.NewCorrespondence

private def TargetMenuSource (source : PactType) (env : TypeEnvironment) : Prop :=
  match source with
  | .skip _ | .message _ _ _ | .tock _ | .progress _ _ | .recur _ _ _ | .offer _ _ _ => True
  | .xoffer _ _ branches => ¬ TypeResolved env branches
  | _ => False

private theorem targetMenuSource_replaceVar (name : String) (replacement source : PactType)
    (env : TypeEnvironment) (hSource : TargetMenuSource source env) :
    TargetMenuSource (source.replaceVar name replacement) env := by
  cases source <;> simp_all [TargetMenuSource, PactType.replaceVar, TypeResolved_replaceBranches]
  split_ifs <;> simp [TargetMenuSource]

private theorem targetMenuSource_future {source target : PactType} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hSource : TargetMenuSource source env) (hNonClock : label ≠ .tock)
    (hOffers : TypeOffers env source label target current future) :
    future = typeFutureOffers target \ current := by
  cases source with
  | skip a | message a m d | tock a | progress a p | recur a name body =>
    cases hOffers <;> simp_all [typeFutureOffers, typeFutureOffersFuel, TypeLabel.silent]
  | offer a other branches => exact hOffers.offer_future_eq
  | xoffer a other branches =>
    cases hOffers with
    | xoffer_branch _ _ _ _ _ _ hCond _ => exact (hSource hCond.2.2.2).elim
    | xoffer_else _ _ _ _ hCond _ => exact (hSource hCond.2.2.2).elim
    | xoffer_wait => rfl
  | _ => exact hSource.elim

private theorem childTargetField (index : Nat) (child : PendingAutomatonEdge)
    (removed : Finset BareMessage)
    (hField : (childPendingEdge index child).future =
      .at (childPendingEdge index child).target removed) :
    child.future = .at child.target removed := by
  obtain ⟨inner, hInner, hTarget⟩ :=
    childFutureSpec_at index child.future (childState index child.target) removed hField
  have hEq : child.target = inner := by
    simpa only [childState, TypeAutomatonState.child.injEq, true_and] using hTarget
  exact hEq ▸ hInner

private theorem compileTypeFuel_targetMenuSource :
    ∀ fuel ty, typeCompilationFuel ty ≤ fuel →
      ∀ bound, TypeWellFormedIn bound ty →
      ∀ source edge, (source, edge.source) ∈ buildRelationSetCoreFuel fuel ty →
      edge ∈ (compileTypeFuel fuel ty).edges →
      ∀ label, edge.label = .visible label →
      ∀ removed, edge.future = .at edge.target removed →
        TargetMenuSource source edge.environment := by
  intro fuel
  induction fuel with
  | zero => intro ty _ bound _ source edge _ hEdge; simp [compileTypeFuel] at hEdge
  | succ fuel ih =>
    intro ty hFuel bound hWF source edge hRelated hEdge label hLabel removed hField
    have hChild (child : PactType) (index : Nat) (childBound : List String)
        (hChildFuel : typeCompilationFuel child ≤ fuel)
        (hChildWF : TypeWellFormedIn childBound child)
        (hChildEdge : edge ∈ childPendingEdges index (compileTypeFuel fuel child))
        (hPull : ∀ q, (source, .child index q) ∈ buildRelationSetCoreFuel (fuel + 1) ty →
          (source, q) ∈ buildRelationSetCoreFuel fuel child) :
        TargetMenuSource source edge.environment := by
      obtain ⟨inner, hInner, rfl⟩ := Finset.mem_image.mp hChildEdge
      exact ih child hChildFuel childBound hChildWF source inner (hPull _ hRelated)
        hInner label hLabel removed (childTargetField index inner removed hField)
    have hCanonical : relationMembership (buildRelationSet ty (compileType ty)) source edge.source := by
      rw [buildRelationSetCoreFuel_eq_of_sufficient ty hFuel le_rfl] at hRelated
      exact hRelated
    cases ty with
    | skip a | message a m d | tock a | progress a p =>
      first
      | obtain ⟨rfl, _⟩ := relationMembership_skip_cases a hCanonical
        trivial
      | obtain hRoot | hFinal := relationMembership_message_cases a m d hCanonical
        · rw [hRoot.1]; trivial
        · rw [hFinal.1]; trivial
      | obtain hRoot | hFinal := relationMembership_tock_cases a hCanonical
        · rw [hRoot.1]; trivial
        · rw [hFinal.1]; trivial
      | obtain hRoot | hFinal := relationMembership_progress_cases a p hCanonical
        · rw [hRoot.1]; trivial
        · rw [hFinal.1]; trivial
    | var a name =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image,
        Finset.mem_filter] at hEdge
      obtain ⟨env, _, rfl⟩ := hEdge
      simp at hLabel
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
        rcases hCase with rfl | rfl <;> simp [childState] at hField
    | seq a left right =>
      have hRight : typeCompilationFuel right ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      simp only [compileTypeFuel, buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with (hLeftEdge | hRightEdge) | hRedirect
      · simp only [sequenceLeftEdges, Finset.mem_image, Finset.mem_filter] at hLeftEdge
        obtain ⟨child, _, rfl⟩ := hLeftEdge
        simp only [sequenceKeptLeftEdge, sequenceLeftFutureSpec] at hField
        split_ifs at hField
      · apply hChild right 1 bound hRight (typeWellFormedIn_seq hWF).2 hRightEdge
        intro q hRho
        simpa [buildRelationSetCoreFuel, Finset.mem_image, Prod.mk.injEq] using hRho
      · simp only [sequenceRedirectEdges, Finset.mem_image, Finset.mem_filter] at hRedirect
        obtain ⟨child, _, rfl⟩ := hRedirect
        simp only [sequenceRedirectEdge, sequenceLeftFutureSpec] at hField
        split_ifs at hField
    | recur a name body =>
      have hBody : typeCompilationFuel body ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      have hBodyWF := typeWellFormedIn_recur hWF
      simp only [compileTypeFuel, buildRecursionAutomaton, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image] at hEdge
      rcases hEdge with ⟨env, _, rfl⟩ | ⟨child, hChildEdge, rfl⟩
      · simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_image,
          Prod.mk.injEq, childState] at hRelated
        rcases hRelated with ⟨rfl, _⟩ | ⟨entry, _, _, hState⟩
        · trivial
        · simp at hState
      · have hR : (source, .child 0 child.source) ∈
            buildRelationSetCoreFuel (fuel + 1) (.recur a name body) := by
          split_ifs at hRelated <;> exact hRelated
        simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_image,
          Prod.mk.injEq, TypeAutomatonState.child.injEq] at hR
        rcases hR with ⟨_, hImpossible⟩ | ⟨entry, hEntry, hSource, _, hState⟩
        · simp at hImpossible
        change (entry.1, entry.2) ∈ _ at hEntry
        have hBodyRelated : relationMembership (buildRelationSet body (compileType body))
            entry.1 child.source := by
          rw [buildRelationSetCoreFuel_eq_of_sufficient body hBody le_rfl] at hEntry
          simpa only [hState] using hEntry
        by_cases hMarker : child.label = .variable name
        · have hRec : body.TailOccurrences name True ∧ body.TailRecursive := by
            simpa only [PactType.TailRecursive] using hWF.2.2.2.2.2.1
          have hTail := hRec.1
          have hMarkerSource : MarkerSource (compileTypeFuel (typeCompilationFuel body) body)
              name child.source := by
            rw [compileTypeFuel_eq_of_sufficient body hBody le_rfl] at hChildEdge
            exact ⟨child, hChildEdge, rfl, hMarker⟩
          obtain ⟨varAlphabet, hVar⟩ :=
            (markerSource_iff_var_residual body name hTail hBodyRelated).mp hMarkerSource
          rw [← hSource, hVar]
          simp [PactType.replaceVar, TargetMenuSource, hMarker]
        · simp only [if_neg hMarker] at hLabel hField ⊢
          have hDirect := ih body hBody (name :: bound) hBodyWF entry.1 child
            (by simpa only [hState] using hEntry) hChildEdge label hLabel removed
            (childTargetField 0 child removed hField)
          rw [← hSource]
          exact targetMenuSource_replaceVar name (.recur a name body) entry.1 _ hDirect
    | par a left right interface =>
      simp only [compileTypeFuel, buildParallelAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with ((((((hRaw | hLC) | hRC) | hLS) | hRS) | hLD) | hRD) | hDone
      · simp only [parallelRawTransitionEdges, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image] at hRaw
        obtain ⟨le, _, re, _, rfl⟩ := hRaw
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image] at hLC
        obtain ⟨q, _, re, _, env, _, rfl⟩ := hLC
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelRightCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image] at hRC
        obtain ⟨q, _, le, _, env, _, rfl⟩ := hRC
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter, Finset.mem_image] at hLS
        obtain ⟨e, _, rfl⟩ := hLS
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter, Finset.mem_image] at hRS
        obtain ⟨e, _, rfl⟩ := hRS
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter, Finset.mem_image] at hLD
        obtain ⟨e, _, rfl⟩ := hLD
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelRightCompleteDoneEdges, Finset.mem_filter, Finset.mem_image] at hRD
        obtain ⟨e, _, rfl⟩ := hRD
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelDoneEdges, Finset.mem_image, Finset.mem_filter] at hDone
        obtain ⟨env, _, rfl⟩ := hDone
        simp at hField

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
          first
          | solve | simp [childState] at hField
          | have hCanonical : relationMembership (buildRelationSet (.offer a other branches)
                (compileType (.offer a other branches))) source .root := by
              rw [buildRelationSetCoreFuel_eq_of_sufficient _ hFuel le_rfl] at hRelated
              exact hRelated
            have hEq := relationMembership_functional _ _ hCanonical (relationMembership_offer_root a other branches)
            rw [hEq]; trivial
      · obtain ⟨env, hEnv, rfl⟩ := Finset.mem_image.mp hWait
        first
        | have hEq := relationMembership_functional _ _ hCanonical (relationMembership_xoffer_root a other branches)
          rw [hEq]
          exact (Finset.mem_filter.mp hEnv).2.2.1
        | have hEq := relationMembership_functional _ _ hCanonical (relationMembership_offer_root a other branches)
          rw [hEq]; trivial
      · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hDefault
        first
        | solve | simp [childState] at hField
        | have hCanonical : relationMembership (buildRelationSet (.offer a other branches)
              (compileType (.offer a other branches))) source .root := by
            rw [buildRelationSetCoreFuel_eq_of_sufficient _ hFuel le_rfl] at hRelated
            exact hRelated
          have hEq := relationMembership_functional _ _ hCanonical (relationMembership_offer_root a other branches)
          rw [hEq]; trivial

/-- A copied target field reads the substituted target's menu, with the same removal set. -/
theorem TypeOffers.replaceVar_compiled_at_target_future
    (ty : PactType) {bound : List String} (hWF : TypeWellFormedIn bound ty)
    (name : String) (replacement : PactType)
    (menus : TypeAutomatonState → Finset BareMessage)
    (hMenus : ∀ rho q,
      relationMembership (buildRelationSet ty (compileType ty)) rho q →
        menus q = typeFutureOffers (rho.replaceVar name replacement))
    {source target : PactType} (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel (typeCompilationFuel ty) ty).edges)
    {label : TypeLabel} (hLabel : edge.label = .visible label)
    (removed : Finset BareMessage) (hField : edge.future = .at edge.target removed)
    (hSource : relationMembership (buildRelationSet ty (compileType ty)) source edge.source)
    (hTarget : relationMembership (buildRelationSet ty (compileType ty)) target edge.target)
    {future : Finset BareMessage}
    (hOffers : TypeOffers edge.environment (source.replaceVar name replacement)
      label (target.replaceVar name replacement) edge.current future) :
    future = resolveFutureSpec menus edge.future := by
  have hShape := compileTypeFuel_targetMenuSource (typeCompilationFuel ty) ty le_rfl
    bound hWF source edge hSource hEdge label hLabel removed hField
  have hNonClock := (compileTypeFuel_at_endpoint (typeCompilationFuel ty) ty edge hEdge
    edge.target removed hField).1
  simp only [hLabel, AutomatonConstructionLabel.semantic] at hNonClock
  have hFuture := targetMenuSource_future
    (targetMenuSource_replaceVar name replacement source _ hShape) hNonClock hOffers
  rw [hFuture, hField, resolveFutureSpec, hMenus _ _ hTarget]
  rcases compileTypeFuel_at_target_removal (typeCompilationFuel ty) ty edge hEdge
      removed hField with hRemoved | hFinal
  · rw [hRemoved]
  · obtain ⟨alphabet, hSkip⟩ := final_state_represents_skip ty hTarget hFinal
    simp [hSkip, PactType.replaceVar, typeFutureOffers, typeFutureOffersFuel]

end

end Pact
