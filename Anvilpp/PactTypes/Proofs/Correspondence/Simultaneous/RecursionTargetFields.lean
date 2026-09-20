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
  split_ifs <;> simp

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
    | xoffer_branch _ _ _ _ _ _ hCond => exact (hSource hCond.2.2.2).elim
    | xoffer_else _ _ _ _ hCond => exact (hSource hCond.2.2.2).elim
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

/-- A visible compiled edge reading its target menu represents a `TargetMenuSource`. -/
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
    have hCanonical : relationMembership (buildRelationSet ty (compileType ty)) source edge.source := by
      rw [buildRelationSetCoreFuel_eq_of_sufficient ty hFuel le_rfl] at hRelated
      exact hRelated
    -- Pull a copied edge back to its child and apply the induction hypothesis.
    have hChild (child : PactType) (index : Nat) (childBound : List String)
        (hChildFuel : typeCompilationFuel child ≤ fuel)
        (hChildWF : TypeWellFormedIn childBound child)
        (hChildEdge : edge ∈ childPendingEdges index (compileTypeFuel fuel child))
        (hPull : ∀ q,
          relationMembership (buildRelationSet ty (compileType ty)) source (.child index q) →
          relationMembership (buildRelationSet child (compileType child)) source q) :
        TargetMenuSource source edge.environment := by
      obtain ⟨inner, hInner, rfl⟩ := Finset.mem_image.mp hChildEdge
      have hChildRelated := hPull _ hCanonical
      change (source, inner.source) ∈ buildRelationSetCoreFuel (typeCompilationFuel child) child
        at hChildRelated
      rw [← buildRelationSetCoreFuel_eq_of_sufficient child hChildFuel le_rfl] at hChildRelated
      exact ih child hChildFuel childBound hChildWF source inner hChildRelated
        hInner label hLabel removed (childTargetField index inner removed hField)
    cases ty with
    | skip a | message a m d | tock a | progress a p =>
      -- Atomic residuals are either the original type or `skip`.
      simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at hRelated
      rcases hRelated with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> trivial
    | var a name =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image,
        Finset.mem_filter] at hEdge
      obtain ⟨env, _, rfl⟩ := hEdge
      simp at hLabel
    | choice a left right | fairChoice a bid left right =>
      -- Only child edges qualify: choice edges read the root menu.
      have hLeft : typeCompilationFuel left ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      have hRight : typeCompilationFuel right ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      have hWFChildren : TypeWellFormedIn bound left ∧ TypeWellFormedIn bound right := by
        first | exact typeWellFormedIn_choice hWF | exact typeWellFormedIn_fairChoice hWF
      simp only [compileTypeFuel, buildChoiceAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with (hLeftEdge | hRightEdge) | hRoot
      · apply hChild left 0 bound hLeft hWFChildren.1 hLeftEdge
        intro q hRho
        first
        | simpa [binaryChoiceRelationShape] using relationMembership_choice_cases a left right hRho
        | simpa [binaryChoiceRelationShape] using relationMembership_fairChoice_cases a bid left right hRho
      · apply hChild right 1 bound hRight hWFChildren.2 hRightEdge
        intro q hRho
        first
        | simpa [binaryChoiceRelationShape] using relationMembership_choice_cases a left right hRho
        | simpa [binaryChoiceRelationShape] using relationMembership_fairChoice_cases a bid left right hRho
      · simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton] at hRoot
        obtain ⟨env, _, hCase⟩ := hRoot
        rcases hCase with rfl | rfl <;> simp [childState] at hField
    | seq a left right =>
      -- Left edges use explicit or union fields; only the right child can qualify.
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
        simpa [seqRelationShape] using relationMembership_seq_cases a left right hRho
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
          Prod.mk.injEq] at hRelated
        rcases hRelated with ⟨rfl, _⟩ | ⟨entry, _, _, hState⟩
        · trivial
        · simp at hState
      · have hR : (source, .child 0 child.source) ∈
            buildRelationSetCoreFuel (fuel + 1) (.recur a name body) := by
          split_ifs at hRelated <;> exact hRelated
        simp [buildRelationSetCoreFuel, Finset.mem_image, Prod.exists] at hR
        obtain ⟨inner, hInner, rfl⟩ := hR
        by_cases hMarker : child.label = .variable name
        · -- A bound-variable marker becomes the recursive type itself.
          have hRec : body.TailOccurrences name True ∧ body.TailRecursive := by
            simpa only [PactType.TailRecursive] using hWF.2.2.2.2.2.1
          have hBodyRelated : relationMembership (buildRelationSet body (compileType body))
              inner child.source := by
            rwa [buildRelationSetCoreFuel_eq_of_sufficient body hBody le_rfl] at hInner
          have hMarkerSource : MarkerSource (compileTypeFuel (typeCompilationFuel body) body)
              name child.source := by
            rw [compileTypeFuel_eq_of_sufficient body hBody le_rfl] at hChildEdge
            exact ⟨child, hChildEdge, rfl, hMarker⟩
          obtain ⟨varAlphabet, hVar⟩ :=
            (markerSource_iff_var_residual body name hRec.1 hBodyRelated).mp hMarkerSource
          rw [hVar]
          simp [PactType.replaceVar, TargetMenuSource]
        · -- Other body edges preserve the property under substitution.
          simp only [if_neg hMarker] at hLabel hField ⊢
          apply targetMenuSource_replaceVar
          exact ih body hBody (name :: bound) hBodyWF inner child hInner hChildEdge
            label hLabel removed (childTargetField 0 child removed hField)
    | par a left right interface =>
      -- Parallel edges store explicit futures, so none can read a target menu.
      exfalso
      clear ih hChild hCanonical hRelated hWF hFuel hLabel
      simp only [compileTypeFuel, buildParallelAutomaton, finishAutomatonFragment,
        parallelRawTransitionEdges, parallelLeftCompleteEdges,
        parallelRightCompleteEdges, parallelLeftCompleteSurvivorEdges,
        parallelRightCompleteSurvivorEdges, parallelLeftCompleteDoneEdges,
        parallelRightCompleteDoneEdges, parallelDoneEdges,
        Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image] at hEdge
      aesop (add simp [parallelFutureSpec, apply_ite])

    | xoffer a other branches | offer a other branches =>
      -- Recurse through copied branches, then check the offer's own root edges.
      have hElse : typeCompilationFuel other ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      have hElseWF : TypeWellFormedIn bound other := by
        first | exact (typeWellFormedIn_xoffer hWF).1 | exact (typeWellFormedIn_offer hWF).1
      simp only [compileTypeFuel, buildExclusiveOfferAutomaton, buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, Finset.mem_union] at hEdge
      rcases hEdge with (((hElseEdge | hIndexed) | hBranch) | hWait) | hDefault
      · apply hChild other 0 bound hElse hElseWF hElseEdge
        intro q hRho
        first
        | simpa [xofferRelationShape] using relationMembership_xoffer_cases a other branches hRho
        | simpa [offerRelationShape] using relationMembership_offer_cases a other branches hRho
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
            -- Specialize the existing relation cases to this branch's index.
            rcases entry with ⟨⟨⟨msg, dir⟩, branch⟩, index⟩
            first
            | simpa [xofferRelationShape, hGet] using
                relationMembership_xoffer_cases a other branches hRho
            | simpa [offerRelationShape, hGet] using
                relationMembership_offer_cases a other branches hRho
      · rw [mem_foldl_union_iff] at hBranch
        rcases hBranch with hEmpty | ⟨entry, _, hNew⟩
        · simp at hEmpty
        · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hNew
          first
          | solve | simp [childState] at hField
          | have hEq := relationMembership_functional _ _ hCanonical
              (relationMembership_offer_root a other branches)
            rw [hEq]; trivial
      · obtain ⟨env, hEnv, rfl⟩ := Finset.mem_image.mp hWait
        first
        | have hEq := relationMembership_functional _ _ hCanonical (relationMembership_xoffer_root a other branches)
          rw [hEq]
          exact (Finset.mem_filter.mp hEnv).2.2
        | have hEq := relationMembership_functional _ _ hCanonical (relationMembership_offer_root a other branches)
          rw [hEq]; trivial
      · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hDefault
        first
        | solve | simp [childState] at hField
        | have hEq := relationMembership_functional _ _ hCanonical
            (relationMembership_offer_root a other branches)
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
