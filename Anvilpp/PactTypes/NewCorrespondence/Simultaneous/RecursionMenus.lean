import Anvilpp.PactTypes.NewCorrespondence.Simultaneous.Base
import Anvilpp.PactTypes.NewCorrespondence.Helpers.SequenceMenus
import Anvilpp.PactTypes.NewCorrespondence.Helpers.MenuLinkCompletion
import Anvilpp.PactTypes.Automata.RecursionMenuLemmas

namespace Pact

noncomputable section

open Classical Pact.NewCorrespondence

/-- Before installation, a marker represents a variable and has an empty menu
by the child hypothesis. Suppressing its bookkeeping reference loses no offer. -/
theorem computeFutureOf_markerStopped (ty : PactType) (name : String)
    (hDisjoint : ty.OfferBranchesDisjoint) (hTail : ty.TailClosed)
    (hCurrent : CurrentOfferCorrespondence ty) (hMenus : FutureOffersAgree ty)
    {rho : PactType} {source : TypeAutomatonState}
    (hRelated : relationMembership (buildRelationSet ty (compileType ty)) rho source) :
    let fragment := compileTypeFuel (typeCompilationFuel ty) ty
    let stopped := (markerStoppedFragment fragment name).toPending.withMenuDependencies
      (compileTypeMenuLinksFuel (typeCompilationFuel ty) ty)
    (stopped.menuFrom (compiledMenuContribution ty) source).filter
      (fun action => action ∈ ty.alphabet.actions) = computeFutureOf ty source := by
  intro fragment stopped
  let original := compiledMenuGraphFuel (typeCompilationFuel ty) ty
  let contribution := fun q => (compiledMenuContribution ty q).filter
    (fun action => action ∈ ty.alphabet.actions)
  have hMenu : ∀ q, original.menuFrom contribution q = computeFutureOf ty q := by
    intro q
    rw [computeFutureOf_eq_menuFrom]
    exact (Finset.filter_biUnion _ _ _).symm
  have hSubset : ∀ q, stopped.referencedStates q ⊆ original.referencedStates q := by
    intro q
    simp only [original, compiledMenuGraphFuel, Nat.min_self,
      PendingAutomaton.withMenuDependencies]
    change _ ∪ _ ⊆ _
    change _ ⊆ fragment.toPending.referencedStates q ∪
      menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel ty) ty) q
    exact Finset.union_subset_union
      (markerStoppedFragment_referencedStates_subset fragment name q) (Finset.Subset.refl _)
  have hStep : ∀ q,
      (∃ theta, relationMembership (buildRelationSet ty (compileType ty)) theta q) →
      ∀ t ∈ original.referencedStates q,
        ((∃ theta, relationMembership (buildRelationSet ty (compileType ty)) theta t) ∧
          t ∈ stopped.referencedStates q) ∨ original.menuFrom contribution q = ∅ := by
    intro q ⟨theta, hTheta⟩ t ht
    simp only [original, compiledMenuGraphFuel, Nat.min_self,
      PendingAutomaton.withMenuDependencies] at ht
    change t ∈ fragment.toPending.referencedStates q ∪
      menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel ty) ty) q at ht
    rcases Finset.mem_union.mp ht with hExecution | hLink
    · obtain ⟨e, hE, hRef⟩ := Finset.mem_biUnion.mp hExecution
      obtain ⟨hE, hSource⟩ := Finset.mem_filter.mp hE
      cases hLabel : e.label with
      | «variable» other =>
        obtain ⟨a, rfl⟩ := (markerSource_iff_var_residual ty other (hTail other)
          hTheta).mp ⟨e, hE, hSource, hLabel⟩
        right
        rw [hMenu, hMenus hTheta]
        simp [typeFutureOffers, typeFutureOffersFuel]
      | visible label =>
        by_cases hClock : e.label.semantic = .tock
        · simp [hClock] at hRef
        have hTarget : t = e.target := by
          cases hFuture : e.future with
          | explicit offers => simp [hClock, hFuture] at hRef
          | «at» s removed =>
            have hs : t = s := by simpa [hClock, hFuture] using hRef
            rw [hs, compileTypeFuel_futureTargetsAreEdgeTargets _ ty e hE s removed hFuture]
        subst t
        have hEdge : (compileType ty).HasEdge q e.environment label
            ⟨e.current, match e.future with
              | .explicit f => f
              | .at s removed => computeFutureOf ty s \ removed⟩ e.target :=
          (compileType_hasEdge_iff_hasResolvedEdge ty _ _ _ _ _).mpr
            ⟨e, hE, hSource, rfl, hLabel, rfl, rfl, rfl⟩
        obtain ⟨target, _, _, hTarget⟩ := hCurrent.2 hTheta hEdge
        refine Or.inl ⟨⟨target, hTarget⟩, Finset.mem_union_left _ ?_⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨e, Finset.mem_filter.mpr ⟨?_, hSource⟩, hRef⟩
        exact Finset.mem_image.mpr ⟨e, hE, by simp [hLabel]⟩
    · obtain ⟨link, hLink', hTarget⟩ := Finset.mem_image.mp hLink
      obtain ⟨hLink', _⟩ := Finset.mem_filter.mp hLink'
      obtain ⟨_, target, _, hTargetRelated, _⟩ :=
        compileTypeMenuLinksFuel_completion_transport _ ty le_rfl link hLink'
      exact Or.inl ⟨⟨target, hTarget ▸ hTargetRelated⟩, Finset.mem_union_right _ hLink⟩
  have hEq := FiniteMenuGraph.menuFrom_eq_of_pruning original stopped contribution
    (fun q => ∃ theta, relationMembership (buildRelationSet ty (compileType ty)) theta q)
    rfl (compiledMenuGraphFuel_referencesClosed _ ty le_rfl hDisjoint) hSubset hStep
    source (relationMembership_state_mem ty rho source hDisjoint hRelated) ⟨rho, hRelated⟩
  rw [hMenu] at hEq
  exact (Finset.filter_biUnion _ _ _).trans hEq

/-- The recursion clause copies precisely the body's optimistic dependencies. -/
theorem compiledMenuGraph_recur (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType) :
    compiledMenuGraphFuel (typeCompilationFuel (.recur alphabet name body))
      (.recur alphabet name body) =
    (buildRecursionAutomaton alphabet name
      (compileTypeFuel (typeCompilationFuel body) body)).toPending.withMenuDependencies
      ((compileTypeMenuLinksFuel (typeCompilationFuel body) body).image fun link =>
        (.child 0 link.1, .child 0 link.2)) := by
  unfold compiledMenuGraphFuel
  rw [Nat.min_self, compileTypeFuel_recur_eq]
  have hFuel : typeCompilationFuel (.recur alphabet name body) =
      typeCompilationFuel body + 1 := by simp only [typeCompilationFuel]; omega
  rw [hFuel]
  simp only [compileTypeMenuLinksFuel]
  rfl

/-- Installing a backedge changes no direct offer or product contribution. -/
theorem compiledMenuContribution_recur_child (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType) (hTail : body.TailOccurrences name True)
    (source : TypeAutomatonState) :
    compiledMenuContribution (.recur alphabet name body) (.child 0 source) =
      compiledMenuContribution body source := by
  have hInfo : stateProductInfo (.recur alphabet name body) (.child 0 source) =
      stateProductInfo body source := by
    unfold stateProductInfo
    rw [show typeCompilationFuel (.recur alphabet name body) =
      typeCompilationFuel body + 1 by simp only [typeCompilationFuel]; omega]
    rfl
  unfold compiledMenuContribution
  rw [compileTypeFuel_recur_eq]
  dsimp only
  rw [hInfo]
  congr 1
  exact buildRecursionAutomaton_offersAt_child alphabet name
    (compileTypeFuel (typeCompilationFuel body) body)
    (compileTypeFuel_markerOffersInert name (typeCompilationFuel body) body hTail) source

/-- The copied-state equation before identifying marker paths with `b_X`.
Stopping markers retains the old carrier and L; it only suppresses their
private bookkeeping references while the new backedges are accounted for. -/
theorem computeFutureOf_recur_child_split (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    (hDisjoint : body.OfferBranchesDisjoint) (hTail : body.TailOccurrences name True)
    (source : TypeAutomatonState)
    (hSource : source ∈ (compileTypeFuel (typeCompilationFuel body) body).states) :
    let fragment := compileTypeFuel (typeCompilationFuel body) body
    let stopped := (markerStoppedFragment fragment name).toPending.withMenuDependencies
      (compileTypeMenuLinksFuel (typeCompilationFuel body) body)
    let menu := fun q => (stopped.menuFrom (compiledMenuContribution body) q).filter
      (fun action => action ∈ alphabet.actions)
    computeFutureOf (.recur alphabet name body) (.child 0 source) =
      menu source ∪
        if ∃ q ∈ stopped.futureReachable source, MarkerSource fragment name q
        then menu fragment.initial else ∅ := by
  intro fragment stopped menu
  have hReach := buildRecursionAutomaton_menuReachable_child alphabet name fragment
    (compileTypeMenuLinksFuel (typeCompilationFuel body) body)
    (referencesClosed_compileTypeFuel body _ le_rfl hDisjoint)
    (compileTypeMenuLinksFuel_targets_mem _ body le_rfl hDisjoint)
    (compileTypeFuel_initial_mem _ body le_rfl) source hSource
  rw [computeFutureOf_eq_menuFrom]
  unfold FiniteMenuGraph.menuFrom
  rw [compiledMenuGraph_recur, hReach, Finset.image_biUnion]
  simp only [compiledMenuContribution_recur_child alphabet name body hTail,
    PactType.alphabet]
  change ((stopped.futureReachable source ∪
    if ∃ q ∈ stopped.futureReachable source, MarkerSource fragment name q
    then stopped.futureReachable fragment.initial else ∅).biUnion
      (compiledMenuContribution body)).filter (fun action => action ∈ alphabet.actions) = _
  split <;> ext action <;>
    simp only [menu, FiniteMenuGraph.menuFrom, Finset.mem_filter, Finset.mem_biUnion,
      Finset.mem_union, Finset.notMem_empty] <;> aesop

/-- At the body entry the additional union is idempotent. -/
theorem computeFutureOf_recur_entry (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    (hDisjoint : body.OfferBranchesDisjoint) (hTail : body.TailOccurrences name True) :
    let fragment := compileTypeFuel (typeCompilationFuel body) body
    let stopped := (markerStoppedFragment fragment name).toPending.withMenuDependencies
      (compileTypeMenuLinksFuel (typeCompilationFuel body) body)
    computeFutureOf (.recur alphabet name body) (.child 0 fragment.initial) =
      (stopped.menuFrom (compiledMenuContribution body) fragment.initial).filter
        (fun action => action ∈ alphabet.actions) := by
  intro fragment stopped
  rw [computeFutureOf_recur_child_split alphabet name body hDisjoint hTail
    fragment.initial (compileTypeFuel_initial_mem _ body le_rfl)]
  split <;> simp only [stopped, fragment, Finset.union_self, Finset.union_empty]

/-- The fresh root reads only the copied body-entry menu, as in the paper. -/
theorem computeFutureOf_recur_root (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType) (hDisjoint : body.OfferBranchesDisjoint) :
    computeFutureOf (.recur alphabet name body) .root =
      computeFutureOf (.recur alphabet name body) (.child 0 (compileType body).initial) := by
  let whole := PactType.recur alphabet name body
  let fragment := compileTypeFuel (typeCompilationFuel whole) whole
  let pending := fragment.toPending
  have hWholeDisjoint : whole.OfferBranchesDisjoint := by
    simpa only [whole, PactType.OfferBranchesDisjoint] using hDisjoint
  have hRefs : pending.referencedStates .root =
      {.child 0 (compileType body).initial} := by
    change (⟨fragment.states, fragment.edges⟩ : PendingAutomaton).referencedStates .root = _
    dsimp only [fragment, whole]
    rw [compileTypeFuel_recur_eq]
    exact buildRecursionAutomaton_referencedStates_root alphabet name _
  have hOffers : pending.offersAt .root = ∅ := by
    change (⟨fragment.states, fragment.edges⟩ : PendingAutomaton).offersAt .root = ∅
    dsimp only [fragment, whole]
    rw [compileTypeFuel_recur_eq]
    ext action
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion, Finset.mem_filter,
      buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union, Finset.mem_image,
      Finset.notMem_empty, iff_false]
    rintro ⟨e, ⟨⟨env, _, rfl⟩ | ⟨ce, _, rfl⟩, hs⟩, ha⟩
    · simp [AutomatonConstructionLabel.semantic, TypeLabel.silent] at ha
    · split at hs <;> simp [childState] at hs
  have hRoot := computeFutureOf_root_decomposition whole .root
    {.child 0 (compileType body).initial} pending rfl
    (referencesClosed_compileTypeFuel whole _ le_rfl hWholeDisjoint)
    (by
      change TypeAutomatonState.root ∈ (compileTypeFuel (typeCompilationFuel whole) whole).states
      rw [compileTypeFuel_recur_eq]
      exact Finset.mem_union_left _ (Finset.mem_singleton_self _))
    (by rw [hRefs]; exact Finset.subset_insert _ _)
    (by rw [hRefs])
    (by
      unfold stateProductInfo
      rw [show typeCompilationFuel whole = typeCompilationFuel body + 1 by
        simp only [whole, typeCompilationFuel]; omega]
      rfl)
    (by intro a ha; rw [hOffers] at ha; exact False.elim (Finset.notMem_empty a ha))
  simpa only [hOffers, Finset.empty_union, Finset.singleton_biUnion] using hRoot

/-- The paper's copied-state equation, now expressed with the ordinary body
menu and marker paths in its full menu graph. -/
theorem computeFutureOf_recur_child_eq (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    (hAlphabet : body.alphabet = alphabet)
    (hDisjoint : body.OfferBranchesDisjoint) (hTail : body.TailClosed)
    (hCurrent : CurrentOfferCorrespondence body) (hMenus : FutureOffersAgree body)
    {rho : PactType} {source : TypeAutomatonState}
    (hRelated : relationMembership (buildRelationSet body (compileType body)) rho source) :
    computeFutureOf (.recur alphabet name body) (.child 0 source) =
      typeFutureOffers rho ∪
        if ∃ q ∈ (compiledMenuGraphFuel (typeCompilationFuel body) body).futureReachable source,
          MarkerSource (compileTypeFuel (typeCompilationFuel body) body) name q
        then typeFutureOffers body else ∅ := by
  have hSource := relationMembership_state_mem body rho source hDisjoint hRelated
  have hEntry := buildRelationSet_initial body (compileType body)
  have hStop := computeFutureOf_markerStopped body name hDisjoint hTail hCurrent hMenus hRelated
  have hStopEntry := computeFutureOf_markerStopped body name hDisjoint hTail hCurrent hMenus hEntry
  rw [hAlphabet] at hStop hStopEntry
  simp only [compileType] at hStopEntry hEntry
  have hEq := computeFutureOf_recur_child_split alphabet name body hDisjoint (hTail name)
    source hSource
  dsimp only at hEq hStop hStopEntry
  rw [hStop, hStopEntry, hMenus hRelated, hMenus hEntry] at hEq
  have hMarker := markerStoppedFragment_menuMarkerReachable_self
    (compileTypeFuel (typeCompilationFuel body) body) name
    (compileTypeMenuLinksFuel (typeCompilationFuel body) body)
    (referencesClosed_compileTypeFuel body _ le_rfl hDisjoint)
    (compileTypeMenuLinksFuel_targets_mem _ body le_rfl hDisjoint) source hSource
  simp only [hMarker] at hEq
  simpa only [compiledMenuGraphFuel, Nat.min_self, AutomatonFragment.toPending] using hEq

/-- The body-entry equation and the child hypothesis close the fresh root. -/
theorem futureOffersAgree_recur_root (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    (hAlphabet : body.alphabet = alphabet)
    (hDisjoint : body.OfferBranchesDisjoint) (hTail : body.TailClosed)
    (hCurrent : CurrentOfferCorrespondence body) (hMenus : FutureOffersAgree body) :
    computeFutureOf (.recur alphabet name body) .root =
      typeFutureOffers (.recur alphabet name body) := by
  rw [computeFutureOf_recur_root alphabet name body hDisjoint]
  change computeFutureOf (.recur alphabet name body)
    (.child 0 (compileTypeFuel (typeCompilationFuel body) body).initial) = _
  rw [computeFutureOf_recur_entry alphabet name body hDisjoint (hTail name)]
  have hEntry := buildRelationSet_initial body (compileType body)
  have hStop := computeFutureOf_markerStopped body name hDisjoint hTail hCurrent hMenus hEntry
  rw [hAlphabet] at hStop
  simp only [compileType] at hStop hEntry
  rw [hStop, hMenus hEntry, typeFutureOffers_recur]

end

end Pact
