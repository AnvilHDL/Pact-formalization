import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.RecursionMenus
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.MarkerMenus

namespace Pact

noncomputable section

open Classical Pact.NewCorrespondence

/-- Stopping bookkeeping references preserves the queried marker observation.
Before that marker is found, every variable source has an empty observation
by the body hypothesis. Execution steps and L retain related residuals. -/
theorem menuMarkerReachable_markerStopped (ty : PactType) (name query : String)
    (hDisjoint : ty.OfferBranchesDisjoint) (hTail : ty.TailClosed)
    (hCurrent : CurrentOfferCorrespondence ty)
    (hMarkers : ∀ rho q,
      relationMembership (buildRelationSet ty (compileType ty)) rho q →
      ((∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel ty) ty).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel ty) ty) query reached) ↔
        menuReachesVar query rho = true))
    {rho : PactType} {source : TypeAutomatonState}
    (hRelated : relationMembership (buildRelationSet ty (compileType ty)) rho source) :
    (∃ reached ∈ ((markerStoppedFragment (compileTypeFuel (typeCompilationFuel ty) ty)
      name).toPending.withMenuDependencies
        (compileTypeMenuLinksFuel (typeCompilationFuel ty) ty)).futureReachable source,
      MarkerSource (compileTypeFuel (typeCompilationFuel ty) ty) query reached) ↔
    (∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel ty) ty).futureReachable source,
      MarkerSource (compileTypeFuel (typeCompilationFuel ty) ty) query reached) := by
  let fragment := compileTypeFuel (typeCompilationFuel ty) ty
  let original := compiledMenuGraphFuel (typeCompilationFuel ty) ty
  let stopped := (markerStoppedFragment fragment name).toPending.withMenuDependencies
    (compileTypeMenuLinksFuel (typeCompilationFuel ty) ty)
  let token : BareMessage := (query, .send)
  let observation : TypeAutomatonState → Finset BareMessage :=
    fun q => if MarkerSource fragment query q then {token} else ∅
  have hObservation : ∀ (graph : FiniteMenuGraph) q,
      token ∈ graph.menuFrom observation q ↔
        ∃ reached ∈ graph.futureReachable q, MarkerSource fragment query reached := by
    intro graph q
    have hAt : ∀ reached, token ∈ observation reached ↔ MarkerSource fragment query reached := by
      intro reached
      by_cases hMarker : MarkerSource fragment query reached <;> simp [observation, hMarker]
    simp only [FiniteMenuGraph.menuFrom, Finset.mem_biUnion, hAt]
  have hClosed : original.ReferencesClosed :=
    compiledMenuGraphFuel_referencesClosed _ ty le_rfl hDisjoint
  have hSource : source ∈ original.states :=
    relationMembership_state_mem ty rho source hDisjoint hRelated
  have hSubset : ∀ q, stopped.referencedStates q ⊆ original.referencedStates q := by
    intro q
    simp only [original, compiledMenuGraphFuel, Nat.min_self,
      PendingAutomaton.withMenuDependencies]
    change _ ∪ _ ⊆ fragment.toPending.menuStep q ∪ _
    exact Finset.union_subset_union
      (markerStoppedFragment_menuStep_subset fragment name q) (Finset.Subset.refl _)
  have hStoppedClosed : stopped.ReferencesClosed := by
    intro q hq t ht
    exact hClosed q hq (hSubset q ht)
  constructor
  · rintro ⟨q, hq, hm⟩
    have hReach := FiniteMenuGraph.futureReachable_image_subset_of_embedding stopped original id
      (by intro q; simpa using hSubset q) hClosed source hSource
    exact ⟨q, hReach (by simpa using hq), hm⟩
  · intro hOriginal
    by_contra hNone
    have hReachStep : ∀ q ∈ stopped.futureReachable source,
        ∀ t ∈ stopped.referencedStates q, t ∈ stopped.futureReachable source := by
      intro q hq t ht
      have hqState := stopped.futureReachable_subset_of_reference_closed source
        stopped.states hSource hStoppedClosed hq
      exact stopped.futureReachable_subset_of_mem hStoppedClosed hSource hq
        (stopped.referencedStates_subset_futureReachable q hStoppedClosed hqState ht)
    have hStep : ∀ q,
        ((∃ theta, relationMembership (buildRelationSet ty (compileType ty)) theta q) ∧
          q ∈ stopped.futureReachable source) →
        ∀ t ∈ original.referencedStates q,
          (((∃ theta, relationMembership (buildRelationSet ty (compileType ty)) theta t) ∧
            t ∈ stopped.futureReachable source) ∧ t ∈ stopped.referencedStates q) ∨
          original.menuFrom observation q = ∅ := by
      rintro q ⟨⟨theta, hTheta⟩, hqReach⟩ t ht
      simp only [original, compiledMenuGraphFuel, Nat.min_self,
        PendingAutomaton.withMenuDependencies] at ht
      change t ∈ fragment.toPending.menuStep q ∪
        menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel ty) ty) q at ht
      rcases Finset.mem_union.mp ht with hExecution | hLink
      · obtain ⟨e, hE, hRef⟩ := Finset.mem_biUnion.mp hExecution
        obtain ⟨hE, hSourceE⟩ := Finset.mem_filter.mp hE
        cases hLabel : e.label with
        | «variable» other =>
          have hDistinct : query ≠ other := by
            intro hEq
            exact hNone ⟨q, hqReach, e, hE, hSourceE, hEq ▸ hLabel⟩
          obtain ⟨a, rfl⟩ := (markerSource_iff_var_residual ty other (hTail other)
            hTheta).mp ⟨e, hE, hSourceE, hLabel⟩
          have hNoMarker : ¬ ∃ reached ∈ original.futureReachable q,
              MarkerSource fragment query reached := by
            intro h
            have hTest := (hMarkers (.var a other) q hTheta).mp h
            simp [menuReachesVar_var, hDistinct] at hTest
          right
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro action hAction
          obtain ⟨reached, hReached, hAction⟩ := Finset.mem_biUnion.mp hAction
          have hMarker : MarkerSource fragment query reached := by
            by_contra hNot
            simp [observation, hNot] at hAction
          exact hNoMarker ⟨reached, hReached, hMarker⟩
        | visible label =>
          by_cases hClock : e.label.semantic = .tock
          · simp [hClock] at hRef
          have hTarget : t = e.target := by
            simpa only [if_neg hClock, Finset.mem_singleton] using hRef
          subst t
          have hEdge : (compileType ty).HasEdge q e.environment label
              ⟨e.current, resolveFutureSpec (computeFutureOf ty) e.future⟩ e.target :=
            (compileType_hasEdge_iff_hasResolvedEdge ty _ _ _ _ _).mpr
              ⟨e, hE, hSourceE, rfl, hLabel, rfl, rfl, rfl⟩
          obtain ⟨target, _, _, hTarget⟩ := hCurrent.2 hTheta hEdge
          have hRetained : e.target ∈ stopped.referencedStates q := by
            apply Finset.mem_union_left
            apply Finset.mem_biUnion.mpr
            refine ⟨e, Finset.mem_filter.mpr ⟨?_, hSourceE⟩, hRef⟩
            exact Finset.mem_filter.mpr ⟨hE, by simp [hLabel]⟩
          exact Or.inl ⟨⟨⟨target, hTarget⟩, hReachStep q hqReach _ hRetained⟩, hRetained⟩
      · obtain ⟨link, hLink', hTarget⟩ := Finset.mem_image.mp hLink
        obtain ⟨hLink', _⟩ := Finset.mem_filter.mp hLink'
        obtain ⟨_, target, _, hTargetRelated, _⟩ :=
          compileTypeMenuLinksFuel_completion_transport _ ty le_rfl link hLink'
        have hRetained : t ∈ stopped.referencedStates q := Finset.mem_union_right _ hLink
        exact Or.inl ⟨⟨⟨target, hTarget ▸ hTargetRelated⟩,
          hReachStep q hqReach t hRetained⟩, hRetained⟩
    have hEq := FiniteMenuGraph.menuFrom_eq_of_pruning original stopped observation
      (fun q => (∃ theta, relationMembership (buildRelationSet ty (compileType ty)) theta q) ∧
        q ∈ stopped.futureReachable source)
      rfl hClosed hSubset hStep source hSource
      ⟨⟨rho, hRelated⟩, stopped.mem_futureReachable_self source⟩
    have hToken := (hObservation original source).mpr hOriginal
    rw [← hEq] at hToken
    exact hNone ((hObservation stopped source).mp hToken)

/-- Installing Y backedges reaches X either in the body copy or through Y
followed by a path from the body entry. All paths include the unchanged L. -/
theorem menuMarkerReachable_recur_child (alphabet : PactTypeAlphabet)
    (name query : String) (body : PactType) (hDistinct : query ≠ name)
    (hDisjoint : body.OfferBranchesDisjoint) (hTail : body.TailClosed)
    (hCurrent : CurrentOfferCorrespondence body)
    (hMarkers : ∀ rho q,
      relationMembership (buildRelationSet body (compileType body)) rho q →
      ((∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel body) body).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel body) body) query reached) ↔
        menuReachesVar query rho = true))
    {rho : PactType} {source : TypeAutomatonState}
    (hRelated : relationMembership (buildRelationSet body (compileType body)) rho source) :
    (∃ reached ∈ (compiledMenuGraphFuel
      (typeCompilationFuel (.recur alphabet name body))
      (.recur alphabet name body)).futureReachable (.child 0 source),
      MarkerSource (compileTypeFuel (typeCompilationFuel (.recur alphabet name body))
        (.recur alphabet name body)) query reached) ↔
    (∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel body) body).futureReachable source,
      MarkerSource (compileTypeFuel (typeCompilationFuel body) body) query reached) ∨
    ((∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel body) body).futureReachable source,
        MarkerSource (compileTypeFuel (typeCompilationFuel body) body) name reached) ∧
      (∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel body) body).futureReachable
        (compileTypeFuel (typeCompilationFuel body) body).initial,
        MarkerSource (compileTypeFuel (typeCompilationFuel body) body) query reached)) := by
  let fragment := compileTypeFuel (typeCompilationFuel body) body
  let links := compileTypeMenuLinksFuel (typeCompilationFuel body) body
  let stopped := (markerStoppedFragment fragment name).toPending.withMenuDependencies links
  have hSource := relationMembership_state_mem body rho source hDisjoint hRelated
  have hEntry := buildRelationSet_initial body (compileType body)
  simp only [compileType] at hEntry
  have hStop := menuMarkerReachable_markerStopped body name query hDisjoint hTail
    hCurrent hMarkers hRelated
  have hStopEntry := menuMarkerReachable_markerStopped body name query hDisjoint hTail
    hCurrent hMarkers hEntry
  have hStopName := markerStoppedFragment_menuMarkerReachable_self fragment name links
    (compileTypeFuel_menuClosed _ body le_rfl hDisjoint)
    (compileTypeMenuLinksFuel_targets_mem _ body le_rfl hDisjoint) source hSource
  have hGraph : compiledMenuGraphFuel (typeCompilationFuel body) body =
      fragment.toPending.withMenuDependencies links := by
    simp only [compiledMenuGraphFuel, Nat.min_self]
    rfl
  rw [← hGraph] at hStopName
  have hReach := buildRecursionAutomaton_menuReachable_child alphabet name fragment links
    (compileTypeFuel_menuClosed _ body le_rfl hDisjoint)
    (compileTypeMenuLinksFuel_targets_mem _ body le_rfl hDisjoint)
    (compileTypeFuel_initial_mem _ body le_rfl) source hSource
  rw [compiledMenuGraph_recur, hReach, compileTypeFuel_recur_eq]
  have hSplit :
      (∃ reached ∈ (stopped.futureReachable source ∪
        if ∃ q ∈ stopped.futureReachable source, MarkerSource fragment name q
        then stopped.futureReachable fragment.initial else ∅).image (.child 0),
        MarkerSource (buildRecursionAutomaton alphabet name fragment) query reached) ↔
      (∃ reached ∈ stopped.futureReachable source, MarkerSource fragment query reached) ∨
      ((∃ reached ∈ stopped.futureReachable source, MarkerSource fragment name reached) ∧
        (∃ reached ∈ stopped.futureReachable fragment.initial,
          MarkerSource fragment query reached)) := by
    constructor
    · rintro ⟨_, hReached, hMarker⟩
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hReached
      have hm := (buildRecursionAutomaton_markerSource_child alphabet name query fragment
        hDistinct q).mp hMarker
      rcases Finset.mem_union.mp hq with hq | hq
      · exact Or.inl ⟨q, hq, hm⟩
      · split at hq
        · exact Or.inr ⟨by assumption, q, hq, hm⟩
        · exact False.elim (Finset.notMem_empty q hq)
    · rintro (⟨q, hq, hm⟩ | ⟨hName, q, hq, hm⟩)
      · exact ⟨.child 0 q, Finset.mem_image.mpr ⟨q, Finset.mem_union_left _ hq, rfl⟩,
          (buildRecursionAutomaton_markerSource_child alphabet name query fragment
            hDistinct q).mpr hm⟩
      · refine ⟨.child 0 q, Finset.mem_image.mpr ⟨q, Finset.mem_union_right _ ?_, rfl⟩,
          (buildRecursionAutomaton_markerSource_child alphabet name query fragment
            hDistinct q).mpr hm⟩
        simpa only [if_pos hName] using hq
  exact hSplit.trans (or_congr hStop (and_congr hStopName hStopEntry))

/-- The fresh header contributes no marker and refers only to the copied entry. -/
theorem menuMarkerReachable_recur_root_child (alphabet : PactTypeAlphabet)
    (name query : String) (body : PactType) (hDisjoint : body.OfferBranchesDisjoint) :
    (∃ reached ∈ (compiledMenuGraphFuel
      (typeCompilationFuel (.recur alphabet name body))
      (.recur alphabet name body)).futureReachable .root,
      MarkerSource (compileTypeFuel (typeCompilationFuel (.recur alphabet name body))
        (.recur alphabet name body)) query reached) ↔
    (∃ reached ∈ (compiledMenuGraphFuel
      (typeCompilationFuel (.recur alphabet name body))
      (.recur alphabet name body)).futureReachable
        (.child 0 (compileTypeFuel (typeCompilationFuel body) body).initial),
      MarkerSource (compileTypeFuel (typeCompilationFuel (.recur alphabet name body))
        (.recur alphabet name body)) query reached) := by
  let whole := PactType.recur alphabet name body
  let graph := compiledMenuGraphFuel (typeCompilationFuel whole) whole
  let entry := TypeAutomatonState.child 0
    (compileTypeFuel (typeCompilationFuel body) body).initial
  have hWholeDisjoint : whole.OfferBranchesDisjoint := by
    simpa only [whole, PactType.OfferBranchesDisjoint] using hDisjoint
  have hClosed : graph.ReferencesClosed :=
    compiledMenuGraphFuel_referencesClosed _ whole le_rfl hWholeDisjoint
  have hRoot : TypeAutomatonState.root ∈ graph.states := by
    change TypeAutomatonState.root ∈ (compileTypeFuel (typeCompilationFuel whole) whole).states
    rw [compileTypeFuel_recur_eq]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
  have hReferences : graph.referencedStates .root = {entry} := by
    dsimp only [graph, whole]
    rw [compiledMenuGraph_recur]
    change (buildRecursionAutomaton alphabet name
      (compileTypeFuel (typeCompilationFuel body) body)).toPending.menuStep .root ∪
      menuDependencyTargets _ .root = _
    rw [menuDependencyTargets_child_root, Finset.union_empty]
    exact buildRecursionAutomaton_menuStep_root alphabet name _
  have hReach := graph.futureReachable_eq_self_union_biUnion .root {entry}
    hClosed hRoot (by rw [hReferences]; exact Finset.subset_insert _ _) (by rw [hReferences])
  simp only [Finset.singleton_biUnion] at hReach
  change (∃ reached ∈ graph.futureReachable .root,
    MarkerSource (compileTypeFuel (typeCompilationFuel whole) whole) query reached) ↔
    (∃ reached ∈ graph.futureReachable entry,
      MarkerSource (compileTypeFuel (typeCompilationFuel whole) whole) query reached)
  rw [hReach]
  constructor
  · rintro ⟨q, hq, hm⟩
    rcases Finset.mem_union.mp hq with hq | hq
    · have hq' : q = .root := Finset.mem_singleton.mp hq
      subst q
      rw [compileTypeFuel_recur_eq] at hm
      exact False.elim (not_buildRecursionAutomaton_markerSource_root alphabet name query _ hm)
    · exact ⟨q, hq, hm⟩
  · rintro ⟨q, hq, hm⟩
    exact ⟨q, Finset.mem_union_right _ hq, hm⟩

/-- At the entry, the possible backedge adds only paths already present there. -/
theorem menuMarkerReachable_recur_root (alphabet : PactTypeAlphabet)
    (name query : String) (body : PactType) (hDistinct : query ≠ name)
    (hDisjoint : body.OfferBranchesDisjoint) (hTail : body.TailClosed)
    (hCurrent : CurrentOfferCorrespondence body)
    (hMarkers : ∀ rho q,
      relationMembership (buildRelationSet body (compileType body)) rho q →
      ((∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel body) body).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel body) body) query reached) ↔
        menuReachesVar query rho = true)) :
    (∃ reached ∈ (compiledMenuGraphFuel
      (typeCompilationFuel (.recur alphabet name body))
      (.recur alphabet name body)).futureReachable .root,
      MarkerSource (compileTypeFuel (typeCompilationFuel (.recur alphabet name body))
        (.recur alphabet name body)) query reached) ↔
    (∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel body) body).futureReachable
      (compileTypeFuel (typeCompilationFuel body) body).initial,
      MarkerSource (compileTypeFuel (typeCompilationFuel body) body) query reached) := by
  have hEntry := buildRelationSet_initial body (compileType body)
  simp only [compileType] at hEntry
  rw [menuMarkerReachable_recur_root_child alphabet name query body hDisjoint,
    menuMarkerReachable_recur_child alphabet name query body hDistinct hDisjoint hTail
      hCurrent hMarkers hEntry]
  constructor
  · rintro (h | ⟨_, h⟩) <;> exact h
  · exact Or.inl

end

end Pact
