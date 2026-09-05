import Anvilpp.PactTypes.NewCorrespondence.Simultaneous.SequenceMarkerPaths
import Anvilpp.PactTypes.NewCorrespondence.Simultaneous.RecursionMarkerPaths
import Anvilpp.PactTypes.NewCorrespondence.Simultaneous.BasicMarkerPaths

namespace Pact

noncomputable section

open Classical

/-- The nested-recursion case identifies the backedge path equation with the
syntax substitution equation, using the same two body hypotheses. -/
theorem markerReachable_iff_menuReachesVar_recur
    (alphabet : PactTypeAlphabet) (binder : String) (body : PactType) (name : String)
    {bound : List String} (hWF : TypeWellFormedIn bound (.recur alphabet binder body))
    (hName : name ∈ bound) (hCurrent : CurrentOfferCorrespondence body)
    (hQuery : ∀ rho q,
      relationMembership (buildRelationSet body (compileType body)) rho q →
      ((∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel body) body).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel body) body) name reached) ↔
        menuReachesVar name rho = true))
    (hBinder : ∀ rho q,
      relationMembership (buildRelationSet body (compileType body)) rho q →
      ((∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel body) body).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel body) body) binder reached) ↔
        menuReachesVar binder rho = true))
    {rho q} (hRelated : relationMembership
      (buildRelationSet (.recur alphabet binder body) (compileType (.recur alphabet binder body)))
      rho q) :
    (∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel (.recur alphabet binder body))
        (.recur alphabet binder body)).futureReachable q,
      MarkerSource (compileTypeFuel (typeCompilationFuel (.recur alphabet binder body))
        (.recur alphabet binder body)) name reached) ↔ menuReachesVar name rho = true := by
  have hBodyWF := typeWellFormedIn_recur hWF
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hBodyWF
  have hTail := hBodyWF.2.2.2.1
  have hHygiene := hWF.2.2.1
  simp only [PactType.BinderHygienic] at hHygiene
  have hDistinct : name ≠ binder := fun h => hHygiene.1 (h ▸ hName)
  have hEntry := hQuery body _ (buildRelationSetCoreFuel_initial_mem _ body
    (typeCompilationFuel_sufficient body))
  rcases relationMembership_recur_cases alphabet binder body hRelated with
    hRoot | ⟨source, residual, hPair, hChild⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hRoot
    rw [menuMarkerReachable_recur_root alphabet binder name body hDistinct hDisjoint hTail
      hCurrent hQuery, hEntry,
      menuReachesVar_recur name binder alphabet body (hTail name), if_neg hDistinct]
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hPair
    rw [menuMarkerReachable_recur_child alphabet binder name body hDistinct hDisjoint hTail
      hCurrent hQuery hChild, hQuery residual source hChild, hBinder residual source hChild, hEntry]
    have hResidualQuery := relationMembership_tailOccurrences body residual source name True
      hBodyWF.2.2.2.2.2.1 (hTail name) hChild
    have hResidualBinder := relationMembership_tailOccurrences body residual source binder True
      hBodyWF.2.2.2.2.2.1 (hTail binder) hChild
    have hFresh := relationMembership_binderFreshFor body residual source (binder :: bound)
      (PactType.binderHygienic_binderFreshFor body (binder :: bound) hBodyWF.2.2.1) hChild
    rw [menuReachesVar_replaceVar name binder (.recur alphabet binder body) hDistinct
      (hWF.2.2.2.1 name) (binder :: bound) (List.mem_cons_of_mem binder hName) residual
      hResidualQuery hResidualBinder hFresh,
      menuReachesVar_recur name binder alphabet body (hTail name), if_neg hDistinct]
    simp only [Bool.or_eq_true, Bool.and_eq_true]

/-- The paper's marker-path equivalence, by compiler rank. The current-offer
hypotheses come from the surrounding simultaneous induction at smaller ranks. -/
theorem markerReachable_iff_menuReachesVar_of_current (ty : PactType) :
    ∀ (bound : List String) (_ : TypeWellFormedIn bound ty)
      (_ : ∀ child childBound, typeCompilationFuel child < typeCompilationFuel ty →
        TypeWellFormedIn childBound child → CurrentOfferCorrespondence child)
      (name : String) (_ : name ∈ bound)
      {rho : PactType} {q : TypeAutomatonState}
      (_ : relationMembership (buildRelationSet ty (compileType ty)) rho q),
      (∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel ty) ty).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel ty) ty) name reached) ↔
        menuReachesVar name rho = true := by
  induction hFuel : typeCompilationFuel ty using Nat.strong_induction_on generalizing ty with
  | h n ih =>
    subst n
    intro bound hWF hCurrent name hName rho q hRelated
    have hChild (child : PactType) (hLt : typeCompilationFuel child < typeCompilationFuel ty)
        (childBound : List String) (hChildWF : TypeWellFormedIn childBound child)
        (query : String) (hQuery : query ∈ childBound)
        {residual : PactType} {state : TypeAutomatonState}
        (hRel : relationMembership (buildRelationSet child (compileType child)) residual state) :
        (∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel child) child).futureReachable state,
          MarkerSource (compileTypeFuel (typeCompilationFuel child) child) query reached) ↔
          menuReachesVar query residual = true := by
      exact ih _ (by omega) child rfl childBound hChildWF
        (fun grandchild grandBound hGrand hGrandWF =>
          hCurrent grandchild grandBound (Nat.lt_trans hGrand hLt) hGrandWF)
        query hQuery hRel
    cases ty with
    | skip a => exact compiledMenuMarkerPath_skip a name hRelated
    | message a m d => exact compiledMenuMarkerPath_message a m d name hRelated
    | progress a p => exact compiledMenuMarkerPath_progress a p name hRelated
    | tock a => exact compiledMenuMarkerPath_tock a name hRelated
    | var a x => exact compiledMenuMarkerPath_var a x name hRelated
    | choice a left right =>
      obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_choice hWF
      exact compiledMenuMarkerPath_choice a left right name hWF
        (hChild left (by simp only [typeCompilationFuel]; omega) bound hLeftWF name hName)
        (hChild right (by simp only [typeCompilationFuel]; omega) bound hRightWF name hName) hRelated
    | fairChoice a tag left right =>
      obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_fairChoice hWF
      exact compiledMenuMarkerPath_fairChoice a tag left right name hWF
        (hChild left (by simp only [typeCompilationFuel]; omega) bound hLeftWF name hName)
        (hChild right (by simp only [typeCompilationFuel]; omega) bound hRightWF name hName) hRelated
    | seq a left right =>
      obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_seq hWF
      exact markerReachable_iff_menuReachesVar_seq a left right name hWF
        (hCurrent left bound (by simp only [typeCompilationFuel]; omega) hLeftWF)
        (hChild right (by simp only [typeCompilationFuel]; omega) bound hRightWF name hName) hRelated
    | par a left right interface =>
      exact compiledMenuMarkerPath_of_absent _ name hWF.2.2.2.2.2.1
        (by simpa only [PactType.TailOccurrences] using hWF.2.2.2.1 name) hRelated
    | recur a binder body =>
      have hBodyWF := typeWellFormedIn_recur hWF
      have hBodyLt : typeCompilationFuel body < typeCompilationFuel (.recur a binder body) := by
        simp only [typeCompilationFuel]; omega
      exact markerReachable_iff_menuReachesVar_recur a binder body name hWF hName
        (hCurrent body (binder :: bound) hBodyLt hBodyWF)
        (fun _ _ hRel => hChild body hBodyLt (binder :: bound) hBodyWF name
          (List.mem_cons_of_mem binder hName) hRel)
        (fun _ _ hRel => hChild body hBodyLt (binder :: bound) hBodyWF binder
          (List.mem_cons_self) hRel) hRelated
    | xoffer a body branches =>
      obtain ⟨hBodyWF, hBranchWF⟩ := typeWellFormedIn_xoffer hWF
      have hBranchLt : ∀ entry ∈ branches,
          typeCompilationFuel entry.2 < typeCompilationFuel (.xoffer a body branches) := by
        intro entry hEntry
        have := typeCompilationFuel_le_typeBranchCompilationFuel branches entry hEntry
        simp only [typeCompilationFuel]; omega
      exact compiledMenuMarkerPath_xoffer a body branches name hWF
        (hChild body (by simp only [typeCompilationFuel]; omega) bound hBodyWF name hName)
        (fun entry hEntry => hChild entry.2 (hBranchLt entry hEntry) bound
          (hBranchWF entry hEntry) name hName) hRelated
    | offer a body branches =>
      obtain ⟨hBodyWF, _⟩ := typeWellFormedIn_offer hWF
      exact compiledMenuMarkerPath_offer a body branches name hWF
        (hChild body (by simp only [typeCompilationFuel]; omega) bound hBodyWF name hName) hRelated

end

end Pact
