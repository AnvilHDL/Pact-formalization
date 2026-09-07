import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.Recursion
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.FutureFieldShape
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.MarkerMenus
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.MenuReferenceShape
import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.RecursionTargetFields
import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.RecursionStoredFields

namespace Pact

noncomputable section

open Classical Pact.NewCorrespondence

private def SourceMenuField (source : PactType) (env : TypeEnvironment)
    (removed : Finset BareMessage) : Prop :=
  match source with
  | .choice _ _ _ | .fairChoice _ _ _ _ => removed = ∅
  | .xoffer _ _ branches => TypeResolved env branches ∧ removed = typeBranchActions branches
  | _ => False

private theorem sourceMenuField_replaceVar (name : String) (replacement source : PactType)
    (env : TypeEnvironment) (removed : Finset BareMessage)
    (hField : SourceMenuField source env removed) :
    SourceMenuField (source.replaceVar name replacement) env removed := by
  cases source <;> simp_all only [SourceMenuField, PactType.replaceVar,
    TypeResolved_replaceBranches, PactType.typeBranchActions_replaceBranches, and_self]

private theorem sourceMenuField_future {source target : PactType} {env : TypeEnvironment}
    {label : TypeLabel} {current future removed : Finset BareMessage}
    (hField : SourceMenuField source env removed)
    (hOffers : TypeOffers env source label target current future) :
    future = typeFutureOffers source \ removed := by
  cases source with
  | choice a left right | fairChoice a bid left right =>
    simp only [SourceMenuField] at hField
    subst removed
    cases hOffers <;> simp
  | xoffer a other branches =>
    exact hOffers.xoffer_future_eq.trans (by rw [if_pos hField.1, hField.2])
  | _ => exact hField.elim

private def SourceFieldRepresented
    (relation : Finset (PactType × TypeAutomatonState)) (edge : PendingAutomatonEdge) : Prop :=
  ∀ reference removed, edge.future = .at reference removed → reference ≠ edge.target →
    ∃ source, (source, edge.source) ∈ relation ∧ SourceMenuField source edge.environment removed

private theorem sourceFieldRepresented_child
    (relation childRelation : Finset (PactType × TypeAutomatonState))
    (index : Nat) (edge : PendingAutomatonEdge)
    (hEdge : SourceFieldRepresented childRelation edge)
    (hLift : ∀ rho q, (rho, q) ∈ childRelation →
      (rho, TypeAutomatonState.child index q) ∈ relation) :
    SourceFieldRepresented relation (childPendingEdge index edge) := by
  intro reference removed hFuture hNotTarget
  obtain ⟨child, hField, rfl⟩ := childFutureSpec_at index edge.future reference removed hFuture
  obtain ⟨source, hRelated, hSource⟩ := hEdge child removed hField
    (fun h => hNotTarget (congrArg (childState index) h))
  exact ⟨source, hLift _ _ hRelated, hSource⟩

private theorem compileTypeFuel_sourceFieldRepresented :
    ∀ fuel ty, typeCompilationFuel ty ≤ fuel →
      ∀ edge ∈ (compileTypeFuel fuel ty).edges,
        SourceFieldRepresented (buildRelationSetCoreFuel fuel ty) edge := by
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
        SourceFieldRepresented (buildRelationSetCoreFuel (fuel + 1) ty) edge := by
      obtain ⟨childEdge, hChild, rfl⟩ := Finset.mem_image.mp hCopied
      exact sourceFieldRepresented_child _ _ index childEdge
        (ih child hChildFuel childEdge hChild) hLift
    cases ty with
    | skip a | var a name =>
      intro reference removed hFuture hNotTarget
      simp only [compileTypeFuel, finishAutomatonFragment,
        Finset.mem_image, Finset.mem_filter] at hEdge
      obtain ⟨env, _, rfl⟩ := hEdge
      simp_all
    | message a msg dir =>
      intro reference removed hFuture hNotTarget
      simp only [compileTypeFuel, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with (⟨env, _, rfl⟩ | ⟨env, _, rfl⟩) | ⟨env, _, rfl⟩ <;> simp_all
    | progress a pid =>
      intro reference removed hFuture hNotTarget
      simp only [compileTypeFuel, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with ⟨env, _, rfl⟩ | ⟨env, _, rfl⟩ <;> simp_all
    | tock a =>
      intro reference removed hFuture hNotTarget
      simp only [compileTypeFuel, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with ⟨env, _, rfl⟩ | ⟨env, _, rfl⟩
      · split at hFuture <;> simp_all
      · simp_all
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
      · intro reference removed hFuture _
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton] at hRoot
        obtain ⟨env, _, hCase⟩ := hRoot
        rcases hCase with rfl | rfl <;>
          simp only [FutureSpec.at.injEq] at hFuture <;>
          obtain ⟨rfl, rfl⟩ := hFuture <;>
          first
          | (refine ⟨.choice a left right, ?_, rfl⟩
             rw [buildRelationSetCoreFuel]
             exact Finset.mem_insert_self _ _)
          | (refine ⟨.fairChoice a bid left right, ?_, rfl⟩
             rw [buildRelationSetCoreFuel]
             exact Finset.mem_insert_self _ _)
    | recur a name body =>
      have hBody : typeCompilationFuel body ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      intro reference removed hFuture hNotTarget
      simp only [compileTypeFuel, buildRecursionAutomaton, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image] at hEdge
      rcases hEdge with ⟨env, _, rfl⟩ | ⟨child, hChild, rfl⟩
      · simp_all
      · by_cases hMarker : child.label = .variable name
        · simp_all [hMarker]
        · simp only [if_neg hMarker] at hFuture hNotTarget ⊢
          obtain ⟨q, hField, rfl⟩ := childFutureSpec_at 0 child.future reference removed hFuture
          obtain ⟨source, hSource, hShape⟩ := ih body hBody child hChild q removed hField
            (fun h => hNotTarget (congrArg (childState 0) h))
          refine ⟨source.replaceVar name (.recur a name body), ?_,
            sourceMenuField_replaceVar name (.recur a name body) source _ _ hShape⟩
          rw [buildRelationSetCoreFuel]
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
            ⟨(source, child.source), hSource, rfl⟩)
    | seq a left right =>
      have hRight : typeCompilationFuel right ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
      simp only [compileTypeFuel, buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with (hLeftEdge | hRightEdge) | hRedirect
      · intro reference removed hFuture _
        simp only [sequenceLeftEdges, Finset.mem_image, Finset.mem_filter] at hLeftEdge
        obtain ⟨child, _, rfl⟩ := hLeftEdge
        simp only [sequenceKeptLeftEdge, sequenceLeftFutureSpec] at hFuture
        split_ifs at hFuture
      · exact hCopy right 1 hRight (by
          intro rho q hRelated
          rw [buildRelationSetCoreFuel]
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(rho, q), hRelated, rfl⟩)) hRightEdge
      · intro reference removed hFuture _
        simp only [sequenceRedirectEdges, Finset.mem_image, Finset.mem_filter] at hRedirect
        obtain ⟨child, _, rfl⟩ := hRedirect
        simp only [sequenceRedirectEdge, sequenceLeftFutureSpec] at hFuture
        split_ifs at hFuture
    | par a left right interface =>
      intro reference removed hFuture _
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
      simp only [compileTypeFuel, buildExclusiveOfferAutomaton, buildSelectedConjunctiveOfferAutomaton,
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
          have hMember : entry.1 ∈ branches := by
            obtain ⟨hBound, hValue⟩ := List.mem_zipIdx' hEntry
            simp [hValue, List.getElem_mem hBound]
          apply hCopy _ (entry.2 + 1) ?_ ?_ hCopyEdge
          · first
            | have := typeCompilationFuel_le_typeBranchCompilationFuel branches entry.1 hMember
              simp [typeCompilationFuel] at hFuel; omega
            | rw [typeCompilationFuel_parallelTypeBranchesSelecting]
              simp [typeCompilationFuel] at hFuel; omega
          · intro rho q hRelated
            simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
              mem_foldl_union_iff, Finset.mem_image]
            exact Or.inr (Or.inr (Or.inr ⟨entry, hEntry, (rho, q), hRelated, rfl⟩))
      · intro reference removed hFuture hNotTarget
        rw [mem_foldl_union_iff] at hBranch
        rcases hBranch with hEmpty | ⟨entry, _, hNew⟩
        · simp at hEmpty
        · obtain ⟨env, hEnv, rfl⟩ := Finset.mem_image.mp hNew
          first
          | exact (hNotTarget (FutureSpec.at.inj hFuture).1.symm).elim
          | obtain ⟨rfl, rfl⟩ := FutureSpec.at.inj hFuture
            exact ⟨.xoffer a other branches, by simp only [buildRelationSetCoreFuel,
              Finset.mem_insert, true_or],
              (Finset.mem_filter.mp hEnv).2.2, rfl⟩
      · intro reference removed hFuture hNotTarget
        obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hWait
        exact (hNotTarget (FutureSpec.at.inj hFuture).1.symm).elim
      · intro reference removed hFuture hNotTarget
        obtain ⟨env, hEnv, rfl⟩ := Finset.mem_image.mp hDefault
        first
        | exact (hNotTarget (FutureSpec.at.inj hFuture).1.symm).elim
        | obtain ⟨rfl, rfl⟩ := FutureSpec.at.inj hFuture
          exact ⟨.xoffer a other branches, by simp only [buildRelationSetCoreFuel,
            Finset.mem_insert, true_or],
            (Finset.mem_filter.mp hEnv).2.2.2, rfl⟩

/-- A non-target plain field reads the source menu with the same mask after substitution. -/
theorem TypeOffers.replaceVar_compiled_at_source_future
    (ty : PactType) (name : String) (replacement : PactType)
    (menus : TypeAutomatonState → Finset BareMessage)
    (hMenus : ∀ rho q,
      relationMembership (buildRelationSet ty (compileType ty)) rho q →
        menus q = typeFutureOffers (rho.replaceVar name replacement))
    {source target : PactType} (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel (typeCompilationFuel ty) ty).edges)
    (reference : TypeAutomatonState) (removed : Finset BareMessage)
    (hField : edge.future = .at reference removed) (hNotTarget : reference ≠ edge.target)
    (hRelated : relationMembership (buildRelationSet ty (compileType ty)) source edge.source)
    {future : Finset BareMessage}
    (hOffers : TypeOffers edge.environment (source.replaceVar name replacement)
      edge.label.semantic target edge.current future) :
    future = resolveFutureSpec menus edge.future := by
  obtain ⟨original, hOriginal, hShape⟩ := compileTypeFuel_sourceFieldRepresented
    (typeCompilationFuel ty) ty le_rfl edge hEdge reference removed hField hNotTarget
  have hEq := buildRelationSetCoreFuel_functional (typeCompilationFuel ty) ty hRelated hOriginal
  subst original
  have hSource := ((compileTypeFuel_at_endpoint (typeCompilationFuel ty) ty edge hEdge
    reference removed hField).2).resolve_right hNotTarget
  rw [hField, resolveFutureSpec, hSource, hMenus _ _ hRelated]
  exact sourceMenuField_future (sourceMenuField_replaceVar name replacement source _ _ hShape) hOffers


/-- With a false left flag, the right continuation contributes no menu before substitution or after it. -/
theorem TypeOffers.replaceVar_seq_incomplete
    (name : String) (replacement : PactType)
    {env : TypeEnvironment} {alphabet : PactTypeAlphabet} {left right target : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.seq alphabet left right) label target current future)
    (hLeftRec : left.TailRecursive) (hLeftTail : left.TailOccurrences name False)
    (hIncomplete : left.CanCompleteDeclared = false) :
    TypeOffers env ((PactType.seq alphabet left right).replaceVar name replacement)
      label (target.replaceVar name replacement) current future := by
  have hLeft := PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement left hLeftTail
  cases hOffers with
  | seq env alphabet left left' right label current childFuture hChild hNotSkip hNonClock =>
    have hTarget := PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement left'
      (hChild.preserves_tailOccurrences name False hLeftRec hLeftTail)
    simpa only [PactType.replaceVar, hLeft, hTarget, sequenceRightMenu, hIncomplete,
      Bool.false_eq_true, ite_false, Finset.union_empty] using
      TypeOffers.seq env alphabet left left' (right.replaceVar name replacement)
        label current childFuture hChild hNotSkip hNonClock
  | seq_tock env alphabet left left' right current childFuture hChild hNotSkip =>
    have hTarget := PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement left'
      (hChild.preserves_tailOccurrences name False hLeftRec hLeftTail)
    simpa only [PactType.replaceVar, hLeft, hTarget] using
      TypeOffers.seq_tock env alphabet left left' (right.replaceVar name replacement)
        current childFuture hChild hNotSkip
  | seq_fuse env alphabet skipAlphabet left right label current childFuture hChild hNonClock =>
    simpa only [PactType.replaceVar, hLeft, sequenceRightMenu, hIncomplete,
      Bool.false_eq_true, ite_false, Finset.union_empty] using
      TypeOffers.seq_fuse env alphabet skipAlphabet left (right.replaceVar name replacement)
        label current childFuture hChild hNonClock
  | seq_fuse_tock env alphabet skipAlphabet left right current childFuture hChild =>
    simpa only [PactType.replaceVar, hLeft] using
      TypeOffers.seq_fuse_tock env alphabet skipAlphabet left (right.replaceVar name replacement)
        current childFuture hChild

/-- Inversion of an incomplete sequence preserves the full pair and recovers a substituted target. -/
theorem TypeOffers.replaceVar_seq_incomplete_inverse
    (name : String) (replacement : PactType)
    {env : TypeEnvironment} {alphabet : PactTypeAlphabet} {left right target : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hOffers : TypeOffers env ((PactType.seq alphabet left right).replaceVar name replacement)
      label target current future)
    (hLeftRec : left.TailRecursive) (hLeftTail : left.TailOccurrences name False)
    (hIncomplete : left.CanCompleteDeclared = false) :
    ∃ original, TypeOffers env (.seq alphabet left right) label original current future ∧
      target = original.replaceVar name replacement := by
  have hLeft := PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement left hLeftTail
  simp only [PactType.replaceVar, hLeft] at hOffers
  cases hOffers with
  | seq _ _ _ left' _ _ _ childFuture hChild hNotSkip hNonClock =>
    have hTarget := PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement left'
      (hChild.preserves_tailOccurrences name False hLeftRec hLeftTail)
    refine ⟨.seq alphabet left' right, ?_, by simp only [PactType.replaceVar, hTarget]⟩
    simpa only [sequenceRightMenu, hIncomplete, Bool.false_eq_true, ite_false,
      Finset.union_empty] using
      TypeOffers.seq env alphabet left left' right label current childFuture hChild hNotSkip hNonClock
  | seq_tock _ _ _ left' _ childCurrent childFuture hChild hNotSkip =>
    have hTarget := PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement left'
      (hChild.preserves_tailOccurrences name False hLeftRec hLeftTail)
    exact ⟨.seq alphabet left' right,
      TypeOffers.seq_tock env alphabet left left' right childCurrent childFuture hChild hNotSkip,
      by simp only [PactType.replaceVar, hTarget]⟩
  | seq_fuse _ _ skipAlphabet _ _ _ _ childFuture hChild hNonClock =>
    refine ⟨right, ?_, rfl⟩
    simpa only [sequenceRightMenu, hIncomplete, Bool.false_eq_true, ite_false,
      Finset.union_empty] using
      TypeOffers.seq_fuse env alphabet skipAlphabet left right label current childFuture hChild hNonClock
  | seq_fuse_tock _ _ skipAlphabet _ _ childCurrent childFuture hChild =>
    exact ⟨right, TypeOffers.seq_fuse_tock env alphabet skipAlphabet left right
      childCurrent childFuture hChild, rfl⟩

/-- Enlarging the shared menu preserves equality of the two union fields. -/
private theorem union_sdiff_eq_of_menu_subset
    (left stored oldMenu newMenu current : Finset BareMessage)
    (hEq : (left ∪ oldMenu) \ current = (stored ∪ oldMenu) \ current)
    (hSubset : oldMenu ⊆ newMenu) :
    (left ∪ newMenu) \ current = (stored ∪ newMenu) \ current := by
  calc
    (left ∪ newMenu) \ current =
        ((left ∪ oldMenu) \ current) ∪ (newMenu \ current) := by
      rw [← Finset.union_sdiff_distrib, Finset.union_assoc,
        Finset.union_eq_right.mpr hSubset]
    _ = ((stored ∪ oldMenu) \ current) ∪ (newMenu \ current) := by rw [hEq]
    _ = (stored ∪ newMenu) \ current := by
      rw [← Finset.union_sdiff_distrib, Finset.union_assoc,
        Finset.union_eq_right.mpr hSubset]

/-- Paper: the left step is unchanged; substitution enlarges only the right-entry menu. -/
theorem TypeOffers.replaceVar_seq_atUnion
    (name : String) (replacement : PactType)
    {env : TypeEnvironment} {alphabet : PactTypeAlphabet} {left right target : PactType}
    {label : TypeLabel} {current future stored : Finset BareMessage}
    (hOffers : TypeOffers env (.seq alphabet left right) label target current future)
    (hLeftRec : left.TailRecursive) (hLeftTail : left.TailOccurrences name False)
    (hRightTail : right.TailOccurrences name True)
    (hComplete : left.CanCompleteDeclared = true) (hNonClock : label ≠ .tock)
    (hField : future = (stored ∪ typeFutureOffers right) \ current) :
    TypeOffers env ((PactType.seq alphabet left right).replaceVar name replacement) label
      (target.replaceVar name replacement) current
      ((stored ∪ typeFutureOffers (right.replaceVar name replacement)) \ current) := by
  have hLeft := PactType.replaceVar_eq_self_of_tailOccurrences_false
    name replacement left hLeftTail
  have hSubset := typeFutureOffers_subset_replaceVar_tail name replacement right hRightTail
  cases hOffers with
  | seq env alphabet left left' right label current childFuture hChild hNotSkip hNotClock =>
    have hTarget := PactType.replaceVar_eq_self_of_tailOccurrences_false
      name replacement left' (hChild.preserves_tailOccurrences name False hLeftRec hLeftTail)
    have hField' : (childFuture ∪ typeFutureOffers (right.replaceVar name replacement)) \ current =
        (stored ∪ typeFutureOffers (right.replaceVar name replacement)) \ current :=
      union_sdiff_eq_of_menu_subset _ _ _ _ _
        (by simpa only [sequenceRightMenu, hComplete, Bool.true_eq, ite_true] using hField) hSubset
    simpa only [PactType.replaceVar, hLeft, hTarget, sequenceRightMenu, hComplete,
      Bool.true_eq, ite_true, hField'] using TypeOffers.seq env alphabet left left'
        (right.replaceVar name replacement) label current childFuture hChild hNotSkip hNotClock
  | seq_fuse env alphabet skipAlphabet left right label current childFuture hChild hNotClock =>
    have hField' : (childFuture ∪ typeFutureOffers (right.replaceVar name replacement)) \ current =
        (stored ∪ typeFutureOffers (right.replaceVar name replacement)) \ current :=
      union_sdiff_eq_of_menu_subset _ _ _ _ _
        (by simpa only [sequenceRightMenu, hComplete, Bool.true_eq, ite_true] using hField) hSubset
    simpa only [PactType.replaceVar, hLeft, sequenceRightMenu, hComplete,
      Bool.true_eq, ite_true, hField'] using
      TypeOffers.seq_fuse env alphabet skipAlphabet left (right.replaceVar name replacement)
        label current childFuture hChild hNotClock
  | seq_tock | seq_fuse_tock => exact (hNonClock rfl).elim

/-- Inversion retains the left witness and records how any matching stored field changes. -/
theorem TypeOffers.replaceVar_seq_atUnion_inverse
    (name : String) (replacement : PactType)
    {env : TypeEnvironment} {alphabet : PactTypeAlphabet} {left right target : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hOffers : TypeOffers env ((PactType.seq alphabet left right).replaceVar name replacement)
      label target current future)
    (hLeftRec : left.TailRecursive) (hLeftTail : left.TailOccurrences name False)
    (hRightTail : right.TailOccurrences name True)
    (hComplete : left.CanCompleteDeclared = true) (hNonClock : label ≠ .tock) :
    ∃ original originalFuture,
      TypeOffers env (.seq alphabet left right) label original current originalFuture ∧
      target = original.replaceVar name replacement ∧
      ∀ stored, originalFuture = (stored ∪ typeFutureOffers right) \ current →
        future = (stored ∪ typeFutureOffers (right.replaceVar name replacement)) \ current := by
  have hLeft := PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement left hLeftTail
  have hSubset := typeFutureOffers_subset_replaceVar_tail name replacement right hRightTail
  simp only [PactType.replaceVar, hLeft] at hOffers
  cases hOffers with
  | seq _ _ _ left' _ _ _ childFuture hChild hNotSkip hNotClock =>
    have hTarget := PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement left'
      (hChild.preserves_tailOccurrences name False hLeftRec hLeftTail)
    refine ⟨.seq alphabet left' right, (childFuture ∪ typeFutureOffers right) \ current, ?_, ?_, ?_⟩
    · simpa only [sequenceRightMenu, hComplete, Bool.true_eq, ite_true] using
        TypeOffers.seq env alphabet left left' right label current childFuture hChild hNotSkip hNotClock
    · simp only [PactType.replaceVar, hTarget]
    · intro stored hField
      simpa only [sequenceRightMenu, hComplete, Bool.true_eq, ite_true] using
        union_sdiff_eq_of_menu_subset childFuture stored _ _ current hField hSubset
  | seq_fuse _ _ skipAlphabet _ _ _ _ childFuture hChild hNotClock =>
    refine ⟨right, (childFuture ∪ typeFutureOffers right) \ current, ?_, rfl, ?_⟩
    · simpa only [sequenceRightMenu, hComplete, Bool.true_eq, ite_true] using
        TypeOffers.seq_fuse env alphabet skipAlphabet left right label current childFuture hChild hNotClock
    · intro stored hField
      simpa only [sequenceRightMenu, hComplete, Bool.true_eq, ite_true] using
        union_sdiff_eq_of_menu_subset childFuture stored _ _ current hField hSubset
  | seq_tock | seq_fuse_tock => exact (hNonClock rfl).elim

/-- A compiled sequence-union field remains exact under the recursion menu substitution. -/
theorem TypeOffers.replaceVar_compiled_atUnion
    (ty : PactType) (name : String) (replacement : PactType)
    (menus : TypeAutomatonState → Finset BareMessage)
    (hMenus : FutureOffersAgree ty)
    (hSubstitutedMenus : ∀ rho q,
      relationMembership (buildRelationSet ty (compileType ty)) rho q →
        menus q = typeFutureOffers (rho.replaceVar name replacement))
    {source target : PactType} (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel (typeCompilationFuel ty) ty).edges)
    (stored removed : Finset BareMessage) (reference : TypeAutomatonState)
    (hField : edge.future = .atUnion stored reference removed)
    (hRelated : relationMembership (buildRelationSet ty (compileType ty)) source edge.source)
    (hTailRec : source.TailRecursive) (hTail : source.TailOccurrences name True)
    (hOffers : TypeOffers edge.environment source edge.label.semantic target edge.current
      (resolveFutureSpec (computeFutureOf ty) edge.future)) :
    TypeOffers edge.environment (source.replaceVar name replacement) edge.label.semantic
      (target.replaceVar name replacement) edge.current (resolveFutureSpec menus edge.future) := by
  obtain ⟨hNonClock, hRemoved, alphabet, left, right, hSource, hRight, hComplete⟩ :=
    compileTypeFuel_atUnion_represented (typeCompilationFuel ty) ty le_rfl edge hEdge
      stored removed reference hField
  have hSourceEq := buildRelationSetCoreFuel_functional (typeCompilationFuel ty) ty
    hRelated hSource
  subst source
  simp only [PactType.TailRecursive] at hTailRec
  simp only [PactType.TailOccurrences] at hTail
  have hOldMenu := hMenus hRight
  have hNewMenu := hSubstitutedMenus right reference hRight
  have hStep := hOffers.replaceVar_seq_atUnion name replacement (stored := stored)
    hTailRec.1 hTail.1 hTail.2
    hComplete hNonClock (by simp only [hField, resolveFutureSpec, hOldMenu, hRemoved])
  simpa only [hField, resolveFutureSpec, hNewMenu, hRemoved] using hStep

/-- Paper: invert the body edge, then identify the copied sequence field using this rank's menus. -/
theorem offer_recur_atUnion_backward
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    {bound : List String} (hWF : TypeWellFormedIn bound (.recur alphabet name body))
    (hBody : TypeAutomatonStepCorrespondence body) (hBodyMenus : FutureOffersAgree body)
    (hMenus : FutureOffersAgree (.recur alphabet name body))
    {source : PactType} (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel (typeCompilationFuel body) body).edges)
    {label : TypeLabel} (hLabel : edge.label = .visible label)
    (stored removed : Finset BareMessage) (reference : TypeAutomatonState)
    (hField : edge.future = .atUnion stored reference removed)
    (hRelated : relationMembership (buildRelationSet body (compileType body)) source edge.source) :
    ∃ target,
      DecoratedTypeTransition edge.environment (source.replaceVar name (.recur alphabet name body))
        label ⟨edge.current, resolveFutureSpec
          (fun q => computeFutureOf (.recur alphabet name body) (.child 0 q)) edge.future⟩ target ∧
      relationMembership (buildRelationSet (.recur alphabet name body)
        (compileType (.recur alphabet name body))) target (.child 0 edge.target) := by
  have hChildEdge : (compileType body).HasEdge edge.source edge.environment label
      ⟨edge.current, resolveFutureSpec (computeFutureOf body) edge.future⟩ edge.target := by
    rw [compileType_hasEdge_iff_hasResolvedEdge]
    exact ⟨edge, hEdge, rfl, rfl, hLabel, rfl, rfl, rfl⟩
  obtain ⟨target, hStep, hTarget⟩ := hBody.2 hRelated hChildEdge
  have hBodyWF := typeWellFormedIn_recur hWF
  have hTailRec := (relationMembership_tailRecursive body source edge.source
    hBodyWF.2.2.2.2.2.1 hBodyWF.2.2.2.1 hRelated).1
  have hTail := relationMembership_tailOccurrences body source edge.source name True
    hBodyWF.2.2.2.2.2.1 (hBodyWF.2.2.2.1 name) hRelated
  have hOffers := TypeOffers.replaceVar_compiled_atUnion body name (.recur alphabet name body)
    (fun q => computeFutureOf (.recur alphabet name body) (.child 0 q)) hBodyMenus
    (fun rho q hRho => hMenus (relationMembership_recur_child alphabet name body rho hRho))
    edge hEdge stored removed reference hField hRelated hTailRec hTail
    (by simpa only [hLabel, AutomatonConstructionLabel.semantic] using hStep.2)
  simp only [hLabel, AutomatonConstructionLabel.semantic] at hOffers
  exact ⟨target.replaceVar name (.recur alphabet name body),
    ⟨hOffers.toTypeTransition, hOffers⟩,
    relationMembership_recur_child alphabet name body target hTarget⟩

/-- Paper: substitution changes the source menu, which is read at the tagged source. -/
theorem offer_recur_at_source_backward
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    {bound : List String} (hWF : TypeWellFormedIn bound (.recur alphabet name body))
    (hBody : TypeAutomatonStepCorrespondence body)
    (hMenus : FutureOffersAgree (.recur alphabet name body))
    {source : PactType} (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel (typeCompilationFuel body) body).edges)
    {label : TypeLabel} (hLabel : edge.label = .visible label)
    (reference : TypeAutomatonState) (removed : Finset BareMessage)
    (hField : edge.future = .at reference removed) (hNotTarget : reference ≠ edge.target)
    (hRelated : relationMembership (buildRelationSet body (compileType body)) source edge.source) :
    ∃ target,
      DecoratedTypeTransition edge.environment (source.replaceVar name (.recur alphabet name body))
        label ⟨edge.current, resolveFutureSpec
          (fun q => computeFutureOf (.recur alphabet name body) (.child 0 q)) edge.future⟩ target ∧
      relationMembership (buildRelationSet (.recur alphabet name body)
        (compileType (.recur alphabet name body))) target (.child 0 edge.target) := by
  have hChildEdge : (compileType body).HasEdge edge.source edge.environment label
      ⟨edge.current, resolveFutureSpec (computeFutureOf body) edge.future⟩ edge.target := by
    rw [compileType_hasEdge_iff_hasResolvedEdge]
    exact ⟨edge, hEdge, rfl, rfl, hLabel, rfl, rfl, rfl⟩
  obtain ⟨target, hStep, hTarget⟩ := hBody.2 hRelated hChildEdge
  obtain ⟨future, hSubstituted⟩ :=
    recursionSubstitutionStepBackward_of_typeWF alphabet name body hWF hRelated hStep
  have hFuture := TypeOffers.replaceVar_compiled_at_source_future body name
    (.recur alphabet name body)
    (fun q => computeFutureOf (.recur alphabet name body) (.child 0 q))
    (fun rho q hRho => hMenus (relationMembership_recur_child alphabet name body rho hRho))
    edge hEdge reference removed hField hNotTarget hRelated
    (by simpa only [hLabel, AutomatonConstructionLabel.semantic] using hSubstituted.2)
  exact ⟨target.replaceVar name (.recur alphabet name body), hFuture ▸ hSubstituted,
    relationMembership_recur_child alphabet name body target hTarget⟩

/-- The source-read calculation also identifies the given semantic pair in the forward direction. -/
theorem offer_recur_at_source_forward
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    (hMenus : FutureOffersAgree (.recur alphabet name body))
    {source target : PactType} (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel (typeCompilationFuel body) body).edges)
    {label : TypeLabel} (hLabel : edge.label = .visible label)
    (reference : TypeAutomatonState) (removed : Finset BareMessage)
    (hField : edge.future = .at reference removed) (hNotTarget : reference ≠ edge.target)
    (hRelated : relationMembership (buildRelationSet body (compileType body)) source edge.source)
    {future : Finset BareMessage}
    (hOffers : TypeOffers edge.environment (source.replaceVar name (.recur alphabet name body))
      label target edge.current future) :
    (compileType (.recur alphabet name body)).HasEdge (.child 0 edge.source)
      edge.environment label ⟨edge.current, future⟩ (.child 0 edge.target) := by
  have hFuture := TypeOffers.replaceVar_compiled_at_source_future body name
    (.recur alphabet name body)
    (fun q => computeFutureOf (.recur alphabet name body) (.child 0 q))
    (fun rho q hRho => hMenus (relationMembership_recur_child alphabet name body rho hRho))
    edge hEdge reference removed hField hNotTarget hRelated
    (by simpa only [hLabel, AutomatonConstructionLabel.semantic] using hOffers)
  rw [hFuture]
  exact compileType_recur_child_pending_lift alphabet name body edge hEdge hLabel

/-- Paper: the copied target represents the substituted body target. -/
theorem offer_recur_at_target_backward
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    {bound : List String} (hWF : TypeWellFormedIn bound (.recur alphabet name body))
    (hBody : TypeAutomatonStepCorrespondence body)
    (hMenus : FutureOffersAgree (.recur alphabet name body))
    {source : PactType} (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel (typeCompilationFuel body) body).edges)
    {label : TypeLabel} (hLabel : edge.label = .visible label)
    (removed : Finset BareMessage) (hField : edge.future = .at edge.target removed)
    (hRelated : relationMembership (buildRelationSet body (compileType body)) source edge.source) :
    ∃ target,
      DecoratedTypeTransition edge.environment (source.replaceVar name (.recur alphabet name body))
        label ⟨edge.current, resolveFutureSpec
          (fun q => computeFutureOf (.recur alphabet name body) (.child 0 q)) edge.future⟩ target ∧
      relationMembership (buildRelationSet (.recur alphabet name body)
        (compileType (.recur alphabet name body))) target (.child 0 edge.target) := by
  have hChildEdge : (compileType body).HasEdge edge.source edge.environment label
      ⟨edge.current, resolveFutureSpec (computeFutureOf body) edge.future⟩ edge.target := by
    rw [compileType_hasEdge_iff_hasResolvedEdge]
    exact ⟨edge, hEdge, rfl, rfl, hLabel, rfl, rfl, rfl⟩
  obtain ⟨target, hStep, hTarget⟩ := hBody.2 hRelated hChildEdge
  obtain ⟨future, hSubstituted⟩ :=
    recursionSubstitutionStepBackward_of_typeWF alphabet name body hWF hRelated hStep
  have hFuture := TypeOffers.replaceVar_compiled_at_target_future body
    (typeWellFormedIn_recur hWF) name (.recur alphabet name body)
    (fun q => computeFutureOf (.recur alphabet name body) (.child 0 q))
    (fun rho q hRho => hMenus (relationMembership_recur_child alphabet name body rho hRho))
    edge hEdge hLabel removed hField hRelated hTarget hSubstituted.2
  exact ⟨target.replaceVar name (.recur alphabet name body), hFuture ▸ hSubstituted,
    relationMembership_recur_child alphabet name body target hTarget⟩

/-- The same target-menu equation identifies the given pair in the forward direction. -/
theorem offer_recur_at_target_forward
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    {bound : List String} (hWF : TypeWellFormedIn bound (.recur alphabet name body))
    (hMenus : FutureOffersAgree (.recur alphabet name body))
    {source target : PactType} (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel (typeCompilationFuel body) body).edges)
    {label : TypeLabel} (hLabel : edge.label = .visible label)
    (removed : Finset BareMessage) (hField : edge.future = .at edge.target removed)
    (hRelated : relationMembership (buildRelationSet body (compileType body)) source edge.source)
    (hTarget : relationMembership (buildRelationSet body (compileType body)) target edge.target)
    {future : Finset BareMessage}
    (hOffers : TypeOffers edge.environment (source.replaceVar name (.recur alphabet name body))
      label (target.replaceVar name (.recur alphabet name body)) edge.current future) :
    (compileType (.recur alphabet name body)).HasEdge (.child 0 edge.source)
      edge.environment label ⟨edge.current, future⟩ (.child 0 edge.target) := by
  have hFuture := TypeOffers.replaceVar_compiled_at_target_future body
    (typeWellFormedIn_recur hWF) name (.recur alphabet name body)
    (fun q => computeFutureOf (.recur alphabet name body) (.child 0 q))
    (fun rho q hRho => hMenus (relationMembership_recur_child alphabet name body rho hRho))
    edge hEdge hLabel removed hField hRelated hTarget hOffers
  rw [hFuture]
  exact compileType_recur_child_pending_lift alphabet name body edge hEdge hLabel

/-- Stored fields retain the body pair; tail position excludes substitution from their operands. -/
theorem offer_recur_explicit_backward
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    {bound : List String} (hWF : TypeWellFormedIn bound (.recur alphabet name body))
    (hBody : TypeAutomatonStepCorrespondence body)
    {source : PactType} (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel (typeCompilationFuel body) body).edges)
    {label : TypeLabel} (hLabel : edge.label = .visible label)
    (stored : Finset BareMessage) (hField : edge.future = .explicit stored)
    (hRelated : relationMembership (buildRelationSet body (compileType body)) source edge.source) :
    ∃ target,
      DecoratedTypeTransition edge.environment (source.replaceVar name (.recur alphabet name body))
        label ⟨edge.current, resolveFutureSpec
          (fun q => computeFutureOf (.recur alphabet name body) (.child 0 q)) edge.future⟩ target ∧
      relationMembership (buildRelationSet (.recur alphabet name body)
        (compileType (.recur alphabet name body))) target (.child 0 edge.target) := by
  have hChildEdge : (compileType body).HasEdge edge.source edge.environment label
      ⟨edge.current, stored⟩ edge.target := by
    rw [compileType_hasEdge_iff_hasResolvedEdge]
    exact ⟨edge, hEdge, rfl, rfl, hLabel, rfl, by simp [hField], rfl⟩
  obtain ⟨target, hStep, hTarget⟩ := hBody.2 hRelated hChildEdge
  have hBodyWF := typeWellFormedIn_recur hWF
  have hTailRec := (relationMembership_tailRecursive body source edge.source
    hBodyWF.2.2.2.2.2.1 hBodyWF.2.2.2.1 hRelated).1
  have hTail := relationMembership_tailOccurrences body source edge.source name True
    hBodyWF.2.2.2.2.2.1 (hBodyWF.2.2.2.1 name) hRelated
  have hOffers : TypeOffers edge.environment (source.replaceVar name (.recur alphabet name body))
      label (target.replaceVar name (.recur alphabet name body)) edge.current stored := by
    by_cases hClock : label = .tock
    · obtain ⟨future, hSubstituted⟩ :=
        recursionSubstitutionStepBackward_of_typeWF alphabet name body hWF hRelated hStep
      have hOld := hStep.2.future_eq_empty_of_label_tock hClock
      have hNew := hSubstituted.2.future_eq_empty_of_label_tock hClock
      have hEq : future = stored := hNew.trans hOld.symm
      exact hEq ▸ hSubstituted.2
    · rcases compileTypeFuel_explicit_source (typeCompilationFuel body) body le_rfl hBodyWF
          edge hRelated hEdge (by simpa [hLabel] using hClock) stored hField with
        hClosed | ⟨a, left, right, hSource, hIncomplete⟩
      · exact hStep.2.replaceVar_of_tailOccurrences_false name (.recur alphabet name body)
          hTailRec (hClosed name)
      · subst source
        simp only [PactType.TailRecursive] at hTailRec
        simp only [PactType.TailOccurrences] at hTail
        exact hStep.2.replaceVar_seq_incomplete name (.recur alphabet name body)
          hTailRec.1 hTail.1 hIncomplete
  refine ⟨target.replaceVar name (.recur alphabet name body), ?_,
    relationMembership_recur_child alphabet name body target hTarget⟩
  simpa only [hField, resolveFutureSpec] using
    (⟨hOffers.toTypeTransition, hOffers⟩ : DecoratedTypeTransition _ _ _ _ _)

/-- Inversion keeps the field equations needed when the body IH selects its matching edge. -/
theorem TypeOffers.replaceVar_inverse_with_future_fields
    (name : String) (replacement : PactType)
    {source target : PactType} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hOffers : TypeOffers env (source.replaceVar name replacement) label target current future)
    (hTailRec : source.TailRecursive) (hTail : source.TailOccurrences name True)
    (hFallback : ∃ original originalFuture,
      TypeOffers env source label original current originalFuture ∧
      target = original.replaceVar name replacement) :
    ∃ original originalFuture,
      TypeOffers env source label original current originalFuture ∧
      target = original.replaceVar name replacement ∧
      (source.TailOccurrences name False → future = originalFuture) ∧
      (∀ alphabet left right, source = .seq alphabet left right →
        left.CanCompleteDeclared = false → future = originalFuture) ∧
      (∀ alphabet left right stored, source = .seq alphabet left right →
        left.CanCompleteDeclared = true → label ≠ .tock →
        originalFuture = (stored ∪ typeFutureOffers right) \ current →
        future = (stored ∪ typeFutureOffers (right.replaceVar name replacement)) \ current) := by
  by_cases hAbsent : source.TailOccurrences name False
  · have hSource := PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement source hAbsent
    rw [hSource] at hOffers
    have hTarget := PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement target
      (hOffers.preserves_tailOccurrences name False hTailRec hAbsent)
    refine ⟨target, future, hOffers, hTarget.symm, fun _ => rfl, fun _ _ _ _ _ => rfl, ?_⟩
    intro a left right stored hSeq _ _ hField
    subst source
    simp only [PactType.TailOccurrences] at hAbsent
    rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement right hAbsent.2]
    exact hField
  · by_cases hSeq : ∃ a left right, source = .seq a left right
    · obtain ⟨a, left, right, rfl⟩ := hSeq
      simp only [PactType.TailRecursive] at hTailRec
      simp only [PactType.TailOccurrences] at hTail
      by_cases hClock : label = .tock
      · obtain ⟨original, originalFuture, hOriginal, hTarget⟩ := hFallback
        have hFuture : future = originalFuture :=
          (hOffers.future_eq_empty_of_label_tock hClock).trans
            (hOriginal.future_eq_empty_of_label_tock hClock).symm
        exact ⟨original, originalFuture, hOriginal, hTarget,
          fun _ => hFuture, fun _ _ _ _ _ => hFuture,
          fun _ _ _ _ _ _ hNonClock _ => (hNonClock hClock).elim⟩
      · cases hComplete : left.CanCompleteDeclared with
        | false =>
          obtain ⟨original, hOriginal, hTarget⟩ :=
            hOffers.replaceVar_seq_incomplete_inverse name replacement hTailRec.1 hTail.1 hComplete
          refine ⟨original, future, hOriginal, hTarget, fun _ => rfl, fun _ _ _ _ _ => rfl, ?_⟩
          intro a' left' right' stored hSource hFlag _ _
          cases hSource
          simp [hComplete] at hFlag
        | true =>
          obtain ⟨original, originalFuture, hOriginal, hTarget, hField⟩ :=
            hOffers.replaceVar_seq_atUnion_inverse name replacement
              hTailRec.1 hTail.1 hTail.2 hComplete hClock
          refine ⟨original, originalFuture, hOriginal, hTarget,
            fun h => (hAbsent h).elim, ?_, ?_⟩
          · intro a' left' right' hSource hFlag
            cases hSource
            simp [hComplete] at hFlag
          · intro a' left' right' stored hSource _ _ hStored
            cases hSource
            exact hField stored hStored
    · obtain ⟨original, originalFuture, hOriginal, hTarget⟩ := hFallback
      exact ⟨original, originalFuture, hOriginal, hTarget, fun h => (hAbsent h).elim,
        fun a left right h _ => (hSeq ⟨a, left, right, h⟩).elim,
        fun a left right _ h _ _ _ => (hSeq ⟨a, left, right, h⟩).elim⟩

/-- Paper: choose the inverse body witness, apply the child IH, then identify each copied field. -/
theorem offer_recur_copied_forward
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    {bound : List String} (hWF : TypeWellFormedIn bound (.recur alphabet name body))
    (hBody : TypeAutomatonStepCorrespondence body) (hBodyMenus : FutureOffersAgree body)
    (hMenus : FutureOffersAgree (.recur alphabet name body))
    {source target : PactType} {q : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {current future : Finset BareMessage}
    (hRelated : relationMembership (buildRelationSet body (compileType body)) source q)
    (hStep : DecoratedTypeTransition env (source.replaceVar name (.recur alphabet name body))
      label ⟨current, future⟩ target)
    (hFallback : ∃ original originalFuture,
      DecoratedTypeTransition env source label ⟨current, originalFuture⟩ original ∧
      target = original.replaceVar name (.recur alphabet name body)) :
    ∃ q', (compileType (.recur alphabet name body)).HasEdge (.child 0 q)
        env label ⟨current, future⟩ q' ∧
      relationMembership (buildRelationSet (.recur alphabet name body)
        (compileType (.recur alphabet name body))) target q' := by
  have hBodyWF := typeWellFormedIn_recur hWF
  have hTailRec := (relationMembership_tailRecursive body source q
    hBodyWF.2.2.2.2.2.1 hBodyWF.2.2.2.1 hRelated).1
  have hTail := relationMembership_tailOccurrences body source q name True
    hBodyWF.2.2.2.2.2.1 (hBodyWF.2.2.2.1 name) hRelated
  obtain ⟨original, originalFuture, hOriginal, hTargetEq, hAbsent, hIncomplete, hUnion⟩ :=
    hStep.2.replaceVar_inverse_with_future_fields name (.recur alphabet name body)
      hTailRec hTail (by
        obtain ⟨rho, offers, hRho, hEq⟩ := hFallback
        exact ⟨rho, offers, hRho.2, hEq⟩)
  have hOriginalStep : DecoratedTypeTransition env source label ⟨current, originalFuture⟩ original :=
    ⟨hOriginal.toTypeTransition, hOriginal⟩
  obtain ⟨q', hBodyEdge, hTarget⟩ := hBody.1 hRelated hOriginalStep
  obtain ⟨edge, hEdge, hSource, hEnv, hLabel, hCurrent, hOldFuture, hState⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge body q q' env label ⟨current, originalFuture⟩).mp hBodyEdge
  change edge.current = current at hCurrent
  change resolveFutureSpec (computeFutureOf body) edge.future = originalFuture at hOldFuture
  subst q
  subst env
  subst current
  subst q'
  have hFuture : future = resolveFutureSpec
      (fun q => computeFutureOf (.recur alphabet name body) (.child 0 q)) edge.future := by
    cases hSpec : edge.future with
    | explicit stored =>
      have hStored : stored = originalFuture := by simpa only [hSpec, resolveFutureSpec] using hOldFuture
      simp only [hSpec, resolveFutureSpec]
      by_cases hClock : label = .tock
      · have hEq : future = originalFuture :=
          (hStep.2.future_eq_empty_of_label_tock hClock).trans
            (hOriginal.future_eq_empty_of_label_tock hClock).symm
        exact hEq.trans hStored.symm
      · rcases compileTypeFuel_explicit_source (typeCompilationFuel body) body le_rfl hBodyWF
            edge hRelated hEdge (by simpa [hLabel] using hClock) stored hSpec with
          hClosed | ⟨a, left, right, hSeq, hFlag⟩
        · exact (hAbsent (hClosed name)).trans hStored.symm
        · exact (hIncomplete a left right hSeq hFlag).trans hStored.symm
    | «at» reference removed =>
      by_cases hRef : reference = edge.target
      · subst reference
        simpa only [hSpec] using TypeOffers.replaceVar_compiled_at_target_future body hBodyWF
          name (.recur alphabet name body)
          (fun q => computeFutureOf (.recur alphabet name body) (.child 0 q))
          (fun rho q hRho => hMenus (relationMembership_recur_child alphabet name body rho hRho))
          edge hEdge hLabel removed hSpec hRelated hTarget (hTargetEq ▸ hStep.2)
      · simpa only [hSpec] using TypeOffers.replaceVar_compiled_at_source_future body name (.recur alphabet name body)
          (fun q => computeFutureOf (.recur alphabet name body) (.child 0 q))
          (fun rho q hRho => hMenus (relationMembership_recur_child alphabet name body rho hRho))
          edge hEdge reference removed hSpec hRef hRelated
          (by simpa only [hLabel, AutomatonConstructionLabel.semantic] using hStep.2)
    | atUnion stored reference removed =>
      obtain ⟨hNC, hRemoved, a, left, right, hSeqRelated, hRightRelated, hComplete⟩ :=
        compileTypeFuel_atUnion_represented (typeCompilationFuel body) body le_rfl edge hEdge
          stored removed reference hSpec
      have hSeq := buildRelationSetCoreFuel_functional (typeCompilationFuel body) body
        hRelated hSeqRelated
      have hOldMenu := hBodyMenus hRightRelated
      have hNewMenu := hMenus (relationMembership_recur_child alphabet name body right hRightRelated)
      have hEq := hUnion a left right stored hSeq hComplete
        (by simpa only [hLabel, AutomatonConstructionLabel.semantic] using hNC)
        (by simpa only [hSpec, resolveFutureSpec, hOldMenu, hRemoved] using hOldFuture.symm)
      simpa only [hSpec, resolveFutureSpec, hNewMenu, hRemoved] using hEq
  refine ⟨.child 0 edge.target, ?_,
    hTargetEq ▸ relationMembership_recur_child alphabet name body original hTarget⟩
  rw [hFuture]
  exact compileType_recur_child_pending_lift alphabet name body edge hEdge hLabel

/-- Every ordinary copied field is explicit, a source/target read, or a sequence union. -/
theorem offer_recur_copied_backward
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    {bound : List String} (hWF : TypeWellFormedIn bound (.recur alphabet name body))
    (hBody : TypeAutomatonStepCorrespondence body) (hBodyMenus : FutureOffersAgree body)
    (hMenus : FutureOffersAgree (.recur alphabet name body))
    {source : PactType} (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel (typeCompilationFuel body) body).edges)
    {label : TypeLabel} (hLabel : edge.label = .visible label)
    (hRelated : relationMembership (buildRelationSet body (compileType body)) source edge.source) :
    ∃ target,
      DecoratedTypeTransition edge.environment (source.replaceVar name (.recur alphabet name body))
        label ⟨edge.current, resolveFutureSpec
          (fun q => computeFutureOf (.recur alphabet name body) (.child 0 q)) edge.future⟩ target ∧
      relationMembership (buildRelationSet (.recur alphabet name body)
        (compileType (.recur alphabet name body))) target (.child 0 edge.target) := by
  cases hSpec : edge.future with
  | explicit stored =>
    simpa only [hSpec] using
      offer_recur_explicit_backward alphabet name body hWF hBody edge hEdge hLabel stored hSpec hRelated
  | «at» reference removed =>
    by_cases hRef : reference = edge.target
    · subst reference
      simpa only [hSpec] using offer_recur_at_target_backward alphabet name body hWF hBody hMenus
        edge hEdge hLabel removed hSpec hRelated
    · simpa only [hSpec] using offer_recur_at_source_backward alphabet name body hWF hBody hMenus
        edge hEdge hLabel reference removed hSpec hRef hRelated
  | atUnion stored reference removed =>
    simpa only [hSpec] using offer_recur_atUnion_backward alphabet name body hWF hBody hBodyMenus hMenus
      edge hEdge hLabel stored removed reference hSpec hRelated

/-- Paper: current matching and this rank's menus determine the full recursion pair. -/
theorem offerCorrespondence_recur
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    {bound : List String} (hWF : TypeWellFormedIn bound (.recur alphabet name body))
    (hBody : TypeAutomatonStepCorrespondence body) (hBodyMenus : FutureOffersAgree body)
    (hMenus : FutureOffersAgree (.recur alphabet name body)) :
    TypeAutomatonStepCorrespondence (.recur alphabet name body) := by
  have hCurrent := currentOfferCorrespondence_recur_of_typeWF alphabet name body hWF hBody.toCurrent
  have hBodyWF := typeWellFormedIn_recur hWF
  have hBodyTail : body.TailOccurrences name True := by
    have h := hWF.2.2.2.2.2.1
    simp only [PactType.TailRecursive] at h
    exact h.1
  have hBodyAlphabet : body.alphabet = alphabet := by
    have h := hWF.1
    simp only [PactType.AlphabetWellFormed] at h
    exact h.2.1
  have hBodyLocal : EdgeLocalAt (typeCompilationFuel body) body :=
    edgeLocalAt_holds (typeCompilationFuel body) body le_rfl hBodyWF.1
      hBodyWF.2.2.2.2.2.2.2.2.2.2.2.2.1 hBodyWF.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBodyClock := compileTypeFuel_clockEdgesAreTock (typeCompilationFuel body) body le_rfl
  constructor
  · intro residual residual' state env label offers hRelated hStep
    rcases offers with ⟨current, future⟩
    rcases relationMembership_recur_cases alphabet name body hRelated with
      hRoot | ⟨q, bodyResidual, hEntry, hBodyRelated⟩
    · cases hRoot
      exact offer_recur_root_forward alphabet name body hMenus hStep
    · cases hEntry
      rcases recursionSubstitutionStepForward_of_typeWF alphabet name body hWF hBodyRelated hStep with
        ⟨bodyTarget, bodyFuture, hBodyStep, hTargetEq⟩ |
        ⟨varAlphabet, markerEdge, hVar, hMarkerEdge, hMarkerSource,
          hMarkerEnv, hMarkerLabel, _, _, _, _, _⟩
      · exact offer_recur_copied_forward alphabet name body hWF hBody hBodyMenus hMenus
          hBodyRelated hStep ⟨bodyTarget, bodyFuture, hBodyStep, hTargetEq⟩
      · subst bodyResidual
        have hUnfold : DecoratedTypeTransition markerEdge.environment (.recur alphabet name body)
            label ⟨current, future⟩ residual' := by
          simpa only [PactType.replaceVar, if_pos rfl, hMarkerEnv] using hStep
        obtain ⟨q', hParent, hTarget⟩ := offer_recur_backedge_forward alphabet name body hMenus
          markerEdge hMarkerEdge hMarkerLabel hUnfold
        exact ⟨q', by simpa only [hMarkerSource, hMarkerEnv] using hParent, hTarget⟩
  · intro residual state state' env label offers hRelated hEdge
    rcases offers with ⟨current, future⟩
    rcases relationMembership_recur_cases alphabet name body hRelated with
      hRoot | ⟨q, bodyResidual, hEntry, hBodyRelated⟩
    · cases hRoot
      exact offer_recur_root_backward alphabet name body hCurrent hMenus hEdge
    · cases hEntry
      rcases compileType_recur_child_edge_cases alphabet name body
          hBodyTail hBodyAlphabet hBodyLocal hBodyClock hBodyRelated hEdge with
        ⟨bodyEdge, hBodyMem, hSource, hEnv, hLabel, hCurrentOffer, hStateEq, hFuture⟩ |
        ⟨varAlphabet, hVar, _, _, _, _, _, _⟩
      · subst q
        subst env
        subst current
        subst state'
        subst future
        exact offer_recur_copied_backward alphabet name body hWF hBody hBodyMenus hMenus
          bodyEdge hBodyMem hLabel hBodyRelated
      · subst bodyResidual
        simpa only [PactType.replaceVar, if_pos rfl] using
          offer_recur_backedge_backward alphabet name body hBody.toCurrent hCurrent hMenus
            hBodyRelated hEdge

end

end Pact
