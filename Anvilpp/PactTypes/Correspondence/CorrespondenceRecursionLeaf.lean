import Anvilpp.PactTypes.Correspondence.CorrespondenceMarkerReachability

/-!
# Recursion leaf: future-references-target, RecursionBodyScopedStepCorrect, bounded leaf assembly
-/

namespace Pact

noncomputable section

/-- Tagging preserves "the symbolic future reference is the edge's own
target". -/
private theorem childPendingEdge_futureReferencesTarget
    (index : Nat) (edge : PendingAutomatonEdge)
    (hEdge : ∀ inner removed, edge.future = .at inner removed →
      inner = edge.target) :
    ∀ inner removed,
      (childPendingEdge index edge).future = .at inner removed →
        inner = (childPendingEdge index edge).target := by
  intro inner removed hFuture
  cases hSpec : edge.future with
  | explicit future =>
      have hParent : (childPendingEdge index edge).future =
          .explicit future := by
        simp [childPendingEdge, childFutureSpec, hSpec]
      rw [hParent] at hFuture
      simp at hFuture
  | «at» reference removedInner =>
      have hParent : (childPendingEdge index edge).future =
          .at (childState index reference) removedInner := by
        simp [childPendingEdge, childFutureSpec, hSpec]
      rw [hParent] at hFuture
      have hInner : childState index reference = inner := by
        injection hFuture
      rw [← hInner, hEdge reference removedInner hSpec]
      rfl

/-- **Every symbolic future reference of a compiled edge is that edge's own
target.**  Each constructor either stores an explicit menu or points at the
state the edge moves to; `childFutureSpec` retags a reference and the edge's
target in lockstep.  This is what turns
`CompilationResolvedEdgeTargetsRelated` into a statement about the state whose
menu an edge actually resolves. -/
private theorem compileTypeFuel_futureReferencesTarget
    (signature : TypeAlphabet) :
    ∀ (fuel : Nat) (processType : PactType),
      ∀ edge ∈ (compileTypeFuel signature fuel processType).edges,
        ∀ inner removed, edge.future = .at inner removed →
          inner = edge.target := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro processType edge hEdge
      simp [compileTypeFuel] at hEdge
  | succ fuel ih =>
      intro processType edge hEdge inner removed hFuture
      cases processType with
      | skip =>
          exfalso
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with ⟨environment, _, hEq⟩
          rw [← hEq] at hFuture
          simp at hFuture
      | message msg dir =>
          exfalso
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with ((⟨e, _, hEq⟩ | ⟨e, _, hEq⟩) | ⟨e, _, hEq⟩) <;>
            (rw [← hEq] at hFuture; simp at hFuture)
      | tock =>
          exfalso
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with (⟨e, _, hEq⟩ | ⟨e, _, hEq⟩)
          · rw [← hEq] at hFuture
            split at hFuture <;> simp at hFuture
          · rw [← hEq] at hFuture
            simp at hFuture
      | progress pid =>
          exfalso
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with (⟨e, _, hEq⟩ | ⟨e, _, hEq⟩) <;>
            (rw [← hEq] at hFuture; simp at hFuture)
      | var other =>
          exfalso
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image] at hEdge
          rcases hEdge with ⟨environment, _, hEq⟩
          rw [← hEq] at hFuture
          simp at hFuture
      | recur binder body =>
          simp only [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
            at hEdge
          rcases hEdge with ⟨environment, _, hEq⟩ | ⟨bodyEdge, hBodyEdge, hEq⟩
          · rw [← hEq] at hFuture ⊢
            simp only at hFuture ⊢
            have hInner : childState 0 (compileTypeFuel signature fuel
                body).initial = inner := by injection hFuture
            rw [← hInner]
          · by_cases hMarker :
                bodyEdge.label = AutomatonConstructionLabel.variable binder
            · rw [if_pos hMarker] at hEq
              rw [← hEq] at hFuture ⊢
              simp only at hFuture ⊢
              have hInner : childState 0 (compileTypeFuel signature fuel
                  body).initial = inner := by injection hFuture
              rw [← hInner]
            · rw [if_neg hMarker] at hEq
              have hShape : edge = childPendingEdge 0 bodyEdge := by
                rw [← hEq]
                rfl
              rw [hShape] at hFuture ⊢
              exact childPendingEdge_futureReferencesTarget 0 bodyEdge
                (ih body bodyEdge hBodyEdge) inner removed hFuture
      | choice left right =>
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
            Finset.mem_singleton] at hEdge
          rcases hEdge with (hLeft | hRight) | hSelection
          · rcases hLeft with ⟨childEdge, hChildEdge, hEq⟩
            rw [← hEq] at hFuture ⊢
            exact childPendingEdge_futureReferencesTarget 0 childEdge
              (ih left childEdge hChildEdge) inner removed hFuture
          · rcases hRight with ⟨childEdge, hChildEdge, hEq⟩
            rw [← hEq] at hFuture ⊢
            exact childPendingEdge_futureReferencesTarget 1 childEdge
              (ih right childEdge hChildEdge) inner removed hFuture
          · rcases hSelection with ⟨environment, _, hEq | hEq⟩ <;>
              (rw [hEq] at hFuture ⊢
               simp only at hFuture ⊢
               injection hFuture with hInner
               rw [← hInner])
      | fairChoice bid left right =>
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
            Finset.mem_singleton] at hEdge
          rcases hEdge with (hLeft | hRight) | hSelection
          · rcases hLeft with ⟨childEdge, hChildEdge, hEq⟩
            rw [← hEq] at hFuture ⊢
            exact childPendingEdge_futureReferencesTarget 0 childEdge
              (ih left childEdge hChildEdge) inner removed hFuture
          · rcases hRight with ⟨childEdge, hChildEdge, hEq⟩
            rw [← hEq] at hFuture ⊢
            exact childPendingEdge_futureReferencesTarget 1 childEdge
              (ih right childEdge hChildEdge) inner removed hFuture
          · rcases hSelection with ⟨environment, _, hEq | hEq⟩ <;>
              (rw [hEq] at hFuture ⊢
               simp only at hFuture ⊢
               injection hFuture with hInner
               rw [← hInner])
      | seq left right =>
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion] at hEdge
          rcases hEdge with ((hLeft | hRight) | hBridge) | hFutureBridge
          · rcases hLeft with ⟨childEdge, hChildEdge, hEq⟩
            rw [← hEq] at hFuture ⊢
            simp only at hFuture ⊢
            cases hLabel : childEdge.label with
            | future =>
                rw [hLabel] at hFuture
                simp only at hFuture
                exact childPendingEdge_futureReferencesTarget 0 childEdge
                  (ih left childEdge hChildEdge) inner removed (by
                    simp [childPendingEdge, hFuture])
            | visible visibleLabel =>
                rw [hLabel] at hFuture
                simp only at hFuture
                injection hFuture with hInner
                rw [← hInner]
            | «variable» markerName =>
                rw [hLabel] at hFuture
                simp only at hFuture
                injection hFuture with hInner
                rw [← hInner]
          · rcases hRight with ⟨childEdge, hChildEdge, hEq⟩
            rw [← hEq] at hFuture ⊢
            exact childPendingEdge_futureReferencesTarget 1 childEdge
              (ih right childEdge hChildEdge) inner removed hFuture
          · rcases hBridge with ⟨state, _, environment, _, hEq⟩
            rw [← hEq] at hFuture ⊢
            simp only at hFuture ⊢
            injection hFuture with hInner
            rw [← hInner]
          · rcases hFutureBridge with ⟨state, _, hEq⟩
            rw [← hEq] at hFuture ⊢
            simp only at hFuture ⊢
            injection hFuture with hInner
            rw [← hInner]
      | par left right interface =>
          exfalso
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, Finset.mem_union, Finset.mem_biUnion,
            Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with hTransition | hObservation
          · rcases hTransition with
              ⟨leftEdge, _, rightEdge, _, hEq⟩
            rw [← hEq] at hFuture
            simp at hFuture
          · rcases hObservation with ⟨leftState, _, rightState, _, hEq⟩ |
              ⟨leftState, _, rightState, _, hEq⟩ <;>
              (rw [← hEq] at hFuture; simp at hFuture)
      | xoffer elseType branches =>
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with
            ((((hElseEdge | hIndexed) | hBranch) | hWait) | hResolved)
          · simp only [childPendingEdges, Finset.mem_image] at hElseEdge
            rcases hElseEdge with ⟨childEdge, hChildEdge, hEq⟩
            rw [← hEq] at hFuture ⊢
            exact childPendingEdge_futureReferencesTarget 0 childEdge
              (ih elseType childEdge hChildEdge) inner removed hFuture
          · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
            rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
            · simp at hEmpty
            · simp only [childPendingEdges, Finset.mem_image] at hChild
              rcases hChild with ⟨childEdge, hChildEdge, hEq⟩
              rcases compiledBranch_zipIdx_cases signature fuel branches indexed
                hIndexedMem with ⟨action, branchType, _, hCompiled⟩
              rw [hCompiled] at hChildEdge
              rw [← hEq] at hFuture ⊢
              exact childPendingEdge_futureReferencesTarget (indexed.2 + 1)
                childEdge (ih branchType childEdge hChildEdge) inner removed
                  hFuture
          · rw [mem_foldl_union_iff] at hBranch
            rcases hBranch with hEmpty | ⟨indexed, _, hNewEdge⟩
            · simp at hEmpty
            · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
              rcases hNewEdge with ⟨environment, _, hEq⟩
              rw [← hEq] at hFuture ⊢
              simp only at hFuture ⊢
              injection hFuture with hInner
              rw [← hInner]
          · simp only [Finset.mem_image, Finset.mem_filter] at hWait
            rcases hWait with ⟨environment, _, hEq⟩
            rw [← hEq] at hFuture ⊢
            simp only at hFuture ⊢
            injection hFuture with hInner
            rw [← hInner]
          · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
            rcases hResolved with ⟨environment, _, hEq⟩
            rw [← hEq] at hFuture ⊢
            simp only at hFuture ⊢
            injection hFuture with hInner
            rw [← hInner]
      | offer elseType branches =>
          simp only [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with
            ((((hElseEdge | hIndexed) | hEnabled) | hWait) | hResolved)
          · simp only [childPendingEdges, Finset.mem_image] at hElseEdge
            rcases hElseEdge with ⟨childEdge, hChildEdge, hEq⟩
            rw [← hEq] at hFuture ⊢
            exact childPendingEdge_futureReferencesTarget 0 childEdge
              (ih elseType childEdge hChildEdge) inner removed hFuture
          · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
            rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
            · simp at hEmpty
            · simp only [childPendingEdges, Finset.mem_image] at hChild
              rcases hChild with ⟨childEdge, hChildEdge, hEq⟩
              rcases selectedConjunction_zipIdx_cases signature fuel branches
                indexed hIndexedMem with ⟨selected, _, hCompiled⟩
              rw [hCompiled] at hChildEdge
              rw [← hEq] at hFuture ⊢
              exact childPendingEdge_futureReferencesTarget (indexed.2 + 1)
                childEdge
                (ih (parallelTypeBranchesSelecting selected branches) childEdge
                  hChildEdge) inner removed hFuture
          · rw [mem_foldl_union_iff] at hEnabled
            rcases hEnabled with hEmpty | ⟨indexed, _, hNewEdge⟩
            · simp at hEmpty
            · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
              rcases hNewEdge with ⟨environment, _, hEq⟩
              rw [← hEq] at hFuture ⊢
              simp only at hFuture ⊢
              injection hFuture with hInner
              rw [← hInner]
          · simp only [Finset.mem_image, Finset.mem_filter] at hWait
            rcases hWait with ⟨environment, _, hEq⟩
            rw [← hEq] at hFuture ⊢
            simp only at hFuture ⊢
            injection hFuture with hInner
            rw [← hInner]
          · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
            rcases hResolved with ⟨environment, _, hEq⟩
            rw [← hEq] at hFuture ⊢
            simp only at hFuture ⊢
            injection hFuture with hInner
            rw [← hInner]

/-- A semantic step out of a type in which `name` does not occur reaches a
type in which `name` still does not occur.  Recursion is the only case with
content: unfolding substitutes the binder for its own variable, and either the
binder shadows `name` (so the result is closed for `name` outright) or the
replacement itself is `name`-free. -/
private theorem typeOffers_tailOccurrences_false (name : String) :
    ∀ source : PactType, ∀ env label target current future,
      TypeOffers env source label target current future →
        source.TailOccurrences name False →
          target.TailOccurrences name False := by
  intro source
  induction hSize : sizeOf source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
      intro env label target current future hOffers hTail
      cases source with
      | message msg dir =>
          cases hOffers <;> simp_all [PactType.TailOccurrences]
      | progress pid =>
          cases hOffers <;> simp [PactType.TailOccurrences]
      | tock =>
          cases hOffers <;> simp [PactType.TailOccurrences]
      | skip =>
          cases hOffers <;> simp [PactType.TailOccurrences]
      | var current' => cases hOffers
      | recur binder body =>
          cases hOffers with
          | recur _ _ _ _ =>
              by_cases hBinder : binder = name
              · subst hBinder
                exact PactType.tailOccurrences_false_replaceVar_self_recur
                  binder body body
              · have hBody : body.TailOccurrences name False := by
                  simpa only [PactType.TailOccurrences, if_neg hBinder]
                    using hTail
                exact PactType.tailOccurrences_false_replaceVar name binder
                  (.recur binder body) hTail body hBody
      | choice left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          cases hOffers with
          | choice_left => exact hFields.1
          | choice_right => exact hFields.2
      | fairChoice bid left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          cases hOffers with
          | fair_left => exact hFields.1
          | fair_right => exact hFields.2
      | seq left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          cases hOffers with
          | skip_seq => exact hFields.2
          | seq _ _ leftTarget _ _ _ _ hChild =>
              simp only [PactType.TailOccurrences]
              exact ⟨ih (sizeOf left) hLeftSize left rfl _ _ _ _ _ hChild
                hFields.1, hFields.2⟩
      | par left right interface =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          cases hOffers with
          | par _ _ _ _ _ leftTarget _ rightTarget _ _ _ _ _ _ hLeft hRight =>
              simp only [PactType.TailOccurrences]
              exact ⟨ih (sizeOf left) hLeftSize left rfl _ _ _ _ _ hLeft
                  hFields.1,
                ih (sizeOf right) hRightSize right rfl _ _ _ _ _ hRight
                  hFields.2⟩
      | xoffer elseType branches =>
          have hFields : elseType.TailOccurrences name False ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          cases hOffers with
          | xoffer_branch _ _ _ _ _ hBranch =>
              exact tailOccurrences_branch_of_mem name False branches
                hFields.2 _ hBranch.2.1
          | xoffer_else => exact hFields.1
          | xoffer_wait => exact hTail
      | offer elseType branches =>
          have hFields : elseType.TailOccurrences name False ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          cases hOffers with
          | offer_some _ _ _ _ _ =>
              exact tailOccurrences_parallelTypeBranchesSelecting name _
                branches hFields.2
          | offer_else => exact hFields.1
          | offer_wait => exact hTail

/-- The future menu decorating a step is always contained in the target's own
menu.  Every constructor either publishes the target menu outright or removes
a set from it; the product hides a union of component menus, each contained in
its component's target menu by induction.  This is what makes the `removed`
component of the substitution correspondence always available. -/
private theorem typeOffers_future_subset_targetFuture :
    ∀ source : PactType, ∀ env label target current future,
      TypeOffers env source label target current future →
        future ⊆ typeFutureOffers target := by
  intro source
  induction hSize : sizeOf source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
      intro env label target current future hOffers
      cases source with
      | message msg dir =>
          cases hOffers with
          | action => exact Finset.Subset.refl _
          | action_wait => exact Finset.sdiff_subset
      | progress pid =>
          cases hOffers with
          | progress => exact Finset.empty_subset _
      | tock =>
          cases hOffers with
          | cycle => exact Finset.empty_subset _
          | cycle_wait => exact Finset.empty_subset _
      | skip =>
          cases hOffers with
          | skip => exact Finset.empty_subset _
      | var current' => cases hOffers
      | recur binder body =>
          cases hOffers with
          | recur => exact Finset.Subset.refl _
      | choice left right =>
          cases hOffers with
          | choice_left => exact Finset.Subset.refl _
          | choice_right => exact Finset.Subset.refl _
      | fairChoice bid left right =>
          cases hOffers with
          | fair_left => exact Finset.Subset.refl _
          | fair_right => exact Finset.Subset.refl _
      | seq left right =>
          cases hOffers with
          | skip_seq => exact Finset.Subset.refl _
          | seq => exact Finset.sdiff_subset
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          cases hOffers with
          | par _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLeft hRight =>
              rw [typeFutureOffers_parallel]
              intro action hAction
              simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union]
                at hAction ⊢
              refine ⟨?_, hAction.2⟩
              rcases hAction.1 with hLeftAction | hRightAction
              · exact Or.inl (ih (sizeOf left) hLeftSize left rfl _ _ _ _ _
                  hLeft hLeftAction)
              · exact Or.inr (ih (sizeOf right) hRightSize right rfl _ _ _ _ _
                  hRight hRightAction)
      | xoffer elseType branches =>
          cases hOffers with
          | xoffer_branch => exact Finset.Subset.refl _
          | xoffer_else => exact Finset.Subset.refl _
          | xoffer_wait => exact Finset.sdiff_subset
      | offer elseType branches =>
          cases hOffers with
          | offer_some => exact Finset.Subset.refl _
          | offer_else => exact Finset.Subset.refl _
          | offer_wait => exact Finset.sdiff_subset

/-- A decorated step is *exactly* an offer derivation: the undecorated
transition it also mentions is already implied by the offers
(`TypeOffers.to_transition`).  This halves the substitution reasoning needed
by the recursion step leaf — only `TypeOffers` has to be transported. -/
private theorem decoratedTypeTransition_iff_typeOffers
    (env : TypeEnvironment) (source : PactType) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : PactType) :
    DecoratedTypeTransition env source label offers target ↔
      TypeOffers env source label target offers.current offers.future :=
  ⟨fun hStep => hStep.2, fun hOffers => ⟨TypeOffers.to_transition hOffers,
    hOffers⟩⟩

/-- A substituted residual is a bare variable only when it already was one,
and then the substituted binder is a different name.  `replaceVar` maps a
non-variable to the same constructor, and maps the substituted variable to the
binder itself, which is a `.recur`. -/
private theorem replaceVar_recur_eq_var
    {source : PactType} {binder markerName : String} {body : PactType}
    (hEqual : source.replaceVar binder (.recur binder body) =
      .var markerName) :
    source = .var markerName ∧ ¬ binder = markerName := by
  cases source with
  | var current =>
      by_cases hCase : binder = current
      · rw [PactType.replaceVar, if_pos hCase] at hEqual
        exact absurd hEqual (by simp)
      · rw [PactType.replaceVar, if_neg hCase] at hEqual
        have hName : current = markerName := by
          injection hEqual
        subst hName
        exact ⟨rfl, hCase⟩
  | recur current inner =>
      rw [PactType.replaceVar] at hEqual
      split at hEqual <;> exact absurd hEqual (by simp)
  | message msg dir => simp [PactType.replaceVar] at hEqual
  | progress pid => simp [PactType.replaceVar] at hEqual
  | tock => simp [PactType.replaceVar] at hEqual
  | skip => simp [PactType.replaceVar] at hEqual
  | choice left right => simp [PactType.replaceVar] at hEqual
  | fairChoice bid left right => simp [PactType.replaceVar] at hEqual
  | seq left right => simp [PactType.replaceVar] at hEqual
  | par left right interface => simp [PactType.replaceVar] at hEqual
  | xoffer elseType branches => simp [PactType.replaceVar] at hEqual
  | offer elseType branches => simp [PactType.replaceVar] at hEqual

set_option maxHeartbeats 1600000 in
/-- **Converse of `compileTypeFuel_variableEdge_source_var`.**  Every state
representing a bare recursive call really is a marker source, and it carries a
marker edge for *every* local environment — the `.var` fragment emits one per
environment, and every constructor lift preserves an edge's label and
environment.  This is what lets the recursion step correspondence produce the
installed backedge at the environment the semantic step was taken in. -/
private theorem compileTypeFuel_markerEdge_of_variableRelation
    (signature : TypeAlphabet) (markerName : String) :
    ∀ (fuel : Nat) (processType : PactType),
      TypeCompilationFuelSufficient processType fuel →
      PactType.TailOccurrences markerName True processType →
      ∀ state residual, TypeCompilationRelation processType state residual →
        residual = PactType.var markerName →
        ∀ env ∈ signature.localEnvironments,
          ∃ edge ∈ (compileTypeFuel signature fuel processType).edges,
            edge.source = state ∧
              edge.label = AutomatonConstructionLabel.variable markerName ∧
              edge.environment = env := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel _
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel hTail state residual hRelated hResidual env hEnv
      cases processType with
      | skip => cases hRelated <;> simp at hResidual
      | message msg dir => cases hRelated <;> simp at hResidual
      | tock => cases hRelated <;> simp at hResidual
      | progress pid => cases hRelated <;> simp at hResidual
      | par left right interface => cases hRelated <;> simp at hResidual
      | var current =>
          cases hRelated with
          | «variable» _ =>
              have hName : current = markerName := by injection hResidual
              subst hName
              refine ⟨{ source := .root
                        environment := env
                        label := .variable current
                        current := ∅
                        future := .explicit ∅
                        target := .final }, ?_, rfl, rfl, rfl⟩
              simp only [compileTypeFuel, finishAutomatonFragment,
                Finset.mem_image]
              exact ⟨env, hEnv, rfl⟩
      | recur binder body =>
          have hBodyFuel : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          cases hRelated with
          | recur_source => simp at hResidual
          | recur_body _ _ _ childQ hChild =>
              obtain ⟨hChildResidual, hDistinct⟩ :=
                replaceVar_recur_eq_var hResidual
              have hTailBody : PactType.TailOccurrences markerName True body := by
                have hTail' := hTail
                simp only [PactType.TailOccurrences] at hTail'
                rw [if_neg hDistinct] at hTail'
                exact hTail'
              obtain ⟨childEdge, hChildEdge, hSource, hLabel, hEnvironment⟩ :=
                ih body hBodyFuel hTailBody childQ _ hChild
                  hChildResidual env hEnv
              have hBinderNe : ¬ markerName = binder := fun hEq =>
                hDistinct hEq.symm
              have hNotBinder : ¬ childEdge.label =
                  AutomatonConstructionLabel.variable binder := by
                rw [hLabel]
                simp [hBinderNe]
              refine ⟨{ source := childState 0 childEdge.source
                        environment := childEdge.environment
                        label := childEdge.label
                        current := childEdge.current
                        future := childFutureSpec 0 childEdge.future
                        target := childState 0 childEdge.target }, ?_, ?_,
                      hLabel, hEnvironment⟩
              · simp only [compileTypeFuel, buildRecursionAutomaton,
                  finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
                exact Or.inr ⟨childEdge, hChildEdge, by
                  rw [if_neg hNotBinder]⟩
              · simp [childState, hSource]
      | choice left right =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : PactType.TailOccurrences markerName True left ∧
              PactType.TailOccurrences markerName True right := by
            simpa only [PactType.TailOccurrences] using hTail
          cases hRelated with
          | choice_source => simp at hResidual
          | choice_left _ _ _ childQ hChild =>
              obtain ⟨childEdge, hChildEdge, hSource, hLabel, hEnvironment⟩ :=
                ih left hLeftFuel hTailFields.1 childQ _ hChild
                  hResidual env hEnv
              refine ⟨childPendingEdge 0 childEdge, ?_, ?_, hLabel,
                hEnvironment⟩
              · exact ((buildChoiceAutomaton_outgoing_left signature
                  (compileTypeFuel signature fuel left)
                  (compileTypeFuel signature fuel right) TypeLabel.silent
                  TypeLabel.silent childQ
                  (childPendingEdge 0 childEdge)).mpr
                    ⟨childEdge, hChildEdge, hSource, rfl⟩).1
              · simp [childPendingEdge, childState, hSource]
          | choice_right _ _ _ childQ hChild =>
              obtain ⟨childEdge, hChildEdge, hSource, hLabel, hEnvironment⟩ :=
                ih right hRightFuel hTailFields.2 childQ _ hChild hResidual env hEnv
              refine ⟨childPendingEdge 1 childEdge, ?_, ?_, hLabel,
                hEnvironment⟩
              · exact ((buildChoiceAutomaton_outgoing_right signature
                  (compileTypeFuel signature fuel left)
                  (compileTypeFuel signature fuel right) TypeLabel.silent
                  TypeLabel.silent childQ
                  (childPendingEdge 1 childEdge)).mpr
                    ⟨childEdge, hChildEdge, hSource, rfl⟩).1
              · simp [childPendingEdge, childState, hSource]
      | fairChoice bid left right =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : PactType.TailOccurrences markerName True left ∧
              PactType.TailOccurrences markerName True right := by
            simpa only [PactType.TailOccurrences] using hTail
          cases hRelated with
          | fair_source => simp at hResidual
          | fair_left _ _ _ _ childQ hChild =>
              obtain ⟨childEdge, hChildEdge, hSource, hLabel, hEnvironment⟩ :=
                ih left hLeftFuel hTailFields.1 childQ _ hChild
                  hResidual env hEnv
              refine ⟨childPendingEdge 0 childEdge, ?_, ?_, hLabel,
                hEnvironment⟩
              · exact ((buildChoiceAutomaton_outgoing_left signature
                  (compileTypeFuel signature fuel left)
                  (compileTypeFuel signature fuel right)
                  (TypeLabel.fair bid true) (TypeLabel.fair bid false)
                  childQ (childPendingEdge 0 childEdge)).mpr
                    ⟨childEdge, hChildEdge, hSource, rfl⟩).1
              · simp [childPendingEdge, childState, hSource]
          | fair_right _ _ _ _ childQ hChild =>
              obtain ⟨childEdge, hChildEdge, hSource, hLabel, hEnvironment⟩ :=
                ih right hRightFuel hTailFields.2 childQ _ hChild hResidual env hEnv
              refine ⟨childPendingEdge 1 childEdge, ?_, ?_, hLabel,
                hEnvironment⟩
              · exact ((buildChoiceAutomaton_outgoing_right signature
                  (compileTypeFuel signature fuel left)
                  (compileTypeFuel signature fuel right)
                  (TypeLabel.fair bid true) (TypeLabel.fair bid false)
                  childQ (childPendingEdge 1 childEdge)).mpr
                    ⟨childEdge, hChildEdge, hSource, rfl⟩).1
              · simp [childPendingEdge, childState, hSource]
      | seq left right =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : PactType.TailOccurrences markerName False left ∧
              PactType.TailOccurrences markerName True right := by
            simpa only [PactType.TailOccurrences] using hTail
          cases hRelated with
          | sequence_left _ _ _ _ _ => simp at hResidual
          | sequence_right _ _ _ childQ hChild =>
              obtain ⟨childEdge, hChildEdge, hSource, hLabel, hEnvironment⟩ :=
                ih right hRightFuel hTailFields.2 childQ _ hChild hResidual env hEnv
              refine ⟨childPendingEdge 1 childEdge, ?_, ?_, hLabel,
                hEnvironment⟩
              · exact ((buildSequenceAutomaton_outgoing_right signature
                  (compileTypeFuel signature fuel left)
                  (compileTypeFuel signature fuel right) childQ
                  (childPendingEdge 1 childEdge)).mpr
                    ⟨childEdge, hChildEdge, hSource, rfl⟩).1
              · simp [childPendingEdge, childState, hSource]
      | xoffer elseType branches =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hBranchBudget : typeBranchCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hTailFields :
              PactType.TailOccurrences markerName True elseType ∧
              PactType.TailBranchOccurrences markerName True branches := by
            simpa only [PactType.TailOccurrences] using hTail
          have hFragmentEq : compileTypeFuel signature (fuel + 1)
              (PactType.xoffer elseType branches) =
              buildExclusiveOfferAutomaton signature branches
                (compileTypeFuel signature fuel elseType)
                (branches.map fun branch =>
                  (branch.1, compileTypeFuel signature fuel branch.2)) := rfl
          rw [hFragmentEq]
          cases hRelated with
          | xoffer_source => simp at hResidual
          | xoffer_else _ _ _ childQ hChild =>
              obtain ⟨childEdge, hChildEdge, hSource, hLabel, hEnvironment⟩ :=
                ih elseType hElseFuel hTailFields.1 childQ _ hChild hResidual env hEnv
              refine ⟨childPendingEdge 0 childEdge, ?_, ?_, hLabel,
                hEnvironment⟩
              · exact ((buildExclusiveOfferAutomaton_outgoing_else signature
                  branches (compileTypeFuel signature fuel elseType)
                  (branches.map fun branch =>
                    (branch.1, compileTypeFuel signature fuel branch.2))
                  childQ (childPendingEdge 0 childEdge)).mpr
                    ⟨childEdge, hChildEdge, hSource, rfl⟩).1
              · simp [childPendingEdge, childState, hSource]
          | xoffer_branch _ branchType _ _ action index childQ
              hEntry hChild =>
              have hMember : (action, branchType) ∈ branches :=
                List.mem_of_getElem? hEntry
              have hBranchFuel : TypeCompilationFuelSufficient branchType
                  fuel :=
                le_trans (typeCompilationFuel_le_typeBranchCompilationFuel
                  branches (action, branchType) hMember) hBranchBudget
              have hBranchTail : PactType.TailOccurrences markerName True
                  branchType :=
                tailOccurrences_branch_of_mem markerName True branches
                  hTailFields.2 (action, branchType) hMember
              obtain ⟨childEdge, hChildEdge, hSource, hLabel, hEnvironment⟩ :=
                ih branchType hBranchFuel hBranchTail childQ _ hChild hResidual env hEnv
              have hAutomatonEntry :
                  (branches.map fun branch =>
                    (branch.1, compileTypeFuel signature fuel
                      branch.2))[index]? =
                    some (action, compileTypeFuel signature fuel branchType) := by
                simp [List.getElem?_map, hEntry]
              refine ⟨childPendingEdge (index + 1) childEdge, ?_, ?_, hLabel,
                hEnvironment⟩
              · exact ((buildExclusiveOfferAutomaton_outgoing_branch signature
                  branches (compileTypeFuel signature fuel elseType)
                  (branches.map fun branch =>
                    (branch.1, compileTypeFuel signature fuel branch.2))
                  index (action, compileTypeFuel signature fuel branchType)
                  hAutomatonEntry childQ
                  (childPendingEdge (index + 1) childEdge)).mpr
                    ⟨childEdge, hChildEdge, hSource, rfl⟩).1
              · simp [childPendingEdge, childState, hSource]
      | offer elseType branches =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields :
              PactType.TailOccurrences markerName True elseType ∧
              PactType.TailBranchOccurrences markerName False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          have hFragmentEq : compileTypeFuel signature (fuel + 1)
              (PactType.offer elseType branches) =
              buildSelectedConjunctiveOfferAutomaton signature branches
                (compileTypeFuel signature fuel elseType)
                (branches.map fun selected =>
                  (selected.1, compileTypeFuel signature fuel
                    (parallelTypeBranchesSelecting selected branches))) := rfl
          rw [hFragmentEq]
          cases hRelated with
          | offer_source => simp at hResidual
          | offer_else _ _ _ childQ hChild =>
              obtain ⟨childEdge, hChildEdge, hSource, hLabel, hEnvironment⟩ :=
                ih elseType hElseFuel hTailFields.1 childQ _ hChild hResidual env hEnv
              refine ⟨childPendingEdge 0 childEdge, ?_, ?_, hLabel,
                hEnvironment⟩
              · exact
                  ((buildSelectedConjunctiveOfferAutomaton_outgoing_else
                    signature branches
                    (compileTypeFuel signature fuel elseType)
                    (branches.map fun selected =>
                      (selected.1, compileTypeFuel signature fuel
                        (parallelTypeBranchesSelecting selected branches)))
                    childQ (childPendingEdge 0 childEdge)).mpr
                      ⟨childEdge, hChildEdge, hSource, rfl⟩).1
              · simp [childPendingEdge, childState, hSource]
          | offer_branches _ _ _ selected index childQ hEntry
              hChild =>
              exfalso
              have hAbsent : PactType.TailOccurrences markerName False
                  (parallelTypeBranchesSelecting selected branches) :=
                tailOccurrences_parallelTypeBranchesSelecting markerName
                  selected branches hTailFields.2
              have hChildAbsent : PactType.TailOccurrences markerName False
                  (PactType.var markerName) := hResidual ▸
                compilationRelation_tailOccurrences_false markerName hChild
                  hAbsent
              simp [PactType.TailOccurrences] at hChildAbsent

/-- **The recursion body future invariant, from the marker correspondence.**

The installed graph is the body's own graph plus one back-reference out of each
recursive-call marker.  Syntax splits the same way: the substituted menu is the
residual's own menu together with the binder's menu exactly when a call is
still same-cycle reachable.  The two conditions agree by
`compilationMarkerReachable_iff`. -/
private theorem recursionBodyFutureCorrect_of_bundle
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hTailBody : body.TailOccurrences name True)
    (hTailRecursiveBody : body.TailRecursive)
    (hBodyFuture : CompilationFutureCorrect signature body)
    (hMarker : ∀ q r, TypeCompilationRelation body q r →
      (MarkerReachable (compileTypeFuel signature (typeCompilationFuel body)
        body) name q ↔ PactType.markerReachableSubst name r = true)) :
    RecursionBodyFutureCorrect signature name body := by
  classical
  intro state residual hRelated
  set bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
    with hBodyFragment
  have hBodyFuel : TypeCompilationFuelSufficient body
      (typeCompilationFuel body) := typeCompilationFuel_sufficient body
  have hMarkers : MarkerEdgesInert bodyFragment name :=
    compileTypeFuel_markerEdgesInert signature name (typeCompilationFuel body)
      body True hBodyFuel hTailBody
  have hBodyTargets : bodyFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature (typeCompilationFuel body)
      body hBodyFuel
  have hBodyInitial : bodyFragment.initial ∈ bodyFragment.states :=
    compileTypeFuel_initial_mem signature (typeCompilationFuel body) body
      hBodyFuel
  have hBodyClosed : (⟨bodyFragment.states, bodyFragment.edges⟩ :
      PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates bodyFragment
      hBodyTargets
  have hParentClosed : (⟨(buildRecursionAutomaton signature name
        bodyFragment).states,
      (buildRecursionAutomaton signature name bodyFragment).edges⟩ :
        PendingAutomaton).ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_of_futureTargetsInStates
    exact buildRecursionAutomaton_futureTargetsInStates signature name
      bodyFragment hBodyTargets hBodyInitial
  have hState : state ∈ bodyFragment.states := by
    have hCanonical := compilationStateCorrect_of_compilation signature body
      state residual hRelated
    simpa [hBodyFragment] using hCanonical
  have hResidualTail : residual.TailOccurrences name True :=
    compilationRelation_tailOccurrences_true name hRelated hTailRecursiveBody
      hTailBody
  have hInitialRelation : TypeCompilationRelation body bodyFragment.initial
      body := compileTypeFuel_initial_relation signature
        (typeCompilationFuel body) body hBodyFuel
  have hResidualMenu : computeFuture
      (⟨bodyFragment.states, bodyFragment.edges⟩ : PendingAutomaton) state =
      typeFutureOffers residual := hBodyFuture state residual hRelated
  have hBodyMenu : computeFuture
      (⟨bodyFragment.states, bodyFragment.edges⟩ : PendingAutomaton)
        bodyFragment.initial = typeFutureOffers body :=
    hBodyFuture bodyFragment.initial body hInitialRelation
  show computeFuture (⟨(buildRecursionAutomaton signature name
      bodyFragment).states,
      (buildRecursionAutomaton signature name bodyFragment).edges⟩ :
        PendingAutomaton) (.child 0 state) =
    typeFutureOffers (residual.replaceVar name (.recur name body))
  rw [PactType.replaceVar_typeFutureOffers_recur,
    PactType.futureOffersSubst_eq_union_marker name body.CanCompleteBeforeTock
      (typeFutureOffers body) residual hResidualTail]
  by_cases hReach : MarkerReachable bodyFragment name state
  · rw [show (TypeAutomatonState.child 0 state) = childState 0 state from rfl,
      computeFuture_buildRecursionAutomaton_child_of_marker signature name
        bodyFragment hMarkers hBodyClosed hParentClosed hBodyInitial state
          hState hReach,
      computeFuture_buildRecursionAutomaton_child_at_initial signature name
        bodyFragment hMarkers hBodyClosed hParentClosed hBodyInitial,
      hResidualMenu, hBodyMenu,
      if_pos ((hMarker state residual hRelated).mp hReach)]
  · rw [show (TypeAutomatonState.child 0 state) = childState 0 state from rfl,
      computeFuture_buildRecursionAutomaton_child_of_no_marker signature name
        bodyFragment hMarkers hBodyClosed hParentClosed state hState
          (by simpa [MarkerReachable] using hReach),
      hResidualMenu,
      if_neg (by
        intro hValue
        exact hReach ((hMarker state residual hRelated).mpr hValue))]
    simp

/-- Scoped variant of `RecursionBodyStepCorrect`: the tagged-body obligation,
restricted to environments that avoid the body's own parallel interfaces.
`PactType.ParallelInterfaces (.recur name body) = body.ParallelInterfaces`
definitionally, so the ambient scoping premise transports unchanged. -/
private def RecursionBodyScopedStepCorrect
    (signature : TypeAlphabet) (name : String) (body : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.recur name body)) (.recur name body)
  ∀ {state : TypeAutomatonState} {residual residual' : PactType}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    TypeCompilationRelation body state residual →
    env ∈ signature.localEnvironments →
    env.AvoidsInterface body.ParallelInterfaces →
    (DecoratedTypeTransition env
        (residual.replaceVar name (.recur name body)) label offers residual' ↔
      ∃ target,
        fragment.HasResolvedEdge (.child 0 state) env label offers target ∧
        TypeCompilationRelation (.recur name body) target residual')

/-- **Marker half of the tagged-body obligation.**  When the represented
residual is the bare recursive call, the substituted residual is the binder
itself, whose only step is the silent unfolding; on the graph side the
installed backedge is the only resolved edge, because a state representing
`.var name` has no *visible* body edge at all. -/
private theorem recursionBodyScopedStep_marker
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hTailBody : body.TailOccurrences name True)
    (hBodyStep : CompilationScopedFragmentStepCorrect signature body)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    {state : TypeAutomatonState} {residual' : PactType}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation body state (.var name))
    (hLocal : env ∈ signature.localEnvironments)
    (hAvoids : env.AvoidsInterface body.ParallelInterfaces) :
    (DecoratedTypeTransition env
        ((PactType.var name).replaceVar name (.recur name body)) label offers
          residual' ↔
      ∃ target,
        (compileTypeFuel signature (typeCompilationFuel (.recur name body))
          (.recur name body)).HasResolvedEdge (.child 0 state) env label offers
            target ∧
        TypeCompilationRelation (.recur name body) target residual') := by
  classical
  have hBodyFuel : TypeCompilationFuelSufficient body
      (typeCompilationFuel body) := typeCompilationFuel_sufficient body
  set bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
    with hBodyFragment
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (PactType.recur name body)) (.recur name body) =
      buildRecursionAutomaton signature name bodyFragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
      hBodyFragment]
  have hSubst : (PactType.var name).replaceVar name (.recur name body) =
      .recur name body := by
    simp [PactType.replaceVar]
  have hInitRelation : TypeCompilationRelation body bodyFragment.initial body :=
    compileTypeFuel_initial_relation signature (typeCompilationFuel body) body
      hBodyFuel
  have hEntryMenu : computeFuture
      (⟨(buildRecursionAutomaton signature name bodyFragment).states,
        (buildRecursionAutomaton signature name bodyFragment).edges⟩ :
          PendingAutomaton) (.child 0 bodyFragment.initial) =
      typeFutureOffers (body.replaceVar name (.recur name body)) :=
    hFuture bodyFragment.initial body hInitRelation
  have hTargetRel : TypeCompilationRelation (.recur name body)
      (.child 0 bodyFragment.initial)
        (body.replaceVar name (.recur name body)) :=
    TypeCompilationRelation.recur_body name body body bodyFragment.initial
      hInitRelation
  rw [hSubst, hFragment, decoratedTypeTransition_recur_iff]
  constructor
  · rintro ⟨hWellFormed, rfl, rfl, hCurrent, hFutureEq⟩
    obtain ⟨edge, hEdge, hSource, hLabel, hEnvironment⟩ :=
      compileTypeFuel_markerEdge_of_variableRelation signature name
        (typeCompilationFuel body) body hBodyFuel hTailBody state (.var name)
          hRelated rfl env hLocal
    refine ⟨.child 0 bodyFragment.initial, ?_, hTargetRel⟩
    have hResolved := buildRecursionAutomaton_variable_marker_hasResolvedEdge
      signature name bodyFragment edge hEdge hLabel
    have hOffers : offers =
        { current := ∅,
          future := computeFuture
            (⟨(buildRecursionAutomaton signature name bodyFragment).states,
              (buildRecursionAutomaton signature name bodyFragment).edges⟩ :
                PendingAutomaton) (.child 0 bodyFragment.initial) } := by
      rw [hEntryMenu]
      cases offers
      simp_all
    rw [hOffers, ← hSource, ← hEnvironment]
    exact hResolved
  · rintro ⟨target, hEdge, hTarget⟩
    rcases (buildRecursionAutomaton_body_hasResolvedEdge_iff signature name
      bodyFragment state env label offers target).mp hEdge with
      ⟨edge, hEdge', hSource, hMarkerLabel, hEnvironment, hSilent, hCurrent,
        hFutureEq, hTargetEq⟩ |
      ⟨edge, hEdge', hSource, hNotMarker, hEnvironment, hVisible, hCurrent,
        hFutureEq, hTargetEq⟩
    · subst hTargetEq
      have hResidual : residual' = body.replaceVar name (.recur name body) :=
        TypeCompilationRelation.residual_unique hTarget hTargetRel
      exact ⟨TypeAlphabet.localEnvironment_wellFormed hLocal, hSilent,
        hResidual, hCurrent, by rw [← hFutureEq, hEntryMenu]⟩
    · exfalso
      have hBodyEdge : bodyFragment.HasResolvedEdge state env label
          { current := offers.current,
            future :=
              (match edge.future with
                | .explicit future => future
                | .at inner removed =>
                    computeFuture
                      (⟨bodyFragment.states, bodyFragment.edges⟩ :
                        PendingAutomaton) inner \ removed) }
          edge.target :=
        ⟨edge, hEdge', hSource, hEnvironment, hVisible, hCurrent, rfl, rfl⟩
      obtain ⟨targetResidual, hTargetResidual⟩ :=
        compilationResolvedEdgeTargetsRelated_all signature body hRelated
          hBodyEdge
      have hSemantic := (hBodyStep hRelated hLocal hAvoids).mpr
        ⟨edge.target, hBodyEdge, hTargetResidual⟩
      exact nomatch hSemantic.1

/-- Ordinary half of the tagged-body obligation: away from the marker itself,
substituting the binder neither creates nor destroys a step, and the resolved
future of the corresponding body edge is exactly the substituted menu.  This
is the remaining semantics-level content of the recursion step leaf. -/
private theorem recursionBodyScopedStep_nonMarker
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hTailBody : body.TailOccurrences name True)
    (hTailRecursiveBody : body.TailRecursive)
    (hBodyStep : CompilationScopedFragmentStepCorrect signature body)
    (hBodyFutureCorrect : CompilationFutureCorrect signature body)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    {state : TypeAutomatonState} {residual residual' : PactType}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation body state residual)
    (hNotMarker : ¬ residual = PactType.var name)
    (hLocal : env ∈ signature.localEnvironments)
    (hAvoids : env.AvoidsInterface body.ParallelInterfaces) :
    (DecoratedTypeTransition env
        (residual.replaceVar name (.recur name body)) label offers residual' ↔
      ∃ target,
        (compileTypeFuel signature (typeCompilationFuel (.recur name body))
          (.recur name body)).HasResolvedEdge (.child 0 state) env label offers
            target ∧
        TypeCompilationRelation (.recur name body) target residual') := by
  sorry

/-- The two halves compose into the scoped tagged-body obligation. -/
private theorem recursionBodyScopedStepCorrect_of_bundle
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hTailBody : body.TailOccurrences name True)
    (hTailRecursiveBody : body.TailRecursive)
    (hBodyStep : CompilationScopedFragmentStepCorrect signature body)
    (hBodyFutureCorrect : CompilationFutureCorrect signature body)
    (hFuture : RecursionBodyFutureCorrect signature name body) :
    RecursionBodyScopedStepCorrect signature name body := by
  intro state residual residual' env label offers hRelated hLocal hAvoids
  by_cases hMarker : residual = PactType.var name
  · subst hMarker
    exact recursionBodyScopedStep_marker signature name body hTailBody
      hBodyStep hFuture hRelated hLocal hAvoids
  · exact recursionBodyScopedStep_nonMarker signature name body hTailBody
      hTailRecursiveBody hBodyStep hBodyFutureCorrect hFuture hRelated hMarker
        hLocal hAvoids

/-- Header composition plus the tagged-body obligation give the whole scoped
recursion step correspondence. -/
private theorem compilationScopedFragmentStepCorrect_recursion_of_body
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    (hBodyStep : RecursionBodyScopedStepCorrect signature name body) :
    CompilationScopedFragmentStepCorrect signature (.recur name body) := by
  intro residual residual' state env label offers hRelated hLocal hAvoids
  have hAvoidsBody : env.AvoidsInterface body.ParallelInterfaces := by
    simpa only [PactType.ParallelInterfaces] using hAvoids
  cases hRelated with
  | recur_source =>
      exact compilationFragmentStepCorrect_recursion_root signature name body
        hFuture hLocal
  | recur_body _ _ _ childQ hChild =>
      exact hBodyStep hChild hLocal hAvoidsBody

/-- Same-cycle execution metadata for a closed binder.  This is the remaining
recursion obligation on the `sequenceExecutionAutomaton` view of the installed
graph; the ordinary future menu is already supplied by
`recursionBodyFutureCorrect_of_bundle`. -/
private theorem compilationSequenceExecutionCorrect_recursion_bounded_leaf
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.recur name body))
    (hGuarded : PactType.ClockGuarded (.recur name body))
    (hTail : PactType.TailRecursive (.recur name body))
    (hLinear : PactType.SameCycleMessageLinear (.recur name body))
    (hBodyBundle : CompilationProofBundle signature body)
    (hBodyFuture : RecursionBodyFutureCorrect signature name body) :
    CompilationSequenceExecutionCorrect signature (.recur name body) := by
  sorry

/-- Scoped step correspondence for a closed binder.  Header composition is
already proved by `compilationFragmentStepCorrect_recursion`; what remains is
the tagged-body package `RecursionBodyStepCorrect`, i.e. that a semantic step
of the substituted residual matches a resolved edge of the installed graph. -/
private theorem compilationScopedFragmentStepCorrect_recursion_bounded_leaf
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.recur name body))
    (hGuarded : PactType.ClockGuarded (.recur name body))
    (hTail : PactType.TailRecursive (.recur name body))
    (hLinear : PactType.SameCycleMessageLinear (.recur name body))
    (hScoped : PactType.InterfaceScoped (.recur name body))
    (hBodyBundle : CompilationProofBundle signature body)
    (hBodyFuture : RecursionBodyFutureCorrect signature name body) :
    CompilationScopedFragmentStepCorrect signature (.recur name body) := by
  have hTailFields : body.TailOccurrences name True ∧ body.TailRecursive := by
    simpa only [PactType.TailRecursive] using hTail
  intro residual residual' state env label offers hRelated hLocal hAvoids
  exact compilationScopedFragmentStepCorrect_recursion_of_body signature name
    body hBodyFuture
    (recursionBodyScopedStepCorrect_of_bundle signature name body
      hTailFields.1 hTailFields.2 hBodyBundle.scopedStep hBodyBundle.future
        hBodyFuture) hRelated hLocal hAvoids

/-- Recursion closure against an ambient bound-name list.  The body itself is
compiled open: only `AllVariablesBound (name :: bound)` is available for it,
so every component is obtained from the body's own bundle plus the marker
correspondence, never from a closedness assumption about `body`. -/
theorem compilationProofBundle_recursion_bounded_leaf
    (signature : TypeAlphabet) (bound : List String) (name : String)
    (body : PactType)
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.recur name body))
    (hHygienic : PactType.BinderHygienic bound (.recur name body))
    (hGuarded : PactType.ClockGuarded (.recur name body))
    (hTail : PactType.TailRecursive (.recur name body))
    (hLinear : PactType.SameCycleMessageLinear (.recur name body))
    (hScoped : PactType.InterfaceScoped (.recur name body))
    (hBodyBundle : CompilationProofBundle signature body)
    (hMarker : ∀ q r, TypeCompilationRelation body q r →
      (MarkerReachable (compileTypeFuel signature (typeCompilationFuel body)
        body) name q ↔ PactType.markerReachableSubst name r = true)) :
    CompilationProofBundle signature (.recur name body) := by
  have hGuardedFields : body.GuardedOccurrences name False ∧
      body.ClockGuarded := by
    simpa only [PactType.ClockGuarded] using hGuarded
  have hTailFields : body.TailOccurrences name True ∧ body.TailRecursive := by
    simpa only [PactType.TailRecursive] using hTail
  have hHygienicEmpty : PactType.BinderHygienic [] (.recur name body) :=
    PactType.binderHygienic_mono (by intro m hm; simp at hm)
      (.recur name body) hHygienic
  have hBodyFuture : RecursionBodyFutureCorrect signature name body :=
    recursionBodyFutureCorrect_of_bundle signature name body hTailFields.1
      hTailFields.2 hBodyBundle.future hMarker
  exact
    { future := compilationFutureCorrect_recursion signature name body
        hGuardedFields.1 hBodyFuture
      completing := compilationCompletingCorrect_recursion_regular_leaf
        signature name body hSupports hGuarded hTail hHygienicEmpty
      scopedStep :=
        compilationScopedFragmentStepCorrect_recursion_bounded_leaf signature
          name body hSignature hSupports hGuarded hTail hLinear hScoped
            hBodyBundle hBodyFuture
      execution :=
        compilationSequenceExecutionCorrect_recursion_bounded_leaf signature
          name body hSignature hSupports hGuarded hTail hLinear hBodyBundle
            hBodyFuture }

end

end Pact
