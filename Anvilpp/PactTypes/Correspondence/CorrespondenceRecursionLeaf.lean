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

/- The raw compiler has two kinds of future decoration.  This semantic copy
forgets the referenced automaton state but retains the exact payload whose
preservation matters when a recursion binder installs backedges. -/
private inductive SemanticFuturePolicy where
  | explicit (future : Finset BareMessage)
  | subtract (removed : Finset BareMessage)

private def resolveSemanticFuture (target : PactType) :
    SemanticFuturePolicy → Finset BareMessage
  | .explicit future => future
  | .subtract removed => typeFutureOffers target \ removed

/- `TypeOffers` with the exact compiler decoration policy retained.  The
constructors deliberately mirror the constructor compiler: atomic and
parallel edges carry explicit futures; constructor-selection edges point at
their target with an empty removal; sequence and waiting edges remove exactly
the set used by their operational rule. -/
private inductive PolicyTypeOffers :
    TypeEnvironment → PactType → TypeLabel → PactType →
      Finset BareMessage → SemanticFuturePolicy → Prop where
  | action (env : TypeEnvironment) (msg : MessageId) (dir : MessageDir) :
      env.WellFormed ∧ env.hasNeed (msg, dir) →
      PolicyTypeOffers env (.message msg dir) (.message msg dir) .skip
        {(msg, dir)} (.explicit ∅)
  | action_wait (env : TypeEnvironment) (msg : MessageId) (dir : MessageDir) :
      env.WellFormed ∧ ¬ env.hasNeed (msg, dir) ∧ env.clock = false →
      PolicyTypeOffers env (.message msg dir) .silent (.message msg dir)
        {(msg, dir)} (.explicit ∅)
  | choice_left (env : TypeEnvironment) (left right : PactType) :
      env.WellFormed →
      PolicyTypeOffers env (.choice left right) .silent left ∅ (.subtract ∅)
  | choice_right (env : TypeEnvironment) (left right : PactType) :
      env.WellFormed →
      PolicyTypeOffers env (.choice left right) .silent right ∅ (.subtract ∅)
  | fair_left (env : TypeEnvironment) (bid : BranchId)
      (left right : PactType) :
      env.WellFormed →
      PolicyTypeOffers env (.fairChoice bid left right) (.fair bid true) left
        ∅ (.subtract ∅)
  | fair_right (env : TypeEnvironment) (bid : BranchId)
      (left right : PactType) :
      env.WellFormed →
      PolicyTypeOffers env (.fairChoice bid left right) (.fair bid false) right
        ∅ (.subtract ∅)
  | cycle (env : TypeEnvironment) :
      env.WellFormed ∧ env.clock = true →
      PolicyTypeOffers env .tock .tock .skip ∅ (.explicit ∅)
  | cycle_wait (env : TypeEnvironment) :
      env.WellFormed ∧ env.clock = false →
      PolicyTypeOffers env .tock .silent .tock ∅ (.explicit ∅)
  | skip (env : TypeEnvironment) :
      env.WellFormed ∧ env.clock = false ∧ env.immediate = ∅ →
      PolicyTypeOffers env .skip .silent .skip ∅ (.explicit ∅)
  | skip_seq (env : TypeEnvironment) (processType : PactType) :
      env.WellFormed →
      PolicyTypeOffers env (.seq .skip processType) .silent processType ∅
        (.subtract ∅)
  | progress (env : TypeEnvironment) (pid : ProcId) :
      env.WellFormed →
      PolicyTypeOffers env (.progress pid) (.progress pid) .skip ∅
        (.explicit ∅)
  | recur (env : TypeEnvironment) (binder : String) (body : PactType) :
      env.WellFormed →
      PolicyTypeOffers env (.recur binder body) .silent
        (body.replaceVar binder (.recur binder body)) ∅ (.subtract ∅)
  | seq (env : TypeEnvironment) (left left' right : PactType)
      (label : TypeLabel) (current : Finset BareMessage)
      (childPolicy : SemanticFuturePolicy) :
      PolicyTypeOffers env left label left' current childPolicy →
      PolicyTypeOffers env (.seq left right) label (.seq left' right) current
        (.subtract current)
  | xoffer_branch (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType))
      (action : BareMessage) (processType : PactType) :
      env.WellFormed ∧ (action, processType) ∈ branches ∧
        TypeBranchEnabled env (action, processType) ∧ TypeResolved env branches →
      PolicyTypeOffers env (.xoffer elseType branches)
        (.message action.1 action.2) processType {action} (.subtract ∅)
  | xoffer_else (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧ TypeNoImmediateBranch env branches ∧
        TypeResolved env branches →
      PolicyTypeOffers env (.xoffer elseType branches) .silent elseType ∅
        (.subtract ∅)
  | xoffer_wait (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧ ¬ TypeResolved env branches ∧ env.clock = false →
      PolicyTypeOffers env (.xoffer elseType branches) .silent
        (.xoffer elseType branches) (typeWaitingOffers env branches)
        (.subtract (typeWaitingOffers env branches))
  | offer_some (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType))
      (enabled : BareMessage × PactType) :
      env.WellFormed ∧ enabled ∈ branches ∧ TypeBranchEnabled env enabled →
      PolicyTypeOffers env (.offer elseType branches) .silent
        (parallelTypeBranchesSelecting enabled branches) ∅ (.subtract ∅)
  | offer_else (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧ TypeNoImmediateBranch env branches ∧
        TypeResolved env branches →
      PolicyTypeOffers env (.offer elseType branches) .silent elseType
        (typeBranchActions branches) (.subtract ∅)
  | offer_wait (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧ TypeNoImmediateBranch env branches ∧
        ¬ TypeResolved env branches ∧ env.clock = false →
      PolicyTypeOffers env (.offer elseType branches) .silent
        (.offer elseType branches) (typeWaitingOffers env branches)
        (.subtract (typeWaitingOffers env branches))
  | par (outer leftEnv rightEnv : TypeEnvironment) (interface : Interface)
      (left left' right right' : PactType) (leftLabel rightLabel : TypeLabel)
      (leftCurrent rightCurrent : Finset BareMessage)
      (leftPolicy rightPolicy : SemanticFuturePolicy) :
      PolicyTypeOffers leftEnv left leftLabel left' leftCurrent leftPolicy →
      PolicyTypeOffers rightEnv right rightLabel right' rightCurrent rightPolicy →
      LocalTypeEnvironment outer interface rightEnv right rightLabel leftEnv →
      LocalTypeEnvironment outer interface leftEnv left leftLabel rightEnv →
      outer.WellFormed ∧ TypeLabel.Sync interface leftLabel rightLabel →
      PolicyTypeOffers outer (.par left right interface)
        (TypeLabel.combine interface leftLabel rightLabel)
        (.par left' right' interface)
        (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
        (.explicit (hideTypeOffers interface
          (resolveSemanticFuture left' leftPolicy ∪
            resolveSemanticFuture right' rightPolicy)))

private theorem PolicyTypeOffers.xoffer_root_policy
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)} {label : TypeLabel}
    {target : PactType} {current : Finset BareMessage}
    {policy : SemanticFuturePolicy}
    (hOffers : PolicyTypeOffers env (.xoffer elseType branches) label target
      current policy) :
    (policy = .subtract ∅ ∧ TypeResolved env branches) ∨
      (current = ∅ ∧ policy = .subtract ∅) ∨
      (policy = .subtract current ∧ ¬ TypeResolved env branches) := by
  cases hOffers with
  | xoffer_branch _ _ _ _ _ hFields =>
      exact Or.inl ⟨rfl, hFields.2.2.2⟩
  | xoffer_else _ _ _ hFields =>
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | xoffer_wait _ _ _ hFields =>
      exact Or.inr (Or.inr ⟨rfl, hFields.2.1⟩)

private theorem PolicyTypeOffers.offer_root_policy
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)} {label : TypeLabel}
    {target : PactType} {current : Finset BareMessage}
    {policy : SemanticFuturePolicy}
    (hOffers : PolicyTypeOffers env (.offer elseType branches) label target
      current policy) :
    (current = ∅ ∧ policy = .subtract ∅) ∨
      (policy = .subtract ∅ ∧ TypeResolved env branches) ∨
      (policy = .subtract current ∧ ¬ TypeResolved env branches) := by
  cases hOffers with
  | offer_some _ _ _ _ _ =>
      exact Or.inl ⟨rfl, rfl⟩
  | offer_else _ _ _ hFields =>
      exact Or.inr (Or.inl ⟨rfl, hFields.2.2⟩)
  | offer_wait _ _ _ hFields =>
      exact Or.inr (Or.inr ⟨rfl, hFields.2.2.1⟩)

private theorem binderFreshFor_branch_of_mem_policy
    (forbidden : List String) :
    ∀ (branches : List (BareMessage × PactType)) entry,
      PactType.BinderFreshForBranches forbidden branches →
      entry ∈ branches → entry.2.BinderFreshFor forbidden := by
  intro branches
  induction branches with
  | nil => simp
  | cons head rest ih =>
      rcases head with ⟨action, processType⟩
      intro entry hFresh hEntry
      have hFreshFields : processType.BinderFreshFor forbidden ∧
          PactType.BinderFreshForBranches forbidden rest := by
        simpa only [PactType.BinderFreshForBranches] using hFresh
      simp only [List.mem_cons] at hEntry
      rcases hEntry with rfl | hRest
      · exact hFreshFields.1
      · exact ih entry hFreshFields.2 hRest

private theorem binderFreshFor_parallelTypeBranches_policy
    (forbidden : List String) :
    ∀ branches : List (BareMessage × PactType),
      PactType.BinderFreshForBranches forbidden branches →
      (parallelTypeBranches branches).BinderFreshFor forbidden := by
  intro branches
  induction branches with
  | nil => simp [parallelTypeBranches, PactType.BinderFreshFor]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      intro hFresh
      have hFields : processType.BinderFreshFor forbidden ∧
          PactType.BinderFreshForBranches forbidden rest := by
        simpa only [PactType.BinderFreshForBranches] using hFresh
      cases rest with
      | nil =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.BinderFreshFor, PactType.BinderFreshForBranches]
            using hFields.1
      | cons next tail =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.BinderFreshFor, PactType.BinderFreshForBranches]
            using And.intro hFields.1 (ih hFields.2)

private theorem binderFreshFor_parallelTypeBranchesSelecting_policy
    (forbidden : List String) (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType),
      PactType.BinderFreshForBranches forbidden branches →
      (parallelTypeBranchesSelecting selected branches).BinderFreshFor
        forbidden := by
  intro branches
  induction branches with
  | nil =>
      simp [parallelTypeBranchesSelecting, PactType.BinderFreshFor]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      intro hFresh
      have hFields : processType.BinderFreshFor forbidden ∧
          PactType.BinderFreshForBranches forbidden rest := by
        simpa only [PactType.BinderFreshForBranches] using hFresh
      cases rest with
      | nil =>
          by_cases hSelected : (action, processType) = selected
          · simp [parallelTypeBranchesSelecting, hSelected,
              selectedTypeBranch, PactType.BinderFreshFor, hFields.1]
          · simp [parallelTypeBranchesSelecting, hSelected,
              singletonTypeXOffer, PactType.BinderFreshFor,
              PactType.BinderFreshForBranches, hFields.1]
      | cons next tail =>
          by_cases hSelected : (action, processType) = selected
          · simp [parallelTypeBranchesSelecting, hSelected,
              selectedTypeBranch, PactType.BinderFreshFor, hFields.1,
              binderFreshFor_parallelTypeBranches_policy forbidden
                (next :: tail) hFields.2]
          · simp [parallelTypeBranchesSelecting, hSelected,
              singletonTypeXOffer, PactType.BinderFreshFor,
              PactType.BinderFreshForBranches, hFields.1, ih hFields.2]

private theorem PolicyTypeOffers.target_binderFreshFor
    {env : TypeEnvironment} {source : PactType} {label : TypeLabel}
    {target : PactType} {current : Finset BareMessage}
    {policy : SemanticFuturePolicy}
    (hOffers : PolicyTypeOffers env source label target current policy) :
    ∀ forbidden, source.BinderFreshFor forbidden →
      target.BinderFreshFor forbidden := by
  intro forbidden hFresh
  induction hOffers with
  | action | action_wait | cycle | cycle_wait | skip | progress =>
      simp [PactType.BinderFreshFor]
  | choice_left env left right h =>
      have hFields : left.BinderFreshFor forbidden ∧
          right.BinderFreshFor forbidden := by
        simpa only [PactType.BinderFreshFor] using hFresh
      exact hFields.1
  | choice_right env left right h =>
      have hFields : left.BinderFreshFor forbidden ∧
          right.BinderFreshFor forbidden := by
        simpa only [PactType.BinderFreshFor] using hFresh
      exact hFields.2
  | fair_left env bid left right h =>
      have hFields : left.BinderFreshFor forbidden ∧
          right.BinderFreshFor forbidden := by
        simpa only [PactType.BinderFreshFor] using hFresh
      exact hFields.1
  | fair_right env bid left right h =>
      have hFields : left.BinderFreshFor forbidden ∧
          right.BinderFreshFor forbidden := by
        simpa only [PactType.BinderFreshFor] using hFresh
      exact hFields.2
  | skip_seq env processType h =>
      have hFields : PactType.skip.BinderFreshFor forbidden ∧
          processType.BinderFreshFor forbidden := by
        simpa only [PactType.BinderFreshFor] using hFresh
      exact hFields.2
  | recur env binder body h =>
      have hFields : binder ∉ forbidden ∧ body.BinderFreshFor forbidden := by
        simpa only [PactType.BinderFreshFor] using hFresh
      apply PactType.replaceVar_binderFreshFor_same forbidden binder
        (.recur binder body)
      · simpa only [PactType.BinderFreshFor] using hFields
      · exact hFields.2
  | seq env left left' right childLabel childCurrent childPolicy hChild ih =>
      have hFields : left.BinderFreshFor forbidden ∧
          right.BinderFreshFor forbidden := by
        simpa only [PactType.BinderFreshFor] using hFresh
      simpa only [PactType.BinderFreshFor] using
        And.intro (ih hFields.1) hFields.2
  | xoffer_branch env elseType branches action processType h =>
      have hFields : elseType.BinderFreshFor forbidden ∧
          PactType.BinderFreshForBranches forbidden branches := by
        simpa only [PactType.BinderFreshFor] using hFresh
      exact binderFreshFor_branch_of_mem_policy forbidden branches
        (action, processType) hFields.2 h.2.1
  | xoffer_else env elseType branches h =>
      have hFields : elseType.BinderFreshFor forbidden ∧
          PactType.BinderFreshForBranches forbidden branches := by
        simpa only [PactType.BinderFreshFor] using hFresh
      exact hFields.1
  | xoffer_wait => exact hFresh
  | offer_some env elseType branches enabled h =>
      have hFields : elseType.BinderFreshFor forbidden ∧
          PactType.BinderFreshForBranches forbidden branches := by
        simpa only [PactType.BinderFreshFor] using hFresh
      exact binderFreshFor_parallelTypeBranchesSelecting_policy forbidden
        enabled branches hFields.2
  | offer_else env elseType branches h =>
      have hFields : elseType.BinderFreshFor forbidden ∧
          PactType.BinderFreshForBranches forbidden branches := by
        simpa only [PactType.BinderFreshFor] using hFresh
      exact hFields.1
  | offer_wait => exact hFresh
  | par outer leftEnv rightEnv interface left left' right right' leftLabel
      rightLabel leftCurrent rightCurrent leftPolicy rightPolicy hLeft hRight
      hLocalLeft hLocalRight hSync ihLeft ihRight =>
      have hFields : left.BinderFreshFor forbidden ∧
          right.BinderFreshFor forbidden := by
        simpa only [PactType.BinderFreshFor] using hFresh
      simpa only [PactType.BinderFreshFor] using
        And.intro (ihLeft hFields.1) (ihRight hFields.2)

private theorem PolicyTypeOffers.toTypeOffers
    {env : TypeEnvironment} {source : PactType} {label : TypeLabel}
    {target : PactType} {current : Finset BareMessage}
    {policy : SemanticFuturePolicy}
    (hOffers : PolicyTypeOffers env source label target current policy) :
    TypeOffers env source label target current
      (resolveSemanticFuture target policy) := by
  induction hOffers with
  | action env msg dir h =>
      simpa [resolveSemanticFuture, typeFutureOffers, typeFutureOffersFuel] using
        (TypeOffers.action env msg dir h)
  | action_wait env msg dir h =>
      simpa [resolveSemanticFuture, typeFutureOffers, typeFutureOffersFuel] using
        (TypeOffers.action_wait env msg dir h)
  | choice_left env left right h =>
      simpa [resolveSemanticFuture] using
        (TypeOffers.choice_left env left right h)
  | choice_right env left right h =>
      simpa [resolveSemanticFuture] using
        (TypeOffers.choice_right env left right h)
  | fair_left env bid left right h =>
      simpa [resolveSemanticFuture] using
        (TypeOffers.fair_left env bid left right h)
  | fair_right env bid left right h =>
      simpa [resolveSemanticFuture] using
        (TypeOffers.fair_right env bid left right h)
  | cycle env h =>
      simpa [resolveSemanticFuture] using (TypeOffers.cycle env h)
  | cycle_wait env h =>
      simpa [resolveSemanticFuture] using (TypeOffers.cycle_wait env h)
  | skip env h =>
      simpa [resolveSemanticFuture] using (TypeOffers.skip env h)
  | skip_seq env processType h =>
      simpa [resolveSemanticFuture] using
        (TypeOffers.skip_seq env processType h)
  | progress env pid h =>
      simpa [resolveSemanticFuture] using (TypeOffers.progress env pid h)
  | recur env binder body h =>
      simpa [resolveSemanticFuture] using (TypeOffers.recur env binder body h)
  | seq env left left' right label current childPolicy hChild ih =>
      simpa [resolveSemanticFuture] using
        (TypeOffers.seq env left left' right label current
          (resolveSemanticFuture left' childPolicy) ih)
  | xoffer_branch env elseType branches action processType h =>
      simpa [resolveSemanticFuture] using
        TypeOffers.xoffer_branch env elseType branches action processType h
  | xoffer_else env elseType branches h =>
      simpa [resolveSemanticFuture] using
        TypeOffers.xoffer_else env elseType branches h
  | xoffer_wait env elseType branches h =>
      simpa [resolveSemanticFuture] using
        TypeOffers.xoffer_wait env elseType branches h
  | offer_some env elseType branches enabled h =>
      simpa [resolveSemanticFuture] using
        TypeOffers.offer_some env elseType branches enabled h
  | offer_else env elseType branches h =>
      simpa [resolveSemanticFuture] using
        TypeOffers.offer_else env elseType branches h
  | offer_wait env elseType branches h =>
      simpa [resolveSemanticFuture] using
        TypeOffers.offer_wait env elseType branches h
  | par outer leftEnv rightEnv interface left left' right right' leftLabel
      rightLabel leftCurrent rightCurrent leftPolicy rightPolicy hLeft hRight
      hLocalLeft hLocalRight hSync ihLeft ihRight =>
      exact TypeOffers.par outer leftEnv rightEnv interface left left' right
        right' leftLabel rightLabel leftCurrent
        (resolveSemanticFuture left' leftPolicy) rightCurrent
        (resolveSemanticFuture right' rightPolicy) ihLeft ihRight hLocalLeft
          hLocalRight hSync

private theorem typeOffers_toPolicy :
    ∀ source : PactType, ∀ env label target current future,
      TypeOffers env source label target current future →
        ∃ policy,
          PolicyTypeOffers env source label target current policy ∧
            future = resolveSemanticFuture target policy := by
  intro source
  induction hSize : sizeOf source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
      intro env label target current future hOffers
      cases source with
      | message msg dir =>
          cases hOffers with
          | action env _ _ h =>
              exact ⟨.explicit ∅, PolicyTypeOffers.action env msg dir h, by
                simp [resolveSemanticFuture, typeFutureOffers,
                  typeFutureOffersFuel]⟩
          | action_wait env _ _ h =>
              exact ⟨.explicit ∅,
                PolicyTypeOffers.action_wait env msg dir h, by
                  simp [resolveSemanticFuture, typeFutureOffers,
                    typeFutureOffersFuel]⟩
      | progress pid =>
          cases hOffers with
          | progress env _ h =>
              exact ⟨.explicit ∅, PolicyTypeOffers.progress env pid h, by
                simp [resolveSemanticFuture]⟩
      | tock =>
          cases hOffers with
          | cycle env h =>
              exact ⟨.explicit ∅, PolicyTypeOffers.cycle env h, by
                simp [resolveSemanticFuture]⟩
          | cycle_wait env h =>
              exact ⟨.explicit ∅, PolicyTypeOffers.cycle_wait env h, by
                simp [resolveSemanticFuture]⟩
      | skip =>
          cases hOffers with
          | skip env h =>
              exact ⟨.explicit ∅, PolicyTypeOffers.skip env h, by
                simp [resolveSemanticFuture]⟩
      | var name => cases hOffers
      | recur binder body =>
          cases hOffers with
          | recur env _ _ h =>
              exact ⟨.subtract ∅,
                PolicyTypeOffers.recur env binder body h, by
                  simp [resolveSemanticFuture]⟩
      | choice left right =>
          cases hOffers with
          | choice_left env _ _ h =>
              exact ⟨.subtract ∅,
                PolicyTypeOffers.choice_left env _ _ h, by
                  simp [resolveSemanticFuture]⟩
          | choice_right env _ _ h =>
              exact ⟨.subtract ∅,
                PolicyTypeOffers.choice_right env _ _ h, by
                  simp [resolveSemanticFuture]⟩
      | fairChoice bid left right =>
          cases hOffers with
          | fair_left env _ _ _ h =>
              exact ⟨.subtract ∅,
                PolicyTypeOffers.fair_left env bid _ _ h, by
                  simp [resolveSemanticFuture]⟩
          | fair_right env _ _ _ h =>
              exact ⟨.subtract ∅,
                PolicyTypeOffers.fair_right env bid _ _ h, by
                  simp [resolveSemanticFuture]⟩
      | seq left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          cases hOffers with
          | skip_seq env _ h =>
              exact ⟨.subtract ∅,
                PolicyTypeOffers.skip_seq env _ h, by
                  simp [resolveSemanticFuture]⟩
          | seq env _ leftTarget _ childLabel childCurrent childFuture hChild =>
              obtain ⟨childPolicy, hChildPolicy, hChildFuture⟩ :=
                ih (sizeOf left) hLeftSize left rfl env label leftTarget
                  current childFuture hChild
              exact ⟨.subtract current,
                PolicyTypeOffers.seq env left leftTarget right label
                  current childPolicy hChildPolicy, by
                    simp [resolveSemanticFuture]⟩
      | xoffer elseType branches =>
          cases hOffers with
          | xoffer_branch env _ _ action processType h =>
              exact ⟨.subtract ∅,
                PolicyTypeOffers.xoffer_branch env _ _ action _ h, by
                  simp [resolveSemanticFuture]⟩
          | xoffer_else env _ _ h =>
              exact ⟨.subtract ∅,
                PolicyTypeOffers.xoffer_else env _ _ h, by
                  simp [resolveSemanticFuture]⟩
          | xoffer_wait env _ _ h =>
              exact ⟨.subtract (typeWaitingOffers env _),
                PolicyTypeOffers.xoffer_wait env _ _ h, by
                  simp [resolveSemanticFuture]⟩
      | offer elseType branches =>
          cases hOffers with
          | offer_some env _ _ enabled h =>
              exact ⟨.subtract ∅,
                PolicyTypeOffers.offer_some env _ _ enabled h, by
                  simp [resolveSemanticFuture]⟩
          | offer_else env _ _ h =>
              exact ⟨.subtract ∅,
                PolicyTypeOffers.offer_else env _ _ h, by
                  simp [resolveSemanticFuture]⟩
          | offer_wait env _ _ h =>
              exact ⟨.subtract (typeWaitingOffers env _),
                PolicyTypeOffers.offer_wait env _ _ h, by
                  simp [resolveSemanticFuture]⟩
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          cases hOffers with
          | par outer leftEnv rightEnv _ _ leftTarget _ rightTarget leftLabel
              rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeft
              hRight hLocalLeft hLocalRight hSync =>
              obtain ⟨leftPolicy, hLeftPolicy, hLeftFuture⟩ :=
                ih (sizeOf left) hLeftSize left rfl leftEnv leftLabel leftTarget
                  leftCurrent leftFuture hLeft
              obtain ⟨rightPolicy, hRightPolicy, hRightFuture⟩ :=
                ih (sizeOf right) hRightSize right rfl rightEnv rightLabel
                  rightTarget rightCurrent rightFuture hRight
              refine ⟨.explicit (hideTypeOffers interface
                  (resolveSemanticFuture leftTarget leftPolicy ∪
                    resolveSemanticFuture rightTarget rightPolicy)),
                PolicyTypeOffers.par env leftEnv rightEnv interface left
                  leftTarget right rightTarget leftLabel rightLabel leftCurrent
                  rightCurrent leftPolicy rightPolicy hLeftPolicy hRightPolicy
                  hLocalLeft hLocalRight hSync, ?_⟩
              rw [hLeftFuture, hRightFuture]
              rfl

private theorem typeBranchNeeds_replaceBranches
    (branches : List (BareMessage × PactType)) (name : String)
    (replacement : PactType) :
    typeBranchNeeds (PactType.replaceBranches branches name replacement) =
      typeBranchNeeds branches := by
  unfold typeBranchNeeds
  apply congrArg List.toFinset
  calc
    List.map (fun branch => typeNeed branch.1)
        (PactType.replaceBranches branches name replacement) =
      List.map typeNeed
        (List.map Prod.fst
          (PactType.replaceBranches branches name replacement)) := by
            simp only [List.map_map, Function.comp_def]
    _ = List.map typeNeed (List.map Prod.fst branches) := by
      rw [PactType.replaceBranches_map_fst]
    _ = List.map (fun branch => typeNeed branch.1) branches := by
      simp only [List.map_map, Function.comp_def]

private theorem typeBranchActions_replaceBranches
    (branches : List (BareMessage × PactType)) (name : String)
    (replacement : PactType) :
    typeBranchActions (PactType.replaceBranches branches name replacement) =
      typeBranchActions branches := by
  simp only [typeBranchActions, PactType.replaceBranches_map_fst]

private theorem typeWaitingOffers_replaceBranches
    (env : TypeEnvironment) (branches : List (BareMessage × PactType))
    (name : String) (replacement : PactType) :
    typeWaitingOffers env
        (PactType.replaceBranches branches name replacement) =
      typeWaitingOffers env branches := by
  simp only [typeWaitingOffers,
    typeBranchActions_replaceBranches]

/- Tail-position substitution preserves the exact raw-edge future policy. -/
private theorem policyTypeOffers_replaceVar_forward
    (bound : List String) (name : String) (body : PactType)
    (hBoundBody : body.AllVariablesBound (name :: bound)) :
    ∀ {env : TypeEnvironment} {source : PactType} {label : TypeLabel}
      {target : PactType} {current : Finset BareMessage}
      {policy : SemanticFuturePolicy},
      source.TailOccurrences name True →
      source.AllVariablesBound (name :: bound) →
      source.BinderFreshFor (name :: bound) →
      PolicyTypeOffers env source label target current policy →
      PolicyTypeOffers env
        (source.replaceVar name (.recur name body)) label
        (target.replaceVar name (.recur name body)) current policy := by
  intro env source label target current policy hTail hBound hFresh hOffers
  let recursiveType := PactType.recur name body
  have hRecursiveBound : recursiveType.AllVariablesBound bound := by
    simpa [recursiveType, PactType.AllVariablesBound] using hBoundBody
  induction hOffers with
  | action env msg dir h =>
      simpa [recursiveType, PactType.replaceVar] using
        (PolicyTypeOffers.action env msg dir h)
  | action_wait env msg dir h =>
      simpa [recursiveType, PactType.replaceVar] using
        (PolicyTypeOffers.action_wait env msg dir h)
  | choice_left env left right h =>
      simpa [recursiveType, PactType.replaceVar] using
        (PolicyTypeOffers.choice_left env
          (left.replaceVar name recursiveType)
          (right.replaceVar name recursiveType) h)
  | choice_right env left right h =>
      simpa [recursiveType, PactType.replaceVar] using
        (PolicyTypeOffers.choice_right env
          (left.replaceVar name recursiveType)
          (right.replaceVar name recursiveType) h)
  | fair_left env bid left right h =>
      simpa [recursiveType, PactType.replaceVar] using
        (PolicyTypeOffers.fair_left env bid
          (left.replaceVar name recursiveType)
          (right.replaceVar name recursiveType) h)
  | fair_right env bid left right h =>
      simpa [recursiveType, PactType.replaceVar] using
        (PolicyTypeOffers.fair_right env bid
          (left.replaceVar name recursiveType)
          (right.replaceVar name recursiveType) h)
  | cycle env h =>
      simpa [recursiveType, PactType.replaceVar] using
        (PolicyTypeOffers.cycle env h)
  | cycle_wait env h =>
      simpa [recursiveType, PactType.replaceVar] using
        (PolicyTypeOffers.cycle_wait env h)
  | skip env h =>
      simpa [recursiveType, PactType.replaceVar] using
        (PolicyTypeOffers.skip env h)
  | skip_seq env processType h =>
      simpa [recursiveType, PactType.replaceVar] using
        (PolicyTypeOffers.skip_seq env
          (processType.replaceVar name recursiveType) h)
  | progress env pid h =>
      simpa [recursiveType, PactType.replaceVar] using
        (PolicyTypeOffers.progress env pid h)
  | recur env binder nestedBody h =>
      have hFreshFields : binder ∉ name :: bound ∧
          nestedBody.BinderFreshFor (name :: bound) := by
        simpa only [PactType.BinderFreshFor] using hFresh
      have hDistinct : ¬ name = binder := by
        intro hEq
        exact hFreshFields.1 (by simp [hEq])
      have hBinderNotBound : binder ∉ bound := by
        intro hMem
        exact hFreshFields.1 (List.mem_cons_of_mem name hMem)
      have hRecursiveTailFalse :
          recursiveType.TailOccurrences binder False :=
        PactType.tailOccurrences_false_of_allVariablesBound_not_mem binder
          bound recursiveType hRecursiveBound hBinderNotBound
      have hRecursiveClosed : ∀ q,
          recursiveType.replaceVar binder q = recursiveType := by
        intro q
        exact PactType.replaceVar_eq_self_of_tailOccurrences_false binder q
          recursiveType hRecursiveTailFalse
      have hNestedFresh : nestedBody.BinderFreshFor [name] :=
        PactType.binderFreshFor_mono
          (by
            intro x hx
            rw [List.mem_singleton] at hx
            subst x
            exact List.mem_cons_self)
          nestedBody hFreshFields.2
      have hComm := PactType.replaceVar_comm name binder recursiveType
        (.recur binder nestedBody) hDistinct hRecursiveClosed nestedBody
          hNestedFresh
      have hTarget :
          ((nestedBody.replaceVar binder (.recur binder nestedBody)).replaceVar
              name recursiveType) =
            (nestedBody.replaceVar name recursiveType).replaceVar binder
              (.recur binder (nestedBody.replaceVar name recursiveType)) := by
        simpa [PactType.replaceVar, hDistinct] using hComm
      rw [PactType.replaceVar, if_neg hDistinct, hTarget]
      exact PolicyTypeOffers.recur env binder
        (nestedBody.replaceVar name recursiveType) h
  | seq env left left' right label current childPolicy hChild =>
      have hTailFields : left.TailOccurrences name False ∧
          right.TailOccurrences name True := by
        simpa only [PactType.TailOccurrences] using hTail
      have hLeftUnchanged :=
        PactType.replaceVar_eq_self_of_tailOccurrences_false name recursiveType
          left hTailFields.1
      have hLeftTargetTail := typeOffers_tailOccurrences_false name left env
        label left' current (resolveSemanticFuture left' childPolicy)
          hChild.toTypeOffers hTailFields.1
      have hLeftTargetUnchanged :=
        PactType.replaceVar_eq_self_of_tailOccurrences_false name recursiveType
          left' hLeftTargetTail
      simpa only [recursiveType, PactType.replaceVar, hLeftUnchanged,
        hLeftTargetUnchanged] using
          (PolicyTypeOffers.seq env left left'
            (right.replaceVar name recursiveType) label current childPolicy
            hChild)
  | xoffer_branch env elseType branches action processType h =>
      have hMember : (action,
          processType.replaceVar name recursiveType) ∈
          PactType.replaceBranches branches name recursiveType :=
        PactType.mem_replaceBranches name recursiveType action processType
          branches h.2.1
      have hFields : env.WellFormed ∧
          (action, processType.replaceVar name recursiveType) ∈
            PactType.replaceBranches branches name recursiveType ∧
          TypeBranchEnabled env
            (action, processType.replaceVar name recursiveType) ∧
          TypeResolved env
            (PactType.replaceBranches branches name recursiveType) := by
        simpa only [TypeResolved,
          typeBranchNeeds_replaceBranches] using
            And.intro h.1 (And.intro hMember h.2.2)
      simpa [recursiveType, PactType.replaceVar] using
        (PolicyTypeOffers.xoffer_branch env
          (elseType.replaceVar name recursiveType)
          (PactType.replaceBranches branches name recursiveType) action
          (processType.replaceVar name recursiveType) hFields)
  | xoffer_else env elseType branches h =>
      have hFields : env.WellFormed ∧
          TypeNoImmediateBranch env
            (PactType.replaceBranches branches name recursiveType) ∧
          TypeResolved env
            (PactType.replaceBranches branches name recursiveType) := by
        simpa only [TypeNoImmediateBranch, TypeResolved,
          typeBranchNeeds_replaceBranches] using h
      simpa [recursiveType, PactType.replaceVar] using
        (PolicyTypeOffers.xoffer_else env
          (elseType.replaceVar name recursiveType)
          (PactType.replaceBranches branches name recursiveType) hFields)
  | xoffer_wait env elseType branches h =>
      have hFields : env.WellFormed ∧
          ¬ TypeResolved env
            (PactType.replaceBranches branches name recursiveType) ∧
          env.clock = false := by
        simpa only [TypeResolved,
          typeBranchNeeds_replaceBranches] using h
      simpa only [recursiveType, PactType.replaceVar,
        typeWaitingOffers_replaceBranches] using
          (PolicyTypeOffers.xoffer_wait env
            (elseType.replaceVar name recursiveType)
            (PactType.replaceBranches branches name recursiveType) hFields)
  | offer_some env elseType branches enabled h =>
      have hTailFields : elseType.TailOccurrences name True ∧
          PactType.TailBranchOccurrences name False branches := by
        simpa only [PactType.TailOccurrences] using hTail
      have hBranchesUnchanged :=
        PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false name
          recursiveType branches hTailFields.2
      have hTargetTail :
          (parallelTypeBranchesSelecting enabled branches).TailOccurrences
            name False :=
        tailOccurrences_parallelTypeBranchesSelecting name enabled branches
          hTailFields.2
      have hTargetUnchanged :=
        PactType.replaceVar_eq_self_of_tailOccurrences_false name recursiveType
          (parallelTypeBranchesSelecting enabled branches) hTargetTail
      rw [PactType.replaceVar, hBranchesUnchanged, hTargetUnchanged]
      exact PolicyTypeOffers.offer_some env
        (elseType.replaceVar name recursiveType) branches enabled h
  | offer_else env elseType branches h =>
      have hTailFields : elseType.TailOccurrences name True ∧
          PactType.TailBranchOccurrences name False branches := by
        simpa only [PactType.TailOccurrences] using hTail
      have hBranchesUnchanged :=
        PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false name
          recursiveType branches hTailFields.2
      rw [PactType.replaceVar, hBranchesUnchanged]
      exact PolicyTypeOffers.offer_else env
        (elseType.replaceVar name recursiveType) branches h
  | offer_wait env elseType branches h =>
      have hTailFields : elseType.TailOccurrences name True ∧
          PactType.TailBranchOccurrences name False branches := by
        simpa only [PactType.TailOccurrences] using hTail
      have hBranchesUnchanged :=
        PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false name
          recursiveType branches hTailFields.2
      rw [PactType.replaceVar, hBranchesUnchanged]
      exact PolicyTypeOffers.offer_wait env
        (elseType.replaceVar name recursiveType) branches h
  | par outer leftEnv rightEnv interface left left' right right' leftLabel
      rightLabel leftCurrent rightCurrent leftPolicy rightPolicy hLeft hRight
      hLocalLeft hLocalRight hSync =>
      have hTailFields : left.TailOccurrences name False ∧
          right.TailOccurrences name False := by
        simpa only [PactType.TailOccurrences] using hTail
      have hWholeTailFalse :
          (PactType.par left right interface).TailOccurrences name False := by
        simpa only [PactType.TailOccurrences] using hTailFields
      have hSourceUnchanged :
          (PactType.par left right interface).replaceVar name recursiveType =
            .par left right interface := by
        exact PactType.replaceVar_eq_self_of_tailOccurrences_false name
          recursiveType (.par left right interface) hWholeTailFalse
      have hTargetTail := typeOffers_tailOccurrences_false name
        (.par left right interface) outer
          (TypeLabel.combine interface leftLabel rightLabel)
          (.par left' right' interface)
          (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
          (hideTypeOffers interface
            (resolveSemanticFuture left' leftPolicy ∪
              resolveSemanticFuture right' rightPolicy))
          (PolicyTypeOffers.toTypeOffers
            (PolicyTypeOffers.par outer leftEnv rightEnv interface left left'
              right right' leftLabel rightLabel leftCurrent rightCurrent
              leftPolicy rightPolicy hLeft hRight hLocalLeft hLocalRight hSync))
          hWholeTailFalse
      have hTargetUnchanged :=
        PactType.replaceVar_eq_self_of_tailOccurrences_false name recursiveType
          (.par left' right' interface) hTargetTail
      rw [hSourceUnchanged, hTargetUnchanged]
      exact PolicyTypeOffers.par outer leftEnv rightEnv interface left left'
        right right' leftLabel rightLabel leftCurrent rightCurrent leftPolicy
          rightPolicy hLeft hRight hLocalLeft hLocalRight hSync

/- Away from the substituted marker, every policy step of the substituted
residual comes from the same exact policy step before substitution. -/
private theorem policyTypeOffers_replaceVar_backward
    (bound : List String) (name : String) (body : PactType)
    (hBoundBody : body.AllVariablesBound (name :: bound)) :
    ∀ {env : TypeEnvironment} {source : PactType} {label : TypeLabel}
      {target : PactType} {current : Finset BareMessage}
      {policy : SemanticFuturePolicy},
      source.TailOccurrences name True →
      source.AllVariablesBound (name :: bound) →
      source.BinderFreshFor (name :: bound) →
      source ≠ .var name →
      PolicyTypeOffers env
          (source.replaceVar name (.recur name body)) label target current
            policy →
      ∃ bodyTarget,
        PolicyTypeOffers env source label bodyTarget current policy ∧
          target = bodyTarget.replaceVar name (.recur name body) := by
  intro env source label target current policy hTail hBound hFresh hNotMarker
    hOffers
  let recursiveType := PactType.recur name body
  have hRecursiveBound : recursiveType.AllVariablesBound bound := by
    simpa [recursiveType, PactType.AllVariablesBound] using hBoundBody
  cases source with
  | message msg dir =>
      simp only [PactType.replaceVar] at hOffers
      cases hOffers with
      | action env _ _ h =>
          exact ⟨.skip, PolicyTypeOffers.action env msg dir h, by
            simp [PactType.replaceVar]⟩
      | action_wait env _ _ h =>
          exact ⟨.message msg dir, PolicyTypeOffers.action_wait env msg dir h,
            by simp [PactType.replaceVar]⟩
  | progress pid =>
      simp only [PactType.replaceVar] at hOffers
      cases hOffers with
      | progress env _ h =>
          exact ⟨.skip, PolicyTypeOffers.progress env pid h, by
            simp [PactType.replaceVar]⟩
  | tock =>
      simp only [PactType.replaceVar] at hOffers
      cases hOffers with
      | cycle env h =>
          exact ⟨.skip, PolicyTypeOffers.cycle env h, by
            simp [PactType.replaceVar]⟩
      | cycle_wait env h =>
          exact ⟨.tock, PolicyTypeOffers.cycle_wait env h, by
            simp [PactType.replaceVar]⟩
  | skip =>
      simp only [PactType.replaceVar] at hOffers
      cases hOffers with
      | skip env h =>
          exact ⟨.skip, PolicyTypeOffers.skip env h, by
            simp [PactType.replaceVar]⟩
  | var other =>
      by_cases hName : other = name
      · subst other
        exact (hNotMarker rfl).elim
      · simp only [PactType.replaceVar, if_neg (Ne.symm hName)] at hOffers
        cases hOffers
  | choice left right =>
      simp only [PactType.replaceVar] at hOffers
      cases hOffers with
      | choice_left env _ _ h =>
          exact ⟨left, PolicyTypeOffers.choice_left env left right h, rfl⟩
      | choice_right env _ _ h =>
          exact ⟨right, PolicyTypeOffers.choice_right env left right h, rfl⟩
  | fairChoice bid left right =>
      simp only [PactType.replaceVar] at hOffers
      cases hOffers with
      | fair_left env _ _ _ h =>
          exact ⟨left, PolicyTypeOffers.fair_left env bid left right h, rfl⟩
      | fair_right env _ _ _ h =>
          exact ⟨right, PolicyTypeOffers.fair_right env bid left right h, rfl⟩
  | seq left right =>
      have hTailFields : left.TailOccurrences name False ∧
          right.TailOccurrences name True := by
        simpa only [PactType.TailOccurrences] using hTail
      have hLeftUnchanged :=
        PactType.replaceVar_eq_self_of_tailOccurrences_false name recursiveType
          left hTailFields.1
      simp only [PactType.replaceVar, recursiveType, hLeftUnchanged] at hOffers
      cases hOffers with
      | skip_seq env processType h =>
          exact ⟨right, PolicyTypeOffers.skip_seq env right h, rfl⟩
      | seq env _ leftTarget _ childLabel childCurrent childPolicy hChild =>
          have hLeftTargetTail := typeOffers_tailOccurrences_false name left env
            label leftTarget current
              (resolveSemanticFuture leftTarget childPolicy)
              hChild.toTypeOffers hTailFields.1
          have hLeftTargetUnchanged :=
            PactType.replaceVar_eq_self_of_tailOccurrences_false name
              recursiveType leftTarget hLeftTargetTail
          refine ⟨.seq leftTarget right,
            PolicyTypeOffers.seq env left leftTarget right label
              current childPolicy hChild, ?_⟩
          simp only [PactType.replaceVar, recursiveType, hLeftTargetUnchanged]
  | recur binder nestedBody =>
      have hFreshFields : binder ∉ name :: bound ∧
          nestedBody.BinderFreshFor (name :: bound) := by
        simpa only [PactType.BinderFreshFor] using hFresh
      have hDistinct : ¬ name = binder := by
        intro hEq
        exact hFreshFields.1 (by simp [hEq])
      have hBinderNotBound : binder ∉ bound := by
        intro hMem
        exact hFreshFields.1 (List.mem_cons_of_mem name hMem)
      have hRecursiveTailFalse :
          recursiveType.TailOccurrences binder False :=
        PactType.tailOccurrences_false_of_allVariablesBound_not_mem binder
          bound recursiveType hRecursiveBound hBinderNotBound
      have hRecursiveClosed : ∀ q,
          recursiveType.replaceVar binder q = recursiveType := by
        intro q
        exact PactType.replaceVar_eq_self_of_tailOccurrences_false binder q
          recursiveType hRecursiveTailFalse
      have hNestedFresh : nestedBody.BinderFreshFor [name] :=
        PactType.binderFreshFor_mono
          (by
            intro x hx
            rw [List.mem_singleton] at hx
            subst x
            exact List.mem_cons_self)
          nestedBody hFreshFields.2
      have hComm := PactType.replaceVar_comm name binder recursiveType
        (.recur binder nestedBody) hDistinct hRecursiveClosed nestedBody
          hNestedFresh
      have hTarget :
          ((nestedBody.replaceVar binder (.recur binder nestedBody)).replaceVar
              name recursiveType) =
            (nestedBody.replaceVar name recursiveType).replaceVar binder
              (.recur binder (nestedBody.replaceVar name recursiveType)) := by
        simpa [PactType.replaceVar, hDistinct] using hComm
      simp only [PactType.replaceVar, if_neg hDistinct] at hOffers
      cases hOffers with
      | recur env _ _ h =>
          refine ⟨nestedBody.replaceVar binder (.recur binder nestedBody),
            PolicyTypeOffers.recur env binder nestedBody h, ?_⟩
          exact hTarget.symm
  | xoffer elseType branches =>
      simp only [PactType.replaceVar] at hOffers
      cases hOffers with
      | xoffer_branch env substitutedElse substitutedBranches action
          substitutedType h =>
          obtain ⟨original, hMember, hOriginal⟩ :=
            PactType.mem_replaceBranches_cases name recursiveType
              (action, target) branches h.2.1
          obtain ⟨originalAction, originalType⟩ := original
          simp only [Prod.fst, Prod.snd, Prod.mk.injEq] at hOriginal
          obtain ⟨rfl, hType⟩ := hOriginal
          have hFields : env.WellFormed ∧
              (action, originalType) ∈ branches ∧
              TypeBranchEnabled env (action, originalType) ∧
              TypeResolved env branches := by
            simpa only [TypeResolved, typeBranchNeeds_replaceBranches] using
              And.intro h.1 (And.intro hMember h.2.2)
          exact ⟨originalType,
            PolicyTypeOffers.xoffer_branch env elseType branches action
              originalType hFields, hType⟩
      | xoffer_else env substitutedElse substitutedBranches h =>
          have hFields : env.WellFormed ∧ TypeNoImmediateBranch env branches ∧
              TypeResolved env branches := by
            simpa only [TypeNoImmediateBranch, TypeResolved,
              typeBranchNeeds_replaceBranches] using h
          exact ⟨elseType,
            PolicyTypeOffers.xoffer_else env elseType branches hFields, rfl⟩
      | xoffer_wait env substitutedElse substitutedBranches h =>
          have hFields : env.WellFormed ∧ ¬ TypeResolved env branches ∧
              env.clock = false := by
            simpa only [TypeResolved, typeBranchNeeds_replaceBranches] using h
          refine ⟨.xoffer elseType branches,
            ?_, ?_⟩
          · simpa only [typeWaitingOffers_replaceBranches] using
              (PolicyTypeOffers.xoffer_wait env elseType branches hFields)
          simp only [PactType.replaceVar]
  | offer elseType branches =>
      have hTailFields : elseType.TailOccurrences name True ∧
          PactType.TailBranchOccurrences name False branches := by
        simpa only [PactType.TailOccurrences] using hTail
      have hBranchesUnchanged :=
        PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false name
          recursiveType branches hTailFields.2
      simp only [PactType.replaceVar, recursiveType, hBranchesUnchanged]
        at hOffers
      cases hOffers with
      | offer_some env _ _ enabled h =>
          have hTargetTail :
              (parallelTypeBranchesSelecting enabled branches).TailOccurrences
                name False :=
            tailOccurrences_parallelTypeBranchesSelecting name enabled branches
              hTailFields.2
          have hTargetUnchanged :=
            PactType.replaceVar_eq_self_of_tailOccurrences_false name
              recursiveType (parallelTypeBranchesSelecting enabled branches)
                hTargetTail
          refine ⟨parallelTypeBranchesSelecting enabled branches,
            PolicyTypeOffers.offer_some env elseType branches enabled h, ?_⟩
          exact hTargetUnchanged.symm

      | offer_else env _ _ h =>
          exact ⟨elseType,
            PolicyTypeOffers.offer_else env elseType branches h, rfl⟩
      | offer_wait env _ _ h =>
          refine ⟨.offer elseType branches,
            PolicyTypeOffers.offer_wait env elseType branches h, ?_⟩
          simp only [PactType.replaceVar, recursiveType, hBranchesUnchanged]
  | par left right interface =>
      have hTailFields : left.TailOccurrences name False ∧
          right.TailOccurrences name False := by
        simpa only [PactType.TailOccurrences] using hTail
      have hWholeTailFalse :
          (PactType.par left right interface).TailOccurrences name False := by
        simpa only [PactType.TailOccurrences] using hTailFields
      have hSourceUnchanged :=
        PactType.replaceVar_eq_self_of_tailOccurrences_false name recursiveType
          (.par left right interface) hWholeTailFalse
      rw [hSourceUnchanged] at hOffers
      cases hOffers with
      | par outer leftEnv rightEnv _ _ leftTarget _ rightTarget leftLabel
          rightLabel leftCurrent rightCurrent leftPolicy rightPolicy hLeft
          hRight hLocalLeft hLocalRight hSync =>
          have hTargetTail := typeOffers_tailOccurrences_false name
            (.par left right interface) env
              (TypeLabel.combine interface leftLabel rightLabel)
              (.par leftTarget rightTarget interface)
              (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
              (hideTypeOffers interface
                (resolveSemanticFuture leftTarget leftPolicy ∪
                  resolveSemanticFuture rightTarget rightPolicy))
              (PolicyTypeOffers.toTypeOffers
                (PolicyTypeOffers.par env leftEnv rightEnv interface left
                  leftTarget right rightTarget leftLabel rightLabel leftCurrent
                  rightCurrent leftPolicy rightPolicy hLeft hRight hLocalLeft
                  hLocalRight hSync)) hWholeTailFalse
          have hTargetUnchanged :=
            PactType.replaceVar_eq_self_of_tailOccurrences_false name
              recursiveType (.par leftTarget rightTarget interface) hTargetTail
          refine ⟨.par leftTarget rightTarget interface,
            PolicyTypeOffers.par env leftEnv rightEnv interface left
              leftTarget right rightTarget leftLabel rightLabel leftCurrent
              rightCurrent leftPolicy rightPolicy hLeft hRight hLocalLeft
              hLocalRight hSync, ?_⟩
          exact hTargetUnchanged.symm

private def futureSpecMatchesPolicy (edge : PendingAutomatonEdge) :
    SemanticFuturePolicy → Prop
  | .explicit _ => ∃ future, edge.future = .explicit future
  | .subtract removed => edge.future = .at edge.target removed

private theorem futureSpecMatchesPolicy_childPendingEdge
    (index : Nat) (edge : PendingAutomatonEdge)
    (policy : SemanticFuturePolicy) :
    futureSpecMatchesPolicy (childPendingEdge index edge) policy ↔
      futureSpecMatchesPolicy edge policy := by
  cases policy with
  | explicit future =>
      simp only [futureSpecMatchesPolicy]
      constructor
      · rintro ⟨offers, hOffers⟩
        cases hSpec : edge.future with
        | explicit childOffers => exact ⟨childOffers, rfl⟩
        | «at» state removed =>
            simp [childPendingEdge, childFutureSpec, hSpec] at hOffers
      · rintro ⟨offers, hOffers⟩
        exact ⟨offers, by simp [childPendingEdge, childFutureSpec, hOffers]⟩
  | subtract removed =>
      simp only [futureSpecMatchesPolicy]
      cases hSpec : edge.future with
      | explicit offers =>
          simp [childPendingEdge, childFutureSpec, hSpec]
      | «at» state childRemoved =>
          simp [childPendingEdge, childFutureSpec, childState, hSpec]

private theorem PactType.seq_ne_right (left right : PactType) :
    PactType.seq left right ≠ right := by
  intro hEqual
  have hSize := congrArg sizeOf hEqual
  have hLt : sizeOf right < sizeOf (PactType.seq left right) := by
    simp_wf
    omega
  omega

private theorem PolicyTypeOffers.par_policy_explicit
    {env : TypeEnvironment} {left right : PactType} {interface : Interface}
    {label : TypeLabel} {target : PactType}
    {current : Finset BareMessage} {policy : SemanticFuturePolicy}
    (hPolicy : PolicyTypeOffers env (.par left right interface) label target
      current policy) :
    ∃ future, policy = .explicit future := by
  cases hPolicy
  exact ⟨_, rfl⟩

private theorem replaceVar_recur_eq_var_for_policy
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
        have hName : current = markerName := by injection hEqual
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
private theorem compileTypeFuel_variableRelation_outgoing_label
    (signature : TypeAlphabet) (markerName : String) :
    ∀ (fuel : Nat) (processType : PactType),
      TypeCompilationFuelSufficient processType fuel →
      PactType.TailOccurrences markerName True processType →
      ∀ state residual, TypeCompilationRelation processType state residual →
        residual = .var markerName →
        ∀ edge ∈ (compileTypeFuel signature fuel processType).edges,
          edge.source = state → edge.label = .variable markerName := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel hTail state residual hRelated hResidual edge
        hEdge hSource
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
              subst current
              simp only [compileTypeFuel, finishAutomatonFragment,
                Finset.mem_image] at hEdge
              rcases hEdge with ⟨environment, _, hEq⟩
              rw [← hEq]
      | recur binder body =>
          have hBodyFuel : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          cases hRelated with
          | recur_source => simp at hResidual
          | recur_body _ _ childResidual childQ hChild =>
              obtain ⟨hChildResidual, hDistinct⟩ :=
                replaceVar_recur_eq_var_for_policy hResidual
              have hTailBody : PactType.TailOccurrences markerName True body := by
                have hTail' := hTail
                simp only [PactType.TailOccurrences] at hTail'
                rw [if_neg hDistinct] at hTail'
                exact hTail'
              simp only [compileTypeFuel, buildRecursionAutomaton,
                finishAutomatonFragment, Finset.mem_union,
                Finset.mem_image] at hEdge
              rcases hEdge with ⟨environment, _, hEq⟩ |
                  ⟨childEdge, hChildEdge, hEq⟩
              · rw [← hEq] at hSource
                simp [childState] at hSource
              · rw [← hEq] at hSource ⊢
                by_cases hBinder : childEdge.label = .variable binder
                · rw [if_pos hBinder] at hSource ⊢
                  exfalso
                  have hChildSource : childEdge.source = childQ := by
                    simpa [childState] using hSource
                  have hChildLabel := ih body hBodyFuel hTailBody childQ
                    childResidual hChild hChildResidual childEdge hChildEdge
                      hChildSource
                  have hNameEq : markerName = binder := by
                    rw [hChildLabel] at hBinder
                    injection hBinder
                  exact hDistinct hNameEq.symm
                · rw [if_neg hBinder] at hSource ⊢
                  apply ih body hBodyFuel hTailBody childQ childResidual hChild
                    hChildResidual childEdge hChildEdge
                  simpa [childState] using hSource
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
              obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
                (buildChoiceAutomaton_outgoing_left signature
                  (compileTypeFuel signature fuel left)
                  (compileTypeFuel signature fuel right) .silent .silent
                  childQ edge).mp ⟨hEdge, hSource⟩
              subst edge
              simpa [childPendingEdge] using
                (ih left hLeftFuel hTailFields.1 childQ residual hChild
                  hResidual childEdge hChildEdge hChildSource)
          | choice_right _ _ _ childQ hChild =>
              obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
                (buildChoiceAutomaton_outgoing_right signature
                  (compileTypeFuel signature fuel left)
                  (compileTypeFuel signature fuel right) .silent .silent
                  childQ edge).mp ⟨hEdge, hSource⟩
              subst edge
              simpa [childPendingEdge] using
                (ih right hRightFuel hTailFields.2 childQ residual hChild
                  hResidual childEdge hChildEdge hChildSource)
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
              obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
                (buildChoiceAutomaton_outgoing_left signature
                  (compileTypeFuel signature fuel left)
                  (compileTypeFuel signature fuel right) (.fair bid true)
                  (.fair bid false) childQ edge).mp ⟨hEdge, hSource⟩
              subst edge
              simpa [childPendingEdge] using
                (ih left hLeftFuel hTailFields.1 childQ residual hChild
                  hResidual childEdge hChildEdge hChildSource)
          | fair_right _ _ _ _ childQ hChild =>
              obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
                (buildChoiceAutomaton_outgoing_right signature
                  (compileTypeFuel signature fuel left)
                  (compileTypeFuel signature fuel right) (.fair bid true)
                  (.fair bid false) childQ edge).mp ⟨hEdge, hSource⟩
              subst edge
              simpa [childPendingEdge] using
                (ih right hRightFuel hTailFields.2 childQ residual hChild
                  hResidual childEdge hChildEdge hChildSource)
      | seq left right =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : PactType.TailOccurrences markerName False left ∧
              PactType.TailOccurrences markerName True right := by
            simpa only [PactType.TailOccurrences] using hTail
          cases hRelated with
          | sequence_left => simp at hResidual
          | sequence_right _ _ _ childQ hChild =>
              obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
                (buildSequenceAutomaton_outgoing_right signature
                  (compileTypeFuel signature fuel left)
                  (compileTypeFuel signature fuel right) childQ edge).mp
                    ⟨hEdge, hSource⟩
              subst edge
              simpa [childPendingEdge] using
                (ih right hRightFuel hTailFields.2 childQ residual hChild
                  hResidual childEdge hChildEdge hChildSource)
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
          let branchFragments := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          change edge ∈ (buildExclusiveOfferAutomaton signature branches
            (compileTypeFuel signature fuel elseType) branchFragments).edges
              at hEdge
          cases hRelated with
          | xoffer_source => simp at hResidual
          | xoffer_else _ _ _ childQ hChild =>
              obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
                (buildExclusiveOfferAutomaton_outgoing_else signature branches
                  (compileTypeFuel signature fuel elseType) branchFragments
                  childQ edge).mp ⟨hEdge, hSource⟩
              subst edge
              simpa [childPendingEdge] using
                (ih elseType hElseFuel hTailFields.1 childQ residual
                  hChild hResidual childEdge hChildEdge hChildSource)
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
              have hAutomatonEntry : branchFragments[index]? = some
                  (action, compileTypeFuel signature fuel branchType) := by
                simp [branchFragments, List.getElem?_map, hEntry]
              obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
                (buildExclusiveOfferAutomaton_outgoing_branch signature
                  branches (compileTypeFuel signature fuel elseType)
                  branchFragments index
                  (action, compileTypeFuel signature fuel branchType)
                  hAutomatonEntry childQ edge).mp ⟨hEdge, hSource⟩
              subst edge
              simpa [childPendingEdge] using
                (ih branchType hBranchFuel hBranchTail childQ residual
                  hChild hResidual childEdge hChildEdge hChildSource)
      | offer elseType branches =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields :
              PactType.TailOccurrences markerName True elseType ∧
              PactType.TailBranchOccurrences markerName False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          let selectedFragments := branches.map fun selected =>
            (selected.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting selected branches))
          change edge ∈ (buildSelectedConjunctiveOfferAutomaton signature
            branches (compileTypeFuel signature fuel elseType)
              selectedFragments).edges at hEdge
          cases hRelated with
          | offer_source => simp at hResidual
          | offer_else _ _ _ childQ hChild =>
              obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
                (buildSelectedConjunctiveOfferAutomaton_outgoing_else
                  signature branches (compileTypeFuel signature fuel elseType)
                  selectedFragments childQ edge).mp ⟨hEdge, hSource⟩
              subst edge
              simpa [childPendingEdge] using
                (ih elseType hElseFuel hTailFields.1 childQ residual
                  hChild hResidual childEdge hChildEdge hChildSource)
          | offer_branches _ childResidual _ selected _ childQ _ hChild =>
              exfalso
              have hAbsent : PactType.TailOccurrences markerName False
                  (parallelTypeBranchesSelecting selected branches) :=
                tailOccurrences_parallelTypeBranchesSelecting markerName
                  selected branches hTailFields.2
              have hChildAbsent : PactType.TailOccurrences markerName False
                  (.var markerName) := hResidual ▸
                compilationRelation_tailOccurrences_false markerName hChild
                  hAbsent
              simp [PactType.TailOccurrences] at hChildAbsent

set_option maxHeartbeats 1600000 in
private theorem compilationRelation_futureSpecMatchesPolicy
    (signature : TypeAlphabet) :
    ∀ {original state residual},
      TypeCompilationRelation original state residual →
      ∀ (bound : List String),
        original.AllVariablesBound bound →
        original.BinderHygienic bound →
        original.TailRecursive →
        ∀ {edge : PendingAutomatonEdge} {label : TypeLabel}
          {targetResidual : PactType} {policy : SemanticFuturePolicy},
          edge ∈ (compileTypeFuel signature (typeCompilationFuel original)
            original).edges →
          edge.source = state →
          edge.label = .visible label →
          TypeCompilationRelation original edge.target targetResidual →
          PolicyTypeOffers edge.environment residual label targetResidual
            edge.current policy →
          futureSpecMatchesPolicy edge policy := by
  intro original state residual hRelated bound hBound hHygienic hTail
  intro edge label targetResidual policy hEdge hSource hLabel hTarget hPolicy
  induction hRelated generalizing bound edge label targetResidual policy with
  | skip =>
      simp only [typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment, Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with ⟨environment, hEnvironment, rfl⟩
      cases hPolicy
      exact ⟨∅, rfl⟩
  | message_source msg dir =>
      simp only [typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_image,
        Finset.mem_filter] at hEdge
      rcases hEdge with ((⟨environment, _, rfl⟩ |
          ⟨environment, _, rfl⟩) | ⟨environment, _, rfl⟩)
      · cases hTarget
        cases hPolicy
        exact ⟨∅, rfl⟩
      · cases hTarget
        cases hPolicy
        exact ⟨∅, rfl⟩
      · simp at hSource
  | message_final msg dir =>
      simp only [typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_image,
        Finset.mem_filter] at hEdge
      rcases hEdge with ((⟨environment, _, rfl⟩ |
          ⟨environment, _, rfl⟩) | ⟨environment, _, rfl⟩)
      · simp at hSource
      · simp at hSource
      · cases hTarget
        cases hPolicy
        exact ⟨∅, rfl⟩
  | cycle_source =>
      simp only [typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_image,
        Finset.mem_filter] at hEdge
      rcases hEdge with ⟨environment, _, rfl⟩ | ⟨environment, _, rfl⟩
      · by_cases hClock : environment.clock = true
        · simp only [hClock, if_true] at hTarget hPolicy ⊢
          cases hTarget
          cases hPolicy
          exact ⟨∅, rfl⟩
        · simp only [hClock, if_false] at hTarget hPolicy ⊢
          cases hTarget
          cases hPolicy
          exact ⟨∅, rfl⟩
      · simp at hSource
  | cycle_final =>
      simp only [typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_image,
        Finset.mem_filter] at hEdge
      rcases hEdge with ⟨environment, _, rfl⟩ | ⟨environment, _, rfl⟩
      · split at hSource <;> simp at hSource
      · cases hTarget
        cases hPolicy
        exact ⟨∅, rfl⟩
  | progress_source pid =>
      simp only [typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_image,
        Finset.mem_filter] at hEdge
      rcases hEdge with ⟨environment, _, rfl⟩ | ⟨environment, _, rfl⟩
      · cases hTarget
        cases hPolicy
        exact ⟨∅, rfl⟩
      · simp at hSource
  | progress_final pid =>
      simp only [typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_image,
        Finset.mem_filter] at hEdge
      rcases hEdge with ⟨environment, _, rfl⟩ | ⟨environment, _, rfl⟩
      · simp at hSource
      · cases hTarget
        cases hPolicy
        exact ⟨∅, rfl⟩
  | «variable» name =>
      cases hPolicy
  | recur_source name body =>
      simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image] at hEdge
      rcases hEdge with ⟨environment, _, hEq⟩ |
          ⟨bodyEdge, hBodyEdge, hEq⟩
      · rw [← hEq] at hSource hPolicy ⊢
        cases hPolicy
        rfl
      · rw [← hEq] at hSource
        split at hSource <;> simp [childState] at hSource
  | recur_body name body childResidual childQ hChild ih =>
      have hBoundBody : body.AllVariablesBound (name :: bound) := by
        simpa only [PactType.AllVariablesBound] using hBound
      have hHygienicFields : name ∉ bound ∧
          body.BinderHygienic (name :: bound) := by
        simpa only [PactType.BinderHygienic] using hHygienic
      have hTailFields : body.TailOccurrences name True ∧
          body.TailRecursive := by
        simpa only [PactType.TailRecursive] using hTail
      have hBodyFuel : TypeCompilationFuelSufficient body
          (typeCompilationFuel body) := typeCompilationFuel_sufficient body
      simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image] at hEdge
      rcases hEdge with ⟨environment, _, hEq⟩ |
          ⟨bodyEdge, hBodyEdge, hEq⟩
      · rw [← hEq] at hSource
        simp [childState] at hSource
      · rw [← hEq] at hSource hLabel hTarget hPolicy ⊢
        by_cases hMarker : bodyEdge.label = .variable name
        · rw [if_pos hMarker] at hSource hLabel hTarget hPolicy ⊢
          have hMarkerRelation : TypeCompilationRelation body bodyEdge.source
              (.var name) :=
            (compileTypeFuel_variableEdge_source_var signature name
              (typeCompilationFuel body) body True hBodyFuel hTailFields.1
              bodyEdge hBodyEdge hMarker).2
          have hBodySource : bodyEdge.source = childQ := by
            simpa [childState] using hSource
          rw [hBodySource] at hMarkerRelation
          have hResidualEq : childResidual = .var name :=
            TypeCompilationRelation.residual_unique hChild hMarkerRelation
          have hSubstitutedSource : childResidual.replaceVar name
              (.recur name body) = .recur name body := by
            rw [hResidualEq]
            simp [PactType.replaceVar]
          rw [hSubstitutedSource] at hPolicy
          cases hPolicy
          rfl
        · rw [if_neg hMarker] at hSource hLabel hTarget hPolicy ⊢
          have hBodySource : bodyEdge.source = childQ := by
            simpa [childState] using hSource
          have hBodyLabel : bodyEdge.label = .visible label := hLabel
          have hResidualTail : childResidual.TailOccurrences name True :=
            compilationRelation_tailOccurrences_true name hChild hTailFields.2
              hTailFields.1
          have hResidualBound : childResidual.AllVariablesBound
              (name :: bound) :=
            compilationRelation_allVariablesBound hChild hBoundBody
          have hResidualFresh : childResidual.BinderFreshFor
              (name :: bound) :=
            compilationRelation_binderFreshFor hChild hHygienicFields.2
          have hNotResidualMarker : childResidual ≠ .var name := by
            intro hResidualEq
            have hBodyMarker :=
              compileTypeFuel_variableRelation_outgoing_label signature name
                (typeCompilationFuel body) body hBodyFuel hTailFields.1 childQ
                childResidual hChild hResidualEq bodyEdge hBodyEdge hBodySource
            exact hMarker hBodyMarker
          cases hTarget with
          | recur_body _ _ targetChildResidual targetChildQ hChildTarget =>
              obtain ⟨bodyTarget, hBodyPolicy, hTargetEq⟩ :=
                policyTypeOffers_replaceVar_backward bound name body hBoundBody
                  hResidualTail hResidualBound hResidualFresh
                    hNotResidualMarker hPolicy
              have hResidualFreshName :
                  childResidual.BinderFreshFor [name] :=
                PactType.binderFreshFor_mono
                  (smaller := [name]) (larger := name :: bound)
                  (by
                    intro x hx
                    rw [List.mem_singleton] at hx
                    subst x
                    exact List.mem_cons_self)
                  childResidual hResidualFresh
              have hBodyTargetFresh : bodyTarget.BinderFreshFor [name] :=
                hBodyPolicy.target_binderFreshFor [name] hResidualFreshName
              have hCompiledTargetFresh :
                  targetChildResidual.BinderFreshFor [name] := by
                apply PactType.binderFreshFor_mono
                  (smaller := [name]) (larger := name :: bound)
                  (by
                    intro x hx
                    rw [List.mem_singleton] at hx
                    subst x
                    exact List.mem_cons_self)
                  targetChildResidual
                exact compilationRelation_binderFreshFor hChildTarget
                  hHygienicFields.2
              have hBodyTargetEq : bodyTarget = targetChildResidual :=
                PactType.replaceVar_recur_injective_of_binderFreshFor name body
                  bodyTarget targetChildResidual hBodyTargetFresh
                    hCompiledTargetFresh hTargetEq.symm
              apply (futureSpecMatchesPolicy_childPendingEdge 0 bodyEdge
                policy).2
              exact ih (name :: bound) hBoundBody hHygienicFields.2
                hTailFields.2 hBodyEdge hBodySource hBodyLabel hChildTarget
                  (hBodyTargetEq ▸ hBodyPolicy)
  | choice_source left right =>
      simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        buildChoiceAutomaton, finishAutomatonFragment, childPendingEdges,
        Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
        Finset.mem_insert, Finset.mem_singleton] at hEdge
      rcases hEdge with (hLeft | hRight) | ⟨environment, _, hEq | hEq⟩
      · rcases hLeft with ⟨childEdge, _, hEq⟩
        rw [← hEq] at hSource
        simp [childPendingEdge, childState] at hSource
      · rcases hRight with ⟨childEdge, _, hEq⟩
        rw [← hEq] at hSource
        simp [childPendingEdge, childState] at hSource
      · rw [hEq] at hTarget hPolicy ⊢
        cases hTarget
        cases hPolicy
        all_goals rfl
      · rw [hEq] at hTarget hPolicy ⊢
        cases hTarget
        cases hPolicy
        all_goals rfl
  | choice_left left right childResidual childQ hChild ih =>
      have hBoundFields : left.AllVariablesBound bound ∧
          right.AllVariablesBound bound := by
        simpa only [PactType.AllVariablesBound] using hBound
      have hHygienicFields : left.BinderHygienic bound ∧
          right.BinderHygienic bound := by
        simpa only [PactType.BinderHygienic] using hHygienic
      have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
        simpa only [PactType.TailRecursive] using hTail
      let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
      let leftFragment := compileTypeFuel signature fuel left
      let rightFragment := compileTypeFuel signature fuel right
      have hRightFuel : TypeCompilationFuelSufficient right fuel := by
        simp [TypeCompilationFuelSufficient, fuel]
      have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
        simp [TypeCompilationFuelSufficient, fuel]
      have hLeftStable : leftFragment = compileTypeFuel signature
          (typeCompilationFuel left) left :=
        compileTypeFuel_eq_of_sufficient signature left hLeftFuel
          (typeCompilationFuel_sufficient left)
      have hParent : compileTypeFuel signature
          (typeCompilationFuel (.choice left right)) (.choice left right) =
          buildChoiceAutomaton signature leftFragment rightFragment
            .silent .silent := by
        simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        rfl
      rw [hParent] at hEdge
      obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
        (buildChoiceAutomaton_outgoing_left signature leftFragment rightFragment
          .silent .silent childQ edge).mp ⟨hEdge, hSource⟩
      subst edge
      rw [hLeftStable] at hChildEdge
      cases hTarget with
      | choice_left _ _ _ _ hChildTarget =>
          apply (futureSpecMatchesPolicy_childPendingEdge 0 childEdge policy).2
          exact ih bound hBoundFields.1 hHygienicFields.1 hTailFields.1
            hChildEdge hChildSource (by
              simpa [childPendingEdge] using hLabel) hChildTarget
                (by simpa [childPendingEdge] using hPolicy)
  | choice_right left right childResidual childQ hChild ih =>
      have hBoundFields : left.AllVariablesBound bound ∧
          right.AllVariablesBound bound := by
        simpa only [PactType.AllVariablesBound] using hBound
      have hHygienicFields : left.BinderHygienic bound ∧
          right.BinderHygienic bound := by
        simpa only [PactType.BinderHygienic] using hHygienic
      have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
        simpa only [PactType.TailRecursive] using hTail
      let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
      let leftFragment := compileTypeFuel signature fuel left
      let rightFragment := compileTypeFuel signature fuel right
      have hRightFuel : TypeCompilationFuelSufficient right fuel := by
        simp [TypeCompilationFuelSufficient, fuel]
      have hRightStable : rightFragment = compileTypeFuel signature
          (typeCompilationFuel right) right :=
        compileTypeFuel_eq_of_sufficient signature right hRightFuel
          (typeCompilationFuel_sufficient right)
      have hParent : compileTypeFuel signature
          (typeCompilationFuel (.choice left right)) (.choice left right) =
          buildChoiceAutomaton signature leftFragment rightFragment
            .silent .silent := by
        simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        rfl
      rw [hParent] at hEdge
      obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
        (buildChoiceAutomaton_outgoing_right signature leftFragment rightFragment
          .silent .silent childQ edge).mp ⟨hEdge, hSource⟩
      subst edge
      rw [hRightStable] at hChildEdge
      cases hTarget with
      | choice_right _ _ _ _ hChildTarget =>
          apply (futureSpecMatchesPolicy_childPendingEdge 1 childEdge policy).2
          exact ih bound hBoundFields.2 hHygienicFields.2 hTailFields.2
            hChildEdge hChildSource (by
              simpa [childPendingEdge] using hLabel) hChildTarget
                (by simpa [childPendingEdge] using hPolicy)
  | fair_source bid left right =>
      simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        buildChoiceAutomaton, finishAutomatonFragment, childPendingEdges,
        Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
        Finset.mem_insert, Finset.mem_singleton] at hEdge
      rcases hEdge with (hLeft | hRight) | ⟨environment, _, hEq | hEq⟩
      · rcases hLeft with ⟨childEdge, _, hEq⟩
        rw [← hEq] at hSource
        simp [childPendingEdge, childState] at hSource
      · rcases hRight with ⟨childEdge, _, hEq⟩
        rw [← hEq] at hSource
        simp [childPendingEdge, childState] at hSource
      · rw [hEq] at hTarget hPolicy ⊢
        cases hTarget
        cases hPolicy
        all_goals rfl
      · rw [hEq] at hTarget hPolicy ⊢
        cases hTarget
        cases hPolicy
        all_goals rfl
  | fair_left bid left right childResidual childQ hChild ih =>
      have hBoundFields : left.AllVariablesBound bound ∧
          right.AllVariablesBound bound := by
        simpa only [PactType.AllVariablesBound] using hBound
      have hHygienicFields : left.BinderHygienic bound ∧
          right.BinderHygienic bound := by
        simpa only [PactType.BinderHygienic] using hHygienic
      have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
        simpa only [PactType.TailRecursive] using hTail
      let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
      let leftFragment := compileTypeFuel signature fuel left
      let rightFragment := compileTypeFuel signature fuel right
      have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
        simp [TypeCompilationFuelSufficient, fuel]
      have hLeftStable : leftFragment = compileTypeFuel signature
          (typeCompilationFuel left) left :=
        compileTypeFuel_eq_of_sufficient signature left hLeftFuel
          (typeCompilationFuel_sufficient left)
      have hParent : compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
            (.fairChoice bid left right) =
          buildChoiceAutomaton signature leftFragment rightFragment
            (.fair bid true) (.fair bid false) := by
        simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        rfl
      rw [hParent] at hEdge
      obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
        (buildChoiceAutomaton_outgoing_left signature leftFragment rightFragment
          (.fair bid true) (.fair bid false) childQ edge).mp ⟨hEdge, hSource⟩
      subst edge
      rw [hLeftStable] at hChildEdge
      cases hTarget with
      | fair_left _ _ _ _ _ hChildTarget =>
          apply (futureSpecMatchesPolicy_childPendingEdge 0 childEdge policy).2
          exact ih bound hBoundFields.1 hHygienicFields.1 hTailFields.1
            hChildEdge hChildSource (by
              simpa [childPendingEdge] using hLabel) hChildTarget
                (by simpa [childPendingEdge] using hPolicy)
  | fair_right bid left right childResidual childQ hChild ih =>
      have hBoundFields : left.AllVariablesBound bound ∧
          right.AllVariablesBound bound := by
        simpa only [PactType.AllVariablesBound] using hBound
      have hHygienicFields : left.BinderHygienic bound ∧
          right.BinderHygienic bound := by
        simpa only [PactType.BinderHygienic] using hHygienic
      have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
        simpa only [PactType.TailRecursive] using hTail
      let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
      let leftFragment := compileTypeFuel signature fuel left
      let rightFragment := compileTypeFuel signature fuel right
      have hRightFuel : TypeCompilationFuelSufficient right fuel := by
        simp [TypeCompilationFuelSufficient, fuel]
      have hRightStable : rightFragment = compileTypeFuel signature
          (typeCompilationFuel right) right :=
        compileTypeFuel_eq_of_sufficient signature right hRightFuel
          (typeCompilationFuel_sufficient right)
      have hParent : compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
            (.fairChoice bid left right) =
          buildChoiceAutomaton signature leftFragment rightFragment
            (.fair bid true) (.fair bid false) := by
        simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        rfl
      rw [hParent] at hEdge
      obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
        (buildChoiceAutomaton_outgoing_right signature leftFragment rightFragment
          (.fair bid true) (.fair bid false) childQ edge).mp ⟨hEdge, hSource⟩
      subst edge
      rw [hRightStable] at hChildEdge
      cases hTarget with
      | fair_right _ _ _ _ _ hChildTarget =>
          apply (futureSpecMatchesPolicy_childPendingEdge 1 childEdge policy).2
          exact ih bound hBoundFields.2 hHygienicFields.2 hTailFields.2
            hChildEdge hChildSource (by
              simpa [childPendingEdge] using hLabel) hChildTarget
                (by simpa [childPendingEdge] using hPolicy)
  | sequence_left left right childResidual childQ hChild ih =>
      let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
      let leftFragment := compileTypeFuel signature fuel left
      let rightFragment := compileTypeFuel signature fuel right
      have hRightFuel : TypeCompilationFuelSufficient right fuel := by
        simp [TypeCompilationFuelSufficient, fuel]
      have hParent : compileTypeFuel signature
          (typeCompilationFuel (.seq left right)) (.seq left right) =
          buildSequenceAutomaton signature leftFragment rightFragment := by
        simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        rfl
      rw [hParent] at hEdge
      rcases (buildSequenceAutomaton_outgoing_left signature leftFragment
        rightFragment childQ edge).mp ⟨hEdge, hSource⟩ with
        ⟨childEdge, hChildEdge, hChildSource, hEq⟩ |
        ⟨hAccepting, environment, hEnvironment, hEq⟩ |
        ⟨hCompleting, hEq⟩
      · subst edge
        simp only [hLabel, futureSpecMatchesPolicy]
        cases hTarget with
        | sequence_left _ _ _ _ hChildTarget =>
            cases hPolicy with
            | seq =>
                have hChildLabel : childEdge.label = .visible label := by
                  simpa using hLabel
                simp only [hChildLabel]
      · subst edge
        cases hTarget with
        | sequence_right _ _ _ _ hRightTarget =>
            cases hPolicy with
            | skip_seq => rfl
            | seq _ _ leftTarget _ _ _ _ _ =>
                exfalso
                have hInitial : TypeCompilationRelation right
                    rightFragment.initial right :=
                  compileTypeFuel_initial_relation signature fuel right
                    hRightFuel
                have hResidualEq :=
                  TypeCompilationRelation.residual_unique hRightTarget hInitial
                exact PactType.seq_ne_right leftTarget right hResidualEq
      · subst edge
        simp at hLabel
  | sequence_right left right childResidual childQ hChild ih =>
      have hBoundFields : left.AllVariablesBound bound ∧
          right.AllVariablesBound bound := by
        simpa only [PactType.AllVariablesBound] using hBound
      have hHygienicFields : left.BinderHygienic bound ∧
          right.BinderHygienic bound := by
        simpa only [PactType.BinderHygienic] using hHygienic
      have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
        simpa only [PactType.TailRecursive] using hTail
      let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
      let leftFragment := compileTypeFuel signature fuel left
      let rightFragment := compileTypeFuel signature fuel right
      have hRightFuel : TypeCompilationFuelSufficient right fuel := by
        simp [TypeCompilationFuelSufficient, fuel]
      have hRightStable : rightFragment = compileTypeFuel signature
          (typeCompilationFuel right) right :=
        compileTypeFuel_eq_of_sufficient signature right hRightFuel
          (typeCompilationFuel_sufficient right)
      have hParent : compileTypeFuel signature
          (typeCompilationFuel (.seq left right)) (.seq left right) =
          buildSequenceAutomaton signature leftFragment rightFragment := by
        simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        rfl
      rw [hParent] at hEdge
      obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
        (buildSequenceAutomaton_outgoing_right signature leftFragment
          rightFragment childQ edge).mp ⟨hEdge, hSource⟩
      subst edge
      rw [hRightStable] at hChildEdge
      cases hTarget with
      | sequence_right _ _ _ _ hChildTarget =>
          apply (futureSpecMatchesPolicy_childPendingEdge 1 childEdge policy).2
          exact ih bound hBoundFields.2 hHygienicFields.2 hTailFields.2
            hChildEdge hChildSource (by
              simpa [childPendingEdge] using hLabel) hChildTarget
                (by simpa [childPendingEdge] using hPolicy)
  | parallel left right leftResidual rightResidual interface leftQ rightQ
      hLeft hRight ihLeft ihRight =>
      obtain ⟨policyFuture, rfl⟩ :=
        PolicyTypeOffers.par_policy_explicit hPolicy
      simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with hTransition | hObservation
      · rcases hTransition with
          ⟨leftEdge, _, rightEdge, _, hEq⟩
        rw [← hEq]
        exact ⟨_, rfl⟩
      · rcases hObservation with ⟨leftState, _, rightState, _, hEq⟩ |
          ⟨leftState, _, rightState, _, hEq⟩ <;>
          (rw [← hEq] at hLabel; simp at hLabel)
  | xoffer_source elseType branches =>
      simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
      · simp only [childPendingEdges, Finset.mem_image] at hElse
        rcases hElse with ⟨childEdge, _, hEq⟩
        rw [← hEq] at hSource
        simp [childPendingEdge, childState] at hSource
      · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
        rcases hIndexed with hEmpty | ⟨indexed, _, hChild⟩
        · simp at hEmpty
        · simp only [childPendingEdges, Finset.mem_image] at hChild
          rcases hChild with ⟨childEdge, _, hEq⟩
          rw [← hEq] at hSource
          simp [childPendingEdge, childState] at hSource
      · rw [mem_foldl_union_iff] at hBranch
        rcases hBranch with hEmpty | ⟨indexed, _, hNewEdge⟩
        · simp at hEmpty
        · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
          rcases hNewEdge with ⟨environment, hConditions, hEq⟩
          rw [← hEq] at hSource hLabel hTarget hPolicy ⊢
          rcases hPolicy.xoffer_root_policy with
            ⟨hPolicyEq, _⟩ | ⟨_, hPolicyEq⟩ | ⟨_, hNotResolved⟩
          · rw [hPolicyEq]
            rfl
          · rw [hPolicyEq]
            rfl
          · exact (hNotResolved hConditions.2.2).elim
      · simp only [Finset.mem_image, Finset.mem_filter] at hWait
        rcases hWait with ⟨environment, hConditions, hEq⟩
        rw [← hEq] at hSource hLabel hTarget hPolicy ⊢
        rcases hPolicy.xoffer_root_policy with
          ⟨_, hResolved⟩ | ⟨hCurrent, hPolicyEq⟩ |
            ⟨hPolicyEq, _⟩
        · exact (hConditions.2.2 hResolved).elim
        · rw [hPolicyEq]
          change (environment.future.image typeNeed ∩
            typeBranchActions branches) = ∅ at hCurrent
          simp [futureSpecMatchesPolicy, hCurrent]
        · rw [hPolicyEq]
          rfl
      · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
        rcases hResolved with ⟨environment, hConditions, hEq⟩
        rw [← hEq] at hSource hLabel hTarget hPolicy ⊢
        rcases hPolicy.xoffer_root_policy with
          ⟨hPolicyEq, _⟩ | ⟨_, hPolicyEq⟩ | ⟨_, hNotResolved⟩
        · rw [hPolicyEq]
          rfl
        · rw [hPolicyEq]
          rfl
        · exact (hNotResolved hConditions.2.2).elim
  | xoffer_else elseType childResidual branches childQ hChild ih =>
      have hBoundFields : elseType.AllVariablesBound bound ∧
          PactType.AllBranchVariablesBound bound branches := by
        simpa only [PactType.AllVariablesBound] using hBound
      have hHygienicFields : elseType.BinderHygienic bound ∧
          PactType.BinderHygienicBranches bound branches := by
        simpa only [PactType.BinderHygienic] using hHygienic
      have hTailFields : elseType.TailRecursive ∧
          PactType.TailRecursiveBranches branches := by
        simpa only [PactType.TailRecursive] using hTail
      let fuel := max (typeCompilationFuel elseType)
        (typeBranchCompilationFuel branches)
      let elseFragment := compileTypeFuel signature fuel elseType
      let branchFragments := branches.map fun branch =>
        (branch.1, compileTypeFuel signature fuel branch.2)
      have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
        simp [TypeCompilationFuelSufficient, fuel]
      have hElseStable : elseFragment = compileTypeFuel signature
          (typeCompilationFuel elseType) elseType :=
        compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
          (typeCompilationFuel_sufficient elseType)
      have hParent : compileTypeFuel signature
          (typeCompilationFuel (.xoffer elseType branches))
            (.xoffer elseType branches) =
          buildExclusiveOfferAutomaton signature branches elseFragment
            branchFragments := by
        simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        rfl
      rw [hParent] at hEdge
      obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
        (buildExclusiveOfferAutomaton_outgoing_else signature branches
          elseFragment branchFragments childQ edge).mp ⟨hEdge, hSource⟩
      subst edge
      rw [hElseStable] at hChildEdge
      cases hTarget with
      | xoffer_else _ _ _ _ hChildTarget =>
          apply (futureSpecMatchesPolicy_childPendingEdge 0 childEdge policy).2
          exact ih bound hBoundFields.1 hHygienicFields.1 hTailFields.1
            hChildEdge hChildSource (by
              simpa [childPendingEdge] using hLabel) hChildTarget
                (by simpa [childPendingEdge] using hPolicy)
  | xoffer_branch elseType branchType childResidual branches action index childQ
      hEntry hChild ih =>
      have hBoundFields : elseType.AllVariablesBound bound ∧
          PactType.AllBranchVariablesBound bound branches := by
        simpa only [PactType.AllVariablesBound] using hBound
      have hHygienicFields : elseType.BinderHygienic bound ∧
          PactType.BinderHygienicBranches bound branches := by
        simpa only [PactType.BinderHygienic] using hHygienic
      have hTailFields : elseType.TailRecursive ∧
          PactType.TailRecursiveBranches branches := by
        simpa only [PactType.TailRecursive] using hTail
      have hMember : (action, branchType) ∈ branches :=
        List.mem_of_getElem? hEntry
      let fuel := max (typeCompilationFuel elseType)
        (typeBranchCompilationFuel branches)
      let elseFragment := compileTypeFuel signature fuel elseType
      let branchFragments := branches.map fun branch =>
        (branch.1, compileTypeFuel signature fuel branch.2)
      have hBranchBudget : typeBranchCompilationFuel branches ≤ fuel := by
        simp [fuel]
      have hBranchFuel : TypeCompilationFuelSufficient branchType fuel :=
        le_trans (typeCompilationFuel_le_typeBranchCompilationFuel branches
          (action, branchType) hMember) hBranchBudget
      have hBranchStable : compileTypeFuel signature fuel branchType =
          compileTypeFuel signature (typeCompilationFuel branchType)
            branchType :=
        compileTypeFuel_eq_of_sufficient signature branchType hBranchFuel
          (typeCompilationFuel_sufficient branchType)
      have hAutomatonEntry : branchFragments[index]? =
          some (action, compileTypeFuel signature fuel branchType) := by
        simp [branchFragments, List.getElem?_map, hEntry]
      have hParent : compileTypeFuel signature
          (typeCompilationFuel (.xoffer elseType branches))
            (.xoffer elseType branches) =
          buildExclusiveOfferAutomaton signature branches elseFragment
            branchFragments := by
        simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        rfl
      rw [hParent] at hEdge
      obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
        (buildExclusiveOfferAutomaton_outgoing_branch signature branches
          elseFragment branchFragments index
          (action, compileTypeFuel signature fuel branchType) hAutomatonEntry
          childQ edge).mp ⟨hEdge, hSource⟩
      subst edge
      rw [hBranchStable] at hChildEdge
      cases hTarget with
      | xoffer_branch _ targetBranchType _ _ targetAction _ _ hTargetEntry
          hChildTarget =>
          have hEntryEquality : (action, branchType) =
              (targetAction, targetBranchType) :=
            Option.some.inj (hEntry.symm.trans hTargetEntry)
          cases hEntryEquality
          apply (futureSpecMatchesPolicy_childPendingEdge (index + 1)
            childEdge policy).2
          exact ih bound
            (allVariablesBound_branch_of_mem bound branches
              (action, branchType) hBoundFields.2 hMember)
            (binderHygienic_branch_of_mem bound branches
              (action, branchType) hHygienicFields.2 hMember)
            (tailRecursive_branch_of_mem branches (action, branchType)
              hTailFields.2 hMember)
            hChildEdge hChildSource (by
              simpa [childPendingEdge] using hLabel) hChildTarget
                (by simpa [childPendingEdge] using hPolicy)
  | offer_source elseType branches =>
      simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
      · simp only [childPendingEdges, Finset.mem_image] at hElse
        rcases hElse with ⟨childEdge, _, hEq⟩
        rw [← hEq] at hSource
        simp [childPendingEdge, childState] at hSource
      · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
        rcases hIndexed with hEmpty | ⟨indexed, _, hChild⟩
        · simp at hEmpty
        · simp only [childPendingEdges, Finset.mem_image] at hChild
          rcases hChild with ⟨childEdge, _, hEq⟩
          rw [← hEq] at hSource
          simp [childPendingEdge, childState] at hSource
      · rw [mem_foldl_union_iff] at hEnabled
        rcases hEnabled with hEmpty | ⟨indexed, _, hNewEdge⟩
        · simp at hEmpty
        · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
          rcases hNewEdge with ⟨environment, hConditions, hEq⟩
          rw [← hEq] at hSource hLabel hTarget hPolicy ⊢
          rcases hPolicy.offer_root_policy with
            ⟨hCurrent, hPolicyEq⟩ | ⟨hPolicyEq, _⟩ |
              ⟨hPolicyEq, _⟩
          · rw [hPolicyEq]
            rfl
          · rw [hPolicyEq]
            rfl
          · rw [hPolicyEq]
            rfl
      · simp only [Finset.mem_image, Finset.mem_filter] at hWait
        rcases hWait with ⟨environment, hConditions, hEq⟩
        rw [← hEq] at hSource hLabel hTarget hPolicy ⊢
        rcases hPolicy.offer_root_policy with
          ⟨hCurrent, hPolicyEq⟩ | ⟨_, hResolved⟩ |
            ⟨hPolicyEq, _⟩
        · rw [hPolicyEq]
          change (environment.future.image typeNeed ∩
            typeBranchActions branches) = ∅ at hCurrent
          simp [futureSpecMatchesPolicy, hCurrent]
        · exact (hConditions.2.2.2 hResolved).elim
        · rw [hPolicyEq]
          rfl
      · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
        rcases hResolved with ⟨environment, hConditions, hEq⟩
        rw [← hEq] at hSource hLabel hTarget hPolicy ⊢
        rcases hPolicy.offer_root_policy with
          ⟨_, hPolicyEq⟩ | ⟨hPolicyEq, _⟩ | ⟨_, hNotResolved⟩
        · rw [hPolicyEq]
          rfl
        · rw [hPolicyEq]
          rfl
        · exact (hNotResolved hConditions.2.2).elim
  | offer_branches elseType childResidual branches selected index childQ hEntry
      hChild ih =>
      have hBoundFields : elseType.AllVariablesBound bound ∧
          PactType.AllBranchVariablesBound bound branches := by
        simpa only [PactType.AllVariablesBound] using hBound
      have hHygienicFields : elseType.BinderHygienic bound ∧
          PactType.BinderHygienicBranches bound branches := by
        simpa only [PactType.BinderHygienic] using hHygienic
      have hTailFields : elseType.TailRecursive ∧
          PactType.TailRecursiveBranches branches := by
        simpa only [PactType.TailRecursive] using hTail
      let fuel := max (typeCompilationFuel elseType)
        (conjunctiveCompilationFuel branches)
      let elseFragment := compileTypeFuel signature fuel elseType
      let selectedFragments := branches.map fun entry =>
        (entry.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting entry branches))
      have hSelectedFuel : TypeCompilationFuelSufficient
          (parallelTypeBranchesSelecting selected branches) fuel := by
        simp only [TypeCompilationFuelSufficient,
          typeCompilationFuel_parallelTypeBranchesSelecting, fuel]
        exact le_max_right _ _
      have hSelectedStable : compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches) =
          compileTypeFuel signature
            (typeCompilationFuel
              (parallelTypeBranchesSelecting selected branches))
            (parallelTypeBranchesSelecting selected branches) :=
        compileTypeFuel_eq_of_sufficient signature
          (parallelTypeBranchesSelecting selected branches) hSelectedFuel
          (typeCompilationFuel_sufficient _)
      have hAutomatonEntry : selectedFragments[index]? = some
          (selected.1, compileTypeFuel signature fuel
            (parallelTypeBranchesSelecting selected branches)) := by
        simp [selectedFragments, List.getElem?_map, hEntry]
      have hParent : compileTypeFuel signature
          (typeCompilationFuel (.offer elseType branches))
            (.offer elseType branches) =
          buildSelectedConjunctiveOfferAutomaton signature branches
            elseFragment selectedFragments := by
        simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        rfl
      rw [hParent] at hEdge
      obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
        (buildSelectedConjunctiveOfferAutomaton_outgoing_conjunction
          signature branches elseFragment selectedFragments index
          (selected.1, compileTypeFuel signature fuel
            (parallelTypeBranchesSelecting selected branches))
          hAutomatonEntry childQ edge).mp ⟨hEdge, hSource⟩
      subst edge
      rw [hSelectedStable] at hChildEdge
      cases hTarget with
      | offer_branches _ _ _ targetSelected _ _ hTargetEntry hChildTarget =>
          have hEntryEquality : selected = targetSelected :=
            Option.some.inj (hEntry.symm.trans hTargetEntry)
          cases hEntryEquality
          apply (futureSpecMatchesPolicy_childPendingEdge (index + 1)
            childEdge policy).2
          exact ih bound
            (allVariablesBound_parallelTypeBranchesSelecting bound selected
              branches hBoundFields.2)
            (binderHygienic_parallelTypeBranchesSelecting bound selected
              branches hHygienicFields.2)
            (tailRecursive_parallelTypeBranchesSelecting selected branches
              hTailFields.2)
            hChildEdge hChildSource (by
              simpa [childPendingEdge] using hLabel) hChildTarget
                (by simpa [childPendingEdge] using hPolicy)
  | offer_else elseType childResidual branches childQ hChild ih =>
      have hBoundFields : elseType.AllVariablesBound bound ∧
          PactType.AllBranchVariablesBound bound branches := by
        simpa only [PactType.AllVariablesBound] using hBound
      have hHygienicFields : elseType.BinderHygienic bound ∧
          PactType.BinderHygienicBranches bound branches := by
        simpa only [PactType.BinderHygienic] using hHygienic
      have hTailFields : elseType.TailRecursive ∧
          PactType.TailRecursiveBranches branches := by
        simpa only [PactType.TailRecursive] using hTail
      let fuel := max (typeCompilationFuel elseType)
        (conjunctiveCompilationFuel branches)
      let elseFragment := compileTypeFuel signature fuel elseType
      let selectedFragments := branches.map fun entry =>
        (entry.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting entry branches))
      have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
        simp [TypeCompilationFuelSufficient, fuel]
      have hElseStable : elseFragment = compileTypeFuel signature
          (typeCompilationFuel elseType) elseType :=
        compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
          (typeCompilationFuel_sufficient elseType)
      have hParent : compileTypeFuel signature
          (typeCompilationFuel (.offer elseType branches))
            (.offer elseType branches) =
          buildSelectedConjunctiveOfferAutomaton signature branches
            elseFragment selectedFragments := by
        simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        rfl
      rw [hParent] at hEdge
      obtain ⟨childEdge, hChildEdge, hChildSource, hEq⟩ :=
        (buildSelectedConjunctiveOfferAutomaton_outgoing_else signature
          branches elseFragment selectedFragments childQ edge).mp
            ⟨hEdge, hSource⟩
      subst edge
      rw [hElseStable] at hChildEdge
      cases hTarget with
      | offer_else _ _ _ _ hChildTarget =>
          apply (futureSpecMatchesPolicy_childPendingEdge 0 childEdge policy).2
          exact ih bound hBoundFields.1 hHygienicFields.1 hTailFields.1
            hChildEdge hChildSource (by
              simpa [childPendingEdge] using hLabel) hChildTarget
                (by simpa [childPendingEdge] using hPolicy)

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
    (signature : TypeAlphabet) (bound : List String) (name : String)
    (body : PactType)
    (hBoundBody : body.AllVariablesBound (name :: bound))
    (hHygienicBody : body.BinderHygienic (name :: bound))
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
  classical
  set bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
    with hBodyFragment
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.recur name body)) (.recur name body) =
      buildRecursionAutomaton signature name bodyFragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
      hBodyFragment]
  have hResidualTail : residual.TailOccurrences name True :=
    compilationRelation_tailOccurrences_true name hRelated
      hTailRecursiveBody hTailBody
  have hResidualBound : residual.AllVariablesBound (name :: bound) :=
    compilationRelation_allVariablesBound hRelated hBoundBody
  have hResidualFresh : residual.BinderFreshFor (name :: bound) :=
    compilationRelation_binderFreshFor hRelated hHygienicBody
  constructor
  · intro hSemantic
    have hSubstitutedOffers :=
      (decoratedTypeTransition_iff_typeOffers env
        (residual.replaceVar name (.recur name body)) label offers
          residual').mp hSemantic
    obtain ⟨policy, hSubstitutedPolicy, hSubstitutedFuture⟩ :=
      typeOffers_toPolicy (residual.replaceVar name (.recur name body)) env
        label residual' offers.current offers.future hSubstitutedOffers
    obtain ⟨bodyTarget, hBodyPolicy, hTargetEq⟩ :=
      policyTypeOffers_replaceVar_backward bound name body hBoundBody
        hResidualTail hResidualBound hResidualFresh hNotMarker
          hSubstitutedPolicy
    subst residual'
    let bodyOffers : TypeOfferSummary :=
      { current := offers.current
        future := resolveSemanticFuture bodyTarget policy }
    have hBodySemantic : DecoratedTypeTransition env residual label bodyOffers
        bodyTarget :=
      (decoratedTypeTransition_iff_typeOffers env residual label bodyOffers
        bodyTarget).mpr hBodyPolicy.toTypeOffers
    obtain ⟨bodyTargetState, hBodyResolved, hBodyTargetRelated⟩ :=
      (hBodyStep hRelated hLocal hAvoids).mp hBodySemantic
    rcases hBodyResolved with
      ⟨bodyEdge, hBodyEdge, hBodySource, hBodyEnvironment, hBodyLabel,
        hBodyCurrent, hBodyResolvedFuture, hBodyTarget⟩
    subst bodyTargetState
    have hNotVariable : bodyEdge.label ≠ .variable name := by
      rw [hBodyLabel]
      simp
    have hBodyPolicyRaw : PolicyTypeOffers bodyEdge.environment residual label
        bodyTarget bodyEdge.current policy := by
      rw [hBodyEnvironment, hBodyCurrent]
      exact hBodyPolicy
    have hSpec := compilationRelation_futureSpecMatchesPolicy signature
      hRelated (name :: bound) hBoundBody hHygienicBody hTailRecursiveBody
        hBodyEdge hBodySource hBodyLabel hBodyTargetRelated hBodyPolicyRaw
    have hInstalledTargetFuture : computeFuture
        { states :=
            (buildRecursionAutomaton signature name bodyFragment).states
          edges :=
            (buildRecursionAutomaton signature name bodyFragment).edges }
        (.child 0 bodyEdge.target) =
          typeFutureOffers
            (bodyTarget.replaceVar name (.recur name body)) := by
      simpa [bodyFragment] using
        hFuture bodyEdge.target bodyTarget hBodyTargetRelated
    have hParentFuture :
        (match bodyEdge.future with
          | .explicit future => future
          | .at referenced removed =>
              computeFuture
                { states :=
                    (buildRecursionAutomaton signature name bodyFragment).states
                  edges :=
                    (buildRecursionAutomaton signature name bodyFragment).edges }
                (.child 0 referenced) \ removed) = offers.future := by
      cases policy with
      | explicit semanticFuture =>
          rcases hSpec with ⟨rawFuture, hRawFuture⟩
          rw [hRawFuture] at hBodyResolvedFuture ⊢
          calc
            rawFuture = semanticFuture := by
              simpa [bodyOffers, resolveSemanticFuture] using
                hBodyResolvedFuture
            _ = offers.future := by
              simpa [resolveSemanticFuture] using hSubstitutedFuture.symm
      | subtract removed =>
          rw [hSpec]
          simp only
          rw [hInstalledTargetFuture]
          simpa [resolveSemanticFuture] using hSubstitutedFuture.symm
    refine ⟨.child 0 bodyEdge.target, ?_, ?_⟩
    · rw [hFragment]
      apply (buildRecursionAutomaton_body_hasResolvedEdge_iff signature name
        bodyFragment state env label offers (.child 0 bodyEdge.target)).mpr
      right
      exact ⟨bodyEdge, hBodyEdge, hBodySource, hNotVariable,
        hBodyEnvironment, hBodyLabel, hBodyCurrent, hParentFuture, rfl⟩
    · exact TypeCompilationRelation.recur_body name body bodyTarget
        bodyEdge.target hBodyTargetRelated
  · rintro ⟨target, hParentResolved, hOuterTarget⟩
    rw [hFragment] at hParentResolved
    rcases (buildRecursionAutomaton_body_hasResolvedEdge_iff signature name
      bodyFragment state env label offers target).mp hParentResolved with
      ⟨bodyEdge, hBodyEdge, hBodySource, hVariable, hBodyEnvironment,
        hSilent, hCurrent, hParentFuture, hTargetEq⟩ |
      ⟨bodyEdge, hBodyEdge, hBodySource, hNotVariable, hBodyEnvironment,
        hBodyLabel, hBodyCurrent, hParentFuture, hTargetEq⟩
    · have hVariableRelation : TypeCompilationRelation body bodyEdge.source
          (.var name) :=
        (compileTypeFuel_variableEdge_source_var signature name
          (typeCompilationFuel body) body True
          (typeCompilationFuel_sufficient body) hTailBody bodyEdge hBodyEdge
            hVariable).2
      rw [hBodySource] at hVariableRelation
      have hResidualEq : residual = .var name :=
        TypeCompilationRelation.residual_unique hRelated hVariableRelation
      exact (hNotMarker hResidualEq).elim
    · subst target
      cases hOuterTarget with
      | recur_body _ _ bodyTarget _ hBodyTargetRelated =>
          let bodyOffers : TypeOfferSummary :=
            { current := offers.current
              future :=
                match bodyEdge.future with
                | .explicit future => future
                | .at referenced removed =>
                    computeFuture
                      { states := bodyFragment.states
                        edges := bodyFragment.edges }
                      referenced \ removed }
          have hBodyResolved : bodyFragment.HasResolvedEdge state env label
              bodyOffers bodyEdge.target :=
            ⟨bodyEdge, hBodyEdge, hBodySource, hBodyEnvironment, hBodyLabel,
              hBodyCurrent, rfl, rfl⟩
          have hBodySemantic : DecoratedTypeTransition env residual label
              bodyOffers bodyTarget :=
            (hBodyStep hRelated hLocal hAvoids).mpr
              ⟨bodyEdge.target, hBodyResolved, hBodyTargetRelated⟩
          have hBodyOffers :=
            (decoratedTypeTransition_iff_typeOffers env residual label
              bodyOffers bodyTarget).mp hBodySemantic
          obtain ⟨policy, hBodyPolicy, hBodyPolicyFuture⟩ :=
            typeOffers_toPolicy residual env label bodyTarget
              bodyOffers.current bodyOffers.future hBodyOffers
          have hBodyPolicyRaw : PolicyTypeOffers bodyEdge.environment residual
              label bodyTarget bodyEdge.current policy := by
            rw [hBodyEnvironment, hBodyCurrent]
            exact hBodyPolicy
          have hSpec := compilationRelation_futureSpecMatchesPolicy signature
            hRelated (name :: bound) hBoundBody hHygienicBody
              hTailRecursiveBody hBodyEdge hBodySource hBodyLabel
                hBodyTargetRelated hBodyPolicyRaw
          have hSubstitutedPolicy :=
            policyTypeOffers_replaceVar_forward bound name body hBoundBody
              hResidualTail hResidualBound hResidualFresh hBodyPolicy
          have hSubstitutedFuture : offers.future =
              resolveSemanticFuture
                (bodyTarget.replaceVar name (.recur name body)) policy := by
            cases policy with
            | explicit semanticFuture =>
                rcases hSpec with ⟨rawFuture, hRawFuture⟩
                rw [hRawFuture] at hParentFuture
                have hBodyFutureRaw : rawFuture = semanticFuture := by
                  simpa [bodyOffers, hRawFuture, resolveSemanticFuture] using
                    hBodyPolicyFuture
                calc
                  offers.future = rawFuture := hParentFuture.symm
                  _ = semanticFuture := hBodyFutureRaw
                  _ = resolveSemanticFuture
                      (bodyTarget.replaceVar name (.recur name body))
                        (.explicit semanticFuture) := by
                    simp [resolveSemanticFuture]
            | subtract removed =>
                rw [hSpec] at hParentFuture
                simp only at hParentFuture
                have hInstalledTargetFuture : computeFuture
                    { states :=
                        (buildRecursionAutomaton signature name
                          bodyFragment).states
                      edges :=
                        (buildRecursionAutomaton signature name
                          bodyFragment).edges }
                    (.child 0 bodyEdge.target) =
                      typeFutureOffers
                        (bodyTarget.replaceVar name (.recur name body)) := by
                  simpa [bodyFragment] using
                    hFuture bodyEdge.target bodyTarget hBodyTargetRelated
                rw [hInstalledTargetFuture] at hParentFuture
                simpa [resolveSemanticFuture] using hParentFuture.symm
          apply (decoratedTypeTransition_iff_typeOffers env
            (residual.replaceVar name (.recur name body)) label offers
              (bodyTarget.replaceVar name (.recur name body))).mpr
          rw [hSubstitutedFuture]
          exact hSubstitutedPolicy.toTypeOffers

/-- The two halves compose into the scoped tagged-body obligation. -/
private theorem recursionBodyScopedStepCorrect_of_bundle
    (signature : TypeAlphabet) (bound : List String) (name : String)
    (body : PactType)
    (hBoundBody : body.AllVariablesBound (name :: bound))
    (hHygienicBody : body.BinderHygienic (name :: bound))
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
  · exact recursionBodyScopedStep_nonMarker signature bound name body
      hBoundBody hHygienicBody hTailBody hTailRecursiveBody hBodyStep
        hBodyFutureCorrect hFuture hRelated hMarker hLocal hAvoids

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
    (hHygienic : PactType.BinderHygienic [] (.recur name body))
    (hGuarded : PactType.ClockGuarded (.recur name body))
    (hTail : PactType.TailRecursive (.recur name body))
    (hLinear : PactType.SameCycleMessageLinear (.recur name body))
    (hBodyBundle : CompilationProofBundle signature body)
    (hBodyFuture : RecursionBodyFutureCorrect signature name body)
    (hExecutionMarker : ∀ q r, TypeCompilationRelation body q r →
      (MarkerReachable (sequenceExecutionFragment
        (compileTypeFuel signature (typeCompilationFuel body) body)) name q ↔
          PactType.markerReachableSubst name r = true)) :
    CompilationSequenceExecutionCorrect signature (.recur name body) := by
  classical
  let processType := PactType.recur name body
  let fuel := typeCompilationFuel processType
  let fragment := compileTypeFuel signature fuel processType
  let execution := sequenceExecutionAutomaton fragment
  have hFuel : TypeCompilationFuelSufficient processType fuel := by
    exact typeCompilationFuel_sufficient processType
  have hTargets : fragment.FutureTargetsInStates := by
    exact compileTypeFuel_futureTargetsInStates signature fuel processType hFuel
  have hClosed : execution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed fragment hTargets
  have hCompleting : CompilationCompletingCorrect signature processType := by
    exact compilationCompletingCorrect_recursion_regular_leaf signature name
      body hSupports hGuarded hTail hHygienic
  intro state residual hRelated
  have hStateFragment : state ∈ fragment.states := by
    have hCanonical := compilationStateCorrect_of_compilation signature
      processType state residual hRelated
    simpa [fragment, fuel, processType] using hCanonical
  have hStateExecution : state ∈ execution.states := by
    exact Finset.mem_union_left _ hStateFragment
  constructor
  · let bodyFragment := compileTypeFuel signature
        (typeCompilationFuel body) body
    let bodyExecutionFragment := sequenceExecutionFragment bodyFragment
    let stoppedBody := markerStoppedFragment bodyExecutionFragment name
    let shadowFragment := buildRecursionAutomaton signature name stoppedBody
    let shadow : PendingAutomaton := shadowFragment.toPending
    have hBodyFuel : TypeCompilationFuelSufficient body
        (typeCompilationFuel body) := typeCompilationFuel_sufficient body
    have hBodyTargets : bodyFragment.FutureTargetsInStates :=
      compileTypeFuel_futureTargetsInStates signature
        (typeCompilationFuel body) body hBodyFuel
    have hBodyInitial : bodyFragment.initial ∈ bodyFragment.states :=
      compileTypeFuel_initial_mem signature (typeCompilationFuel body) body
        hBodyFuel
    have hBodyExecutionTargets : bodyExecutionFragment.FutureTargetsInStates :=
      sequenceExecutionFragment_futureTargetsInStates bodyFragment hBodyTargets
    have hBodyExecutionClosed : bodyExecutionFragment.toPending.ReferencesClosed :=
      PendingAutomaton.referencesClosed_of_futureTargetsInStates
        bodyExecutionFragment hBodyExecutionTargets
    have hStoppedTargets : stoppedBody.FutureTargetsInStates :=
      markerStoppedFragment_futureTargetsInStates bodyExecutionFragment name
        hBodyExecutionTargets
    have hStoppedClosed : stoppedBody.toPending.ReferencesClosed :=
      PendingAutomaton.referencesClosed_of_futureTargetsInStates stoppedBody
        hStoppedTargets
    have hStoppedMarkers : MarkerEdgesInert stoppedBody name :=
      markerStoppedFragment_markerEdgesInert bodyExecutionFragment name
    have hStoppedInitial : stoppedBody.initial ∈ stoppedBody.states := by
      exact Finset.mem_union_left _ hBodyInitial
    have hShadowTargets : shadowFragment.FutureTargetsInStates :=
      buildRecursionAutomaton_futureTargetsInStates signature name stoppedBody
        hStoppedTargets hStoppedInitial
    have hShadowClosed : shadow.ReferencesClosed := by
      exact PendingAutomaton.referencesClosed_of_futureTargetsInStates
        shadowFragment hShadowTargets
    have hFragmentEq : fragment =
        buildRecursionAutomaton signature name bodyFragment := by
      simp only [fragment, fuel, processType, bodyFragment,
        typeCompilationFuel, Nat.one_add, compileTypeFuel]
    have hEdges : execution.edges = shadow.edges := by
      simpa [execution, shadow, shadowFragment, stoppedBody,
        bodyExecutionFragment, hFragmentEq] using
          sequenceExecution_buildRecursion_edges signature name bodyFragment
    have hTailFields : body.TailOccurrences name True ∧
        body.TailRecursive := by
      simpa only [PactType.TailRecursive] using hTail
    have hInitialRelation : TypeCompilationRelation body bodyFragment.initial
        body := by
      exact compileTypeFuel_initial_relation signature
        (typeCompilationFuel body) body hBodyFuel
    have hBodyEntryMenu : computeFuture
        (sequenceExecutionAutomaton bodyFragment) bodyFragment.initial =
          typeFutureOffers body := by
      have hCanonical := hBodyBundle.execution bodyFragment.initial body
        hInitialRelation
      simpa [CompilationSequenceExecutionCorrect, bodyFragment] using
        hCanonical.1
    have hStoppedEntryMenu : computeFuture stoppedBody.toPending
        stoppedBody.initial = typeFutureOffers body := by
      have hStopped := markerStopped_sequenceExecution_computeFuture signature
        name (typeCompilationFuel body) body hBodyFuel hTailFields.1
          bodyFragment.initial hBodyInitial
      have hStopped' : computeFuture stoppedBody.toPending
          stoppedBody.initial = computeFuture
            (sequenceExecutionAutomaton bodyFragment) bodyFragment.initial := by
        simpa [stoppedBody, bodyExecutionFragment, bodyFragment] using
          hStopped
      exact hStopped'.trans hBodyEntryMenu
    cases hRelated with
    | recur_source =>
        have hShadowState : (.root : TypeAutomatonState) ∈ shadow.states := by
          simp [shadow, shadowFragment, buildRecursionAutomaton,
            finishAutomatonFragment, AutomatonFragment.toPending]
        have hSameFuture := computeFuture_eq_of_same_edges execution shadow
          hEdges hClosed hShadowClosed .root hStateExecution hShadowState
        have hShadowRoot : computeFuture shadow .root =
            computeFuture shadow (.child 0 stoppedBody.initial) := by
          simpa [shadow, shadowFragment, AutomatonFragment.toPending] using
            buildRecursionAutomaton_computeFuture_root signature name
              stoppedBody hStoppedTargets hStoppedInitial
        have hShadowEntry : computeFuture shadow
            (.child 0 stoppedBody.initial) =
              computeFuture stoppedBody.toPending stoppedBody.initial := by
          simpa [shadow, shadowFragment, AutomatonFragment.toPending] using
            computeFuture_buildRecursionAutomaton_child_at_initial signature
              name stoppedBody hStoppedMarkers hStoppedClosed hShadowClosed
                hStoppedInitial
        exact hSameFuture.trans (hShadowRoot.trans
          (hShadowEntry.trans (hStoppedEntryMenu.trans
            (typeFutureOffers_recur name body).symm)))
    | recur_body _ _ childResidual childQ hChild =>
        have hBodyState : childQ ∈ bodyFragment.states := by
          have hCanonical := compilationStateCorrect_of_compilation signature
            body childQ childResidual hChild
          simpa [bodyFragment] using hCanonical
        have hBodyExecutionState : childQ ∈ bodyExecutionFragment.states :=
          Finset.mem_union_left _ hBodyState
        have hStoppedState : childQ ∈ stoppedBody.states := by
          simpa [stoppedBody, markerStoppedFragment] using hBodyExecutionState
        have hShadowState : (.child 0 childQ : TypeAutomatonState) ∈
            shadow.states := by
          simp [shadow, shadowFragment, buildRecursionAutomaton,
            finishAutomatonFragment, childStates, childState, hStoppedState,
              AutomatonFragment.toPending]
        have hSameFuture := computeFuture_eq_of_same_edges execution shadow
          hEdges hClosed hShadowClosed (.child 0 childQ) hStateExecution
            hShadowState
        have hBodyResidualMenu : computeFuture
            (sequenceExecutionAutomaton bodyFragment) childQ =
              typeFutureOffers childResidual := by
          have hCanonical := hBodyBundle.execution childQ childResidual hChild
          simpa [CompilationSequenceExecutionCorrect, bodyFragment] using
            hCanonical.1
        have hStoppedResidualMenu : computeFuture stoppedBody.toPending childQ =
            typeFutureOffers childResidual := by
          have hStopped := markerStopped_sequenceExecution_computeFuture
            signature name (typeCompilationFuel body) body hBodyFuel
              hTailFields.1 childQ hBodyState
          have hStopped' : computeFuture stoppedBody.toPending childQ =
              computeFuture (sequenceExecutionAutomaton bodyFragment) childQ := by
            simpa [stoppedBody, bodyExecutionFragment, bodyFragment] using
              hStopped
          exact hStopped'.trans hBodyResidualMenu
        have hResidualTail : childResidual.TailOccurrences name True :=
          compilationRelation_tailOccurrences_true name hChild hTailFields.2
            hTailFields.1
        have hExecutionMarker' : MarkerReachable bodyExecutionFragment name
            childQ ↔ PactType.markerReachableSubst name childResidual = true := by
          simpa [bodyExecutionFragment, bodyFragment] using
            hExecutionMarker childQ childResidual hChild
        have hStoppedMarker : MarkerReachable stoppedBody name childQ ↔
            PactType.markerReachableSubst name childResidual = true := by
          exact (markerStoppedFragment_markerReachable_self
            bodyExecutionFragment name hBodyExecutionClosed childQ
              hBodyExecutionState).trans hExecutionMarker'
        rw [PactType.replaceVar_typeFutureOffers_recur,
          PactType.futureOffersSubst_eq_union_marker name
            body.CanCompleteBeforeTock (typeFutureOffers body) childResidual
              hResidualTail]
        by_cases hReach : MarkerReachable stoppedBody name childQ
        · have hShadowChild : computeFuture shadow (.child 0 childQ) =
              computeFuture stoppedBody.toPending childQ ∪
                computeFuture shadow (.child 0 stoppedBody.initial) := by
            simpa [shadow, shadowFragment, AutomatonFragment.toPending] using
              computeFuture_buildRecursionAutomaton_child_of_marker signature
                name stoppedBody hStoppedMarkers hStoppedClosed hShadowClosed
                  hStoppedInitial childQ hStoppedState hReach
          have hShadowEntry : computeFuture shadow
              (.child 0 stoppedBody.initial) =
                computeFuture stoppedBody.toPending stoppedBody.initial := by
            simpa [shadow, shadowFragment, AutomatonFragment.toPending] using
              computeFuture_buildRecursionAutomaton_child_at_initial signature
                name stoppedBody hStoppedMarkers hStoppedClosed hShadowClosed
                  hStoppedInitial
          rw [hSameFuture, hShadowChild, hShadowEntry, hStoppedResidualMenu,
            hStoppedEntryMenu, if_pos (hStoppedMarker.mp hReach)]
        · have hShadowChild : computeFuture shadow (.child 0 childQ) =
              computeFuture stoppedBody.toPending childQ := by
            simpa [shadow, shadowFragment, AutomatonFragment.toPending] using
              computeFuture_buildRecursionAutomaton_child_of_no_marker
                signature name stoppedBody hStoppedMarkers hStoppedClosed
                  hShadowClosed childQ hStoppedState
                    (by simpa [MarkerReachable] using hReach)
          have hMarkerFalse :
              PactType.markerReachableSubst name childResidual ≠ true := by
            intro hValue
            exact hReach (hStoppedMarker.mpr hValue)
          rw [hSameFuture, hShadowChild, hStoppedResidualMenu,
            if_neg hMarkerFalse]
          simp
  · let completes : TypeAutomatonState → Prop := fun candidate =>
      ∃ candidateResidual,
        TypeCompilationRelation processType candidate candidateResidual ∧
          PactType.completionEval (fun _ => false) candidateResidual = true
    have hWitnessCompletes : ∀ completed,
        completed ∈ fragment.accepting ∨ completed ∈ fragment.completing →
          completes completed := by
      intro completed hCompleted
      rcases hCompleted with hAccepting | hCompletingState
      · have hSkip := compiledFragmentAccepting_represented signature fuel
          processType hFuel completed hAccepting
        exact ⟨.skip, hSkip, by simp [PactType.completionEval]⟩
      · obtain ⟨completedResidual, hCompletedRelated, hCanComplete⟩ :=
          compiledFragmentCompleting_represented signature [] fuel processType
            hFuel hTail hHygienic completed hCompletingState
        refine ⟨completedResidual, hCompletedRelated, ?_⟩
        rw [PactType.completionEval_eq_canCompleteBeforeTock_of_all_false]
        · exact hCanComplete
        · intro variableName
          rfl
    constructor
    · rintro ⟨completed, hReachable, hCompleted⟩
      have hCompletedCompletes := hWitnessCompletes completed hCompleted
      have hSourceCompletes : completes state := by
        by_contra hSourceDoesNotComplete
        let allowed := execution.states.filter fun candidate =>
          ¬ completes candidate
        have hSourceAllowed : state ∈ allowed := by
          exact Finset.mem_filter.mpr
            ⟨hStateExecution, hSourceDoesNotComplete⟩
        have hAllowedClosed : ∀ source ∈ allowed,
            execution.referencedStates source ⊆ allowed := by
          intro source hSource target hReference
          have hSourceFields := Finset.mem_filter.mp hSource
          refine Finset.mem_filter.mpr
            ⟨hClosed source hSourceFields.1 hReference, ?_⟩
          intro hTargetCompletes
          obtain ⟨targetResidual, hTargetRelated, hTargetEval⟩ :=
            hTargetCompletes
          simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
            Finset.mem_filter] at hReference
          rcases hReference with
            ⟨executionEdge, ⟨hExecutionEdge, hExecutionSource⟩,
              hExecutionFuture⟩
          simp only [execution, sequenceExecutionAutomaton,
            Finset.mem_image] at hExecutionEdge
          rcases hExecutionEdge with ⟨rawEdge, hRawEdge, rfl⟩
          have hRawSource : rawEdge.source = source := by
            simpa using hExecutionSource
          have hNonClock :
              rawEdge.label.semantic ≠ TypeLabel.tock := by
            intro hClock
            simp [hClock] at hExecutionFuture
          have hRawTarget : target = rawEdge.target := by
            cases hLabel : rawEdge.label with
            | future =>
                cases hSpec : rawEdge.future with
                | explicit offers =>
                    simp [hLabel, hSpec,
                      AutomatonConstructionLabel.semantic] at hExecutionFuture
                | «at» inner removed =>
                    have hTargetInner : target = inner := by
                      simpa [hLabel, hSpec,
                        AutomatonConstructionLabel.semantic,
                        TypeLabel.silent] using hExecutionFuture
                    have hInnerTarget :=
                      compileTypeFuel_futureReferencesTarget signature fuel
                        processType rawEdge hRawEdge inner removed hSpec
                    exact hTargetInner.trans hInnerTarget
            | visible label =>
                have hLabelNonClock : label ≠ TypeLabel.tock := by
                  simpa [hLabel, AutomatonConstructionLabel.semantic] using
                    hNonClock
                simpa [hLabel, AutomatonConstructionLabel.semantic,
                  hLabelNonClock] using hExecutionFuture
            | «variable» variableName =>
                simpa [hLabel, AutomatonConstructionLabel.semantic,
                  TypeLabel.silent] using hExecutionFuture
          have hTargetRelated' : TypeCompilationRelation processType
              rawEdge.target targetResidual := by
            simpa [hRawTarget] using hTargetRelated
          obtain ⟨sourceResidual, hSourceRelated, hSourceEval⟩ :=
            compiledFragmentNonClockPredecessor_eval signature []
              (fun _ => false) fuel processType (by simp) hFuel hTail
                hHygienic rawEdge hRawEdge hNonClock targetResidual
                  hTargetRelated' hTargetEval
          apply hSourceFields.2
          refine ⟨sourceResidual, ?_, hSourceEval⟩
          simpa [hRawSource] using hSourceRelated
        have hCompletedAllowed :=
          execution.futureReachable_subset_of_reference_closed state allowed
            hSourceAllowed hAllowedClosed hReachable
        exact (Finset.mem_filter.mp hCompletedAllowed).2 hCompletedCompletes
      obtain ⟨sourceResidual, hSourceRelated, hSourceEval⟩ := hSourceCompletes
      have hResidual : sourceResidual = residual :=
        TypeCompilationRelation.residual_unique hSourceRelated hRelated
      subst sourceResidual
      rw [PactType.completionEval_eq_canCompleteBeforeTock_of_all_false]
        at hSourceEval
      · exact hSourceEval
      · intro variableName
        rfl
    · intro hCanComplete
      refine ⟨state, execution.mem_futureReachable_self state, Or.inr ?_⟩
      have hCanonical := (hCompleting state residual hRelated).mpr hCanComplete
      simpa [fragment, fuel, processType] using hCanonical

/-- Scoped step correspondence for a closed binder.  Header composition is
already proved by `compilationFragmentStepCorrect_recursion`; what remains is
the tagged-body package `RecursionBodyStepCorrect`, i.e. that a semantic step
of the substituted residual matches a resolved edge of the installed graph. -/
private theorem compilationScopedFragmentStepCorrect_recursion_bounded_leaf
    (signature : TypeAlphabet) (bound : List String) (name : String)
    (body : PactType)
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.recur name body))
    (hBoundBody : body.AllVariablesBound (name :: bound))
    (hHygienic : PactType.BinderHygienic bound (.recur name body))
    (hGuarded : PactType.ClockGuarded (.recur name body))
    (hTail : PactType.TailRecursive (.recur name body))
    (hLinear : PactType.SameCycleMessageLinear (.recur name body))
    (hScoped : PactType.InterfaceScoped (.recur name body))
    (hBodyBundle : CompilationProofBundle signature body)
    (hBodyFuture : RecursionBodyFutureCorrect signature name body) :
    CompilationScopedFragmentStepCorrect signature (.recur name body) := by
  have hTailFields : body.TailOccurrences name True ∧ body.TailRecursive := by
    simpa only [PactType.TailRecursive] using hTail
  have hHygienicBody : body.BinderHygienic (name :: bound) := by
    simpa only [PactType.BinderHygienic] using
      (show name ∉ bound ∧ body.BinderHygienic (name :: bound) by
        simpa only [PactType.BinderHygienic] using hHygienic).2
  intro residual residual' state env label offers hRelated hLocal hAvoids
  exact compilationScopedFragmentStepCorrect_recursion_of_body signature name
    body hBodyFuture
    (recursionBodyScopedStepCorrect_of_bundle signature bound name body
      hBoundBody hHygienicBody hTailFields.1 hTailFields.2
        hBodyBundle.scopedStep hBodyBundle.future hBodyFuture) hRelated hLocal
          hAvoids

/-- Recursion closure against an ambient bound-name list.  The body itself is
compiled open: only `AllVariablesBound (name :: bound)` is available for it,
so every component is obtained from the body's own bundle plus the marker
correspondence, never from a closedness assumption about `body`. -/
theorem compilationProofBundle_recursion_bounded_leaf
    (signature : TypeAlphabet) (bound : List String) (name : String)
    (body : PactType)
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.recur name body))
    (hBoundBody : body.AllVariablesBound (name :: bound))
    (hHygienic : PactType.BinderHygienic bound (.recur name body))
    (hGuarded : PactType.ClockGuarded (.recur name body))
    (hTail : PactType.TailRecursive (.recur name body))
    (hLinear : PactType.SameCycleMessageLinear (.recur name body))
    (hScoped : PactType.InterfaceScoped (.recur name body))
    (hBodyBundle : CompilationProofBundle signature body)
    (hMarker : ∀ q r, TypeCompilationRelation body q r →
      (MarkerReachable (compileTypeFuel signature (typeCompilationFuel body)
        body) name q ↔ PactType.markerReachableSubst name r = true))
    (hExecutionMarker : ∀ q r, TypeCompilationRelation body q r →
      (MarkerReachable (sequenceExecutionFragment
        (compileTypeFuel signature (typeCompilationFuel body) body)) name q ↔
          PactType.markerReachableSubst name r = true)) :
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
          bound name body hSignature hSupports hBoundBody hHygienic hGuarded
            hTail hLinear hScoped hBodyBundle hBodyFuture
      execution :=
        compilationSequenceExecutionCorrect_recursion_bounded_leaf signature
          name body hSignature hSupports hHygienicEmpty hGuarded hTail hLinear
            hBodyBundle hBodyFuture hExecutionMarker }

end

end Pact
