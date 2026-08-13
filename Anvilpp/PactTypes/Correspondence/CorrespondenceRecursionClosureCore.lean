import Anvilpp.PactTypes.Correspondence.CorrespondenceCompletingRepresented

/-!
# Substituted-completion regularity lemmas feeding the recursion completing-closure
-/

namespace Pact

noncomputable section


/- Singleton specialization used by the outermost recursion closure.  The
substantive induction is valuation-polymorphic above so nested binders can
extend the environment without losing enclosing recursion values. -/
theorem compiledFragmentNonClockPredecessor_subst
    (signature : TypeAlphabet) (name : String) (value : Bool)
    (fuel : Nat) (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel)
    (hTail : processType.TailRecursive)
    (hHygienic : processType.BinderHygienic [name])
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel signature fuel processType).edges)
    (hNonClock : edge.label.semantic ≠ TypeLabel.tock)
    (targetResidual : PactType)
    (hTargetRelated : TypeCompilationRelation processType edge.target
      targetResidual)
    (hTargetComplete : PactType.canCompleteBeforeTockSubst name value
      targetResidual = true) :
    ∃ sourceResidual,
      TypeCompilationRelation processType edge.source sourceResidual ∧
        PactType.canCompleteBeforeTockSubst name value sourceResidual = true := by
  let valuation : String → Bool :=
    Function.update (fun _ => false) name value
  have hSupported : ∀ variableName, variableName ∉ [name] →
      valuation variableName = false := by
    intro variableName hNotMem
    have hNe : variableName ≠ name := by
      intro hEq
      subst variableName
      exact hNotMem (by simp)
    simp [valuation, Function.update, hNe]
  have hTargetEval : PactType.completionEval valuation targetResidual = true := by
    simpa [valuation] using
      (show PactType.completionEval
          (Function.update (fun _ => false) name value) targetResidual = true by
        rw [PactType.completionEval_singleton_eq_canCompleteBeforeTockSubst]
        exact hTargetComplete)
  obtain ⟨sourceResidual, hSourceRelated, hSourceEval⟩ :=
    compiledFragmentNonClockPredecessor_eval signature [name] valuation fuel
      processType hSupported hFuel hTail hHygienic edge hEdge hNonClock
        targetResidual hTargetRelated hTargetEval
  refine ⟨sourceResidual, hSourceRelated, ?_⟩
  rw [← PactType.completionEval_singleton_eq_canCompleteBeforeTockSubst]
  simpa [valuation] using hSourceEval

/-- Forward (`⊆`) half of `recursionBodyCompletingClosure_iff`.

`completingBackClosure_subset_of_predecessor_closed` is applied with the
ambient set

  `edges.image (·.source) ∪ completing`

— deliberately *not* `states`, which is exactly what makes any carrier
well-formedness invariant unnecessary — filtered by the predicate

  `fun q => ∃ r, TypeCompilationRelation body q r ∧ subst r = true`.

`TypeCompilationRelation.residual_unique` then transfers the witness to the
given `residual`.  See `compiledFragmentNonClockPredecessor_subst` for why
this predicate is existential rather than universal: the universal variant is
refuted by a `.variable` marker hidden inside a parallel product, whose target
represents nothing.

Seed inclusion has two parts.  The `completing` half combines
`compiledFragmentCompleting_represented` (to get a witness at all) with
`hVanilla` and `PactType.canCompleteBeforeTock_le_subst`.  The recursive-call
half applies only in the branch where the body entry is completing; there
`compileTypeFuel_variableEdge_source_var` supplies both the witness and its
identity `PactType.var name`, whose substituted value is
`body.CanCompleteBeforeTock` — and that is `true` precisely because the entry
is completing, by `hVanilla` at `compileTypeFuel_initial_relation`. -/
theorem recursionBodyCompletingClosure_subset
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hTailOccurrences : PactType.TailOccurrences name True body)
    (hBodyTail : PactType.TailRecursive body)
    (hBodyHygienic : PactType.BinderHygienic [name] body)
    (hVanilla : CompilationCompletingCorrect signature body)
    (state : TypeAutomatonState) (residual : PactType)
    (hRelated : TypeCompilationRelation body state residual)
    (hMem : state ∈ completingBackClosure
        (compileTypeFuel signature (typeCompilationFuel body) body)
        ((if (compileTypeFuel signature (typeCompilationFuel body) body).initial ∈
              (compileTypeFuel signature (typeCompilationFuel body)
                body).completing then
            ((compileTypeFuel signature (typeCompilationFuel body)
                body).edges.filter
              fun edge => edge.label = .variable name).image
                fun edge => edge.source
          else ∅) ∪
          (compileTypeFuel signature (typeCompilationFuel body)
            body).completing)) :
    PactType.canCompleteBeforeTockSubst name body.CanCompleteBeforeTock
      residual = true := by
  classical
  have hMemAllowed := completingBackClosure_subset_of_predecessor_closed
    (compileTypeFuel signature (typeCompilationFuel body) body) _
    ((((compileTypeFuel signature (typeCompilationFuel body) body).edges.image
          fun e => e.source) ∪
        (compileTypeFuel signature (typeCompilationFuel body)
          body).completing).filter
      fun q => ∃ r, TypeCompilationRelation body q r ∧
        PactType.canCompleteBeforeTockSubst name body.CanCompleteBeforeTock r
          = true)
    ?seed ?closed hMem
  · obtain ⟨r, hRel, hSubst⟩ := (Finset.mem_filter.mp hMemAllowed).2
    rwa [TypeCompilationRelation.residual_unique hRel hRelated] at hSubst
  case seed =>
    intro q hq
    rcases Finset.mem_union.mp hq with hVar | hCompleting
    · have hIf : (compileTypeFuel signature (typeCompilationFuel body)
          body).initial ∈ (compileTypeFuel signature
            (typeCompilationFuel body) body).completing := by
        by_contra hNo
        rw [if_neg hNo] at hVar
        exact absurd hVar (by simp)
      rw [if_pos hIf] at hVar
      simp only [Finset.mem_image, Finset.mem_filter] at hVar
      obtain ⟨e, ⟨hE, hLabel⟩, hSource⟩ := hVar
      have hStep := (compileTypeFuel_variableEdge_source_var signature name
        (typeCompilationFuel body) body True
        (typeCompilationFuel_sufficient body) hTailOccurrences e hE hLabel).2
      have hValue : body.CanCompleteBeforeTock = true :=
        (hVanilla _ _ (compileTypeFuel_initial_relation signature
          (typeCompilationFuel body) body
          (typeCompilationFuel_sufficient body))).mp hIf
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, hE, hSource⟩),
          PactType.var name, ?_, ?_⟩
      · rw [← hSource]; exact hStep
      · simp [PactType.canCompleteBeforeTockSubst, hValue]
    · refine Finset.mem_filter.mpr
        ⟨Finset.mem_union_right _ hCompleting, ?_⟩
      obtain ⟨r, hRel, hComplete⟩ :=
        compiledFragmentCompleting_represented signature [name]
          (typeCompilationFuel body) body
            (typeCompilationFuel_sufficient body) hBodyTail hBodyHygienic q
              hCompleting
      exact ⟨r, hRel, PactType.canCompleteBeforeTock_le_subst name _ r
        hComplete⟩
  case closed =>
    intro e hE hSilent hTargetMem
    obtain ⟨rTarget, hRelTarget, hSubstTarget⟩ :=
      (Finset.mem_filter.mp hTargetMem).2
    obtain ⟨rSource, hRelSource, hSubstSource⟩ :=
      compiledFragmentNonClockPredecessor_subst signature name
        body.CanCompleteBeforeTock (typeCompilationFuel body) body
        (typeCompilationFuel_sufficient body) hBodyTail hBodyHygienic e hE
          hSilent rTarget hRelTarget hSubstTarget
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, hE, rfl⟩),
        rSource, hRelSource, hSubstSource⟩

/-- Whenever `value = false`, substituting `.var name` by `false` changes
nothing relative to the unsubstituted predicate: every `.var other` clause of
`canCompleteBeforeTockSubst` already evaluates to `false` unless `other = name`,
in which case it evaluates to `value = false` too.  So a genuine subst/plain
discrepancy is only possible when `value = true`; this lets
`recursionBodyCompletingClosure_superset` skip all graph reasoning whenever
`value = false`. -/
theorem canCompleteBeforeTockSubst_false (name : String)
    (processType : PactType) :
    PactType.canCompleteBeforeTockSubst name false processType =
      processType.CanCompleteBeforeTock := by
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      cases processType with
      | message msg dir =>
          simp [PactType.canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock]
      | progress pid =>
          simp [PactType.canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock]
      | tock =>
          simp [PactType.canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock]
      | skip =>
          simp [PactType.canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock]
      | var other =>
          simp [PactType.canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock]
      | recur other body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          by_cases hName : name = other
          · simp [PactType.canCompleteBeforeTockSubst, hName,
              PactType.CanCompleteBeforeTock]
          · simp only [PactType.canCompleteBeforeTockSubst, hName, if_false,
              PactType.CanCompleteBeforeTock,
              ih (sizeOf body) hBodySize body rfl]
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hBranches :
              PactType.branchCanCompleteBeforeTockSubst name false branches =
                PactType.BranchCanCompleteBeforeTock branches := by
            clear hElseSize hSize
            induction branches with
            | nil =>
                simp [PactType.branchCanCompleteBeforeTockSubst,
                  PactType.BranchCanCompleteBeforeTock]
            | cons branch rest ihRest =>
                have hBranchSize : sizeOf branch.2 < n := by
                  have hHead : sizeOf branch < sizeOf (branch :: rest) := by
                    simp_wf; omega
                  have hPair : sizeOf branch.2 < sizeOf branch := by
                    obtain ⟨action, processType⟩ := branch
                    simp_wf; omega
                  omega
                have hRestSize : sizeOf rest < n := by
                  have hHead : sizeOf rest < sizeOf (branch :: rest) := by
                    simp_wf; omega
                  omega
                unfold PactType.branchCanCompleteBeforeTockSubst
                  PactType.BranchCanCompleteBeforeTock
                rw [ih (sizeOf branch.2) hBranchSize branch.2 rfl,
                  ihRest hRestSize]
          simp only [PactType.canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize elseType rfl, hBranches]

      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hBranches :
              PactType.branchCanCompleteBeforeTockSubst name false branches =
                PactType.BranchCanCompleteBeforeTock branches := by
            clear hElseSize hSize
            induction branches with
            | nil =>
                simp [PactType.branchCanCompleteBeforeTockSubst,
                  PactType.BranchCanCompleteBeforeTock]
            | cons branch rest ihRest =>
                have hBranchSize : sizeOf branch.2 < n := by
                  have hHead : sizeOf branch < sizeOf (branch :: rest) := by
                    simp_wf; omega
                  have hPair : sizeOf branch.2 < sizeOf branch := by
                    obtain ⟨action, processType⟩ := branch
                    simp_wf; omega
                  omega
                have hRestSize : sizeOf rest < n := by
                  have hHead : sizeOf rest < sizeOf (branch :: rest) := by
                    simp_wf; omega
                  omega
                unfold PactType.branchCanCompleteBeforeTockSubst
                  PactType.BranchCanCompleteBeforeTock
                rw [ih (sizeOf branch.2) hBranchSize branch.2 rfl,
                  ihRest hRestSize]
          simp only [PactType.canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize elseType rfl, hBranches]

/- Lift a parametric completion-closure witness through any constructor child
whose pending edges and completing states are embedded by `childState`.  This
is the common graph step used by choice, sequence-right, and both offer
constructors; the hypotheses deliberately mention only the two projections
needed by backward closure. -/
/- A valuation whose live variables occur only in forbidden (non-tail)
positions has no effect on same-cycle completion.  The branch statement is
proved locally so the two offer constructors share the same structural
argument. -/
private theorem completionEval_eq_canCompleteBeforeTock_of_tailFalse
    (valuation : String → Bool) : ∀ processType : PactType,
    (∀ name, valuation name = true →
      processType.TailOccurrences name False) →
    PactType.completionEval valuation processType =
      processType.CanCompleteBeforeTock := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType valuation with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          (∀ name, valuation name = true →
            PactType.TailBranchOccurrences name False branches) →
          PactType.branchCompletionEval valuation branches =
            PactType.BranchCanCompleteBeforeTock branches := by
        intro branches hBranchesSize hTail
        induction branches with
        | nil =>
            simp [PactType.branchCompletionEval,
              PactType.BranchCanCompleteBeforeTock]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hBranchTail : ∀ name, valuation name = true →
                branchType.TailOccurrences name False := by
              intro name hValue
              have hFields := hTail name hValue
              simp only [PactType.TailBranchOccurrences] at hFields
              exact hFields.1
            have hRestTail : ∀ name, valuation name = true →
                PactType.TailBranchOccurrences name False rest := by
              intro name hValue
              have hFields := hTail name hValue
              simp only [PactType.TailBranchOccurrences] at hFields
              exact hFields.2
            simp only [PactType.branchCompletionEval,
              PactType.BranchCanCompleteBeforeTock]
            rw [ih (sizeOf branchType) hBranchSize valuation branchType rfl
                hBranchTail,
              restIH hRestSize hRestTail]
      intro hTail
      cases processType with
      | message msg dir =>
          simp [PactType.completionEval, PactType.CanCompleteBeforeTock]
      | progress pid =>
          simp [PactType.completionEval, PactType.CanCompleteBeforeTock]
      | skip =>
          simp [PactType.completionEval, PactType.CanCompleteBeforeTock]
      | tock =>
          simp [PactType.completionEval, PactType.CanCompleteBeforeTock]
      | var other =>
          have hFalse : valuation other = false := by
            cases hValue : valuation other with
            | false => rfl
            | true =>
                exfalso
                have hImpossible : other = other → False := by
                  simpa only [PactType.TailOccurrences] using
                    (hTail other hValue)
                exact hImpossible rfl
          simp [PactType.completionEval, PactType.CanCompleteBeforeTock,
            hFalse]
      | recur binder body =>
          have hBodySize : sizeOf body < n := by
            rw [← hSize]; simp_wf; omega
          let nestedValuation := Function.update valuation binder false
          have hBodyTail : ∀ name, nestedValuation name = true →
              body.TailOccurrences name False := by
            intro name hValue
            have hNe : name ≠ binder := by
              intro hEq
              subst name
              simp [nestedValuation] at hValue
            have hOuterValue : valuation name = true := by
              simpa [nestedValuation, Function.update, hNe] using hValue
            have hOuterTail := hTail name hOuterValue
            simpa only [PactType.TailOccurrences, if_neg hNe.symm] using
              hOuterTail
          simp only [PactType.completionEval,
            PactType.CanCompleteBeforeTock]
          exact ih (sizeOf body) hBodySize nestedValuation body rfl hBodyTail
      | choice left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          have hFields :
              (∀ name, valuation name = true →
                left.TailOccurrences name False) ∧
              (∀ name, valuation name = true →
                right.TailOccurrences name False) := by
            constructor <;> intro name hValue
            · have hPair := hTail name hValue
              simp only [PactType.TailOccurrences] at hPair
              exact hPair.1
            · have hPair := hTail name hValue
              simp only [PactType.TailOccurrences] at hPair
              exact hPair.2
          simp only [PactType.completionEval,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize valuation left rfl hFields.1,
            ih (sizeOf right) hRightSize valuation right rfl hFields.2]
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          have hFields :
              (∀ name, valuation name = true →
                left.TailOccurrences name False) ∧
              (∀ name, valuation name = true →
                right.TailOccurrences name False) := by
            constructor <;> intro name hValue
            · have hPair := hTail name hValue
              simp only [PactType.TailOccurrences] at hPair
              exact hPair.1
            · have hPair := hTail name hValue
              simp only [PactType.TailOccurrences] at hPair
              exact hPair.2
          simp only [PactType.completionEval,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize valuation left rfl hFields.1,
            ih (sizeOf right) hRightSize valuation right rfl hFields.2]
      | seq left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          have hFields :
              (∀ name, valuation name = true →
                left.TailOccurrences name False) ∧
              (∀ name, valuation name = true →
                right.TailOccurrences name False) := by
            constructor <;> intro name hValue
            · have hPair := hTail name hValue
              simp only [PactType.TailOccurrences] at hPair
              exact hPair.1
            · have hPair := hTail name hValue
              simp only [PactType.TailOccurrences] at hPair
              exact hPair.2
          simp only [PactType.completionEval,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize valuation left rfl hFields.1,
            ih (sizeOf right) hRightSize valuation right rfl hFields.2]
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          have hFields :
              (∀ name, valuation name = true →
                left.TailOccurrences name False) ∧
              (∀ name, valuation name = true →
                right.TailOccurrences name False) := by
            constructor <;> intro name hValue
            · have hPair := hTail name hValue
              simp only [PactType.TailOccurrences] at hPair
              exact hPair.1
            · have hPair := hTail name hValue
              simp only [PactType.TailOccurrences] at hPair
              exact hPair.2
          simp only [PactType.completionEval,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize valuation left rfl hFields.1,
            ih (sizeOf right) hRightSize valuation right rfl hFields.2]
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFields :
              (∀ name, valuation name = true →
                elseType.TailOccurrences name False) ∧
              (∀ name, valuation name = true →
                PactType.TailBranchOccurrences name False branches) := by
            constructor <;> intro name hValue
            · have hPair := hTail name hValue
              simp only [PactType.TailOccurrences] at hPair
              exact hPair.1
            · have hPair := hTail name hValue
              simp only [PactType.TailOccurrences] at hPair
              exact hPair.2
          simp only [PactType.completionEval,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize valuation elseType rfl hFields.1,
            hBranches branches hBranchesSize hFields.2]
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFields :
              (∀ name, valuation name = true →
                elseType.TailOccurrences name False) ∧
              (∀ name, valuation name = true →
                PactType.TailBranchOccurrences name False branches) := by
            constructor <;> intro name hValue
            · have hPair := hTail name hValue
              simp only [PactType.TailOccurrences] at hPair
              exact hPair.1
            · have hPair := hTail name hValue
              simp only [PactType.TailOccurrences] at hPair
              exact hPair.2
          simp only [PactType.completionEval,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize valuation elseType rfl hFields.1,
            hBranches branches hBranchesSize hFields.2]

/- Tail regularity makes completion affine in the live free variables: if a
finite valuation makes a type complete, then either the type already completes
with every free variable false, or one live tail variable suffices by itself.
This is the syntax projection that lets a nested binder reuse the existing
one-variable graph closure induction. -/
private theorem branchCompletionEval_eq_branchCanCompleteBeforeTock_of_tailFalse
    (valuation : String → Bool) :
    ∀ branches : List (BareMessage × PactType),
      (∀ name, valuation name = true →
        PactType.TailBranchOccurrences name False branches) →
      PactType.branchCompletionEval valuation branches =
        PactType.BranchCanCompleteBeforeTock branches := by
  intro branches hTail
  induction branches with
  | nil =>
      simp [PactType.branchCompletionEval,
        PactType.BranchCanCompleteBeforeTock]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      have hHead : ∀ name, valuation name = true →
          branchType.TailOccurrences name False := by
        intro name hValue
        have hFields := hTail name hValue
        simp only [PactType.TailBranchOccurrences] at hFields
        exact hFields.1
      have hRest : ∀ name, valuation name = true →
          PactType.TailBranchOccurrences name False rest := by
        intro name hValue
        have hFields := hTail name hValue
        simp only [PactType.TailBranchOccurrences] at hFields
        exact hFields.2
      simp only [PactType.branchCompletionEval,
        PactType.BranchCanCompleteBeforeTock,
        completionEval_eq_canCompleteBeforeTock_of_tailFalse valuation
          branchType hHead,
        ih hRest]

private theorem replaceBranches_eq_self_of_tailBranchOccurrences_false
    (name : String) (replacement : PactType) :
    ∀ branches : List (BareMessage × PactType),
      PactType.TailBranchOccurrences name False branches →
      PactType.replaceBranches branches name replacement = branches := by
  intro branches hTail
  induction branches with
  | nil => simp [PactType.replaceBranches]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      simp only [PactType.TailBranchOccurrences] at hTail
      simp only [PactType.replaceBranches,
        PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement
          branchType hTail.1,
        ih hTail.2]

/- Substitution preserves a second live tail variable when both the replaced
variable and the second variable occur only in tail positions.  The strong
size induction is deliberate: branch lists contain recursive PactType
children, so a plain mutual theorem creates an unhelpful termination measure. -/
private theorem tailOccurrences_true_replaceVar_of_tail
    (target substituted : String) (replacement : PactType)
    (hReplacement : replacement.TailOccurrences target True) :
    ∀ processType : PactType,
      processType.TailOccurrences target True →
      processType.TailOccurrences substituted True →
      (processType.replaceVar substituted replacement).TailOccurrences
        target True := by
  intro processType hTarget hSubstituted
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.TailBranchOccurrences target True branches →
          PactType.TailBranchOccurrences substituted True branches →
          PactType.TailBranchOccurrences target True
            (PactType.replaceBranches branches substituted replacement) := by
        intro branches hBranchesSize hTargetBranches hSubstitutedBranches
        induction branches with
        | nil =>
            simp [PactType.replaceBranches, PactType.TailBranchOccurrences]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.TailBranchOccurrences]
              at hTargetBranches hSubstitutedBranches ⊢
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.replaceBranches,
              PactType.TailBranchOccurrences]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType
                hTargetBranches.1 hSubstitutedBranches.1 rfl,
              restIH hRestSize hTargetBranches.2 hSubstitutedBranches.2⟩
      cases processType with
      | message msg dir =>
          simp [PactType.replaceVar, PactType.TailOccurrences]
      | progress pid =>
          simp [PactType.replaceVar, PactType.TailOccurrences]
      | tock => simp [PactType.replaceVar, PactType.TailOccurrences]
      | skip => simp [PactType.replaceVar, PactType.TailOccurrences]
      | var other =>
          by_cases hEq : substituted = other
          · subst other
            simpa [PactType.replaceVar] using hReplacement
          · simp [PactType.replaceVar, hEq, PactType.TailOccurrences]
      | recur binder body =>
          by_cases hBinderSubstituted : substituted = binder
          · simpa [PactType.replaceVar, hBinderSubstituted] using hTarget
          · by_cases hBinderTarget : binder = target
            · subst binder
              simp [PactType.replaceVar, hBinderSubstituted,
                PactType.TailOccurrences]
            · have hBinderSubstituted' : binder ≠ substituted :=
                Ne.symm hBinderSubstituted
              simp only [PactType.TailOccurrences, if_neg hBinderTarget,
                if_neg hBinderSubstituted'] at hTarget hSubstituted
              simp only [PactType.replaceVar, if_neg hBinderSubstituted,
                PactType.TailOccurrences, if_neg hBinderTarget]
              have hBodySize : sizeOf body < n := by
                rw [← hSize]; simp_wf; omega
              exact ih (sizeOf body) hBodySize body hTarget hSubstituted rfl
      | choice left right | fairChoice _ left right =>
          simp only [PactType.TailOccurrences] at hTarget hSubstituted
          simp only [PactType.replaceVar, PactType.TailOccurrences]
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize left hTarget.1
              hSubstituted.1 rfl,
            ih (sizeOf right) hRightSize right hTarget.2
              hSubstituted.2 rfl⟩
      | seq left right =>
          simp only [PactType.TailOccurrences] at hTarget hSubstituted
          simp only [PactType.replaceVar, PactType.TailOccurrences]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false substituted
            replacement left hSubstituted.1]
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          exact ⟨hTarget.1,
            ih (sizeOf right) hRightSize right hTarget.2
              hSubstituted.2 rfl⟩
      | par left right interface =>
          simp only [PactType.TailOccurrences] at hTarget hSubstituted
          simp only [PactType.replaceVar, PactType.TailOccurrences]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false substituted
              replacement left hSubstituted.1,
            PactType.replaceVar_eq_self_of_tailOccurrences_false substituted
              replacement right hSubstituted.2]
          exact hTarget
      | xoffer elseType branches =>
          simp only [PactType.TailOccurrences] at hTarget hSubstituted
          simp only [PactType.replaceVar, PactType.TailOccurrences]
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hElseSize elseType hTarget.1
              hSubstituted.1 rfl,
            hBranches branches hBranchesSize hTarget.2 hSubstituted.2⟩
      | offer elseType branches =>
          simp only [PactType.TailOccurrences] at hTarget hSubstituted
          simp only [PactType.replaceVar, PactType.TailOccurrences]
          rw [replaceBranches_eq_self_of_tailBranchOccurrences_false
            substituted replacement branches hSubstituted.2]
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hElseSize elseType hTarget.1
              hSubstituted.1 rfl,
            hTarget.2⟩

private theorem tailOccurrences_true_of_false (name : String) :
    ∀ processType : PactType,
      processType.TailOccurrences name False →
      processType.TailOccurrences name True := by
  intro processType hTail
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.TailBranchOccurrences name False branches →
          PactType.TailBranchOccurrences name True branches := by
        intro branches hBranchesSize h
        induction branches with
        | nil => simp [PactType.TailBranchOccurrences]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.TailBranchOccurrences] at h ⊢
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            exact ⟨ih (sizeOf branchType) hBranchSize branchType h.1 rfl,
              restIH hRestSize h.2⟩
      cases processType with
      | message msg dir => simp [PactType.TailOccurrences]
      | progress pid => simp [PactType.TailOccurrences]
      | tock => simp [PactType.TailOccurrences]
      | skip => simp [PactType.TailOccurrences]
      | var other =>
          simp only [PactType.TailOccurrences] at hTail ⊢
          intro _
          trivial
      | recur binder body =>
          by_cases hEq : binder = name
          · simp [PactType.TailOccurrences, hEq]
          · simp only [PactType.TailOccurrences, if_neg hEq] at hTail ⊢
            have hBodySize : sizeOf body < n := by
              rw [← hSize]; simp_wf; omega
            exact ih (sizeOf body) hBodySize body hTail rfl
      | choice left right | fairChoice _ left right =>
          simp only [PactType.TailOccurrences] at hTail ⊢
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize left hTail.1 rfl,
            ih (sizeOf right) hRightSize right hTail.2 rfl⟩
      | seq left right =>
          simp only [PactType.TailOccurrences] at hTail ⊢
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          exact ⟨hTail.1, ih (sizeOf right) hRightSize right hTail.2 rfl⟩
      | par left right interface =>
          simpa only [PactType.TailOccurrences] using hTail
      | xoffer elseType branches =>
          simp only [PactType.TailOccurrences] at hTail ⊢
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hElseSize elseType hTail.1 rfl,
            hBranches branches hBranchesSize hTail.2⟩
      | offer elseType branches =>
          simp only [PactType.TailOccurrences] at hTail ⊢
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hElseSize elseType hTail.1 rfl,
            hTail.2⟩

/- Tail-position regularity is preserved by every represented residual. -/
theorem compilationRelation_tailOccurrences_true
    (name : String) {processType residual : PactType}
    {state : TypeAutomatonState}
    (hRelated : TypeCompilationRelation processType state residual)
    (hRecursive : processType.TailRecursive)
    (hTail : processType.TailOccurrences name True) :
    residual.TailOccurrences name True := by
  induction hRelated generalizing name with
  | skip => simp [PactType.TailOccurrences]
  | message_source => exact hTail
  | message_final => simp [PactType.TailOccurrences]
  | cycle_source => exact hTail
  | cycle_final => simp [PactType.TailOccurrences]
  | progress_source => exact hTail
  | progress_final => simp [PactType.TailOccurrences]
  | «variable» => exact hTail
  | recur_source => exact hTail
  | recur_body binder body childResidual childState hChild ih =>
      have hRecursiveFields : body.TailOccurrences binder True ∧
          body.TailRecursive := by
        simpa only [PactType.TailRecursive] using hRecursive
      by_cases hEq : binder = name
      · subst binder
        exact tailOccurrences_true_of_false name _
          (PactType.tailOccurrences_false_replaceVar_self_recur name body
            childResidual)
      · have hBodyTarget : body.TailOccurrences name True := by
          simpa only [PactType.TailOccurrences, if_neg hEq] using hTail
        have hChildTarget := ih name hRecursiveFields.2 hBodyTarget
        have hChildBinder := ih binder hRecursiveFields.2 hRecursiveFields.1
        exact tailOccurrences_true_replaceVar_of_tail name binder
          (.recur binder body) hTail childResidual hChildTarget hChildBinder
  | choice_source => exact hTail
  | choice_left left right childResidual childState hChild ih =>
      have hRecursiveFields : left.TailRecursive ∧ right.TailRecursive := by
        simpa only [PactType.TailRecursive] using hRecursive
      have hTailFields : left.TailOccurrences name True ∧
          right.TailOccurrences name True := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih name hRecursiveFields.1 hTailFields.1
  | choice_right left right childResidual childState hChild ih =>
      have hRecursiveFields : left.TailRecursive ∧ right.TailRecursive := by
        simpa only [PactType.TailRecursive] using hRecursive
      have hTailFields : left.TailOccurrences name True ∧
          right.TailOccurrences name True := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih name hRecursiveFields.2 hTailFields.2
  | fair_source => exact hTail
  | fair_left bid left right childResidual childState hChild ih =>
      have hRecursiveFields : left.TailRecursive ∧ right.TailRecursive := by
        simpa only [PactType.TailRecursive] using hRecursive
      have hTailFields : left.TailOccurrences name True ∧
          right.TailOccurrences name True := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih name hRecursiveFields.1 hTailFields.1
  | fair_right bid left right childResidual childState hChild ih =>
      have hRecursiveFields : left.TailRecursive ∧ right.TailRecursive := by
        simpa only [PactType.TailRecursive] using hRecursive
      have hTailFields : left.TailOccurrences name True ∧
          right.TailOccurrences name True := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih name hRecursiveFields.2 hTailFields.2
  | sequence_left left right childResidual childState hChild ih =>
      have hTailFields : left.TailOccurrences name False ∧
          right.TailOccurrences name True := by
        simpa only [PactType.TailOccurrences] using hTail
      have hChildFalse := compilationRelation_tailOccurrences_false name hChild
        hTailFields.1
      simpa only [PactType.TailOccurrences] using
        And.intro hChildFalse hTailFields.2
  | sequence_right left right childResidual childState hChild ih =>
      have hRecursiveFields : left.TailRecursive ∧ right.TailRecursive := by
        simpa only [PactType.TailRecursive] using hRecursive
      have hTailFields : left.TailOccurrences name False ∧
          right.TailOccurrences name True := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih name hRecursiveFields.2 hTailFields.2
  | parallel left right leftResidual rightResidual interface leftState
      rightState hLeft hRight ihLeft ihRight =>
      have hTailFields : left.TailOccurrences name False ∧
          right.TailOccurrences name False := by
        simpa only [PactType.TailOccurrences] using hTail
      have hLeftFalse := compilationRelation_tailOccurrences_false name hLeft
        hTailFields.1
      have hRightFalse := compilationRelation_tailOccurrences_false name hRight
        hTailFields.2
      simpa only [PactType.TailOccurrences] using
        And.intro hLeftFalse hRightFalse
  | xoffer_source => exact hTail
  | xoffer_else elseType childResidual branches childState hChild ih =>
      have hRecursiveFields : elseType.TailRecursive ∧
          PactType.TailRecursiveBranches branches := by
        simpa only [PactType.TailRecursive] using hRecursive
      have hTailFields : elseType.TailOccurrences name True ∧
          PactType.TailBranchOccurrences name True branches := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih name hRecursiveFields.1 hTailFields.1
  | xoffer_branch elseType branchType childResidual branches action index
      childState hEntry hChild ih =>
      have hRecursiveFields : elseType.TailRecursive ∧
          PactType.TailRecursiveBranches branches := by
        simpa only [PactType.TailRecursive] using hRecursive
      have hTailFields : elseType.TailOccurrences name True ∧
          PactType.TailBranchOccurrences name True branches := by
        simpa only [PactType.TailOccurrences] using hTail
      have hMember := List.mem_of_getElem? hEntry
      exact ih name (tailRecursive_branch_of_mem branches (action, branchType)
          hRecursiveFields.2 hMember)
        (tailBranchOccurrences_mem name True branches (action, branchType)
          hTailFields.2 hMember)
  | offer_source => exact hTail
  | offer_branches elseType childResidual branches selected index childState
      hEntry hChild ih =>
      have hTailFields : elseType.TailOccurrences name True ∧
          PactType.TailBranchOccurrences name False branches := by
        simpa only [PactType.TailOccurrences] using hTail
      have hSelectedFalse := compilationRelation_tailOccurrences_false name
        hChild (tailOccurrences_parallelTypeBranchesSelecting name selected
          branches hTailFields.2)
      exact tailOccurrences_true_of_false name childResidual hSelectedFalse
  | offer_else elseType childResidual branches childState hChild ih =>
      have hRecursiveFields : elseType.TailRecursive ∧
          PactType.TailRecursiveBranches branches := by
        simpa only [PactType.TailRecursive] using hRecursive
      have hTailFields : elseType.TailOccurrences name True ∧
          PactType.TailBranchOccurrences name False branches := by
        simpa only [PactType.TailOccurrences] using hTail
      exact ih name hRecursiveFields.1 hTailFields.1

theorem completionEval_eq_true_witness
    (active : List String) (valuation : String → Bool) :
    ∀ processType : PactType,
      processType.BinderFreshFor active →
      (∀ name, name ∈ active →
        processType.TailOccurrences name True) →
      (∀ name, name ∉ active → valuation name = false) →
      PactType.completionEval valuation processType = true →
      processType.CanCompleteBeforeTock = true ∨
        ∃ name ∈ active, valuation name = true ∧
          PactType.canCompleteBeforeTockSubst name true processType = true := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType active valuation with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.BinderFreshForBranches active branches →
          (∀ name, name ∈ active →
            PactType.TailBranchOccurrences name True branches) →
          (∀ name, name ∉ active → valuation name = false) →
          PactType.branchCompletionEval valuation branches = true →
          PactType.BranchCanCompleteBeforeTock branches = true ∨
            ∃ name ∈ active, valuation name = true ∧
              PactType.branchCanCompleteBeforeTockSubst name true branches =
                true := by
        intro branches hBranchesSize hFresh hTail hSupported
          hComplete
        induction branches with
        | nil =>
            simp [PactType.branchCompletionEval] at hComplete
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hFreshFields : branchType.BinderFreshFor active ∧
                PactType.BinderFreshForBranches active rest := by
              simpa only [PactType.BinderFreshForBranches] using hFresh
            have hTailHead : ∀ name, name ∈ active →
                branchType.TailOccurrences name True := by
              intro name hName
              have hFields := hTail name hName
              simp only [PactType.TailBranchOccurrences] at hFields
              exact hFields.1
            have hTailRest : ∀ name, name ∈ active →
                PactType.TailBranchOccurrences name True rest := by
              intro name hName
              have hFields := hTail name hName
              simp only [PactType.TailBranchOccurrences] at hFields
              exact hFields.2
            simp only [PactType.branchCompletionEval, Bool.or_eq_true]
              at hComplete
            rcases hComplete with hHead | hRest
            · rcases ih (sizeOf branchType) hBranchSize active valuation
                branchType rfl hFreshFields.1 hTailHead
                  hSupported hHead with hPlain | hWitness
              · exact Or.inl (by
                  simp [PactType.BranchCanCompleteBeforeTock, hPlain])
              · rcases hWitness with ⟨name, hName, hValue, hSubst⟩
                exact Or.inr ⟨name, hName, hValue, by
                  simp [PactType.branchCanCompleteBeforeTockSubst, hSubst]⟩
            · rcases restIH hRestSize hFreshFields.2
                hTailRest hRest with hPlain | hWitness
              · exact Or.inl (by
                  simp [PactType.BranchCanCompleteBeforeTock, hPlain])
              · rcases hWitness with ⟨name, hName, hValue, hSubst⟩
                exact Or.inr ⟨name, hName, hValue, by
                  simp [PactType.branchCanCompleteBeforeTockSubst, hSubst]⟩
      intro hFresh hTail hSupported hComplete
      cases processType with
      | message msg dir =>
          exact Or.inl (by simp [PactType.CanCompleteBeforeTock])
      | progress pid =>
          exact Or.inl (by simp [PactType.CanCompleteBeforeTock])
      | skip =>
          exact Or.inl (by simp [PactType.CanCompleteBeforeTock])
      | tock =>
          simp [PactType.completionEval] at hComplete
      | var other =>
          have hValue : valuation other = true := by
            simpa only [PactType.completionEval] using hComplete
          have hMember : other ∈ active := by
            by_contra hNotMember
            rw [hSupported other hNotMember] at hValue
            contradiction
          exact Or.inr ⟨other, hMember, hValue, by
            simp [PactType.canCompleteBeforeTockSubst]⟩
      | recur binder body =>
          have hBodySize : sizeOf body < n := by
            rw [← hSize]; simp_wf; omega
          have hFreshFields : binder ∉ active ∧
              body.BinderFreshFor active := by
            simpa only [PactType.BinderFreshFor] using hFresh
          let nestedValuation := Function.update valuation binder false
          have hNestedSupported : ∀ name, name ∉ active →
              nestedValuation name = false := by
            intro name hName
            by_cases hEq : name = binder
            · subst name; simp [nestedValuation]
            · simpa [nestedValuation, Function.update, hEq] using
                hSupported name hName
          have hBodyTail : ∀ name, name ∈ active →
              body.TailOccurrences name True := by
            intro name hName
            have hNe : binder ≠ name := by
              intro hEq; subst name; exact hFreshFields.1 hName
            simpa only [PactType.TailOccurrences, if_neg hNe] using
              hTail name hName
          have hBodyComplete : PactType.completionEval nestedValuation body =
              true := by
            simpa only [PactType.completionEval] using hComplete
          rcases ih (sizeOf body) hBodySize active nestedValuation body rfl
              hFreshFields.2 hBodyTail hNestedSupported
                hBodyComplete with hPlain | hWitness
          · exact Or.inl (by
              simpa only [PactType.CanCompleteBeforeTock] using hPlain)
          · rcases hWitness with ⟨name, hName, hValue, hSubst⟩
            have hNe : name ≠ binder := by
              intro hEq; subst name; exact hFreshFields.1 hName
            have hOuterValue : valuation name = true := by
              simpa [nestedValuation, Function.update, hNe] using hValue
            exact Or.inr ⟨name, hName, hOuterValue, by
              simpa [PactType.canCompleteBeforeTockSubst, hNe] using hSubst⟩
      | choice left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          have hFreshFields : left.BinderFreshFor active ∧
              right.BinderFreshFor active := by
            simpa only [PactType.BinderFreshFor] using hFresh
          have hTailLeft : ∀ name, name ∈ active →
              left.TailOccurrences name True := by
            intro name hName
            have hPair := hTail name hName
            simp only [PactType.TailOccurrences] at hPair
            exact hPair.1
          have hTailRight : ∀ name, name ∈ active →
              right.TailOccurrences name True := by
            intro name hName
            have hPair := hTail name hName
            simp only [PactType.TailOccurrences] at hPair
            exact hPair.2
          simp only [PactType.completionEval, Bool.or_eq_true] at hComplete
          rcases hComplete with hLeft | hRight
          · rcases ih (sizeOf left) hLeftSize active valuation left rfl
                hFreshFields.1 hTailLeft hSupported hLeft
                with hPlain | ⟨name, hName, hValue, hSubst⟩
            · exact Or.inl (by simp [PactType.CanCompleteBeforeTock, hPlain])
            · exact Or.inr ⟨name, hName, hValue, by
                simp [PactType.canCompleteBeforeTockSubst, hSubst]⟩
          · rcases ih (sizeOf right) hRightSize active valuation right rfl
                hFreshFields.2 hTailRight hSupported hRight
                with hPlain | ⟨name, hName, hValue, hSubst⟩
            · exact Or.inl (by simp [PactType.CanCompleteBeforeTock, hPlain])
            · exact Or.inr ⟨name, hName, hValue, by
                simp [PactType.canCompleteBeforeTockSubst, hSubst]⟩
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          have hFreshFields : left.BinderFreshFor active ∧
              right.BinderFreshFor active := by
            simpa only [PactType.BinderFreshFor] using hFresh
          have hTailLeft : ∀ name, name ∈ active →
              left.TailOccurrences name True := by
            intro name hName
            have hPair := hTail name hName
            simp only [PactType.TailOccurrences] at hPair
            exact hPair.1
          have hTailRight : ∀ name, name ∈ active →
              right.TailOccurrences name True := by
            intro name hName
            have hPair := hTail name hName
            simp only [PactType.TailOccurrences] at hPair
            exact hPair.2
          simp only [PactType.completionEval, Bool.or_eq_true] at hComplete
          rcases hComplete with hLeft | hRight
          · rcases ih (sizeOf left) hLeftSize active valuation left rfl
                hFreshFields.1 hTailLeft hSupported hLeft
                with hPlain | ⟨name, hName, hValue, hSubst⟩
            · exact Or.inl (by simp [PactType.CanCompleteBeforeTock, hPlain])
            · exact Or.inr ⟨name, hName, hValue, by
                simp [PactType.canCompleteBeforeTockSubst, hSubst]⟩
          · rcases ih (sizeOf right) hRightSize active valuation right rfl
                hFreshFields.2 hTailRight hSupported hRight
                with hPlain | ⟨name, hName, hValue, hSubst⟩
            · exact Or.inl (by simp [PactType.CanCompleteBeforeTock, hPlain])
            · exact Or.inr ⟨name, hName, hValue, by
                simp [PactType.canCompleteBeforeTockSubst, hSubst]⟩
      | seq left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          have hFreshFields : left.BinderFreshFor active ∧
              right.BinderFreshFor active := by
            simpa only [PactType.BinderFreshFor] using hFresh
          have hTailLeftFalse : ∀ name, valuation name = true →
              left.TailOccurrences name False := by
            intro name hValue
            have hName : name ∈ active := by
              by_contra hNotMember
              rw [hSupported name hNotMember] at hValue
              contradiction
            have hPair := hTail name hName
            simp only [PactType.TailOccurrences] at hPair
            exact hPair.1
          have hTailRight : ∀ name, name ∈ active →
              right.TailOccurrences name True := by
            intro name hName
            have hPair := hTail name hName
            simp only [PactType.TailOccurrences] at hPair
            exact hPair.2
          have hCompleteFields : PactType.completionEval valuation left = true ∧
              PactType.completionEval valuation right = true := by
            simpa only [PactType.completionEval, Bool.and_eq_true] using hComplete
          have hLeftPlain : left.CanCompleteBeforeTock = true := by
            rw [← completionEval_eq_canCompleteBeforeTock_of_tailFalse
              valuation left hTailLeftFalse]
            exact hCompleteFields.1
          rcases ih (sizeOf right) hRightSize active valuation right rfl
              hFreshFields.2 hTailRight hSupported
                hCompleteFields.2 with hPlain | ⟨name, hName, hValue, hSubst⟩
          · exact Or.inl (by
              simp [PactType.CanCompleteBeforeTock, hLeftPlain, hPlain])
          · have hTailPair := hTail name hName
            simp only [PactType.TailOccurrences] at hTailPair
            have hLeftTail := hTailPair.1
            have hLeftSubst :=
              PactType.canCompleteBeforeTockSubst_eq_of_tailOccurrences_false
                name true left hLeftTail
            exact Or.inr ⟨name, hName, hValue, by
              simp [PactType.canCompleteBeforeTockSubst, hLeftSubst,
                hLeftPlain, hSubst]⟩
      | par left right interface =>
          have hCompleteFields : PactType.completionEval valuation left = true ∧
              PactType.completionEval valuation right = true := by
            simpa only [PactType.completionEval, Bool.and_eq_true] using hComplete
          have hLeftTail : ∀ name, valuation name = true →
              left.TailOccurrences name False := by
            intro name hValue
            have hName : name ∈ active := by
              by_contra hNotMember
              rw [hSupported name hNotMember] at hValue
              contradiction
            have hPair := hTail name hName
            simp only [PactType.TailOccurrences] at hPair
            exact hPair.1
          have hRightTail : ∀ name, valuation name = true →
              right.TailOccurrences name False := by
            intro name hValue
            have hName : name ∈ active := by
              by_contra hNotMember
              rw [hSupported name hNotMember] at hValue
              contradiction
            have hPair := hTail name hName
            simp only [PactType.TailOccurrences] at hPair
            exact hPair.2
          have hLeftPlain : left.CanCompleteBeforeTock = true := by
            rw [← completionEval_eq_canCompleteBeforeTock_of_tailFalse
              valuation left hLeftTail]
            exact hCompleteFields.1
          have hRightPlain : right.CanCompleteBeforeTock = true := by
            rw [← completionEval_eq_canCompleteBeforeTock_of_tailFalse
              valuation right hRightTail]
            exact hCompleteFields.2
          exact Or.inl (by
            simp [PactType.CanCompleteBeforeTock, hLeftPlain, hRightPlain])
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFreshFields : elseType.BinderFreshFor active ∧
              PactType.BinderFreshForBranches active branches := by
            simpa only [PactType.BinderFreshFor] using hFresh
          have hTailElse : ∀ name, name ∈ active →
              elseType.TailOccurrences name True := by
            intro name hName
            have hPair := hTail name hName
            simp only [PactType.TailOccurrences] at hPair
            exact hPair.1
          have hTailBranches : ∀ name, name ∈ active →
              PactType.TailBranchOccurrences name True branches := by
            intro name hName
            have hPair := hTail name hName
            simp only [PactType.TailOccurrences] at hPair
            exact hPair.2
          simp only [PactType.completionEval, Bool.or_eq_true] at hComplete
          rcases hComplete with hElse | hBranch
          · rcases ih (sizeOf elseType) hElseSize active valuation elseType rfl
                hFreshFields.1 hTailElse hSupported hElse
                with hPlain | ⟨name, hName, hValue, hSubst⟩
            · exact Or.inl (by simp [PactType.CanCompleteBeforeTock, hPlain])
            · exact Or.inr ⟨name, hName, hValue, by
                simp [PactType.canCompleteBeforeTockSubst, hSubst]⟩
          · rcases hBranches branches hBranchesSize hFreshFields.2
                hTailBranches hSupported hBranch with
                hPlain | ⟨name, hName, hValue, hSubst⟩
            · exact Or.inl (by simp [PactType.CanCompleteBeforeTock, hPlain])
            · exact Or.inr ⟨name, hName, hValue, by
                simp [PactType.canCompleteBeforeTockSubst, hSubst]⟩
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFreshFields : elseType.BinderFreshFor active ∧
              PactType.BinderFreshForBranches active branches := by
            simpa only [PactType.BinderFreshFor] using hFresh
          have hTailElse : ∀ name, name ∈ active →
              elseType.TailOccurrences name True := by
            intro name hName
            have hPair := hTail name hName
            simp only [PactType.TailOccurrences] at hPair
            exact hPair.1
          have hTailBranchesFalse : ∀ name, valuation name = true →
              PactType.TailBranchOccurrences name False branches := by
            intro name hValue
            have hName : name ∈ active := by
              by_contra hNotMember
              rw [hSupported name hNotMember] at hValue
              contradiction
            have hPair := hTail name hName
            simp only [PactType.TailOccurrences] at hPair
            exact hPair.2
          simp only [PactType.completionEval, Bool.or_eq_true] at hComplete
          rcases hComplete with hElse | hBranch
          · rcases ih (sizeOf elseType) hElseSize active valuation elseType rfl
                hFreshFields.1 hTailElse hSupported hElse
                with hPlain | ⟨name, hName, hValue, hSubst⟩
            · exact Or.inl (by simp [PactType.CanCompleteBeforeTock, hPlain])
            · exact Or.inr ⟨name, hName, hValue, by
                simp [PactType.canCompleteBeforeTockSubst, hSubst]⟩
          · have hBranchPlain :
                PactType.BranchCanCompleteBeforeTock branches = true := by
              rw [←
                branchCompletionEval_eq_branchCanCompleteBeforeTock_of_tailFalse
                  valuation branches hTailBranchesFalse]
              exact hBranch
            exact Or.inl (by
              simp [PactType.CanCompleteBeforeTock, hBranchPlain])

end

end Pact
