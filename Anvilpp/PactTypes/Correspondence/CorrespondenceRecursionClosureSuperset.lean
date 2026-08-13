import Anvilpp.PactTypes.Correspondence.CorrespondenceRecursionClosureLift

/-!
# recursionBodyCompletingClosure_superset_aux
-/

namespace Pact

noncomputable section


/-- Generic (not fixed to `body`) form of the reverse-closure argument,
quantified over an arbitrary subterm `processType` with its own compiled
fragment and own seed.  This is required because `TypeCompilationRelation`'s
constructors (e.g. `choice_left`) recurse through strictly smaller *type*
arguments, so a `body`-fixed motive cannot serve as an induction target: the
induction hypothesis needed at `choice_left` is a fact about `left`'s own
fragment, not `body`'s.

`hVanilla` is threaded as an explicit parameter (not re-derived via
`compilationCompletingCorrect_of_nestedRecursion`, which would need a forward
reference to `compilationCompletingCorrect_recursion_regular_leaf`, defined
later in this file, for its nested-recursion case): the CALLER supplies
`CompilationCompletingCorrect signature processType`, and at each recursive
step into a strictly smaller child (`left`/`right`/...), the child's own
`CompilationCompletingCorrect` fact is derived directly from the parent's via
the tagged-completing-set argument above, not re-derived from scratch.

Only the atomic and choice/fairChoice cases are proved here; the remaining
constructors are separate, precisely-scoped sorries (see the comment at each
site for exactly what remains). -/
theorem recursionBodyCompletingClosure_superset_aux
    (signature : TypeAlphabet) :
    ∀ (name : String) (value : Bool) (processType : PactType),
      PactType.TailOccurrences name True processType →
      signature.Supports processType →
      PactType.ClockGuarded processType →
      PactType.TailRecursive processType →
      PactType.BinderHygienic [name] processType →
      (∀ child : PactType, sizeOf child < sizeOf processType →
        signature.Supports child → child.ClockGuarded → child.TailRecursive →
          child.BinderHygienic [] →
            CompilationCompletingCorrect signature child) →
      CompilationCompletingCorrect signature processType →
      ∀ state residual,
        TypeCompilationRelation processType state residual →
        PactType.canCompleteBeforeTockSubst name value residual = true →
        state ∈ completingBackClosure
          (compileTypeFuel signature (typeCompilationFuel processType) processType)
          ((if value then
              ((compileTypeFuel signature (typeCompilationFuel processType)
                  processType).edges.filter
                fun edge => edge.label = .variable name).image
                  fun edge => edge.source
            else ∅) ∪
            (compileTypeFuel signature (typeCompilationFuel processType)
              processType).completing) := by
  classical
  intro name value processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType name value with
  | _ n ih =>
      intro hTailOccurrences hSupports hGuarded hTailRecursive hHygienic
        hChildrenVanilla hVanilla state residual hRelated hComplete
      -- Plain-completion shortcut: whenever the CURRENT residual already
      -- plainly completes, no graph reasoning is needed at all, regardless
      -- of constructor or depth.
      by_cases hPlain : residual.CanCompleteBeforeTock = true
      · have hInCompleting := (hVanilla state residual hRelated).mpr hPlain
        exact completingBackClosure_superset_seed _ _
          (Finset.mem_union_right _ hInCompleting)
      cases processType with
      | message msg dir =>
          exact absurd hPlain (by cases hRelated <;>
            simp [PactType.CanCompleteBeforeTock])
      | progress pid =>
          exact absurd hPlain (by cases hRelated <;>
            simp [PactType.CanCompleteBeforeTock])
      | skip =>
          exact absurd hPlain (by cases hRelated <;>
            simp [PactType.CanCompleteBeforeTock])
      | tock =>
          cases hRelated with
          | cycle_source =>
              -- residual = .tock, which never subst-completes (unconditionally
              -- false in canCompleteBeforeTockSubst's own .tock clause): the
              -- contradiction is in hComplete, not hPlain.
              exact absurd hComplete (by
                simp [PactType.canCompleteBeforeTockSubst])
          | cycle_final =>
              -- residual = .skip, which always plainly completes: the
              -- contradiction is in hPlain.
              exact absurd (by simp [PactType.CanCompleteBeforeTock] :
                (PactType.skip).CanCompleteBeforeTock = true) hPlain
      | var other =>
          cases hRelated
          have hSelectionEnv : (TypeEnvironment.tock : TypeEnvironment) ∈
              signature.localEnvironments := by
            simp [TypeAlphabet.localEnvironments]
          by_cases hName : name = other
          · have hValueTrue : value = true := by
              simpa [PactType.canCompleteBeforeTockSubst, hName] using hComplete
            have hEdgeMem : (TypeAutomatonState.root : TypeAutomatonState) ∈
                ((compileTypeFuel signature
                    (typeCompilationFuel (PactType.var other))
                    (PactType.var other)).edges.filter
                  fun edge => edge.label = .variable name).image
                    fun edge => edge.source := by
              let marker : PendingAutomatonEdge :=
                { source := TypeAutomatonState.root
                  environment := TypeEnvironment.tock
                  label := .variable other
                  current := ∅
                  future := .explicit ∅
                  target := TypeAutomatonState.final }
              refine Finset.mem_image.mpr ⟨marker, ?_, rfl⟩
              simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                finishAutomatonFragment, Finset.mem_filter, Finset.mem_image]
              exact ⟨⟨TypeEnvironment.tock, hSelectionEnv, by simp [marker]⟩,
                by simp [marker, hName]⟩
            rw [hValueTrue]
            exact completingBackClosure_superset_seed _ _
              (Finset.mem_union_left _ hEdgeMem)
          · exfalso
            simp [PactType.canCompleteBeforeTockSubst, hName,
              Ne.symm hName] at hComplete
      | recur other body' =>
          have hSupportBody : signature.Supports body' := by
            simpa only [TypeAlphabet.Supports] using hSupports
          have hGuardFields : body'.GuardedOccurrences other False ∧
              body'.ClockGuarded := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hGuardBody : body'.ClockGuarded := hGuardFields.2
          have hRecursiveFields : body'.TailOccurrences other True ∧
              body'.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTailRecursive
          have hHygienicFields : other ∉ [name] ∧
              body'.BinderHygienic (other :: [name]) := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hDistinct : name ≠ other := by
            intro hEq
            subst other
            exact hHygienicFields.1 (by simp)
          have hTailOuter : body'.TailOccurrences name True := by
            simpa only [PactType.TailOccurrences, if_neg hDistinct.symm]
              using hTailOccurrences
          have hBodySize : sizeOf body' < n := by
            rw [← hSize]
            simp_wf
            omega
          have hHygienicOuter : body'.BinderHygienic [name] :=
            PactType.binderHygienic_mono
              (by
                intro variableName hMember
                exact List.mem_cons_of_mem other hMember)
              body' hHygienicFields.2
          have hHygienicInner : body'.BinderHygienic [other] :=
            PactType.binderHygienic_mono
              (by
                intro variableName hMember
                rcases List.mem_singleton.mp hMember with rfl
                exact List.mem_cons_self)
              body' hHygienicFields.2
          have hHygienicEmpty : body'.BinderHygienic [] :=
            PactType.binderHygienic_mono
              (by intro variableName hMember; simp at hMember)
              body' hHygienicFields.2
          have hVanillaBody : CompilationCompletingCorrect signature body' :=
            hChildrenVanilla body' hBodySize hSupportBody hGuardBody
              hRecursiveFields.2 hHygienicEmpty
          let recursiveType : PactType := .recur other body'
          let childFragment := compileTypeFuel signature
            (typeCompilationFuel body') body'
          let parentFragment := buildRecursionAutomaton signature other
            childFragment
          let outerValuation : String → Bool :=
            Function.update (fun _ => false) name value
          have hOuterSupported : ∀ variableName, variableName ∉ [name] →
              outerValuation variableName = false := by
            intro variableName hNotMember
            have hNe : variableName ≠ name := by
              intro hEq
              subst variableName
              exact hNotMember (by simp)
            simp [outerValuation, Function.update, hNe]
          have hOuterOther : outerValuation other = false :=
            hOuterSupported other (by
              simpa only [List.mem_singleton] using hDistinct.symm)
          have hResetOther : Function.update outerValuation other false =
              outerValuation := by
            funext variableName
            by_cases hEq : variableName = other
            · subst variableName
              simp [hOuterOther]
            · simp [Function.update, hEq]
          have hChildCallback : ∀ child : PactType,
              sizeOf child < sizeOf body' →
              signature.Supports child → child.ClockGuarded →
              child.TailRecursive → child.BinderHygienic [] →
              CompilationCompletingCorrect signature child := by
            intro child hChildSize
            exact hChildrenVanilla child (lt_trans hChildSize hBodySize)
          have hOuterClosure : ∀ (q : TypeAutomatonState)
              (r : PactType),
              TypeCompilationRelation body' q r →
              PactType.canCompleteBeforeTockSubst name value r = true →
              q ∈ completingBackClosure childFragment
                ((if value then
                    (childFragment.edges.filter
                      fun edge => edge.label = .variable name).image
                        fun edge => edge.source
                  else ∅) ∪ childFragment.completing) := by
            intro q r hChildRelated hChildComplete
            exact ih (sizeOf body') hBodySize (name := name) (value := value)
              (processType := body') rfl hTailOuter hSupportBody hGuardBody
                hRecursiveFields.2 hHygienicOuter hChildCallback hVanillaBody
                  q r hChildRelated hChildComplete
          have hInnerClosure : ∀ (q : TypeAutomatonState)
              (r : PactType),
              TypeCompilationRelation body' q r →
              PactType.canCompleteBeforeTockSubst other true r = true →
              q ∈ completingBackClosure childFragment
                ((childFragment.edges.filter
                    fun edge => edge.label = .variable other).image
                      (fun edge => edge.source) ∪ childFragment.completing) := by
            intro q r hChildRelated hChildComplete
            have hResult := ih (sizeOf body') hBodySize (name := other)
              (value := true) (processType := body') rfl
                hRecursiveFields.1 hSupportBody hGuardBody hRecursiveFields.2
                  hHygienicInner hChildCallback hVanillaBody q r
                    hChildRelated hChildComplete
            simpa [childFragment] using hResult
          have hNoInnerSource : ∀ edge ∈ childFragment.edges,
              edge.label = .variable other →
              edge.source ∉ completingBackClosure childFragment
                ((if value then
                    (childFragment.edges.filter
                      fun e => e.label = .variable name).image
                        fun e => e.source
                  else ∅) ∪ childFragment.completing) := by
            intro edge hEdge hLabel hSource
            obtain ⟨sourceResidual, hSourceRelated, hSourceComplete⟩ :=
              parametricCompletingBackClosure_sound signature name value body'
                hTailOuter hRecursiveFields.2 hHygienicOuter edge.source
                  (by simpa [childFragment] using hSource)
            have hMarker :=
              (compileTypeFuel_variableEdge_source_var signature other
                (typeCompilationFuel body') body' True
                (typeCompilationFuel_sufficient body') hRecursiveFields.1 edge
                  (by simpa [childFragment] using hEdge) hLabel).2
            have hResidual : sourceResidual = .var other :=
              TypeCompilationRelation.residual_unique hSourceRelated hMarker
            subst sourceResidual
            simp [PactType.canCompleteBeforeTockSubst, hDistinct]
              at hSourceComplete
          have hLiftOuter : ∀ {q : TypeAutomatonState},
              q ∈ completingBackClosure childFragment
                ((if value then
                    (childFragment.edges.filter
                      fun edge => edge.label = .variable name).image
                        fun edge => edge.source
                  else ∅) ∪ childFragment.completing) →
              childState 0 q ∈ completingBackClosure parentFragment
                ((if value then
                    (parentFragment.edges.filter
                      fun edge => edge.label = .variable name).image
                        fun edge => edge.source
                  else ∅) ∪ parentFragment.completing) := by
            intro q hMember
            exact completingBackClosure_lift_recursion_nonmatching signature
              name other value childFragment hDistinct hNoInnerSource hMember
          have hCompile : compileTypeFuel signature
              (typeCompilationFuel (.recur other body')) (.recur other body') =
              parentFragment := by
            simp [parentFragment, childFragment, typeCompilationFuel,
              Nat.one_add, compileTypeFuel]
          rw [hCompile]
          cases hRelated with
          | recur_source =>
              have hRecursiveEval : PactType.completionEval outerValuation
                  recursiveType = true := by
                rw [PactType.completionEval_singleton_eq_canCompleteBeforeTockSubst]
                simpa [outerValuation, recursiveType] using hComplete
              have hBodyEval : PactType.completionEval outerValuation body' =
                  true := by
                simp only [recursiveType, PactType.completionEval]
                  at hRecursiveEval
                rwa [hResetOther] at hRecursiveEval
              have hBodyComplete :
                  PactType.canCompleteBeforeTockSubst name value body' = true := by
                rw [←
                  PactType.completionEval_singleton_eq_canCompleteBeforeTockSubst]
                simpa [outerValuation] using hBodyEval
              have hInitialRelated : TypeCompilationRelation body'
                  childFragment.initial body' := by
                simpa [childFragment] using
                  compileTypeFuel_initial_relation signature
                    (typeCompilationFuel body') body'
                      (typeCompilationFuel_sufficient body')
              have hTaggedInitial := hLiftOuter
                (hOuterClosure childFragment.initial body' hInitialRelated
                  hBodyComplete)
              let header : PendingAutomatonEdge :=
                { source := TypeAutomatonState.root
                  environment := TypeEnvironment.tock
                  label := .visible TypeLabel.silent
                  current := ∅
                  future := .at (childState 0 childFragment.initial) ∅
                  target := childState 0 childFragment.initial }
              apply completingBackClosure_mem_of_nonClockEdge parentFragment _
                header
              · simp [parentFragment, childFragment,
                  buildRecursionAutomaton, finishAutomatonFragment, header,
                  TypeAlphabet.localEnvironments]
              · simp [header, AutomatonConstructionLabel.semantic,
                  TypeLabel.silent]
              · simpa [header] using hTaggedInitial
          | recur_body _ _ childResidual childQ hChildRelated =>
              have hChildFresh : childResidual.BinderFreshFor
                  (other :: [name]) :=
                compilationRelation_binderFreshFor hChildRelated
                  hHygienicFields.2
              have hChildTailOuter :
                  childResidual.TailOccurrences name True :=
                compilationRelation_tailOccurrences_true name hChildRelated
                  hRecursiveFields.2 hTailOuter
              have hChildTailInner :
                  childResidual.TailOccurrences other True :=
                compilationRelation_tailOccurrences_true other hChildRelated
                  hRecursiveFields.2 hRecursiveFields.1
              let innerValue := PactType.completionEval outerValuation
                recursiveType
              let extendedValuation := Function.update outerValuation other
                innerValue
              have hExtendedSupported : ∀ variableName,
                  variableName ∉ other :: [name] →
                    extendedValuation variableName = false := by
                intro variableName hNotMember
                have hNeOther : variableName ≠ other := by
                  intro hEq
                  subst variableName
                  exact hNotMember (by simp)
                have hNotName : variableName ∉ [name] := by
                  intro hMember
                  exact hNotMember (List.mem_cons_of_mem other hMember)
                simp [extendedValuation, Function.update, hNeOther,
                  hOuterSupported variableName hNotName]
              have hOuterEval : PactType.completionEval outerValuation
                  (childResidual.replaceVar other recursiveType) = true := by
                rw [PactType.completionEval_singleton_eq_canCompleteBeforeTockSubst]
                simpa [outerValuation, recursiveType] using hComplete
              have hChildEval : PactType.completionEval extendedValuation
                  childResidual = true := by
                rw [PactType.completionEval_replaceVar_of_hygienic [name]
                  outerValuation other recursiveType hOuterSupported
                    childResidual hChildFresh] at hOuterEval
                simpa [extendedValuation, innerValue] using hOuterEval
              have hChildTails : ∀ variableName,
                  variableName ∈ other :: [name] →
                    childResidual.TailOccurrences variableName True := by
                intro variableName hMember
                simp only [List.mem_cons, List.mem_singleton,
                  List.not_mem_nil, or_false] at hMember
                rcases hMember with rfl | rfl
                · exact hChildTailInner
                · exact hChildTailOuter
              rcases completionEval_eq_true_witness (other :: [name])
                  extendedValuation childResidual hChildFresh hChildTails
                    hExtendedSupported hChildEval with hChildPlain |
                    ⟨witness, hWitnessMember, hWitnessValue,
                      hWitnessComplete⟩
              · have hResidualPlain :
                    PactType.CanCompleteBeforeTock
                      (childResidual.replaceVar other recursiveType) = true := by
                    rw [PactType.replaceVar_canCompleteBeforeTock]
                    exact PactType.canCompleteBeforeTock_le_subst other
                      recursiveType.CanCompleteBeforeTock childResidual
                        hChildPlain
                exact absurd hResidualPlain hPlain
              · simp only [List.mem_cons, List.mem_singleton,
                    List.not_mem_nil, or_false]
                  at hWitnessMember
                rcases hWitnessMember with hWitnessOther | hWitnessName
                · subst witness
                  have hInnerMember := hInnerClosure childQ childResidual
                      hChildRelated hWitnessComplete
                  have hInnerValueTrue : innerValue = true := by
                    simpa [extendedValuation] using hWitnessValue
                  have hRecursiveEval : PactType.completionEval
                      outerValuation recursiveType = true := by
                    simpa [innerValue] using hInnerValueTrue
                  have hBodyEval : PactType.completionEval outerValuation
                      body' = true := by
                    simp only [recursiveType, PactType.completionEval]
                      at hRecursiveEval
                    rwa [hResetOther] at hRecursiveEval
                  have hBodyComplete :
                      PactType.canCompleteBeforeTockSubst name value body' =
                        true := by
                    rw [←
                      PactType.completionEval_singleton_eq_canCompleteBeforeTockSubst]
                    simpa [outerValuation] using hBodyEval
                  have hInitialRelated : TypeCompilationRelation body'
                      childFragment.initial body' := by
                    simpa [childFragment] using
                      compileTypeFuel_initial_relation signature
                        (typeCompilationFuel body') body'
                          (typeCompilationFuel_sufficient body')
                  have hTaggedInitial := hLiftOuter
                    (hOuterClosure childFragment.initial body'
                      hInitialRelated hBodyComplete)
                  exact completingBackClosure_lift_recursion_matching
                    signature name other value childFragment hTaggedInitial
                      hInnerMember
                · subst witness
                  have hValueTrue : value = true := by
                    simpa [extendedValuation, outerValuation,
                      Function.update, hDistinct] using hWitnessValue
                  subst value
                  exact hLiftOuter
                    (hOuterClosure childQ childResidual hChildRelated
                      hWitnessComplete)
      | choice left right =>
          have hSupportFields : signature.Supports left ∧
              signature.Supports right := by
            simpa only [TypeAlphabet.Supports] using hSupports
          have hGuardFields : left.ClockGuarded ∧ right.ClockGuarded := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hRecursiveFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTailRecursive
          have hHygienicFields : left.BinderHygienic [name] ∧
              right.BinderHygienic [name] := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hTailOccFields : PactType.TailOccurrences name True left ∧
              PactType.TailOccurrences name True right := by
            simpa only [PactType.TailOccurrences] using hTailOccurrences
          have hLeftFuelSufficient : TypeCompilationFuelSufficient left
              (max (typeCompilationFuel left) (typeCompilationFuel right)) :=
            le_max_left _ _
          have hRightFuelSufficient : TypeCompilationFuelSufficient right
              (max (typeCompilationFuel left) (typeCompilationFuel right)) :=
            le_max_right _ _
          have hLeftFuelEq : compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right))
                left =
              compileTypeFuel signature (typeCompilationFuel left) left :=
            compileTypeFuel_eq_of_sufficient signature left
              hLeftFuelSufficient (typeCompilationFuel_sufficient left)
          have hRightFuelEq : compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right))
                right =
              compileTypeFuel signature (typeCompilationFuel right) right :=
            compileTypeFuel_eq_of_sufficient signature right
              hRightFuelSufficient (typeCompilationFuel_sufficient right)
          have hVanillaLeft : CompilationCompletingCorrect signature left := by
            intro s r hr
            constructor
            · intro hMem
              have hMemOuter : (childState 0 s : TypeAutomatonState) ∈
                  (compileTypeFuel signature (typeCompilationFuel
                    (.choice left right)) (.choice left right)).completing := by
                simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                  buildChoiceAutomaton, finishAutomatonFragment,
                  Finset.mem_union, hLeftFuelEq]
                exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨s, hMem, rfl⟩))
              exact (hVanilla (childState 0 s) r
                (TypeCompilationRelation.choice_left left right r s hr)).mp
                hMemOuter
            · intro hCanComplete
              have hMemOuter := (hVanilla (childState 0 s) r
                (TypeCompilationRelation.choice_left left right r s hr)).mpr
                hCanComplete
              simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                buildChoiceAutomaton, finishAutomatonFragment,
                Finset.mem_union, childCompleting, hLeftFuelEq,
                hRightFuelEq] at hMemOuter
              rcases hMemOuter with (hRoot | hLeftMem) | hRightMem
              · exfalso; split at hRoot <;> simp [childState] at hRoot
              · obtain ⟨w, hw, hEq⟩ := Finset.mem_image.mp hLeftMem
                have hws : w = s := by simpa [childState] using hEq
                subst hws; exact hw
              · exfalso
                obtain ⟨w, _, hEq⟩ := Finset.mem_image.mp hRightMem
                simp [childState] at hEq
          have hVanillaRight : CompilationCompletingCorrect signature right := by
            intro s r hr
            constructor
            · intro hMem
              have hMemOuter : (childState 1 s : TypeAutomatonState) ∈
                  (compileTypeFuel signature (typeCompilationFuel
                    (.choice left right)) (.choice left right)).completing := by
                simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                  buildChoiceAutomaton, finishAutomatonFragment,
                  Finset.mem_union, hRightFuelEq]
                exact Or.inr (Finset.mem_image.mpr ⟨s, hMem, rfl⟩)
              exact (hVanilla (childState 1 s) r
                (TypeCompilationRelation.choice_right left right r s hr)).mp
                hMemOuter
            · intro hCanComplete
              have hMemOuter := (hVanilla (childState 1 s) r
                (TypeCompilationRelation.choice_right left right r s hr)).mpr
                hCanComplete
              simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                buildChoiceAutomaton, finishAutomatonFragment,
                Finset.mem_union, childCompleting, hLeftFuelEq,
                hRightFuelEq] at hMemOuter
              rcases hMemOuter with (hRoot | hLeftMem) | hRightMem
              · exfalso; split at hRoot <;> simp [childState] at hRoot
              · exfalso
                obtain ⟨w, _, hEq⟩ := Finset.mem_image.mp hLeftMem
                simp [childState] at hEq
              · obtain ⟨w, hw, hEq⟩ := Finset.mem_image.mp hRightMem
                have hws : w = s := by simpa [childState] using hEq
                subst hws; exact hw
          have hLeftEdgesSubset : ∀ source label target,
              (∃ edge ∈ (taggedFragment 0 (compileTypeFuel signature
                  (typeCompilationFuel left) left)).edges,
                edge.source = source ∧ edge.label = label ∧
                  edge.target = target) →
              (∃ edge ∈ (compileTypeFuel signature (typeCompilationFuel
                  (.choice left right)) (.choice left right)).edges,
                edge.source = source ∧ edge.label = label ∧
                  edge.target = target) := by
            rintro source label target ⟨edge, hEdge, hSourceEq, hLabelEq, hTargetEq⟩
            simp only [taggedFragment, Finset.mem_image] at hEdge
            obtain ⟨original, hOriginal, rfl⟩ := hEdge
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
              buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
              hLeftFuelEq]
            exact ⟨childPendingEdge 0 original,
              Or.inl (Or.inl (Finset.mem_image.mpr ⟨original, hOriginal, rfl⟩)),
              hSourceEq, hLabelEq, hTargetEq⟩
          have hRightEdgesSubset : ∀ source label target,
              (∃ edge ∈ (taggedFragment 1 (compileTypeFuel signature
                  (typeCompilationFuel right) right)).edges,
                edge.source = source ∧ edge.label = label ∧
                  edge.target = target) →
              (∃ edge ∈ (compileTypeFuel signature (typeCompilationFuel
                  (.choice left right)) (.choice left right)).edges,
                edge.source = source ∧ edge.label = label ∧
                  edge.target = target) := by
            rintro source label target ⟨edge, hEdge, hSourceEq, hLabelEq, hTargetEq⟩
            simp only [taggedFragment, Finset.mem_image] at hEdge
            obtain ⟨original, hOriginal, rfl⟩ := hEdge
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
              buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
              hRightFuelEq]
            exact ⟨childPendingEdge 1 original,
              Or.inl (Or.inr (Finset.mem_image.mpr ⟨original, hOriginal, rfl⟩)),
              hSourceEq, hLabelEq, hTargetEq⟩
          have hLeftSeedSubset : ((if value then
                ((compileTypeFuel signature (typeCompilationFuel left)
                    left).edges.filter fun edge => edge.label = .variable name).image
                  fun edge => edge.source
              else ∅) ∪
              (compileTypeFuel signature (typeCompilationFuel left)
                left).completing).image (childState 0) ⊆
              (if value then
                  ((compileTypeFuel signature (typeCompilationFuel
                      (.choice left right)) (.choice left right)).edges.filter
                    fun edge => edge.label = .variable name).image
                      fun edge => edge.source
                else ∅) ∪
                (compileTypeFuel signature (typeCompilationFuel
                  (.choice left right)) (.choice left right)).completing := by
            intro t ht
            simp only [Finset.mem_image] at ht
            obtain ⟨u, hu, rfl⟩ := ht
            rcases Finset.mem_union.mp hu with hVar | hCompleting
            · apply Finset.mem_union_left
              by_cases hv : value
              · simp only [hv, if_true] at hVar ⊢
                simp only [Finset.mem_image, Finset.mem_filter] at hVar ⊢
                obtain ⟨edge, ⟨hEdge, hLabel⟩, hSource⟩ := hVar
                refine ⟨childPendingEdge 0 edge, ⟨?_, ?_⟩, ?_⟩
                · simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                    buildChoiceAutomaton, finishAutomatonFragment,
                    Finset.mem_union, hLeftFuelEq]
                  exact Or.inl (Or.inl (Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩))
                · simpa [childPendingEdge] using hLabel
                · simp [childPendingEdge, ← hSource]
              · simp [hv] at hVar
            · apply Finset.mem_union_right
              simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
                childCompleting, hLeftFuelEq]
              exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨u, hCompleting, rfl⟩))
          have hRightSeedSubset : ((if value then
                ((compileTypeFuel signature (typeCompilationFuel right)
                    right).edges.filter fun edge => edge.label = .variable name).image
                  fun edge => edge.source
              else ∅) ∪
              (compileTypeFuel signature (typeCompilationFuel right)
                right).completing).image (childState 1) ⊆
              (if value then
                  ((compileTypeFuel signature (typeCompilationFuel
                      (.choice left right)) (.choice left right)).edges.filter
                    fun edge => edge.label = .variable name).image
                      fun edge => edge.source
                else ∅) ∪
                (compileTypeFuel signature (typeCompilationFuel
                  (.choice left right)) (.choice left right)).completing := by
            intro t ht
            simp only [Finset.mem_image] at ht
            obtain ⟨u, hu, rfl⟩ := ht
            rcases Finset.mem_union.mp hu with hVar | hCompleting
            · apply Finset.mem_union_left
              by_cases hv : value
              · simp only [hv, if_true] at hVar ⊢
                simp only [Finset.mem_image, Finset.mem_filter] at hVar ⊢
                obtain ⟨edge, ⟨hEdge, hLabel⟩, hSource⟩ := hVar
                refine ⟨childPendingEdge 1 edge, ⟨?_, ?_⟩, ?_⟩
                · simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                    buildChoiceAutomaton, finishAutomatonFragment,
                    Finset.mem_union, hRightFuelEq]
                  exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩))
                · simpa [childPendingEdge] using hLabel
                · simp [childPendingEdge, ← hSource]
              · simp [hv] at hVar
            · apply Finset.mem_union_right
              simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
                childCompleting, hRightFuelEq]
              exact Or.inr (Finset.mem_image.mpr ⟨u, hCompleting, rfl⟩)
          cases hRelated with
          | choice_left _ _ _ innerState hInner =>
              have hLeftMem := ih (sizeOf left) hLeftSize
                (name := name) (value := value) (processType := left) rfl
                hTailOccFields.1 hSupportFields.1 hGuardFields.1
                  hRecursiveFields.1 hHygienicFields.1
                  (fun child hChildSize => hChildrenVanilla child
                    (lt_trans hChildSize hLeftSize)) hVanillaLeft
                innerState residual hInner hComplete
              have hLift1 : childState 0 innerState ∈
                  completingBackClosure
                    (taggedFragment 0 (compileTypeFuel signature
                      (typeCompilationFuel left) left))
                    (((if value then
                        ((compileTypeFuel signature (typeCompilationFuel left)
                            left).edges.filter
                          fun edge => edge.label = .variable name).image
                            fun edge => edge.source
                      else ∅) ∪
                      (compileTypeFuel signature (typeCompilationFuel left)
                        left).completing).image (childState 0)) := by
                rw [completingBackClosure_taggedFragment_image]
                exact Finset.mem_image.mpr ⟨innerState, hLeftMem, rfl⟩
              have hLift2 := completingBackClosure_mono_edges
                (taggedFragment 0 (compileTypeFuel signature
                  (typeCompilationFuel left) left))
                (compileTypeFuel signature (typeCompilationFuel
                  (.choice left right)) (.choice left right))
                hLeftEdgesSubset _ hLift1
              exact completingBackClosure_mono _ hLeftSeedSubset hLift2
          | choice_right _ _ _ innerState hInner =>
              have hRightMem := ih (sizeOf right) hRightSize
                (name := name) (value := value) (processType := right) rfl
                hTailOccFields.2 hSupportFields.2 hGuardFields.2
                  hRecursiveFields.2 hHygienicFields.2
                  (fun child hChildSize => hChildrenVanilla child
                    (lt_trans hChildSize hRightSize)) hVanillaRight
                innerState residual hInner hComplete
              have hLift1 : childState 1 innerState ∈
                  completingBackClosure
                    (taggedFragment 1 (compileTypeFuel signature
                      (typeCompilationFuel right) right))
                    (((if value then
                        ((compileTypeFuel signature (typeCompilationFuel right)
                            right).edges.filter
                          fun edge => edge.label = .variable name).image
                            fun edge => edge.source
                      else ∅) ∪
                      (compileTypeFuel signature (typeCompilationFuel right)
                        right).completing).image (childState 1)) := by
                rw [completingBackClosure_taggedFragment_image]
                exact Finset.mem_image.mpr ⟨innerState, hRightMem, rfl⟩
              have hLift2 := completingBackClosure_mono_edges
                (taggedFragment 1 (compileTypeFuel signature
                  (typeCompilationFuel right) right))
                (compileTypeFuel signature (typeCompilationFuel
                  (.choice left right)) (.choice left right))
                hRightEdgesSubset _ hLift1
              exact completingBackClosure_mono _ hRightSeedSubset hLift2
          | choice_source =>
              -- residual = .choice left right itself; the plain-completion
              -- shortcut already handled ccbtLeft || ccbtRight = true, so
              -- here at least one side has a genuine subst-only discrepancy.
              -- Recurse into that side's OWN initial state, lift, then hop
              -- via the (silent) selection edge.
              have hCompleteFields : PactType.canCompleteBeforeTockSubst name
                    value left = true ∨
                  PactType.canCompleteBeforeTockSubst name value right = true := by
                simpa only [PactType.canCompleteBeforeTockSubst, Bool.or_eq_true]
                  using hComplete
              have hSelectionEnv : (TypeEnvironment.tock : TypeEnvironment) ∈
                  signature.localEnvironments := by
                simp [TypeAlphabet.localEnvironments]
              rcases hCompleteFields with hL | hR
              · have hLeftMem := ih (sizeOf left) hLeftSize
                  (name := name) (value := value) (processType := left) rfl
                  hTailOccFields.1 hSupportFields.1 hGuardFields.1
                  hRecursiveFields.1 hHygienicFields.1
                  (fun child hChildSize => hChildrenVanilla child
                    (lt_trans hChildSize hLeftSize)) hVanillaLeft
                  (compileTypeFuel signature (typeCompilationFuel left)
                    left).initial left
                  (compileTypeFuel_initial_relation signature
                    (typeCompilationFuel left) left
                    (typeCompilationFuel_sufficient left))
                  hL
                have hLift1 : childState 0 (compileTypeFuel signature
                    (typeCompilationFuel left) left).initial ∈
                    completingBackClosure
                      (taggedFragment 0 (compileTypeFuel signature
                        (typeCompilationFuel left) left))
                      (((if value then
                          ((compileTypeFuel signature (typeCompilationFuel left)
                              left).edges.filter
                            fun edge => edge.label = .variable name).image
                              fun edge => edge.source
                        else ∅) ∪
                        (compileTypeFuel signature (typeCompilationFuel left)
                          left).completing).image (childState 0)) := by
                  rw [completingBackClosure_taggedFragment_image]
                  exact Finset.mem_image.mpr ⟨_, hLeftMem, rfl⟩
                have hLift2 := completingBackClosure_mono_edges
                  (taggedFragment 0 (compileTypeFuel signature
                    (typeCompilationFuel left) left))
                  (compileTypeFuel signature (typeCompilationFuel
                    (.choice left right)) (.choice left right))
                  hLeftEdgesSubset _ hLift1
                have hLift3 := completingBackClosure_mono _ hLeftSeedSubset hLift2
                apply completingBackClosure_mem_of_nonClockEdge _ _
                  { source := TypeAutomatonState.root
                    environment := TypeEnvironment.tock
                    label := .visible TypeLabel.silent
                    current := ∅
                    future := .at (childState 0 (compileTypeFuel signature
                      (typeCompilationFuel left) left).initial) ∅
                    target := childState 0 (compileTypeFuel signature
                      (typeCompilationFuel left) left).initial }
                · simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                    buildChoiceAutomaton, finishAutomatonFragment,
                    Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert,
                    Finset.mem_singleton, hLeftFuelEq]
                  exact Or.inr ⟨TypeEnvironment.tock, hSelectionEnv, Or.inl rfl⟩
                · simp [AutomatonConstructionLabel.semantic, TypeLabel.silent]
                · exact hLift3
              · have hRightMem := ih (sizeOf right) hRightSize
                  (name := name) (value := value) (processType := right) rfl
                  hTailOccFields.2 hSupportFields.2 hGuardFields.2
                  hRecursiveFields.2 hHygienicFields.2
                  (fun child hChildSize => hChildrenVanilla child
                    (lt_trans hChildSize hRightSize)) hVanillaRight
                  (compileTypeFuel signature (typeCompilationFuel right)
                    right).initial right
                  (compileTypeFuel_initial_relation signature
                    (typeCompilationFuel right) right
                    (typeCompilationFuel_sufficient right))
                  hR
                have hLift1 : childState 1 (compileTypeFuel signature
                    (typeCompilationFuel right) right).initial ∈
                    completingBackClosure
                      (taggedFragment 1 (compileTypeFuel signature
                        (typeCompilationFuel right) right))
                      (((if value then
                          ((compileTypeFuel signature (typeCompilationFuel right)
                              right).edges.filter
                            fun edge => edge.label = .variable name).image
                              fun edge => edge.source
                        else ∅) ∪
                        (compileTypeFuel signature (typeCompilationFuel right)
                          right).completing).image (childState 1)) := by
                  rw [completingBackClosure_taggedFragment_image]
                  exact Finset.mem_image.mpr ⟨_, hRightMem, rfl⟩
                have hLift2 := completingBackClosure_mono_edges
                  (taggedFragment 1 (compileTypeFuel signature
                    (typeCompilationFuel right) right))
                  (compileTypeFuel signature (typeCompilationFuel
                    (.choice left right)) (.choice left right))
                  hRightEdgesSubset _ hLift1
                have hLift3 := completingBackClosure_mono _ hRightSeedSubset hLift2
                apply completingBackClosure_mem_of_nonClockEdge _ _
                  { source := TypeAutomatonState.root
                    environment := TypeEnvironment.tock
                    label := .visible TypeLabel.silent
                    current := ∅
                    future := .at (childState 1 (compileTypeFuel signature
                      (typeCompilationFuel right) right).initial) ∅
                    target := childState 1 (compileTypeFuel signature
                      (typeCompilationFuel right) right).initial }
                · simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                    buildChoiceAutomaton, finishAutomatonFragment,
                    Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert,
                    Finset.mem_singleton, hRightFuelEq]
                  exact Or.inr ⟨TypeEnvironment.tock, hSelectionEnv, Or.inr rfl⟩
                · simp [AutomatonConstructionLabel.semantic, TypeLabel.silent]
                · exact hLift3
      | fairChoice bid left right =>
          have hSupportFields : signature.Supports left ∧
              signature.Supports right := by
            have hFields : bid ∈ signature.fair ∧
                signature.Supports left ∧ signature.Supports right := by
              simpa only [TypeAlphabet.Supports] using hSupports
            exact hFields.2
          have hGuardFields : left.ClockGuarded ∧ right.ClockGuarded := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hRecursiveFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTailRecursive
          have hHygienicFields : left.BinderHygienic [name] ∧
              right.BinderHygienic [name] := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hTailOccFields : PactType.TailOccurrences name True left ∧
              PactType.TailOccurrences name True right := by
            simpa only [PactType.TailOccurrences] using hTailOccurrences
          have hLeftFuelSufficient : TypeCompilationFuelSufficient left
              (max (typeCompilationFuel left) (typeCompilationFuel right)) :=
            le_max_left _ _
          have hRightFuelSufficient : TypeCompilationFuelSufficient right
              (max (typeCompilationFuel left) (typeCompilationFuel right)) :=
            le_max_right _ _
          have hLeftFuelEq : compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right))
                left =
              compileTypeFuel signature (typeCompilationFuel left) left :=
            compileTypeFuel_eq_of_sufficient signature left
              hLeftFuelSufficient (typeCompilationFuel_sufficient left)
          have hRightFuelEq : compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right))
                right =
              compileTypeFuel signature (typeCompilationFuel right) right :=
            compileTypeFuel_eq_of_sufficient signature right
              hRightFuelSufficient (typeCompilationFuel_sufficient right)
          have hVanillaLeft : CompilationCompletingCorrect signature left := by
            intro s r hr
            constructor
            · intro hMem
              have hMemOuter : (childState 0 s : TypeAutomatonState) ∈
                  (compileTypeFuel signature (typeCompilationFuel
                    (.fairChoice bid left right)) (.fairChoice bid left right)).completing := by
                simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                  buildChoiceAutomaton, finishAutomatonFragment,
                  Finset.mem_union, hLeftFuelEq]
                exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨s, hMem, rfl⟩))
              exact (hVanilla (childState 0 s) r
                (TypeCompilationRelation.fair_left bid left right r s hr)).mp
                hMemOuter
            · intro hCanComplete
              have hMemOuter := (hVanilla (childState 0 s) r
                (TypeCompilationRelation.fair_left bid left right r s hr)).mpr
                hCanComplete
              simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                buildChoiceAutomaton, finishAutomatonFragment,
                Finset.mem_union, childCompleting, hLeftFuelEq,
                hRightFuelEq] at hMemOuter
              rcases hMemOuter with (hRoot | hLeftMem) | hRightMem
              · exfalso; split at hRoot <;> simp [childState] at hRoot
              · obtain ⟨w, hw, hEq⟩ := Finset.mem_image.mp hLeftMem
                have hws : w = s := by simpa [childState] using hEq
                subst hws; exact hw
              · exfalso
                obtain ⟨w, _, hEq⟩ := Finset.mem_image.mp hRightMem
                simp [childState] at hEq
          have hVanillaRight : CompilationCompletingCorrect signature right := by
            intro s r hr
            constructor
            · intro hMem
              have hMemOuter : (childState 1 s : TypeAutomatonState) ∈
                  (compileTypeFuel signature (typeCompilationFuel
                    (.fairChoice bid left right)) (.fairChoice bid left right)).completing := by
                simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                  buildChoiceAutomaton, finishAutomatonFragment,
                  Finset.mem_union, hRightFuelEq]
                exact Or.inr (Finset.mem_image.mpr ⟨s, hMem, rfl⟩)
              exact (hVanilla (childState 1 s) r
                (TypeCompilationRelation.fair_right bid left right r s hr)).mp
                hMemOuter
            · intro hCanComplete
              have hMemOuter := (hVanilla (childState 1 s) r
                (TypeCompilationRelation.fair_right bid left right r s hr)).mpr
                hCanComplete
              simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                buildChoiceAutomaton, finishAutomatonFragment,
                Finset.mem_union, childCompleting, hLeftFuelEq,
                hRightFuelEq] at hMemOuter
              rcases hMemOuter with (hRoot | hLeftMem) | hRightMem
              · exfalso; split at hRoot <;> simp [childState] at hRoot
              · exfalso
                obtain ⟨w, _, hEq⟩ := Finset.mem_image.mp hLeftMem
                simp [childState] at hEq
              · obtain ⟨w, hw, hEq⟩ := Finset.mem_image.mp hRightMem
                have hws : w = s := by simpa [childState] using hEq
                subst hws; exact hw
          have hLeftEdgesSubset : ∀ source label target,
              (∃ edge ∈ (taggedFragment 0 (compileTypeFuel signature
                  (typeCompilationFuel left) left)).edges,
                edge.source = source ∧ edge.label = label ∧
                  edge.target = target) →
              (∃ edge ∈ (compileTypeFuel signature (typeCompilationFuel
                  (.fairChoice bid left right)) (.fairChoice bid left right)).edges,
                edge.source = source ∧ edge.label = label ∧
                  edge.target = target) := by
            rintro source label target ⟨edge, hEdge, hSourceEq, hLabelEq, hTargetEq⟩
            simp only [taggedFragment, Finset.mem_image] at hEdge
            obtain ⟨original, hOriginal, rfl⟩ := hEdge
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
              buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
              hLeftFuelEq]
            exact ⟨childPendingEdge 0 original,
              Or.inl (Or.inl (Finset.mem_image.mpr ⟨original, hOriginal, rfl⟩)),
              hSourceEq, hLabelEq, hTargetEq⟩
          have hRightEdgesSubset : ∀ source label target,
              (∃ edge ∈ (taggedFragment 1 (compileTypeFuel signature
                  (typeCompilationFuel right) right)).edges,
                edge.source = source ∧ edge.label = label ∧
                  edge.target = target) →
              (∃ edge ∈ (compileTypeFuel signature (typeCompilationFuel
                  (.fairChoice bid left right)) (.fairChoice bid left right)).edges,
                edge.source = source ∧ edge.label = label ∧
                  edge.target = target) := by
            rintro source label target ⟨edge, hEdge, hSourceEq, hLabelEq, hTargetEq⟩
            simp only [taggedFragment, Finset.mem_image] at hEdge
            obtain ⟨original, hOriginal, rfl⟩ := hEdge
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
              buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
              hRightFuelEq]
            exact ⟨childPendingEdge 1 original,
              Or.inl (Or.inr (Finset.mem_image.mpr ⟨original, hOriginal, rfl⟩)),
              hSourceEq, hLabelEq, hTargetEq⟩
          have hLeftSeedSubset : ((if value then
                ((compileTypeFuel signature (typeCompilationFuel left)
                    left).edges.filter fun edge => edge.label = .variable name).image
                  fun edge => edge.source
              else ∅) ∪
              (compileTypeFuel signature (typeCompilationFuel left)
                left).completing).image (childState 0) ⊆
              (if value then
                  ((compileTypeFuel signature (typeCompilationFuel
                      (.fairChoice bid left right)) (.fairChoice bid left right)).edges.filter
                    fun edge => edge.label = .variable name).image
                      fun edge => edge.source
                else ∅) ∪
                (compileTypeFuel signature (typeCompilationFuel
                  (.fairChoice bid left right)) (.fairChoice bid left right)).completing := by
            intro t ht
            simp only [Finset.mem_image] at ht
            obtain ⟨u, hu, rfl⟩ := ht
            rcases Finset.mem_union.mp hu with hVar | hCompleting
            · apply Finset.mem_union_left
              by_cases hv : value
              · simp only [hv, if_true] at hVar ⊢
                simp only [Finset.mem_image, Finset.mem_filter] at hVar ⊢
                obtain ⟨edge, ⟨hEdge, hLabel⟩, hSource⟩ := hVar
                refine ⟨childPendingEdge 0 edge, ⟨?_, ?_⟩, ?_⟩
                · simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                    buildChoiceAutomaton, finishAutomatonFragment,
                    Finset.mem_union, hLeftFuelEq]
                  exact Or.inl (Or.inl (Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩))
                · simpa [childPendingEdge] using hLabel
                · simp [childPendingEdge, ← hSource]
              · simp [hv] at hVar
            · apply Finset.mem_union_right
              simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
                childCompleting, hLeftFuelEq]
              exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨u, hCompleting, rfl⟩))
          have hRightSeedSubset : ((if value then
                ((compileTypeFuel signature (typeCompilationFuel right)
                    right).edges.filter fun edge => edge.label = .variable name).image
                  fun edge => edge.source
              else ∅) ∪
              (compileTypeFuel signature (typeCompilationFuel right)
                right).completing).image (childState 1) ⊆
              (if value then
                  ((compileTypeFuel signature (typeCompilationFuel
                      (.fairChoice bid left right)) (.fairChoice bid left right)).edges.filter
                    fun edge => edge.label = .variable name).image
                      fun edge => edge.source
                else ∅) ∪
                (compileTypeFuel signature (typeCompilationFuel
                  (.fairChoice bid left right)) (.fairChoice bid left right)).completing := by
            intro t ht
            simp only [Finset.mem_image] at ht
            obtain ⟨u, hu, rfl⟩ := ht
            rcases Finset.mem_union.mp hu with hVar | hCompleting
            · apply Finset.mem_union_left
              by_cases hv : value
              · simp only [hv, if_true] at hVar ⊢
                simp only [Finset.mem_image, Finset.mem_filter] at hVar ⊢
                obtain ⟨edge, ⟨hEdge, hLabel⟩, hSource⟩ := hVar
                refine ⟨childPendingEdge 1 edge, ⟨?_, ?_⟩, ?_⟩
                · simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                    buildChoiceAutomaton, finishAutomatonFragment,
                    Finset.mem_union, hRightFuelEq]
                  exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩))
                · simpa [childPendingEdge] using hLabel
                · simp [childPendingEdge, ← hSource]
              · simp [hv] at hVar
            · apply Finset.mem_union_right
              simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
                childCompleting, hRightFuelEq]
              exact Or.inr (Finset.mem_image.mpr ⟨u, hCompleting, rfl⟩)
          cases hRelated with
          | fair_left _ _ _ _ innerState hInner =>
              have hLeftMem := ih (sizeOf left) hLeftSize
                (name := name) (value := value) (processType := left) rfl
                hTailOccFields.1 hSupportFields.1 hGuardFields.1
                  hRecursiveFields.1 hHygienicFields.1
                  (fun child hChildSize => hChildrenVanilla child
                    (lt_trans hChildSize hLeftSize)) hVanillaLeft
                innerState residual hInner hComplete
              have hLift1 : childState 0 innerState ∈
                  completingBackClosure
                    (taggedFragment 0 (compileTypeFuel signature
                      (typeCompilationFuel left) left))
                    (((if value then
                        ((compileTypeFuel signature (typeCompilationFuel left)
                            left).edges.filter
                          fun edge => edge.label = .variable name).image
                            fun edge => edge.source
                      else ∅) ∪
                      (compileTypeFuel signature (typeCompilationFuel left)
                        left).completing).image (childState 0)) := by
                rw [completingBackClosure_taggedFragment_image]
                exact Finset.mem_image.mpr ⟨innerState, hLeftMem, rfl⟩
              have hLift2 := completingBackClosure_mono_edges
                (taggedFragment 0 (compileTypeFuel signature
                  (typeCompilationFuel left) left))
                (compileTypeFuel signature (typeCompilationFuel
                  (.fairChoice bid left right)) (.fairChoice bid left right))
                hLeftEdgesSubset _ hLift1
              exact completingBackClosure_mono _ hLeftSeedSubset hLift2
          | fair_right _ _ _ _ innerState hInner =>
              have hRightMem := ih (sizeOf right) hRightSize
                (name := name) (value := value) (processType := right) rfl
                hTailOccFields.2 hSupportFields.2 hGuardFields.2
                  hRecursiveFields.2 hHygienicFields.2
                  (fun child hChildSize => hChildrenVanilla child
                    (lt_trans hChildSize hRightSize)) hVanillaRight
                innerState residual hInner hComplete
              have hLift1 : childState 1 innerState ∈
                  completingBackClosure
                    (taggedFragment 1 (compileTypeFuel signature
                      (typeCompilationFuel right) right))
                    (((if value then
                        ((compileTypeFuel signature (typeCompilationFuel right)
                            right).edges.filter
                          fun edge => edge.label = .variable name).image
                            fun edge => edge.source
                      else ∅) ∪
                      (compileTypeFuel signature (typeCompilationFuel right)
                        right).completing).image (childState 1)) := by
                rw [completingBackClosure_taggedFragment_image]
                exact Finset.mem_image.mpr ⟨innerState, hRightMem, rfl⟩
              have hLift2 := completingBackClosure_mono_edges
                (taggedFragment 1 (compileTypeFuel signature
                  (typeCompilationFuel right) right))
                (compileTypeFuel signature (typeCompilationFuel
                  (.fairChoice bid left right)) (.fairChoice bid left right))
                hRightEdgesSubset _ hLift1
              exact completingBackClosure_mono _ hRightSeedSubset hLift2
          | fair_source =>
              -- residual = .choice left right itself; the plain-completion
              -- shortcut already handled ccbtLeft || ccbtRight = true, so
              -- here at least one side has a genuine subst-only discrepancy.
              -- Recurse into that side's OWN initial state, lift, then hop
              -- via the (silent) selection edge.
              have hCompleteFields : PactType.canCompleteBeforeTockSubst name
                    value left = true ∨
                  PactType.canCompleteBeforeTockSubst name value right = true := by
                simpa only [PactType.canCompleteBeforeTockSubst, Bool.or_eq_true]
                  using hComplete
              have hSelectionEnv : (TypeEnvironment.tock : TypeEnvironment) ∈
                  signature.localEnvironments := by
                simp [TypeAlphabet.localEnvironments]
              rcases hCompleteFields with hL | hR
              · have hLeftMem := ih (sizeOf left) hLeftSize
                  (name := name) (value := value) (processType := left) rfl
                  hTailOccFields.1 hSupportFields.1 hGuardFields.1
                  hRecursiveFields.1 hHygienicFields.1
                  (fun child hChildSize => hChildrenVanilla child
                    (lt_trans hChildSize hLeftSize)) hVanillaLeft
                  (compileTypeFuel signature (typeCompilationFuel left)
                    left).initial left
                  (compileTypeFuel_initial_relation signature
                    (typeCompilationFuel left) left
                    (typeCompilationFuel_sufficient left))
                  hL
                have hLift1 : childState 0 (compileTypeFuel signature
                    (typeCompilationFuel left) left).initial ∈
                    completingBackClosure
                      (taggedFragment 0 (compileTypeFuel signature
                        (typeCompilationFuel left) left))
                      (((if value then
                          ((compileTypeFuel signature (typeCompilationFuel left)
                              left).edges.filter
                            fun edge => edge.label = .variable name).image
                              fun edge => edge.source
                        else ∅) ∪
                        (compileTypeFuel signature (typeCompilationFuel left)
                          left).completing).image (childState 0)) := by
                  rw [completingBackClosure_taggedFragment_image]
                  exact Finset.mem_image.mpr ⟨_, hLeftMem, rfl⟩
                have hLift2 := completingBackClosure_mono_edges
                  (taggedFragment 0 (compileTypeFuel signature
                    (typeCompilationFuel left) left))
                  (compileTypeFuel signature (typeCompilationFuel
                    (.fairChoice bid left right)) (.fairChoice bid left right))
                  hLeftEdgesSubset _ hLift1
                have hLift3 := completingBackClosure_mono _ hLeftSeedSubset hLift2
                apply completingBackClosure_mem_of_nonClockEdge _ _
                  { source := TypeAutomatonState.root
                    environment := TypeEnvironment.tock
                    label := .visible (TypeLabel.fair bid true)
                    current := ∅
                    future := .at (childState 0 (compileTypeFuel signature
                      (typeCompilationFuel left) left).initial) ∅
                    target := childState 0 (compileTypeFuel signature
                      (typeCompilationFuel left) left).initial }
                · simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                    buildChoiceAutomaton, finishAutomatonFragment,
                    Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert,
                    Finset.mem_singleton, hLeftFuelEq]
                  exact Or.inr ⟨TypeEnvironment.tock, hSelectionEnv, Or.inl rfl⟩
                · simp [AutomatonConstructionLabel.semantic, TypeLabel.fair]
                · exact hLift3
              · have hRightMem := ih (sizeOf right) hRightSize
                  (name := name) (value := value) (processType := right) rfl
                  hTailOccFields.2 hSupportFields.2 hGuardFields.2
                  hRecursiveFields.2 hHygienicFields.2
                  (fun child hChildSize => hChildrenVanilla child
                    (lt_trans hChildSize hRightSize)) hVanillaRight
                  (compileTypeFuel signature (typeCompilationFuel right)
                    right).initial right
                  (compileTypeFuel_initial_relation signature
                    (typeCompilationFuel right) right
                    (typeCompilationFuel_sufficient right))
                  hR
                have hLift1 : childState 1 (compileTypeFuel signature
                    (typeCompilationFuel right) right).initial ∈
                    completingBackClosure
                      (taggedFragment 1 (compileTypeFuel signature
                        (typeCompilationFuel right) right))
                      (((if value then
                          ((compileTypeFuel signature (typeCompilationFuel right)
                              right).edges.filter
                            fun edge => edge.label = .variable name).image
                              fun edge => edge.source
                        else ∅) ∪
                        (compileTypeFuel signature (typeCompilationFuel right)
                          right).completing).image (childState 1)) := by
                  rw [completingBackClosure_taggedFragment_image]
                  exact Finset.mem_image.mpr ⟨_, hRightMem, rfl⟩
                have hLift2 := completingBackClosure_mono_edges
                  (taggedFragment 1 (compileTypeFuel signature
                    (typeCompilationFuel right) right))
                  (compileTypeFuel signature (typeCompilationFuel
                    (.fairChoice bid left right)) (.fairChoice bid left right))
                  hRightEdgesSubset _ hLift1
                have hLift3 := completingBackClosure_mono _ hRightSeedSubset hLift2
                apply completingBackClosure_mem_of_nonClockEdge _ _
                  { source := TypeAutomatonState.root
                    environment := TypeEnvironment.tock
                    label := .visible (TypeLabel.fair bid false)
                    current := ∅
                    future := .at (childState 1 (compileTypeFuel signature
                      (typeCompilationFuel right) right).initial) ∅
                    target := childState 1 (compileTypeFuel signature
                      (typeCompilationFuel right) right).initial }
                · simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                    buildChoiceAutomaton, finishAutomatonFragment,
                    Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert,
                    Finset.mem_singleton, hRightFuelEq]
                  exact Or.inr ⟨TypeEnvironment.tock, hSelectionEnv, Or.inr rfl⟩
                · simp [AutomatonConstructionLabel.semantic, TypeLabel.fair]
                · exact hLift3
      | seq left right =>
          have hSupportFields : signature.Supports left ∧
              signature.Supports right := by
            simpa only [TypeAlphabet.Supports] using hSupports
          have hGuardFields : left.ClockGuarded ∧ right.ClockGuarded := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hRecursiveFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTailRecursive
          have hHygienicFields : left.BinderHygienic [name] ∧
              right.BinderHygienic [name] := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hTailOccFields : PactType.TailOccurrences name False left ∧
              PactType.TailOccurrences name True right := by
            simpa only [PactType.TailOccurrences] using hTailOccurrences
          have hVanillaLeft : CompilationCompletingCorrect signature left :=
            hChildrenVanilla left hLeftSize hSupportFields.1 hGuardFields.1
              hRecursiveFields.1
              (PactType.binderHygienic_mono
                (by intro other hMember; simp at hMember) left
                  hHygienicFields.1)
          have hLeftFuelSufficient : TypeCompilationFuelSufficient left
              (max (typeCompilationFuel left) (typeCompilationFuel right)) :=
            le_max_left _ _
          have hLeftFuelEq : compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right))
                left =
              compileTypeFuel signature (typeCompilationFuel left) left :=
            compileTypeFuel_eq_of_sufficient signature left
              hLeftFuelSufficient (typeCompilationFuel_sufficient left)
          have hRightFuelSufficient : TypeCompilationFuelSufficient right
              (max (typeCompilationFuel left) (typeCompilationFuel right)) :=
            le_max_right _ _
          have hRightFuelEq : compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right))
                right =
              compileTypeFuel signature (typeCompilationFuel right) right :=
            compileTypeFuel_eq_of_sufficient signature right
              hRightFuelSufficient (typeCompilationFuel_sufficient right)
          have hTailOccRight : PactType.TailOccurrences name True right :=
            hTailOccFields.2
          -- `.seq left right`'s completing field is
          -- `(if right.initial ∈ right.completing then childCompleting 0 left
          -- else ∅) ∪ childCompleting 1 right`: the `childCompleting 1 right`
          -- part is unconditional, so `childState 1 s`'s membership still
          -- reduces cleanly to `s ∈ right.completing`, exactly as for choice.
          have hVanillaRight : CompilationCompletingCorrect signature right := by
            intro s r hr
            constructor
            · intro hMem
              have hMemOuter : (childState 1 s : TypeAutomatonState) ∈
                  (compileTypeFuel signature (typeCompilationFuel
                    (.seq left right)) (.seq left right)).completing := by
                simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                  buildSequenceAutomaton, finishAutomatonFragment,
                  Finset.mem_union, hRightFuelEq]
                exact Or.inr (Finset.mem_image.mpr ⟨s, hMem, rfl⟩)
              exact (hVanilla (childState 1 s) r
                (TypeCompilationRelation.sequence_right left right r s hr)).mp
                hMemOuter
            · intro hCanComplete
              have hMemOuter := (hVanilla (childState 1 s) r
                (TypeCompilationRelation.sequence_right left right r s hr)).mpr
                hCanComplete
              simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                buildSequenceAutomaton, finishAutomatonFragment,
                Finset.mem_union, childCompleting, hRightFuelEq] at hMemOuter
              rcases hMemOuter with hLeftMem | hRightMem
              · exfalso
                split at hLeftMem
                · obtain ⟨w, _, hEq⟩ := Finset.mem_image.mp hLeftMem
                  simp [childState] at hEq
                · simp at hLeftMem
              · obtain ⟨w, hw, hEq⟩ := Finset.mem_image.mp hRightMem
                have hws : w = s := by simpa [childState] using hEq
                subst hws; exact hw
          have hRightEdgesSubset : ∀ source label target,
              (∃ edge ∈ (taggedFragment 1 (compileTypeFuel signature
                  (typeCompilationFuel right) right)).edges,
                edge.source = source ∧ edge.label = label ∧
                  edge.target = target) →
              (∃ edge ∈ (compileTypeFuel signature (typeCompilationFuel
                  (.seq left right)) (.seq left right)).edges,
                edge.source = source ∧ edge.label = label ∧
                  edge.target = target) := by
            rintro source label target ⟨edge, hEdge, hSourceEq, hLabelEq, hTargetEq⟩
            simp only [taggedFragment, Finset.mem_image] at hEdge
            obtain ⟨original, hOriginal, rfl⟩ := hEdge
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
              buildSequenceAutomaton, finishAutomatonFragment, Finset.mem_union,
              hRightFuelEq]
            exact ⟨childPendingEdge 1 original,
              Or.inl (Or.inl (Or.inr (Finset.mem_image.mpr
                ⟨original, hOriginal, rfl⟩))),
              hSourceEq, hLabelEq, hTargetEq⟩
          have hRightSeedSubset : ((if value then
                ((compileTypeFuel signature (typeCompilationFuel right)
                    right).edges.filter fun edge => edge.label = .variable name).image
                  fun edge => edge.source
              else ∅) ∪
              (compileTypeFuel signature (typeCompilationFuel right)
                right).completing).image (childState 1) ⊆
              (if value then
                  ((compileTypeFuel signature (typeCompilationFuel
                      (.seq left right)) (.seq left right)).edges.filter
                    fun edge => edge.label = .variable name).image
                      fun edge => edge.source
                else ∅) ∪
                (compileTypeFuel signature (typeCompilationFuel
                  (.seq left right)) (.seq left right)).completing := by
            intro t ht
            simp only [Finset.mem_image] at ht
            obtain ⟨u, hu, rfl⟩ := ht
            rcases Finset.mem_union.mp hu with hVar | hCompleting
            · apply Finset.mem_union_left
              by_cases hv : value
              · simp only [hv, if_true] at hVar ⊢
                simp only [Finset.mem_image, Finset.mem_filter] at hVar ⊢
                obtain ⟨edge, ⟨hEdge, hLabel⟩, hSource⟩ := hVar
                refine ⟨childPendingEdge 1 edge, ⟨?_, ?_⟩, ?_⟩
                · simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                    buildSequenceAutomaton, finishAutomatonFragment,
                    Finset.mem_union, hRightFuelEq]
                  exact Or.inl (Or.inl (Or.inr (Finset.mem_image.mpr
                    ⟨edge, hEdge, rfl⟩)))
                · simpa [childPendingEdge] using hLabel
                · simp [childPendingEdge, ← hSource]
              · simp [hv] at hVar
            · apply Finset.mem_union_right
              simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                buildSequenceAutomaton, finishAutomatonFragment, Finset.mem_union,
                childCompleting, hRightFuelEq]
              exact Or.inr (Finset.mem_image.mpr ⟨u, hCompleting, rfl⟩)
          cases hRelated with
          | sequence_right _ _ _ innerState hInner =>
              have hRightMem := ih (sizeOf right) hRightSize
                (name := name) (value := value) (processType := right) rfl
                hTailOccRight hSupportFields.2 hGuardFields.2
                  hRecursiveFields.2 hHygienicFields.2
                  (fun child hChildSize => hChildrenVanilla child
                    (lt_trans hChildSize hRightSize)) hVanillaRight
                innerState residual hInner hComplete
              have hLift1 : childState 1 innerState ∈
                  completingBackClosure
                    (taggedFragment 1 (compileTypeFuel signature
                      (typeCompilationFuel right) right))
                    (((if value then
                        ((compileTypeFuel signature (typeCompilationFuel right)
                            right).edges.filter
                          fun edge => edge.label = .variable name).image
                            fun edge => edge.source
                      else ∅) ∪
                      (compileTypeFuel signature (typeCompilationFuel right)
                        right).completing).image (childState 1)) := by
                rw [completingBackClosure_taggedFragment_image]
                exact Finset.mem_image.mpr ⟨innerState, hRightMem, rfl⟩
              have hLift2 := completingBackClosure_mono_edges
                (taggedFragment 1 (compileTypeFuel signature
                  (typeCompilationFuel right) right))
                (compileTypeFuel signature (typeCompilationFuel
                  (.seq left right)) (.seq left right))
                hRightEdgesSubset _ hLift1
              exact completingBackClosure_mono _ hRightSeedSubset hLift2
          | sequence_left _ _ childResidual innerState hInner =>
              have hCompleteFields :
                  PactType.canCompleteBeforeTockSubst name value
                        childResidual = true ∧
                    PactType.canCompleteBeforeTockSubst name value right =
                      true := by
                simpa only [PactType.canCompleteBeforeTockSubst,
                  Bool.and_eq_true] using hComplete
              have hInnerTail : childResidual.TailOccurrences name False :=
                compilationRelation_tailOccurrences_false name hInner
                  hTailOccFields.1
              have hInnerPlain : childResidual.CanCompleteBeforeTock = true := by
                simpa only [
                  PactType.canCompleteBeforeTockSubst_eq_of_tailOccurrences_false
                    name value childResidual hInnerTail] using hCompleteFields.1
              have hLeftCompleting : innerState ∈
                  (compileTypeFuel signature (typeCompilationFuel left)
                    left).completing :=
                (hVanillaLeft innerState childResidual hInner).mpr hInnerPlain
              have hRightMem := ih (sizeOf right) hRightSize
                (name := name) (value := value) (processType := right) rfl
                hTailOccRight hSupportFields.2 hGuardFields.2
                  hRecursiveFields.2 hHygienicFields.2
                  (fun child hChildSize => hChildrenVanilla child
                    (lt_trans hChildSize hRightSize)) hVanillaRight
                (compileTypeFuel signature (typeCompilationFuel right)
                  right).initial right
                (compileTypeFuel_initial_relation signature
                  (typeCompilationFuel right) right
                  (typeCompilationFuel_sufficient right)) hCompleteFields.2
              have hRightLift1 : childState 1 (compileTypeFuel signature
                    (typeCompilationFuel right) right).initial ∈
                  completingBackClosure
                    (taggedFragment 1 (compileTypeFuel signature
                      (typeCompilationFuel right) right))
                    (((if value then
                        ((compileTypeFuel signature (typeCompilationFuel right)
                            right).edges.filter
                          fun edge => edge.label = .variable name).image
                            fun edge => edge.source
                      else ∅) ∪
                      (compileTypeFuel signature (typeCompilationFuel right)
                        right).completing).image (childState 1)) := by
                rw [completingBackClosure_taggedFragment_image]
                exact Finset.mem_image.mpr ⟨_, hRightMem, rfl⟩
              have hRightLift2 := completingBackClosure_mono_edges
                (taggedFragment 1 (compileTypeFuel signature
                  (typeCompilationFuel right) right))
                (compileTypeFuel signature (typeCompilationFuel
                  (.seq left right)) (.seq left right))
                hRightEdgesSubset _ hRightLift1
              have hRightLifted := completingBackClosure_mono _
                hRightSeedSubset hRightLift2
              let futureBridge : PendingAutomatonEdge :=
                { source := childState 0 innerState
                  environment := .empty
                  label := .future
                  current := ∅
                  future := .at (childState 1
                    (compileTypeFuel signature (typeCompilationFuel right)
                      right).initial) ∅
                  target := childState 1
                    (compileTypeFuel signature (typeCompilationFuel right)
                      right).initial }
              apply completingBackClosure_mem_of_nonClockEdge _ _ futureBridge
              · simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
                  buildSequenceAutomaton, finishAutomatonFragment,
                  Finset.mem_union, Finset.mem_image, hLeftFuelEq,
                  hRightFuelEq, futureBridge]
                exact Or.inr ⟨innerState, hLeftCompleting, rfl⟩
              · simp [futureBridge, AutomatonConstructionLabel.semantic,
                  TypeLabel.silent]
              · exact hRightLifted
      | par left right interface =>
          cases hRelated with
          | parallel _ _ leftResidual rightResidual _ leftState rightState
              hLeftRelated hRightRelated =>
              have hTailFields : left.TailOccurrences name False ∧
                  right.TailOccurrences name False := by
                simpa only [PactType.TailOccurrences] using hTailOccurrences
              have hLeftResidualTail :
                  leftResidual.TailOccurrences name False :=
                compilationRelation_tailOccurrences_false name hLeftRelated
                  hTailFields.1
              have hRightResidualTail :
                  rightResidual.TailOccurrences name False :=
                compilationRelation_tailOccurrences_false name hRightRelated
                  hTailFields.2
              exfalso
              apply hPlain
              simpa only [PactType.canCompleteBeforeTockSubst,
                PactType.CanCompleteBeforeTock,
                PactType.canCompleteBeforeTockSubst_eq_of_tailOccurrences_false
                  name value leftResidual hLeftResidualTail,
                PactType.canCompleteBeforeTockSubst_eq_of_tailOccurrences_false
                  name value rightResidual hRightResidualTail] using hComplete
      | xoffer elseType branches =>
          let fuel := max (typeCompilationFuel elseType)
            (typeBranchCompilationFuel branches)
          let elseFragment := compileTypeFuel signature fuel elseType
          let branchAutomata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          let parentFragment := buildExclusiveOfferAutomaton signature branches
            elseFragment branchAutomata
          have hParent : compileTypeFuel signature
              (typeCompilationFuel (.xoffer elseType branches))
                (.xoffer elseType branches) = parentFragment := by
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
            rfl
          have hSupportFields : signature.Supports elseType ∧
              signature.SupportsBranches branches := by
            simpa only [TypeAlphabet.Supports] using hSupports
          have hTailFields : elseType.TailOccurrences name True ∧
              PactType.TailBranchOccurrences name True branches := by
            simpa only [PactType.TailOccurrences] using hTailOccurrences
          have hGuardFields : elseType.ClockGuarded ∧
              PactType.ClockGuardedBranches branches := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hRecursiveFields : elseType.TailRecursive ∧
              PactType.TailRecursiveBranches branches := by
            simpa only [PactType.TailRecursive] using hTailRecursive
          have hHygienicFields : elseType.BinderHygienic [name] ∧
              PactType.BinderHygienicBranches [name] branches := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, fuel]
          have hElseStable : elseFragment = compileTypeFuel signature
              (typeCompilationFuel elseType) elseType :=
            compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
              (typeCompilationFuel_sufficient elseType)
          have hElseCompleting : ∀ child,
              childState 0 child ∈ parentFragment.completing ↔
                child ∈ elseFragment.completing := by
            intro child
            exact buildExclusiveOffer_child0_completing_iff signature branches
              elseFragment branchAutomata child
          have hElseOutgoing : ∀ child edge,
              edge ∈ parentFragment.edges ∧
                  edge.source = childState 0 child ↔
                ∃ childEdge ∈ elseFragment.edges,
                  childEdge.source = child ∧
                    edge = childPendingEdge 0 childEdge := by
            intro child edge
            exact buildExclusiveOfferAutomaton_outgoing_else signature branches
              elseFragment branchAutomata child edge
          have hVanillaElse : CompilationCompletingCorrect signature elseType := by
            intro child childResidual hChildRelated
            have hParentIff := hVanilla (childState 0 child) childResidual
              (TypeCompilationRelation.xoffer_else elseType childResidual
                branches child hChildRelated)
            rw [hParent] at hParentIff
            rw [← hElseStable]
            exact (hElseCompleting child).symm.trans hParentIff
          have liftElse : ∀ {child},
              child ∈ completingBackClosure elseFragment
                ((if value then
                    (elseFragment.edges.filter fun edge =>
                      edge.label = .variable name).image fun edge => edge.source
                  else ∅) ∪ elseFragment.completing) →
              childState 0 child ∈ completingBackClosure parentFragment
                ((if value then
                    (parentFragment.edges.filter fun edge =>
                      edge.label = .variable name).image fun edge => edge.source
                  else ∅) ∪ parentFragment.completing) := by
            intro child hChild
            exact completingBackClosure_lift_taggedChild parentFragment
              elseFragment 0 name value hElseOutgoing hElseCompleting hChild
          cases hRelated with
          | xoffer_else _ _ _ child hChildRelated =>
              have hChildMem := ih (sizeOf elseType) hElseSize
                (name := name) (value := value) (processType := elseType) rfl
                hTailFields.1 hSupportFields.1 hGuardFields.1
                  hRecursiveFields.1 hHygienicFields.1
                  (fun child hChildSize => hChildrenVanilla child
                    (lt_trans hChildSize hElseSize)) hVanillaElse child residual
                  hChildRelated hComplete
              rw [← hElseStable] at hChildMem
              rw [hParent]
              exact liftElse hChildMem
          | xoffer_branch _ branchType _ _ action index child hEntry
              hChildRelated =>
              have hBranchMember : (action, branchType) ∈ branches :=
                List.mem_of_getElem? hEntry
              have hBranchSize : sizeOf branchType < n := by
                have hPair := List.sizeOf_lt_of_mem hBranchMember
                have hComponent : sizeOf branchType <
                    sizeOf (action, branchType) := by simp_wf; omega
                rw [← hSize]
                simp_wf
                omega
              have hBranchFuel : TypeCompilationFuelSufficient branchType
                  fuel :=
                (typeCompilationFuel_le_typeBranchCompilationFuel branches
                  (action, branchType) hBranchMember).trans (by simp [fuel])
              let branchFragment := compileTypeFuel signature fuel branchType
              have hBranchStable : branchFragment = compileTypeFuel signature
                  (typeCompilationFuel branchType) branchType :=
                compileTypeFuel_eq_of_sufficient signature branchType
                  hBranchFuel (typeCompilationFuel_sufficient branchType)
              have hAutomatonEntry : branchAutomata[index]? =
                  some (action, branchFragment) := by
                simp [branchAutomata, branchFragment, hEntry]
              have hBranchTail : branchType.TailOccurrences name True :=
                tailBranchOccurrences_mem name True branches
                  (action, branchType) hTailFields.2 hBranchMember
              have hBranchSupports : signature.Supports branchType :=
                supports_branch_of_mem signature branches (action, branchType)
                  hSupportFields.2 hBranchMember
              have hBranchGuarded : branchType.ClockGuarded :=
                clockGuarded_branch_of_mem branches (action, branchType)
                  hGuardFields.2 hBranchMember
              have hBranchRecursive : branchType.TailRecursive :=
                tailRecursive_branch_of_mem branches (action, branchType)
                  hRecursiveFields.2 hBranchMember
              have hBranchHygienic : branchType.BinderHygienic [name] :=
                binderHygienic_branch_of_mem [name] branches (action, branchType)
                  hHygienicFields.2 hBranchMember
              have hBranchCompleting : ∀ q,
                  childState (index + 1) q ∈ parentFragment.completing ↔
                    q ∈ branchFragment.completing := by
                intro q
                exact buildExclusiveOffer_branch_completing_iff signature
                  branches elseFragment branchAutomata index
                    (action, branchFragment) hAutomatonEntry q
              have hBranchOutgoing : ∀ q edge,
                  edge ∈ parentFragment.edges ∧
                      edge.source = childState (index + 1) q ↔
                    ∃ childEdge ∈ branchFragment.edges,
                      childEdge.source = q ∧
                        edge = childPendingEdge (index + 1) childEdge := by
                intro q edge
                exact buildExclusiveOfferAutomaton_outgoing_branch signature
                  branches elseFragment branchAutomata index
                    (action, branchFragment) hAutomatonEntry q edge
              have hVanillaBranch : CompilationCompletingCorrect signature
                  branchType := by
                intro q childResidual hChild
                have hParentIff := hVanilla (childState (index + 1) q)
                  childResidual
                  (TypeCompilationRelation.xoffer_branch elseType branchType
                    childResidual branches action index q hEntry hChild)
                rw [hParent] at hParentIff
                rw [← hBranchStable]
                exact (hBranchCompleting q).symm.trans hParentIff
              have hChildMem := ih (sizeOf branchType) hBranchSize
                (name := name) (value := value) (processType := branchType)
                rfl hBranchTail hBranchSupports hBranchGuarded
                  hBranchRecursive hBranchHygienic
                  (fun child hChildSize => hChildrenVanilla child
                    (lt_trans hChildSize hBranchSize)) hVanillaBranch child residual
                  hChildRelated hComplete
              rw [← hBranchStable] at hChildMem
              rw [hParent]
              exact completingBackClosure_lift_taggedChild parentFragment
                branchFragment (index + 1) name value hBranchOutgoing
                  hBranchCompleting hChildMem
          | xoffer_source =>
              have hCompleteFields :
                  PactType.canCompleteBeforeTockSubst name value elseType = true ∨
                    PactType.branchCanCompleteBeforeTockSubst name value
                      branches = true := by
                simpa only [PactType.canCompleteBeforeTockSubst,
                  Bool.or_eq_true] using hComplete
              rw [hParent]
              rcases hCompleteFields with hElseComplete | hBranchComplete
              · have hElseMem := ih (sizeOf elseType) hElseSize
                  (name := name) (value := value) (processType := elseType) rfl
                  hTailFields.1 hSupportFields.1 hGuardFields.1
                    hRecursiveFields.1 hHygienicFields.1
                    (fun child hChildSize => hChildrenVanilla child
                      (lt_trans hChildSize hElseSize)) hVanillaElse
                    elseFragment.initial elseType
                    (by
                      rw [hElseStable]
                      exact compileTypeFuel_initial_relation signature
                        (typeCompilationFuel elseType) elseType
                          (typeCompilationFuel_sufficient elseType))
                    hElseComplete
                rw [← hElseStable] at hElseMem
                have hLifted := liftElse hElseMem
                let elseEdge : PendingAutomatonEdge :=
                  { source := TypeAutomatonState.root
                    environment := TypeEnvironment.tock
                    label := .visible TypeLabel.silent
                    current := ∅
                    future := .at (childState 0 elseFragment.initial) ∅
                    target := childState 0 elseFragment.initial }
                apply completingBackClosure_mem_of_nonClockEdge parentFragment _
                  elseEdge
                · simp [parentFragment, buildExclusiveOfferAutomaton,
                    finishAutomatonFragment, elseEdge,
                    TypeAlphabet.localEnvironments, TypeEnvironment.tock,
                    typeBranchNeeds]
                · simp [elseEdge, AutomatonConstructionLabel.semantic,
                    TypeLabel.silent]
                · exact hLifted
              · rcases (branchCanCompleteBeforeTockSubst_eq_true_iff name value
                    branches).mp hBranchComplete with
                  ⟨branch, hBranchMember, hBranchComplete⟩
                rcases branch with ⟨action, branchType⟩
                rcases exists_getElem?_eq_some_of_mem hBranchMember with
                  ⟨index, hEntry⟩
                have hBranchSize : sizeOf branchType < n := by
                  have hPair := List.sizeOf_lt_of_mem hBranchMember
                  have hComponent : sizeOf branchType <
                      sizeOf (action, branchType) := by simp_wf; omega
                  rw [← hSize]
                  simp_wf
                  omega
                have hBranchFuel : TypeCompilationFuelSufficient branchType
                    fuel :=
                  (typeCompilationFuel_le_typeBranchCompilationFuel branches
                    (action, branchType) hBranchMember).trans (by simp [fuel])
                let branchFragment := compileTypeFuel signature fuel branchType
                have hBranchStable : branchFragment = compileTypeFuel signature
                    (typeCompilationFuel branchType) branchType :=
                  compileTypeFuel_eq_of_sufficient signature branchType
                    hBranchFuel (typeCompilationFuel_sufficient branchType)
                have hAutomatonEntry : branchAutomata[index]? =
                    some (action, branchFragment) := by
                  simp [branchAutomata, branchFragment, hEntry]
                have hBranchTail : branchType.TailOccurrences name True :=
                  tailBranchOccurrences_mem name True branches
                    (action, branchType) hTailFields.2 hBranchMember
                have hBranchSupports : signature.Supports branchType :=
                  supports_branch_of_mem signature branches (action, branchType)
                    hSupportFields.2 hBranchMember
                have hBranchGuarded : branchType.ClockGuarded :=
                  clockGuarded_branch_of_mem branches (action, branchType)
                    hGuardFields.2 hBranchMember
                have hBranchRecursive : branchType.TailRecursive :=
                  tailRecursive_branch_of_mem branches (action, branchType)
                    hRecursiveFields.2 hBranchMember
                have hBranchHygienic : branchType.BinderHygienic [name] :=
                  binderHygienic_branch_of_mem [name] branches
                    (action, branchType) hHygienicFields.2 hBranchMember
                have hBranchCompleting : ∀ q,
                    childState (index + 1) q ∈ parentFragment.completing ↔
                      q ∈ branchFragment.completing := by
                  intro q
                  exact buildExclusiveOffer_branch_completing_iff signature
                    branches elseFragment branchAutomata index
                      (action, branchFragment) hAutomatonEntry q
                have hBranchOutgoing : ∀ q edge,
                    edge ∈ parentFragment.edges ∧
                        edge.source = childState (index + 1) q ↔
                      ∃ childEdge ∈ branchFragment.edges,
                        childEdge.source = q ∧
                          edge = childPendingEdge (index + 1) childEdge := by
                  intro q edge
                  exact buildExclusiveOfferAutomaton_outgoing_branch signature
                    branches elseFragment branchAutomata index
                      (action, branchFragment) hAutomatonEntry q edge
                have hVanillaBranch : CompilationCompletingCorrect signature
                    branchType := by
                  intro q childResidual hChild
                  have hParentIff := hVanilla (childState (index + 1) q)
                    childResidual
                    (TypeCompilationRelation.xoffer_branch elseType branchType
                      childResidual branches action index q hEntry hChild)
                  rw [hParent] at hParentIff
                  rw [← hBranchStable]
                  exact (hBranchCompleting q).symm.trans hParentIff
                have hBranchMem := ih (sizeOf branchType) hBranchSize
                  (name := name) (value := value) (processType := branchType)
                  rfl hBranchTail hBranchSupports hBranchGuarded
                    hBranchRecursive hBranchHygienic
                    (fun child hChildSize => hChildrenVanilla child
                      (lt_trans hChildSize hBranchSize)) hVanillaBranch
                    branchFragment.initial branchType
                    (by
                      rw [hBranchStable]
                      exact compileTypeFuel_initial_relation signature
                        (typeCompilationFuel branchType) branchType
                          (typeCompilationFuel_sufficient branchType))
                    hBranchComplete
                rw [← hBranchStable] at hBranchMem
                have hLifted := completingBackClosure_lift_taggedChild
                  parentFragment branchFragment (index + 1) name value
                    hBranchOutgoing hBranchCompleting hBranchMem
                let branchEnvironment : TypeEnvironment :=
                  { immediate := {typeNeed (action, branchType).1}
                    future := ∅
                    clock := false }
                let branchEdge : PendingAutomatonEdge :=
                  { source := TypeAutomatonState.root
                    environment := branchEnvironment
                    label := .visible
                      (TypeLabel.message (action, branchType).1.1
                        (action, branchType).1.2)
                    current := {(action, branchType).1}
                    future := .at
                      (childState (index + 1) branchFragment.initial) ∅
                    target := childState (index + 1) branchFragment.initial }
                have hAvailable : typeNeed (action, branchType).1 ∈
                    signature.localEnvironmentActions :=
                  supportedBranchNeed_mem_localEnvironmentActions signature
                    branches hSupportFields.2 (action, branchType) hBranchMember
                have hAutomatonBound : index < branchAutomata.length :=
                  (List.getElem?_eq_some_iff.mp hAutomatonEntry).1
                have hZipBound : index < branchAutomata.zipIdx.length := by
                  simpa using hAutomatonBound
                have hZipEntry : ((action, branchFragment), index) ∈
                    branchAutomata.zipIdx := by
                  have hMember := List.getElem_mem hZipBound
                  have hAt := List.getElem_zipIdx (l := branchAutomata)
                    (i := index) (j := 0) hZipBound
                  simp only [zero_add] at hAt
                  have hValue := (List.getElem?_eq_some_iff.mp
                    hAutomatonEntry).2
                  rw [hAt, hValue] at hMember
                  exact hMember
                have hEnvironment : branchEnvironment ∈
                    signature.localEnvironments := by
                  simp [branchEnvironment, TypeAlphabet.localEnvironments,
                    hAvailable]
                apply completingBackClosure_mem_of_nonClockEdge parentFragment _
                  branchEdge
                · simp only [parentFragment, buildExclusiveOfferAutomaton,
                    finishAutomatonFragment, Finset.mem_union]
                  left
                  left
                  right
                  rw [mem_foldl_union_iff]
                  right
                  refine ⟨((action, branchFragment), index), hZipEntry, ?_⟩
                  exact Finset.mem_image.mpr ⟨branchEnvironment,
                    Finset.mem_filter.mpr ⟨hEnvironment, by
                      simp [branchEnvironment]⟩, by
                        simp [branchEdge, branchEnvironment]⟩
                · simp [branchEdge, AutomatonConstructionLabel.semantic,
                    TypeLabel.message]
                · exact hLifted
      | offer elseType branches =>
          have hSupportFields : signature.Supports elseType ∧
              signature.SupportsBranches branches := by
            simpa only [TypeAlphabet.Supports] using hSupports
          have hGuardFields : elseType.ClockGuarded ∧
              PactType.ClockGuardedBranches branches := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hRecursiveFields : elseType.TailRecursive ∧
              PactType.TailRecursiveBranches branches := by
            simpa only [PactType.TailRecursive] using hTailRecursive
          have hHygienicFields : elseType.BinderHygienic [name] ∧
              PactType.BinderHygienicBranches [name] branches := by
            simpa only [PactType.BinderHygienic] using hHygienic
          let fuel := max (typeCompilationFuel elseType)
            (conjunctiveCompilationFuel branches)
          let elseFragment := compileTypeFuel signature fuel elseType
          let selectedConjunctions := branches.map fun selected =>
            (selected.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting selected branches))
          let parentFragment := buildSelectedConjunctiveOfferAutomaton
            signature branches elseFragment selectedConjunctions
          have hParent : compileTypeFuel signature
              (typeCompilationFuel (.offer elseType branches))
                (.offer elseType branches) = parentFragment := by
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
            rfl
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hTailFields : elseType.TailOccurrences name True ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTailOccurrences
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, fuel]
          have hElseStable : elseFragment = compileTypeFuel signature
              (typeCompilationFuel elseType) elseType :=
            compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
              (typeCompilationFuel_sufficient elseType)
          have hElseCompleting : ∀ child,
              childState 0 child ∈ parentFragment.completing ↔
                child ∈ elseFragment.completing := by
            intro child
            simp only [parentFragment,
              buildSelectedConjunctiveOfferAutomaton,
              finishAutomatonFragment, Finset.mem_union]
            constructor
            · rintro ((hRoot | hElse) | hIndexed)
              · split at hRoot <;> simp [childState] at hRoot
              · simpa [childCompleting, childState] using hElse
              · exact (child_zero_not_mem_indexedFragmentCompleting
                  selectedConjunctions child hIndexed).elim
            · intro hElse
              exact Or.inl (Or.inr (by
                simpa [childCompleting, childState] using hElse))
          have hVanillaElse : CompilationCompletingCorrect signature elseType := by
            intro child childResidual hChildRelated
            have hParentIff := hVanilla (childState 0 child) childResidual
              (TypeCompilationRelation.offer_else elseType childResidual
                branches child hChildRelated)
            rw [hParent] at hParentIff
            have hCanonical : child ∈ (compileTypeFuel signature
                  (typeCompilationFuel elseType) elseType).completing ↔
                childResidual.CanCompleteBeforeTock = true := by
              rw [← hElseStable]
              exact (hElseCompleting child).symm.trans hParentIff
            exact hCanonical
          have hElseOutgoing : ∀ child edge,
              edge ∈ parentFragment.edges ∧
                  edge.source = childState 0 child ↔
                ∃ childEdge ∈ elseFragment.edges,
                  childEdge.source = child ∧
                    edge = childPendingEdge 0 childEdge := by
            intro child edge
            simpa [parentFragment] using
              (buildSelectedConjunctiveOfferAutomaton_outgoing_else signature
                branches elseFragment selectedConjunctions child edge)
          cases hRelated with
          | offer_else _ _ _ child hChildRelated =>
              have hChildMem := ih (sizeOf elseType) hElseSize
                (name := name) (value := value) (processType := elseType) rfl
                hTailFields.1 hSupportFields.1 hGuardFields.1
                  hRecursiveFields.1 hHygienicFields.1
                  (fun child hChildSize => hChildrenVanilla child
                    (lt_trans hChildSize hElseSize)) hVanillaElse child residual
                  hChildRelated hComplete
              rw [← hElseStable] at hChildMem
              rw [hParent]
              exact completingBackClosure_lift_taggedChild parentFragment
                elseFragment 0 name value hElseOutgoing hElseCompleting
                  hChildMem
          | offer_branches _ _ _ selected index child hEntry
              hChildRelated =>
              have hSelectedTail :
                  (parallelTypeBranchesSelecting selected branches).TailOccurrences
                    name False :=
                tailOccurrences_parallelTypeBranchesSelecting name selected
                  branches hTailFields.2
              have hResidualTail : residual.TailOccurrences name False :=
                compilationRelation_tailOccurrences_false name hChildRelated
                  hSelectedTail
              exfalso
              apply hPlain
              simpa only [PactType.canCompleteBeforeTockSubst_eq_of_tailOccurrences_false
                name value residual hResidualTail] using hComplete
          | offer_source =>
              have hCompleteFields :
                  PactType.canCompleteBeforeTockSubst name value elseType = true ∨
                    PactType.branchCanCompleteBeforeTockSubst name value
                      branches = true := by
                simpa only [PactType.canCompleteBeforeTockSubst,
                  Bool.or_eq_true] using hComplete
              have hElseComplete :
                  PactType.canCompleteBeforeTockSubst name value elseType =
                    true := by
                rcases hCompleteFields with hElse | hBranches
                · exact hElse
                · exfalso
                  apply hPlain
                  have hPlainBranches :
                      PactType.BranchCanCompleteBeforeTock branches = true := by
                    rw [← branchCanCompleteBeforeTockSubst_eq_of_tailOccurrences_false
                      name value branches hTailFields.2]
                    exact hBranches
                  simp [PactType.CanCompleteBeforeTock, hPlainBranches]
              have hElseMem := ih (sizeOf elseType) hElseSize
                (name := name) (value := value) (processType := elseType) rfl
                hTailFields.1 hSupportFields.1 hGuardFields.1
                  hRecursiveFields.1 hHygienicFields.1
                  (fun child hChildSize => hChildrenVanilla child
                    (lt_trans hChildSize hElseSize)) hVanillaElse
                  elseFragment.initial elseType
                (by
                  rw [hElseStable]
                  exact compileTypeFuel_initial_relation signature
                    (typeCompilationFuel elseType) elseType
                      (typeCompilationFuel_sufficient elseType))
                hElseComplete
              rw [← hElseStable] at hElseMem
              have hLifted : childState 0 elseFragment.initial ∈
                  completingBackClosure parentFragment
                    ((if value then
                        (parentFragment.edges.filter fun edge =>
                          edge.label = .variable name).image fun edge => edge.source
                      else ∅) ∪ parentFragment.completing) :=
                completingBackClosure_lift_taggedChild parentFragment
                  elseFragment 0 name value hElseOutgoing hElseCompleting hElseMem
              rw [hParent]
              let elseEdge : PendingAutomatonEdge :=
                { source := TypeAutomatonState.root
                  environment := TypeEnvironment.tock
                  label := .visible TypeLabel.silent
                  current := typeBranchActions branches
                  future := .at (childState 0 elseFragment.initial) ∅
                  target := childState 0 elseFragment.initial }
              apply completingBackClosure_mem_of_nonClockEdge parentFragment _
                elseEdge
              · simp [parentFragment, buildSelectedConjunctiveOfferAutomaton,
                  finishAutomatonFragment, elseEdge,
                  TypeAlphabet.localEnvironments, TypeEnvironment.tock,
                  typeBranchNeeds]
              · simp [elseEdge, AutomatonConstructionLabel.semantic,
                  TypeLabel.silent]
              · exact hLifted

end

end Pact
