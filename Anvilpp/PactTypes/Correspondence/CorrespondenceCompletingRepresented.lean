import Anvilpp.PactTypes.Correspondence.CorrespondenceMarkerSkipping

/-!
# compiledFragmentCompleting_represented (mutual induction)
-/

namespace Pact

noncomputable section

/- **Non-clock predecessor step for substituted completion.**

If the target of a non-clock edge of a compiled fragment represents a residual
that completes before the next tock — scoring a bare `.var name` as `value`
rather than `false` — then the edge's source also represents such a residual.
This is the graph obligation of the forward (`⊆`) half of
`recursionBodyCompletingClosure_iff`.

Two features of this statement were forced by counterexamples found while
assembling the forward half, and must not be weakened back:

* The conclusion is **existential** (`∃ sourceResidual, related ∧ complete`),
  not the seemingly more convenient universal form `∀ r, related → complete`.
  The universal form cannot be discharged, and a parallel product refutes it
  up to the existence of one synchronised edge.  Take
  `body = .par (.var "y") .skip ∅` inside a binder for `"x"`.  The product
  edge synchronising the left fragment's `.variable "y"` marker
  (`.root → .final`, silent) with the right fragment's silent self-loop is
  itself silent; its source `.pair .root .root` represents
  `.par (.var "y") .skip ∅`, whose substituted completion for `"x"` is
  `false`; and its target `.pair .final .root` represents *nothing at all*,
  since the `.var` fragment's `.final` is unrelated.  So the universal
  premise holds vacuously while the universal conclusion fails.  (This was
  not turned into a kernel-checked regression lemma: whether that product
  edge is actually emitted depends on `syncAutomatonEdges` at a concrete
  signature, and the point stands regardless — the universal form is not
  provable by this induction.)  Crucially, filtering the ambient set by the
  universal predicate does *not* rescue it either: `buildParallelAutomaton`
  emits a `.future` self-loop at *every* product state, so the unrepresented
  target is an edge source and therefore does lie in the ambient set.  The
  existential form is immune, because the vacuous premise becomes an
  unsatisfiable one.
* The hypothesis is `≠ TypeLabel.tock`, not `= TypeLabel.silent`.  Silent
  implies non-clock, so this is only a strengthening at the use site, but the
  induction *requires* it: `buildParallelAutomaton` can hide two visible
  message edges inside one silent product edge, and the induction hypothesis
  has to be applied to those non-silent components.  `≠ tock` survives that
  decomposition by `AutomatonConstructionLabel.component_nonclock_of_sync`,
  whereas `= silent` does not.  It is also exactly the right condition
  semantically: the only compiled edge that legitimately destroys completion
  is the clock edge of `.tock`.

Intended proof: induction on the compilation fuel, one case per constructor.
Atomic constructors are direct (the clock edge of `.tock` is excluded by the
hypothesis, every other atomic edge is a silent self-loop or lands in
`.skip`); the `.var` case is vacuous because its `.final` target represents
nothing.  Child edges of `.choice`/`.fairChoice`/`.seq`/`.xoffer`/`.offer`
transport through the matching relation constructor and the corresponding
`canCompleteBeforeTockSubst` clause.  Fresh administrative edges are handled
by `compileTypeFuel_initial_relation` (their targets are child entries).  The
`.seq` bridge edges additionally need that a `skipping` state represents
`.skip` — a further mechanical induction that does not exist yet.  The `.par`
case decomposes through `resolvedAutomatonEdges` and
`component_nonclock_of_sync`.  The `.recur` case relates the header edge and
the installed backedges to `PactType.replaceVar_canCompleteBeforeTock`. -/
mutual

theorem compiledFragmentNonClockPredecessor_eval
    (signature : TypeAlphabet) (active : List String)
    (valuation : String → Bool) (fuel : Nat) :
    ∀ (processType : PactType),
      (∀ name, name ∉ active → valuation name = false) →
      TypeCompilationFuelSufficient processType fuel →
      PactType.TailRecursive processType →
      PactType.BinderHygienic active processType →
      ∀ edge ∈ (compileTypeFuel signature fuel processType).edges,
        edge.label.semantic ≠ TypeLabel.tock →
        ∀ targetResidual,
          TypeCompilationRelation processType edge.target targetResidual →
          PactType.completionEval valuation targetResidual = true →
            ∃ sourceResidual,
              TypeCompilationRelation processType edge.source sourceResidual ∧
              PactType.completionEval valuation sourceResidual = true := by
  classical
  cases fuel with
  | zero =>
      intro processType _ hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel =>
      have ih := fun (active : List String) (valuation : String → Bool) =>
        compiledFragmentNonClockPredecessor_eval signature active valuation fuel
      intro processType hSupported hFuel hTail hHygienic edge hEdge
        hNonClock targetResidual hTargetRelated hTargetComplete
      generalize hTargetState : edge.target = targetState at hTargetRelated
      cases processType with
      | skip =>
          cases hTargetRelated
          refine ⟨.skip, ?_, by simp [PactType.completionEval]⟩
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with ⟨environment, _, hEq⟩
          simpa [← hEq] using TypeCompilationRelation.skip
      | message msg dir =>
          cases hTargetRelated with
          | message_source =>
              simp only [compileTypeFuel, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
              rcases hEdge with ((⟨environment, _, hEq⟩ |
                  ⟨environment, _, hEq⟩) | ⟨environment, _, hEq⟩)
              · rw [← hEq] at hTargetState
                simp at hTargetState
              · refine ⟨.message msg dir, ?_, by simp
                    [PactType.completionEval]⟩
                simpa [← hEq] using
                  TypeCompilationRelation.message_source msg dir
              · rw [← hEq] at hTargetState
                simp at hTargetState
          | message_final =>
              simp only [compileTypeFuel, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
              rcases hEdge with ((⟨environment, _, hEq⟩ |
                  ⟨environment, _, hEq⟩) | ⟨environment, _, hEq⟩)
              · refine ⟨.message msg dir, ?_, by simp
                    [PactType.completionEval]⟩
                simpa [← hEq] using
                  TypeCompilationRelation.message_source msg dir
              · rw [← hEq] at hTargetState
                simp at hTargetState
              · refine ⟨.skip, ?_, by simp
                    [PactType.completionEval]⟩
                simpa [← hEq] using
                  TypeCompilationRelation.message_final msg dir
      | tock =>
          cases hTargetRelated with
          | cycle_source =>
              simp [PactType.completionEval] at hTargetComplete
          | cycle_final =>
              simp only [compileTypeFuel, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_image] at hEdge
              rcases hEdge with ⟨environment, _, hEq⟩ | ⟨environment, _, hEq⟩
              · rw [← hEq] at hTargetState hNonClock
                by_cases hClock : environment.clock = true
                · apply (hNonClock (by simp [hClock,
                    AutomatonConstructionLabel.semantic])).elim
                · simp [hClock] at hTargetState
              · refine ⟨.skip, ?_, by simp
                    [PactType.completionEval]⟩
                simpa [← hEq] using TypeCompilationRelation.cycle_final
      | progress pid =>
          cases hTargetRelated with
          | progress_source =>
              simp only [compileTypeFuel, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
              rcases hEdge with ⟨environment, _, hEq⟩ | ⟨environment, _, hEq⟩
              · rw [← hEq] at hTargetState
                simp at hTargetState
              · rw [← hEq] at hTargetState
                simp at hTargetState
          | progress_final =>
              simp only [compileTypeFuel, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
              rcases hEdge with ⟨environment, _, hEq⟩ | ⟨environment, _, hEq⟩
              · refine ⟨.progress pid, ?_, by simp
                    [PactType.completionEval]⟩
                simpa [← hEq] using
                  TypeCompilationRelation.progress_source pid
              · refine ⟨.skip, ?_, by simp
                    [PactType.completionEval]⟩
                simpa [← hEq] using
                  TypeCompilationRelation.progress_final pid
      | var other =>
          cases hTargetRelated
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image] at hEdge
          rcases hEdge with ⟨environment, _, hEq⟩
          rw [← hEq] at hTargetState
          simp at hTargetState
      | recur binder body =>
          have hBodyFuel : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : body.TailOccurrences binder True ∧
              body.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hHygienicFields : binder ∉ active ∧
              body.BinderHygienic (binder :: active) := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hFreshBody : body.BinderFreshFor (binder :: active) :=
            PactType.binderHygienic_binderFreshFor (binder :: active) body
              hHygienicFields.2
          let recursiveType : PactType := .recur binder body
          let bodyFragment := compileTypeFuel signature fuel body
          simp only [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
              at hEdge
          cases hTargetRelated with
          | recur_source =>
              rcases hEdge with ⟨environment, _, hEq⟩ |
                ⟨bodyEdge, _, hEq⟩
              · subst edge
                simp [Pact.childState] at hTargetState
              · by_cases hVariable : bodyEdge.label = .variable binder
                · rw [if_pos hVariable] at hEq
                  subst edge
                  simp [Pact.childState] at hTargetState
                · rw [if_neg hVariable] at hEq
                  subst edge
                  simp [Pact.childState] at hTargetState
          | recur_body _ _ childResidual childState hChildRelated =>
              rcases hEdge with ⟨environment, _, hEq⟩ |
                ⟨bodyEdge, hBodyEdge, hEq⟩
              · subst edge
                have hChildState : bodyFragment.initial = childState := by
                  injection hTargetState
                have hInitial := compileTypeFuel_initial_relation signature
                  fuel body hBodyFuel
                have hResidual : childResidual = body :=
                  TypeCompilationRelation.residual_unique hChildRelated
                    (hChildState ▸ hInitial)
                subst childResidual
                refine ⟨recursiveType, ?_, ?_⟩
                · simpa [recursiveType] using
                    TypeCompilationRelation.recur_source binder body
                · rw [← completionEval_unfold_recur_of_hygienic active
                    valuation binder body hSupported hFreshBody]
                  simpa [recursiveType] using hTargetComplete
              · by_cases hVariable : bodyEdge.label = .variable binder
                · rw [if_pos hVariable] at hEq
                  subst edge
                  have hChildState : bodyFragment.initial = childState := by
                    injection hTargetState
                  have hInitial := compileTypeFuel_initial_relation signature
                    fuel body hBodyFuel
                  have hResidual : childResidual = body :=
                    TypeCompilationRelation.residual_unique hChildRelated
                      (hChildState ▸ hInitial)
                  subst childResidual
                  have hMarker := compileTypeFuel_variableEdge_source_var
                    signature binder fuel body True hBodyFuel hTailFields.1
                      bodyEdge hBodyEdge hVariable
                  have hSourceRelation : TypeCompilationRelation
                      (.recur binder body) (.child 0 bodyEdge.source)
                        recursiveType := by
                    have hLifted := TypeCompilationRelation.recur_body binder
                      body (.var binder) bodyEdge.source hMarker.2
                    simpa [recursiveType, PactType.replaceVar] using hLifted
                  refine ⟨recursiveType, hSourceRelation, ?_⟩
                  rw [← completionEval_unfold_recur_of_hygienic active
                      valuation binder body hSupported hFreshBody]
                  simpa [recursiveType] using hTargetComplete
                · rw [if_neg hVariable] at hEq
                  subst edge
                  have hChildTarget : bodyEdge.target = childState := by
                    injection hTargetState
                  let extendedValuation : String → Bool :=
                    Function.update valuation binder
                      (PactType.completionEval valuation recursiveType)
                  have hExtendedSupported : ∀ variableName,
                      variableName ∉ binder :: active →
                        extendedValuation variableName = false := by
                    intro variableName hNotMem
                    have hNe : variableName ≠ binder := by
                      intro hEq
                      subst variableName
                      exact hNotMem (by simp)
                    simp [extendedValuation, Function.update, hNe,
                      hSupported variableName (by
                        intro hMem
                        exact hNotMem (List.mem_cons_of_mem binder hMem))]
                  have hTargetFresh :
                      childResidual.BinderFreshFor (binder :: active) :=
                    compilationRelation_binderFreshFor hChildRelated
                      hHygienicFields.2
                  have hTargetEval : PactType.completionEval extendedValuation
                      childResidual = true := by
                    rw [← PactType.completionEval_replaceVar_of_hygienic active
                      valuation binder recursiveType hSupported
                        childResidual hTargetFresh]
                    simpa [recursiveType] using hTargetComplete
                  have hBodyNonClock :
                      bodyEdge.label.semantic ≠ TypeLabel.tock := by
                    simpa using hNonClock
                  obtain ⟨sourceResidual, hSourceRelated, hSourceComplete⟩ :=
                    ih (binder :: active) extendedValuation body
                      hExtendedSupported hBodyFuel hTailFields.2
                        hHygienicFields.2 bodyEdge hBodyEdge hBodyNonClock
                          childResidual (hChildTarget ▸ hChildRelated) hTargetEval
                  have hSourceFresh :
                      sourceResidual.BinderFreshFor (binder :: active) :=
                    compilationRelation_binderFreshFor hSourceRelated
                      hHygienicFields.2
                  refine ⟨sourceResidual.replaceVar binder recursiveType,
                    TypeCompilationRelation.recur_body binder body
                      sourceResidual bodyEdge.source hSourceRelated, ?_⟩
                  rw [PactType.completionEval_replaceVar_of_hygienic active
                    valuation binder recursiveType hSupported
                      sourceResidual hSourceFresh]
                  exact hSourceComplete
      | choice left right =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hHygienicFields : left.BinderHygienic active ∧
              right.BinderHygienic active := by
            simpa only [PactType.BinderHygienic] using hHygienic
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union, childPendingEdges,
            Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
            Finset.mem_singleton] at hEdge
          cases hTargetRelated with
          | choice_source =>
              rcases hEdge with
                (⟨childEdge, _, hEq⟩ | ⟨childEdge, _, hEq⟩) |
                  ⟨environment, _, hEq | hEq⟩
              all_goals subst edge
              all_goals simp [childPendingEdge, Pact.childState] at hTargetState
          | choice_left _ _ _ childState hChildRelated =>
              rcases hEdge with
                (⟨childEdge, hChildEdge, hEq⟩ |
                  ⟨childEdge, _, hEq⟩) |
                    ⟨environment, _, hEq | hEq⟩
              · subst edge
                have hChildTarget : childEdge.target = childState := by
                  injection hTargetState
                have hChildNonClock :
                    childEdge.label.semantic ≠ TypeLabel.tock := by
                  simpa [childPendingEdge] using hNonClock
                obtain ⟨sourceResidual, hSourceRelated, hSourceComplete⟩ :=
                  ih active valuation left hSupported hLeftFuel hTailFields.1
                    hHygienicFields.1 childEdge hChildEdge
                    hChildNonClock targetResidual
                      (hChildTarget ▸ hChildRelated) hTargetComplete
                exact ⟨sourceResidual,
                  TypeCompilationRelation.choice_left left right
                    sourceResidual childEdge.source hSourceRelated,
                  hSourceComplete⟩
              · subst edge
                simp [childPendingEdge, Pact.childState] at hTargetState
              · subst edge
                have hChildState :
                    (compileTypeFuel signature fuel left).initial =
                      childState := by
                  injection hTargetState
                have hInitial := compileTypeFuel_initial_relation signature
                  fuel left hLeftFuel
                have hResidual : targetResidual = left :=
                  TypeCompilationRelation.residual_unique hChildRelated
                    (hChildState ▸ hInitial)
                subst targetResidual
                refine ⟨.choice left right,
                  TypeCompilationRelation.choice_source left right, ?_⟩
                simpa [PactType.completionEval] using
                  (show PactType.completionEval valuation left = true ∨
                    PactType.completionEval valuation right = true from
                      Or.inl hTargetComplete)
              · subst edge
                simp [Pact.childState] at hTargetState
          | choice_right _ _ _ childState hChildRelated =>
              rcases hEdge with
                (⟨childEdge, _, hEq⟩ |
                  ⟨childEdge, hChildEdge, hEq⟩) |
                    ⟨environment, _, hEq | hEq⟩
              · subst edge
                simp [childPendingEdge, Pact.childState] at hTargetState
              · subst edge
                have hChildTarget : childEdge.target = childState := by
                  injection hTargetState
                have hChildNonClock :
                    childEdge.label.semantic ≠ TypeLabel.tock := by
                  simpa [childPendingEdge] using hNonClock
                obtain ⟨sourceResidual, hSourceRelated, hSourceComplete⟩ :=
                  ih active valuation right hSupported hRightFuel hTailFields.2
                    hHygienicFields.2 childEdge hChildEdge
                    hChildNonClock targetResidual
                      (hChildTarget ▸ hChildRelated) hTargetComplete
                exact ⟨sourceResidual,
                  TypeCompilationRelation.choice_right left right
                    sourceResidual childEdge.source hSourceRelated,
                  hSourceComplete⟩
              · subst edge
                simp [Pact.childState] at hTargetState
              · subst edge
                have hChildState :
                    (compileTypeFuel signature fuel right).initial =
                      childState := by
                  injection hTargetState
                have hInitial := compileTypeFuel_initial_relation signature
                  fuel right hRightFuel
                have hResidual : targetResidual = right :=
                  TypeCompilationRelation.residual_unique hChildRelated
                    (hChildState ▸ hInitial)
                subst targetResidual
                refine ⟨.choice left right,
                  TypeCompilationRelation.choice_source left right, ?_⟩
                simpa [PactType.completionEval] using
                  (show PactType.completionEval valuation left = true ∨
                    PactType.completionEval valuation right = true from
                      Or.inr hTargetComplete)
      | fairChoice bid left right =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hHygienicFields : left.BinderHygienic active ∧
              right.BinderHygienic active := by
            simpa only [PactType.BinderHygienic] using hHygienic
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union, childPendingEdges,
            Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
            Finset.mem_singleton] at hEdge
          cases hTargetRelated with
          | fair_source =>
              rcases hEdge with
                (⟨childEdge, _, hEq⟩ | ⟨childEdge, _, hEq⟩) |
                  ⟨environment, _, hEq | hEq⟩
              all_goals subst edge
              all_goals simp [childPendingEdge, Pact.childState] at hTargetState
          | fair_left _ _ _ _ childState hChildRelated =>
              rcases hEdge with
                (⟨childEdge, hChildEdge, hEq⟩ |
                  ⟨childEdge, _, hEq⟩) |
                    ⟨environment, _, hEq | hEq⟩
              · subst edge
                have hChildTarget : childEdge.target = childState := by
                  injection hTargetState
                have hChildNonClock :
                    childEdge.label.semantic ≠ TypeLabel.tock := by
                  simpa [childPendingEdge] using hNonClock
                obtain ⟨sourceResidual, hSourceRelated, hSourceComplete⟩ :=
                  ih active valuation left hSupported hLeftFuel hTailFields.1
                    hHygienicFields.1 childEdge hChildEdge
                    hChildNonClock targetResidual
                      (hChildTarget ▸ hChildRelated) hTargetComplete
                exact ⟨sourceResidual,
                  TypeCompilationRelation.fair_left bid left right
                    sourceResidual childEdge.source hSourceRelated,
                  hSourceComplete⟩
              · subst edge
                simp [childPendingEdge, Pact.childState] at hTargetState
              · subst edge
                have hChildState :
                    (compileTypeFuel signature fuel left).initial =
                      childState := by
                  injection hTargetState
                have hInitial := compileTypeFuel_initial_relation signature
                  fuel left hLeftFuel
                have hResidual : targetResidual = left :=
                  TypeCompilationRelation.residual_unique hChildRelated
                    (hChildState ▸ hInitial)
                subst targetResidual
                refine ⟨.fairChoice bid left right,
                  TypeCompilationRelation.fair_source bid left right, ?_⟩
                simpa [PactType.completionEval] using
                  (show PactType.completionEval valuation left = true ∨
                    PactType.completionEval valuation right = true from
                      Or.inl hTargetComplete)
              · subst edge
                simp [Pact.childState] at hTargetState
          | fair_right _ _ _ _ childState hChildRelated =>
              rcases hEdge with
                (⟨childEdge, _, hEq⟩ |
                  ⟨childEdge, hChildEdge, hEq⟩) |
                    ⟨environment, _, hEq | hEq⟩
              · subst edge
                simp [childPendingEdge, Pact.childState] at hTargetState
              · subst edge
                have hChildTarget : childEdge.target = childState := by
                  injection hTargetState
                have hChildNonClock :
                    childEdge.label.semantic ≠ TypeLabel.tock := by
                  simpa [childPendingEdge] using hNonClock
                obtain ⟨sourceResidual, hSourceRelated, hSourceComplete⟩ :=
                  ih active valuation right hSupported hRightFuel hTailFields.2
                    hHygienicFields.2 childEdge hChildEdge
                    hChildNonClock targetResidual
                      (hChildTarget ▸ hChildRelated) hTargetComplete
                exact ⟨sourceResidual,
                  TypeCompilationRelation.fair_right bid left right
                    sourceResidual childEdge.source hSourceRelated,
                  hSourceComplete⟩
              · subst edge
                simp [Pact.childState] at hTargetState
              · subst edge
                have hChildState :
                    (compileTypeFuel signature fuel right).initial =
                      childState := by
                  injection hTargetState
                have hInitial := compileTypeFuel_initial_relation signature
                  fuel right hRightFuel
                have hResidual : targetResidual = right :=
                  TypeCompilationRelation.residual_unique hChildRelated
                    (hChildState ▸ hInitial)
                subst targetResidual
                refine ⟨.fairChoice bid left right,
                  TypeCompilationRelation.fair_source bid left right, ?_⟩
                simpa [PactType.completionEval] using
                  (show PactType.completionEval valuation left = true ∨
                    PactType.completionEval valuation right = true from
                      Or.inr hTargetComplete)
      | seq left right =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hHygienicFields : left.BinderHygienic active ∧
              right.BinderHygienic active := by
            simpa only [PactType.BinderHygienic] using hHygienic
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion] at hEdge
          cases hTargetRelated with
          | sequence_left _ _ childResidual childState hChildRelated =>
              simp only [PactType.completionEval,
                Bool.and_eq_true] at hTargetComplete
              rcases hEdge with
                ((⟨childEdge, hChildEdge, hEq⟩ |
                    ⟨childEdge, _, hEq⟩) |
                  ⟨bridgeState, _, environment, _, hEq⟩) |
                    ⟨bridgeState, _, hEq⟩
              · subst edge
                have hChildTarget : childEdge.target = childState := by
                  injection hTargetState
                have hChildNonClock :
                    childEdge.label.semantic ≠ TypeLabel.tock := by
                  simpa using hNonClock
                obtain ⟨sourceResidual, hSourceRelated, hSourceComplete⟩ :=
                  ih active valuation left hSupported hLeftFuel hTailFields.1
                    hHygienicFields.1 childEdge hChildEdge
                    hChildNonClock childResidual
                      (hChildTarget ▸ hChildRelated) hTargetComplete.1
                refine ⟨.seq sourceResidual right,
                  TypeCompilationRelation.sequence_left left right
                    sourceResidual childEdge.source hSourceRelated, ?_⟩
                simp [PactType.completionEval, hSourceComplete,
                  hTargetComplete.2]
              · subst edge
                simp [childPendingEdge, Pact.childState] at hTargetState
              · subst edge
                simp [Pact.childState] at hTargetState
              · subst edge
                simp [Pact.childState] at hTargetState
          | sequence_right _ _ childResidual childState hChildRelated =>
              rcases hEdge with
                ((⟨childEdge, _, hEq⟩ |
                  ⟨childEdge, hChildEdge, hEq⟩) |
                  ⟨bridgeState, hBridgeSkipping, environment, _, hEq⟩) |
                    ⟨bridgeState, hBridgeCompleting, hEq⟩
              · subst edge
                simp [Pact.childState] at hTargetState
              · subst edge
                have hChildTarget : childEdge.target = childState := by
                  injection hTargetState
                have hChildNonClock :
                    childEdge.label.semantic ≠ TypeLabel.tock := by
                  simpa [childPendingEdge] using hNonClock
                obtain ⟨sourceResidual, hSourceRelated, hSourceComplete⟩ :=
                  ih active valuation right hSupported hRightFuel hTailFields.2
                    hHygienicFields.2 childEdge hChildEdge
                    hChildNonClock targetResidual
                      (hChildTarget ▸ hChildRelated) hTargetComplete
                exact ⟨sourceResidual,
                  TypeCompilationRelation.sequence_right left right
                    sourceResidual childEdge.source hSourceRelated,
                  hSourceComplete⟩
              · subst edge
                have hChildState :
                    (compileTypeFuel signature fuel right).initial =
                      childState := by
                  injection hTargetState
                have hRightInitial := compileTypeFuel_initial_relation
                  signature fuel right hRightFuel
                have hResidual : targetResidual = right :=
                  TypeCompilationRelation.residual_unique hChildRelated
                    (hChildState ▸ hRightInitial)
                subst targetResidual
                have hLeftSkip : TypeCompilationRelation left bridgeState .skip :=
                  compiledFragmentSkipping_represented signature fuel left
                    hLeftFuel bridgeState hBridgeSkipping
                refine ⟨.seq .skip right,
                  TypeCompilationRelation.sequence_left left right .skip
                    bridgeState hLeftSkip, ?_⟩
                simp [PactType.completionEval, hTargetComplete]
              · subst edge
                have hChildState :
                    (compileTypeFuel signature fuel right).initial =
                      childState := by
                  injection hTargetState
                have hRightInitial := compileTypeFuel_initial_relation
                  signature fuel right hRightFuel
                have hResidual : targetResidual = right :=
                  TypeCompilationRelation.residual_unique hChildRelated
                    (hChildState ▸ hRightInitial)
                subst targetResidual
                obtain ⟨leftResidual, hLeftRelated, hLeftComplete⟩ :=
                  compiledFragmentCompleting_represented signature active fuel
                    left hLeftFuel hTailFields.1
                      hHygienicFields.1 bridgeState hBridgeCompleting
                have hLeftEval : PactType.completionEval valuation
                    leftResidual = true := by
                  apply PactType.completionEval_mono (fun _ => false) valuation
                    (by intro variableName; simp)
                  rw [PactType.completionEval_eq_canCompleteBeforeTock_of_all_false]
                  · exact hLeftComplete
                  · intro variableName
                    rfl
                refine ⟨.seq leftResidual right,
                  TypeCompilationRelation.sequence_left left right
                    leftResidual bridgeState hLeftRelated, ?_⟩
                simp [PactType.completionEval, hLeftEval,
                  hTargetComplete]
      | par left right interface =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hHygienicFields : left.BinderHygienic active ∧
              right.BinderHygienic active := by
            simpa only [PactType.BinderHygienic] using hHygienic
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, Finset.mem_union, Finset.mem_biUnion,
            Finset.mem_image, Finset.mem_filter] at hEdge
          cases hTargetRelated with
          | parallel _ _ leftResidual rightResidual _ leftState rightState
              hLeftRelated hRightRelated =>
              simp only [PactType.completionEval,
                Bool.and_eq_true] at hTargetComplete
              rcases hEdge with hTransition | hObservation
              · rcases hTransition with
                  ⟨leftEdge, ⟨hLeftEdge, _⟩, rightEdge,
                    ⟨⟨hRightEdge, _⟩, hSync⟩, hEq⟩
                subst edge
                rcases hSync with
                  ⟨leftWitness, hLeftWitness, rightWitness, hRightWitness,
                    hWitnesses⟩
                have hLabelSync : TypeLabel.Sync interface
                    leftEdge.label.semantic rightEdge.label.semantic :=
                  hWitnesses.2.2.2
                have hComponentNonClock :=
                  AutomatonConstructionLabel.component_nonclock_of_sync
                    interface leftEdge.label rightEdge.label hLabelSync
                      hNonClock
                simp only [resolvedAutomatonEdges, Finset.mem_image]
                  at hLeftEdge hRightEdge
                rcases hLeftEdge with
                  ⟨leftRaw, hLeftRaw, hLeftResolved⟩
                rcases hRightEdge with
                  ⟨rightRaw, hRightRaw, hRightResolved⟩
                have hLeftTarget : leftRaw.target = leftState := by
                  rw [← hLeftResolved] at hTargetState
                  injection hTargetState
                have hRightTarget : rightRaw.target = rightState := by
                  rw [← hRightResolved] at hTargetState
                  injection hTargetState
                have hLeftNonClock :
                    leftRaw.label.semantic ≠ TypeLabel.tock := by
                  simpa [← hLeftResolved] using hComponentNonClock.1
                have hRightNonClock :
                    rightRaw.label.semantic ≠ TypeLabel.tock := by
                  simpa [← hRightResolved] using hComponentNonClock.2
                obtain ⟨leftSourceResidual, hLeftSource,
                    hLeftComplete⟩ :=
                  ih active valuation left hSupported hLeftFuel hTailFields.1
                    hHygienicFields.1 leftRaw hLeftRaw
                    hLeftNonClock leftResidual
                      (hLeftTarget ▸ hLeftRelated) hTargetComplete.1
                obtain ⟨rightSourceResidual, hRightSource,
                    hRightComplete⟩ :=
                  ih active valuation right hSupported hRightFuel hTailFields.2
                    hHygienicFields.2 rightRaw hRightRaw
                    hRightNonClock rightResidual
                      (hRightTarget ▸ hRightRelated) hTargetComplete.2
                refine ⟨.par leftSourceResidual rightSourceResidual interface,
                  ?_, ?_⟩
                · convert TypeCompilationRelation.parallel left right
                    leftSourceResidual rightSourceResidual interface
                      leftRaw.source rightRaw.source hLeftSource hRightSource
                    using 1 <;>
                      simp [← hLeftResolved, ← hRightResolved]
                · simp [PactType.completionEval,
                    hLeftComplete, hRightComplete]
              · rcases hObservation with hLeftFuture | hRightFuture
                · rcases hLeftFuture with
                    ⟨leftSource, _, rightSource, _, hEq⟩
                  subst edge
                  have hLeftState : leftSource = leftState := by
                    injection hTargetState
                  have hRightState : rightSource = rightState := by
                    injection hTargetState
                  subst leftSource
                  subst rightSource
                  exact ⟨.par leftResidual rightResidual interface,
                    TypeCompilationRelation.parallel left right leftResidual
                      rightResidual interface leftState rightState hLeftRelated
                        hRightRelated,
                    by simpa [PactType.completionEval] using
                      hTargetComplete⟩
                · rcases hRightFuture with
                    ⟨leftSource, _, rightSource, _, hEq⟩
                  subst edge
                  have hLeftState : leftSource = leftState := by
                    injection hTargetState
                  have hRightState : rightSource = rightState := by
                    injection hTargetState
                  subst leftSource
                  subst rightSource
                  exact ⟨.par leftResidual rightResidual interface,
                    TypeCompilationRelation.parallel left right leftResidual
                      rightResidual interface leftState rightState hLeftRelated
                        hRightRelated,
                    by simpa [PactType.completionEval] using
                      hTargetComplete⟩
      | xoffer elseType branches =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hBranchFuel : typeBranchCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hTailFields : elseType.TailRecursive ∧
              PactType.TailRecursiveBranches branches := by
            simpa only [PactType.TailRecursive] using hTail
          have hHygienicFields : elseType.BinderHygienic active ∧
              PactType.BinderHygienicBranches active branches := by
            simpa only [PactType.BinderHygienic] using hHygienic
          let branchAutomata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          cases hTargetRelated with
          | xoffer_source =>
              rcases hEdge with
                ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
              · simp only [childPendingEdges, Finset.mem_image] at hElse
                rcases hElse with ⟨childEdge, _, hEq⟩
                subst edge
                simp [childPendingEdge, Pact.childState] at hTargetState
              · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
                rcases hIndexed with hEmpty | ⟨indexed, _, hChild⟩
                · simp at hEmpty
                · simp only [childPendingEdges, Finset.mem_image] at hChild
                  rcases hChild with ⟨childEdge, _, hEq⟩
                  subst edge
                  simp [childPendingEdge, Pact.childState] at hTargetState
              · rw [mem_foldl_union_iff] at hBranch
                rcases hBranch with hEmpty | ⟨indexed, _, hNewEdge⟩
                · simp at hEmpty
                · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
                  rcases hNewEdge with ⟨environment, _, hEq⟩
                  subst edge
                  simp [Pact.childState] at hTargetState
              · simp only [Finset.mem_image, Finset.mem_filter] at hWait
                rcases hWait with ⟨environment, _, hEq⟩
                subst edge
                exact ⟨.xoffer elseType branches,
                  TypeCompilationRelation.xoffer_source elseType branches,
                  hTargetComplete⟩
              · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
                rcases hResolved with ⟨environment, _, hEq⟩
                subst edge
                simp [Pact.childState] at hTargetState
          | xoffer_else _ childResidual _ childState hChildRelated =>
              rcases hEdge with
                ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
              · simp only [childPendingEdges, Finset.mem_image] at hElse
                rcases hElse with ⟨childEdge, hChildEdge, hEq⟩
                subst edge
                have hChildTarget : childEdge.target = childState := by
                  injection hTargetState
                have hChildNonClock :
                    childEdge.label.semantic ≠ TypeLabel.tock := by
                  simpa [childPendingEdge] using hNonClock
                obtain ⟨sourceResidual, hSourceRelated, hSourceComplete⟩ :=
                  ih active valuation elseType hSupported hElseFuel
                    hTailFields.1 hHygienicFields.1 childEdge hChildEdge
                    hChildNonClock targetResidual
                      (hChildTarget ▸ hChildRelated) hTargetComplete
                exact ⟨sourceResidual,
                  TypeCompilationRelation.xoffer_else elseType sourceResidual
                    branches childEdge.source hSourceRelated,
                  hSourceComplete⟩
              · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
                rcases hIndexed with hEmpty | ⟨indexed, _, hChild⟩
                · simp at hEmpty
                · simp only [childPendingEdges, Finset.mem_image] at hChild
                  rcases hChild with ⟨childEdge, _, hEq⟩
                  subst edge
                  simp [childPendingEdge, Pact.childState] at hTargetState
              · rw [mem_foldl_union_iff] at hBranch
                rcases hBranch with hEmpty | ⟨indexed, _, hNewEdge⟩
                · simp at hEmpty
                · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
                  rcases hNewEdge with ⟨environment, _, hEq⟩
                  subst edge
                  simp [Pact.childState] at hTargetState
              · simp only [Finset.mem_image, Finset.mem_filter] at hWait
                rcases hWait with ⟨environment, _, hEq⟩
                subst edge
                simp [Pact.childState] at hTargetState
              · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
                rcases hResolved with ⟨environment, _, hEq⟩
                subst edge
                have hChildState :
                    (compileTypeFuel signature fuel elseType).initial =
                      childState := by
                  injection hTargetState
                have hInitial := compileTypeFuel_initial_relation signature
                  fuel elseType hElseFuel
                have hResidual : targetResidual = elseType :=
                  TypeCompilationRelation.residual_unique hChildRelated
                    (hChildState ▸ hInitial)
                subst targetResidual
                refine ⟨.xoffer elseType branches,
                  TypeCompilationRelation.xoffer_source elseType branches, ?_⟩
                simpa [PactType.completionEval] using
                  (show PactType.completionEval valuation elseType = true ∨
                    PactType.branchCompletionEval valuation branches = true
                      from Or.inl hTargetComplete)
          | xoffer_branch _ branchType childResidual _ action index childState
              hEntry hChildRelated =>
              rcases hEdge with
                ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
              · simp only [childPendingEdges, Finset.mem_image] at hElse
                rcases hElse with ⟨childEdge, _, hEq⟩
                subst edge
                simp [childPendingEdge, Pact.childState] at hTargetState
              · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
                rcases hIndexed with hEmpty | ⟨indexedEntry, hIndexedMem,
                    hChild⟩
                · simp at hEmpty
                · simp only [childPendingEdges, Finset.mem_image] at hChild
                  rcases hChild with ⟨childEdge, hChildEdge, hEq⟩
                  subst edge
                  have hIndex : indexedEntry.2 = index := by
                    injection hTargetState with hTag hChildTarget
                    omega
                  subst index
                  have hChildTarget : childEdge.target = childState := by
                    injection hTargetState
                  have hFields := List.mem_zipIdx hIndexedMem
                  simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
                    at hFields
                  rcases hFields with ⟨hBound, hValue⟩
                  have hIndexedAt : branchAutomata[indexedEntry.2]? =
                      some indexedEntry.1 := by
                    rw [List.getElem?_eq_getElem hBound, ← hValue]
                  have hCanonicalAt : branchAutomata[indexedEntry.2]? = some
                      (action, compileTypeFuel signature fuel branchType) := by
                    simp [branchAutomata, hEntry]
                  rw [hCanonicalAt] at hIndexedAt
                  have hEntryEq : indexedEntry.1 =
                      (action, compileTypeFuel signature fuel branchType) :=
                    Option.some.inj hIndexedAt.symm
                  rw [hEntryEq] at hChildEdge
                  have hBranchMember : (action, branchType) ∈ branches :=
                    List.mem_of_getElem? hEntry
                  have hThisFuel : TypeCompilationFuelSufficient branchType fuel :=
                    (typeCompilationFuel_le_typeBranchCompilationFuel branches
                      (action, branchType) hBranchMember).trans hBranchFuel
                  have hThisTail : branchType.TailRecursive :=
                    tailRecursive_branch_of_mem branches (action, branchType)
                      hTailFields.2 hBranchMember
                  have hThisHygienic : branchType.BinderHygienic active :=
                    binderHygienic_branch_of_mem active branches
                      (action, branchType) hHygienicFields.2 hBranchMember
                  have hChildNonClock :
                      childEdge.label.semantic ≠ TypeLabel.tock := by
                    simpa [childPendingEdge] using hNonClock
                  obtain ⟨sourceResidual, hSourceRelated, hSourceComplete⟩ :=
                    ih active valuation branchType hSupported hThisFuel
                      hThisTail hThisHygienic childEdge hChildEdge
                      hChildNonClock targetResidual
                        (hChildTarget ▸ hChildRelated) hTargetComplete
                  exact ⟨sourceResidual,
                    TypeCompilationRelation.xoffer_branch elseType branchType
                      sourceResidual branches action indexedEntry.2 childEdge.source
                        hEntry hSourceRelated,
                    hSourceComplete⟩
              · rw [mem_foldl_union_iff] at hBranch
                rcases hBranch with hEmpty | ⟨indexedEntry, hIndexedMem,
                    hNewEdge⟩
                · simp at hEmpty
                · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
                  rcases hNewEdge with ⟨environment, _, hEq⟩
                  subst edge
                  have hIndex : indexedEntry.2 = index := by
                    injection hTargetState with hTag hChildTarget
                    omega
                  subst index
                  have hFields := List.mem_zipIdx hIndexedMem
                  simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
                    at hFields
                  rcases hFields with ⟨hBound, hValue⟩
                  have hIndexedAt : branchAutomata[indexedEntry.2]? =
                      some indexedEntry.1 := by
                    rw [List.getElem?_eq_getElem hBound, ← hValue]
                  have hCanonicalAt : branchAutomata[indexedEntry.2]? = some
                      (action, compileTypeFuel signature fuel branchType) := by
                    simp [branchAutomata, hEntry]
                  rw [hCanonicalAt] at hIndexedAt
                  have hEntryEq : indexedEntry.1 =
                      (action, compileTypeFuel signature fuel branchType) :=
                    Option.some.inj hIndexedAt.symm
                  have hInitial := compileTypeFuel_initial_relation signature
                    fuel branchType (by
                      have hMember : (action, branchType) ∈ branches :=
                        List.mem_of_getElem? hEntry
                      exact (typeCompilationFuel_le_typeBranchCompilationFuel
                        branches (action, branchType) hMember).trans hBranchFuel)
                  have hInitialState :
                      (compileTypeFuel signature fuel branchType).initial =
                        childState := by
                    rw [hEntryEq] at hTargetState
                    injection hTargetState
                  have hResidual : targetResidual = branchType :=
                    TypeCompilationRelation.residual_unique hChildRelated
                      (hInitialState ▸ hInitial)
                  subst targetResidual
                  refine ⟨.xoffer elseType branches,
                    TypeCompilationRelation.xoffer_source elseType branches,
                    ?_⟩
                  simpa [PactType.completionEval] using
                    (show PactType.completionEval valuation elseType = true ∨
                      PactType.branchCompletionEval valuation branches = true
                        from Or.inr
                          (branchCompletionEval_of_getElem valuation branches
                            indexedEntry.2 action branchType hEntry
                              hTargetComplete))
              · simp only [Finset.mem_image, Finset.mem_filter] at hWait
                rcases hWait with ⟨environment, _, hEq⟩
                subst edge
                simp [Pact.childState] at hTargetState
              · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
                rcases hResolved with ⟨environment, _, hEq⟩
                subst edge
                simp [Pact.childState] at hTargetState
      | offer elseType branches =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : elseType.TailRecursive ∧
              PactType.TailRecursiveBranches branches := by
            simpa only [PactType.TailRecursive] using hTail
          have hHygienicFields : elseType.BinderHygienic active ∧
              PactType.BinderHygienicBranches active branches := by
            simpa only [PactType.BinderHygienic] using hHygienic
          let selectedConjunctions := branches.map fun selected =>
            (selected.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting selected branches))
          simp only [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          cases hTargetRelated with
          | offer_source =>
              rcases hEdge with
                ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
              · simp only [childPendingEdges, Finset.mem_image] at hElse
                rcases hElse with ⟨childEdge, _, hEq⟩
                subst edge
                simp [childPendingEdge, Pact.childState] at hTargetState
              · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
                rcases hIndexed with hEmpty | ⟨indexed, _, hChild⟩
                · simp at hEmpty
                · simp only [childPendingEdges, Finset.mem_image] at hChild
                  rcases hChild with ⟨childEdge, _, hEq⟩
                  subst edge
                  simp [childPendingEdge, Pact.childState] at hTargetState
              · rw [mem_foldl_union_iff] at hEnabled
                rcases hEnabled with hEmpty | ⟨indexed, _, hNewEdge⟩
                · simp at hEmpty
                · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
                  rcases hNewEdge with ⟨environment, _, hEq⟩
                  subst edge
                  simp [Pact.childState] at hTargetState
              · simp only [Finset.mem_image, Finset.mem_filter] at hWait
                rcases hWait with ⟨environment, _, hEq⟩
                subst edge
                exact ⟨.offer elseType branches,
                  TypeCompilationRelation.offer_source elseType branches,
                  hTargetComplete⟩
              · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
                rcases hResolved with ⟨environment, _, hEq⟩
                subst edge
                simp [Pact.childState] at hTargetState
          | offer_else _ childResidual _ childState hChildRelated =>
              rcases hEdge with
                ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
              · simp only [childPendingEdges, Finset.mem_image] at hElse
                rcases hElse with ⟨childEdge, hChildEdge, hEq⟩
                subst edge
                have hChildTarget : childEdge.target = childState := by
                  injection hTargetState
                have hChildNonClock :
                    childEdge.label.semantic ≠ TypeLabel.tock := by
                  simpa [childPendingEdge] using hNonClock
                obtain ⟨sourceResidual, hSourceRelated, hSourceComplete⟩ :=
                  ih active valuation elseType hSupported hElseFuel
                    hTailFields.1 hHygienicFields.1 childEdge hChildEdge
                    hChildNonClock targetResidual
                      (hChildTarget ▸ hChildRelated) hTargetComplete
                exact ⟨sourceResidual,
                  TypeCompilationRelation.offer_else elseType sourceResidual
                    branches childEdge.source hSourceRelated,
                  hSourceComplete⟩
              · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
                rcases hIndexed with hEmpty | ⟨indexed, _, hChild⟩
                · simp at hEmpty
                · simp only [childPendingEdges, Finset.mem_image] at hChild
                  rcases hChild with ⟨childEdge, _, hEq⟩
                  subst edge
                  simp [childPendingEdge, Pact.childState] at hTargetState
              · rw [mem_foldl_union_iff] at hEnabled
                rcases hEnabled with hEmpty | ⟨indexed, _, hNewEdge⟩
                · simp at hEmpty
                · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
                  rcases hNewEdge with ⟨environment, _, hEq⟩
                  subst edge
                  simp [Pact.childState] at hTargetState
              · simp only [Finset.mem_image, Finset.mem_filter] at hWait
                rcases hWait with ⟨environment, _, hEq⟩
                subst edge
                simp [Pact.childState] at hTargetState
              · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
                rcases hResolved with ⟨environment, _, hEq⟩
                subst edge
                have hChildState :
                    (compileTypeFuel signature fuel elseType).initial =
                      childState := by
                  injection hTargetState
                have hInitial := compileTypeFuel_initial_relation signature
                  fuel elseType hElseFuel
                have hResidual : targetResidual = elseType :=
                  TypeCompilationRelation.residual_unique hChildRelated
                    (hChildState ▸ hInitial)
                subst targetResidual
                refine ⟨.offer elseType branches,
                  TypeCompilationRelation.offer_source elseType branches, ?_⟩
                simpa [PactType.completionEval] using
                  (show PactType.completionEval valuation elseType = true ∨
                    PactType.branchCompletionEval valuation branches = true
                      from Or.inl hTargetComplete)
          | offer_branches _ childResidual _ selected index childState hEntry
              hChildRelated =>
              rcases hEdge with
                ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
              · simp only [childPendingEdges, Finset.mem_image] at hElse
                rcases hElse with ⟨childEdge, _, hEq⟩
                subst edge
                simp [childPendingEdge, Pact.childState] at hTargetState
              · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
                rcases hIndexed with hEmpty | ⟨indexedEntry, hIndexedMem,
                    hChild⟩
                · simp at hEmpty
                · simp only [childPendingEdges, Finset.mem_image] at hChild
                  rcases hChild with ⟨childEdge, hChildEdge, hEq⟩
                  subst edge
                  have hIndex : indexedEntry.2 = index := by
                    injection hTargetState with hTag hChildTarget
                    omega
                  subst index
                  have hChildTarget : childEdge.target = childState := by
                    injection hTargetState
                  have hFields := List.mem_zipIdx hIndexedMem
                  simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
                    at hFields
                  rcases hFields with ⟨hBound, hValue⟩
                  have hIndexedAt : selectedConjunctions[indexedEntry.2]? =
                      some indexedEntry.1 := by
                    rw [List.getElem?_eq_getElem hBound, ← hValue]
                  have hCanonicalAt : selectedConjunctions[indexedEntry.2]? =
                      some (selected.1, compileTypeFuel signature fuel
                        (parallelTypeBranchesSelecting selected branches)) := by
                    simp [selectedConjunctions, hEntry]
                  rw [hCanonicalAt] at hIndexedAt
                  have hEntryEq : indexedEntry.1 =
                      (selected.1, compileTypeFuel signature fuel
                        (parallelTypeBranchesSelecting selected branches)) :=
                    Option.some.inj hIndexedAt.symm
                  rw [hEntryEq] at hChildEdge
                  have hThisFuel : TypeCompilationFuelSufficient
                      (parallelTypeBranchesSelecting selected branches) fuel := by
                    rw [TypeCompilationFuelSufficient,
                      typeCompilationFuel_parallelTypeBranchesSelecting]
                    simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                      at hFuel
                    omega
                  have hThisTail :=
                    tailRecursive_parallelTypeBranchesSelecting selected
                      branches hTailFields.2
                  have hThisHygienic :=
                    binderHygienic_parallelTypeBranchesSelecting active
                      selected branches hHygienicFields.2
                  have hChildNonClock :
                      childEdge.label.semantic ≠ TypeLabel.tock := by
                    simpa [childPendingEdge] using hNonClock
                  obtain ⟨sourceResidual, hSourceRelated, hSourceComplete⟩ :=
                    ih active valuation
                      (parallelTypeBranchesSelecting selected branches)
                      hSupported hThisFuel hThisTail hThisHygienic childEdge
                        hChildEdge hChildNonClock
                        targetResidual (hChildTarget ▸ hChildRelated)
                          hTargetComplete
                  exact ⟨sourceResidual,
                    TypeCompilationRelation.offer_branches elseType
                      sourceResidual branches selected indexedEntry.2
                        childEdge.source hEntry hSourceRelated,
                    hSourceComplete⟩
              · rw [mem_foldl_union_iff] at hEnabled
                rcases hEnabled with hEmpty | ⟨indexedEntry, hIndexedMem,
                    hNewEdge⟩
                · simp at hEmpty
                · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
                  rcases hNewEdge with ⟨environment, _, hEq⟩
                  subst edge
                  have hIndex : indexedEntry.2 = index := by
                    injection hTargetState with hTag hChildTarget
                    omega
                  subst index
                  have hFields := List.mem_zipIdx hIndexedMem
                  simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
                    at hFields
                  rcases hFields with ⟨hBound, hValue⟩
                  have hIndexedAt : selectedConjunctions[indexedEntry.2]? =
                      some indexedEntry.1 := by
                    rw [List.getElem?_eq_getElem hBound, ← hValue]
                  have hCanonicalAt : selectedConjunctions[indexedEntry.2]? =
                      some (selected.1, compileTypeFuel signature fuel
                        (parallelTypeBranchesSelecting selected branches)) := by
                    simp [selectedConjunctions, hEntry]
                  rw [hCanonicalAt] at hIndexedAt
                  have hEntryEq : indexedEntry.1 =
                      (selected.1, compileTypeFuel signature fuel
                        (parallelTypeBranchesSelecting selected branches)) :=
                    Option.some.inj hIndexedAt.symm
                  have hThisFuel : TypeCompilationFuelSufficient
                      (parallelTypeBranchesSelecting selected branches) fuel := by
                    rw [TypeCompilationFuelSufficient,
                      typeCompilationFuel_parallelTypeBranchesSelecting]
                    simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                      at hFuel
                    omega
                  have hInitial := compileTypeFuel_initial_relation signature
                    fuel (parallelTypeBranchesSelecting selected branches)
                      hThisFuel
                  have hInitialState : (compileTypeFuel signature fuel
                      (parallelTypeBranchesSelecting selected branches)).initial =
                        childState := by
                    rw [hEntryEq] at hTargetState
                    injection hTargetState
                  have hResidual : targetResidual =
                      parallelTypeBranchesSelecting selected branches :=
                    TypeCompilationRelation.residual_unique hChildRelated
                      (hInitialState ▸ hInitial)
                  subst targetResidual
                  have hSelectedMem : selected ∈ branches :=
                    List.mem_of_getElem? hEntry
                  have hSelectedComplete : PactType.completionEval valuation
                      selected.2 = true := by
                    rw [← completionEval_parallelTypeBranchesSelecting_of_mem
                      valuation selected branches hSelectedMem]
                    exact hTargetComplete
                  refine ⟨.offer elseType branches,
                    TypeCompilationRelation.offer_source elseType branches,
                    ?_⟩
                  simpa [PactType.completionEval] using
                    (show PactType.completionEval valuation elseType = true ∨
                      PactType.branchCompletionEval valuation branches = true
                        from Or.inr
                          (branchCompletionEval_of_getElem valuation branches
                            indexedEntry.2 selected.1 selected.2 hEntry
                              hSelectedComplete))
              · simp only [Finset.mem_image, Finset.mem_filter] at hWait
                rcases hWait with ⟨environment, _, hEq⟩
                subst edge
                simp [Pact.childState] at hTargetState
              · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
                rcases hResolved with ⟨environment, _, hEq⟩
                subst edge
                simp [Pact.childState] at hTargetState

  termination_by fuel
  decreasing_by all_goals omega

/-- Every compiler state marked as completing represents a semantic residual.
The proof carries the stronger fact that the witness itself completes; the
recursion case then closes the non-clock predecessor saturation using
`compiledFragmentNonClockPredecessor_subst`. -/
theorem compiledFragmentCompleting_represented
    (signature : TypeAlphabet) (bound : List String) (fuel : Nat) :
    ∀ (processType : PactType),
      TypeCompilationFuelSufficient processType fuel →
      PactType.TailRecursive processType →
      PactType.BinderHygienic bound processType →
      ∀ state ∈ (compileTypeFuel signature fuel processType).completing,
        ∃ residual, TypeCompilationRelation processType state residual ∧
          residual.CanCompleteBeforeTock = true := by
  classical
  cases fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel =>
      have ih := fun (bound : List String) =>
        compiledFragmentCompleting_represented signature bound fuel
      intro processType hFuel hTail hHygienic state hCompleting
      cases processType with
      | message msg dir =>
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_insert, Finset.mem_singleton] at hCompleting
          rcases hCompleting with rfl | rfl
          · exact ⟨.message msg dir,
              TypeCompilationRelation.message_source msg dir, by
                simp [PactType.CanCompleteBeforeTock]⟩
          · exact ⟨.skip, TypeCompilationRelation.message_final msg dir, by
                simp [PactType.CanCompleteBeforeTock]⟩
      | progress pid =>
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_insert, Finset.mem_singleton] at hCompleting
          rcases hCompleting with rfl | rfl
          · exact ⟨.progress pid,
              TypeCompilationRelation.progress_source pid, by
                simp [PactType.CanCompleteBeforeTock]⟩
          · exact ⟨.skip, TypeCompilationRelation.progress_final pid, by
                simp [PactType.CanCompleteBeforeTock]⟩
      | tock =>
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_singleton] at hCompleting
          subst state
          exact ⟨.skip, TypeCompilationRelation.cycle_final, by
            simp [PactType.CanCompleteBeforeTock]⟩
      | skip =>
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_singleton] at hCompleting
          subst state
          exact ⟨.skip, TypeCompilationRelation.skip, by
            simp [PactType.CanCompleteBeforeTock]⟩
      | var other =>
          simp [compileTypeFuel, finishAutomatonFragment] at hCompleting
      | choice left right =>
          have hFuelLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hFuelRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hHygienicFields : left.BinderHygienic bound ∧
              right.BinderHygienic bound := by
            simpa only [PactType.BinderHygienic] using hHygienic
          let leftFragment := compileTypeFuel signature fuel left
          let rightFragment := compileTypeFuel signature fuel right
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hCompleting
          rcases hCompleting with (hRoot | hLeft) | hRight
          · have hInitial : leftFragment.initial ∈ leftFragment.completing ∨
                rightFragment.initial ∈ rightFragment.completing := by
              by_contra hNo
              rw [if_neg hNo] at hRoot
              simp at hRoot
            have hState : state = .root := by
              rw [if_pos hInitial] at hRoot
              simpa using hRoot
            subst state
            rcases hInitial with hLeftInitial | hRightInitial
            · obtain ⟨residual, hRelated, hComplete⟩ :=
                ih bound left hFuelLeft hTailFields.1 hHygienicFields.1
                  leftFragment.initial
                  (by simpa [leftFragment] using hLeftInitial)
              have hResidual : residual = left :=
                TypeCompilationRelation.residual_unique hRelated
                  (compileTypeFuel_initial_relation signature fuel left
                    hFuelLeft)
              subst residual
              exact ⟨.choice left right,
                TypeCompilationRelation.choice_source left right, by
                  simp [PactType.CanCompleteBeforeTock, hComplete]⟩
            · obtain ⟨residual, hRelated, hComplete⟩ :=
                ih bound right hFuelRight hTailFields.2 hHygienicFields.2
                  rightFragment.initial
                  (by simpa [rightFragment] using hRightInitial)
              have hResidual : residual = right :=
                TypeCompilationRelation.residual_unique hRelated
                  (compileTypeFuel_initial_relation signature fuel right
                    hFuelRight)
              subst residual
              exact ⟨.choice left right,
                TypeCompilationRelation.choice_source left right, by
                  simp [PactType.CanCompleteBeforeTock, hComplete]⟩
          · rcases Finset.mem_image.mp hLeft with
              ⟨child, hChildCompleting, rfl⟩
            obtain ⟨residual, hRelated, hComplete⟩ :=
              ih bound left hFuelLeft hTailFields.1 hHygienicFields.1 child
                hChildCompleting
            exact ⟨residual,
              TypeCompilationRelation.choice_left left right residual child
                hRelated, hComplete⟩
          · rcases Finset.mem_image.mp hRight with
              ⟨child, hChildCompleting, rfl⟩
            obtain ⟨residual, hRelated, hComplete⟩ :=
              ih bound right hFuelRight hTailFields.2 hHygienicFields.2 child
                hChildCompleting
            exact ⟨residual,
              TypeCompilationRelation.choice_right left right residual child
                hRelated, hComplete⟩
      | fairChoice bid left right =>
          have hFuelLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hFuelRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hHygienicFields : left.BinderHygienic bound ∧
              right.BinderHygienic bound := by
            simpa only [PactType.BinderHygienic] using hHygienic
          let leftFragment := compileTypeFuel signature fuel left
          let rightFragment := compileTypeFuel signature fuel right
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hCompleting
          rcases hCompleting with (hRoot | hLeft) | hRight
          · have hInitial : leftFragment.initial ∈ leftFragment.completing ∨
                rightFragment.initial ∈ rightFragment.completing := by
              by_contra hNo
              rw [if_neg hNo] at hRoot
              simp at hRoot
            have hState : state = .root := by
              rw [if_pos hInitial] at hRoot
              simpa using hRoot
            subst state
            rcases hInitial with hLeftInitial | hRightInitial
            · obtain ⟨residual, hRelated, hComplete⟩ :=
                ih bound left hFuelLeft hTailFields.1 hHygienicFields.1
                  leftFragment.initial
                  (by simpa [leftFragment] using hLeftInitial)
              have hResidual : residual = left :=
                TypeCompilationRelation.residual_unique hRelated
                  (compileTypeFuel_initial_relation signature fuel left
                    hFuelLeft)
              subst residual
              exact ⟨.fairChoice bid left right,
                TypeCompilationRelation.fair_source bid left right, by
                  simp [PactType.CanCompleteBeforeTock, hComplete]⟩
            · obtain ⟨residual, hRelated, hComplete⟩ :=
                ih bound right hFuelRight hTailFields.2 hHygienicFields.2
                  rightFragment.initial
                  (by simpa [rightFragment] using hRightInitial)
              have hResidual : residual = right :=
                TypeCompilationRelation.residual_unique hRelated
                  (compileTypeFuel_initial_relation signature fuel right
                    hFuelRight)
              subst residual
              exact ⟨.fairChoice bid left right,
                TypeCompilationRelation.fair_source bid left right, by
                  simp [PactType.CanCompleteBeforeTock, hComplete]⟩
          · rcases Finset.mem_image.mp hLeft with
              ⟨child, hChildCompleting, rfl⟩
            obtain ⟨residual, hRelated, hComplete⟩ :=
              ih bound left hFuelLeft hTailFields.1 hHygienicFields.1 child
                hChildCompleting
            exact ⟨residual,
              TypeCompilationRelation.fair_left bid left right residual child
                hRelated, hComplete⟩
          · rcases Finset.mem_image.mp hRight with
              ⟨child, hChildCompleting, rfl⟩
            obtain ⟨residual, hRelated, hComplete⟩ :=
              ih bound right hFuelRight hTailFields.2 hHygienicFields.2 child
                hChildCompleting
            exact ⟨residual,
              TypeCompilationRelation.fair_right bid left right residual child
                hRelated, hComplete⟩
      | seq left right =>
          have hFuelLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hFuelRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hHygienicFields : left.BinderHygienic bound ∧
              right.BinderHygienic bound := by
            simpa only [PactType.BinderHygienic] using hHygienic
          let leftFragment := compileTypeFuel signature fuel left
          let rightFragment := compileTypeFuel signature fuel right
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hCompleting
          rcases hCompleting with hLeft | hRight
          · have hRightInitial : rightFragment.initial ∈
                rightFragment.completing := by
              by_contra hNo
              rw [if_neg hNo] at hLeft
              simp at hLeft
            rw [if_pos hRightInitial] at hLeft
            rcases Finset.mem_image.mp hLeft with
              ⟨leftState, hLeftCompleting, rfl⟩
            obtain ⟨leftResidual, hLeftRelated, hLeftComplete⟩ :=
              ih bound left hFuelLeft hTailFields.1 hHygienicFields.1 leftState
                hLeftCompleting
            obtain ⟨rightResidual, hRightRelated, hRightComplete⟩ :=
              ih bound right hFuelRight hTailFields.2 hHygienicFields.2
                rightFragment.initial
                hRightInitial
            have hRightResidual : rightResidual = right :=
              TypeCompilationRelation.residual_unique hRightRelated
                (compileTypeFuel_initial_relation signature fuel right
                  hFuelRight)
            subst rightResidual
            exact ⟨.seq leftResidual right,
              TypeCompilationRelation.sequence_left left right leftResidual
                leftState hLeftRelated, by
                  simp [PactType.CanCompleteBeforeTock, hLeftComplete,
                    hRightComplete]⟩
          · rcases Finset.mem_image.mp hRight with
              ⟨rightState, hRightCompleting, rfl⟩
            obtain ⟨rightResidual, hRightRelated, hRightComplete⟩ :=
              ih bound right hFuelRight hTailFields.2 hHygienicFields.2
                rightState
                hRightCompleting
            exact ⟨rightResidual,
              TypeCompilationRelation.sequence_right left right rightResidual
                rightState hRightRelated, hRightComplete⟩
      | par left right interface =>
          have hFuelLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hFuelRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hHygienicFields : left.BinderHygienic bound ∧
              right.BinderHygienic bound := by
            simpa only [PactType.BinderHygienic] using hHygienic
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, Finset.mem_biUnion,
            Finset.mem_image] at hCompleting
          rcases hCompleting with
            ⟨leftState, hLeftCompleting, rightState, hRightCompleting, rfl⟩
          obtain ⟨leftResidual, hLeftRelated, hLeftComplete⟩ :=
            ih bound left hFuelLeft hTailFields.1 hHygienicFields.1 leftState
              hLeftCompleting
          obtain ⟨rightResidual, hRightRelated, hRightComplete⟩ :=
            ih bound right hFuelRight hTailFields.2 hHygienicFields.2
              rightState
              hRightCompleting
          exact ⟨.par leftResidual rightResidual interface,
            TypeCompilationRelation.parallel left right leftResidual
              rightResidual interface leftState rightState hLeftRelated
                hRightRelated, by
              simp [PactType.CanCompleteBeforeTock, hLeftComplete,
                hRightComplete]⟩
      | recur binder body =>
          have hFuelBody : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : body.TailOccurrences binder True ∧
              body.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hHygienicFields : binder ∉ bound ∧
              body.BinderHygienic (binder :: bound) := by
            simpa only [PactType.BinderHygienic] using hHygienic
          let bodyFragment := compileTypeFuel signature fuel body
          simp only [compileTypeFuel] at hCompleting
          rw [buildRecursionAutomaton_completing_eq signature binder
            bodyFragment] at hCompleting
          rcases Finset.mem_union.mp hCompleting with hRoot | hTagged
          · have hBodyInitial : bodyFragment.initial ∈
                bodyFragment.completing := by
              by_contra hNo
              rw [if_neg hNo] at hRoot
              simp at hRoot
            have hState : state = .root := by
              rw [if_pos hBodyInitial] at hRoot
              simpa using hRoot
            subst state
            obtain ⟨bodyResidual, hBodyRelated, hBodyComplete⟩ :=
              ih (binder :: bound) body hFuelBody hTailFields.2
                hHygienicFields.2
                bodyFragment.initial
                hBodyInitial
            have hResidual : bodyResidual = body :=
              TypeCompilationRelation.residual_unique hBodyRelated
                (compileTypeFuel_initial_relation signature fuel body
                  hFuelBody)
            subst bodyResidual
            exact ⟨.recur binder body,
              TypeCompilationRelation.recur_source binder body, by
                simpa [PactType.CanCompleteBeforeTock] using hBodyComplete⟩
          · rcases Finset.mem_image.mp hTagged with
              ⟨bodyState, hClosure, rfl⟩
            let seed :=
              (if bodyFragment.initial ∈ bodyFragment.completing then
                  (bodyFragment.edges.filter
                    fun edge => edge.label = .variable binder).image
                      fun edge => edge.source
                else ∅) ∪ bodyFragment.completing
            let allowed :=
              ((bodyFragment.edges.image fun edge => edge.source) ∪
                  bodyFragment.completing).filter fun q =>
                ∃ residual, TypeCompilationRelation body q residual ∧
                  PactType.canCompleteBeforeTockSubst binder
                    body.CanCompleteBeforeTock residual = true
            have hSeed : seed ⊆ allowed := by
              intro q hq
              rcases Finset.mem_union.mp hq with hVariable | hBodyCompleting
              · have hInitial : bodyFragment.initial ∈
                    bodyFragment.completing := by
                  by_contra hNo
                  simp [seed, hNo] at hVariable
                simp only [seed, hInitial, if_true, Finset.mem_image,
                  Finset.mem_filter] at hVariable
                rcases hVariable with ⟨edge, ⟨hEdge, hLabel⟩, rfl⟩
                obtain ⟨entryResidual, hEntryRelated, hEntryComplete⟩ :=
                  ih (binder :: bound) body hFuelBody hTailFields.2
                    hHygienicFields.2
                    bodyFragment.initial hInitial
                have hEntryResidual : entryResidual = body :=
                  TypeCompilationRelation.residual_unique hEntryRelated
                    (compileTypeFuel_initial_relation signature fuel body
                      hFuelBody)
                subst entryResidual
                have hMarker := compileTypeFuel_variableEdge_source_var
                  signature binder fuel body True hFuelBody hTailFields.1 edge
                    hEdge hLabel
                exact Finset.mem_filter.mpr
                  ⟨Finset.mem_union_left _
                    (Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩),
                    .var binder, hMarker.2, by
                      simp [PactType.canCompleteBeforeTockSubst,
                        hEntryComplete]⟩
              · obtain ⟨residual, hRelated, hComplete⟩ :=
                  ih (binder :: bound) body hFuelBody hTailFields.2
                    hHygienicFields.2 q hBodyCompleting
                exact Finset.mem_filter.mpr
                  ⟨Finset.mem_union_right _ hBodyCompleting, residual,
                    hRelated, PactType.canCompleteBeforeTock_le_subst binder
                      body.CanCompleteBeforeTock residual hComplete⟩
            have hClosed : ∀ edge ∈ bodyFragment.edges,
                edge.label.semantic ≠ TypeLabel.tock →
                edge.target ∈ allowed → edge.source ∈ allowed := by
              intro edge hEdge hNonClock hTarget
              obtain ⟨targetResidual, hTargetRelated, hTargetComplete⟩ :=
                (Finset.mem_filter.mp hTarget).2
              let recursiveValuation : String → Bool :=
                Function.update (fun _ => false) binder
                  body.CanCompleteBeforeTock
              have hSupported : ∀ variableName,
                  variableName ∉ binder :: bound →
                    recursiveValuation variableName = false := by
                intro variableName hNotMem
                have hNe : variableName ≠ binder := by
                  intro hEq
                  subst variableName
                  exact hNotMem (by simp)
                simp [recursiveValuation, Function.update, hNe]
              have hTargetEval : PactType.completionEval recursiveValuation
                  targetResidual = true := by
                simpa [recursiveValuation] using
                  (show PactType.completionEval
                      (Function.update (fun _ => false) binder
                        body.CanCompleteBeforeTock) targetResidual = true by
                    rw [PactType.completionEval_singleton_eq_canCompleteBeforeTockSubst]
                    exact hTargetComplete)
              obtain ⟨sourceResidual, hSourceRelated, hSourceComplete⟩ :=
                compiledFragmentNonClockPredecessor_eval signature
                  (binder :: bound) recursiveValuation fuel body hSupported
                    hFuelBody hTailFields.2 hHygienicFields.2 edge
                      hEdge hNonClock targetResidual hTargetRelated hTargetEval
              have hSourceSubst :
                  PactType.canCompleteBeforeTockSubst binder
                    body.CanCompleteBeforeTock sourceResidual = true := by
                rw [← PactType.completionEval_singleton_eq_canCompleteBeforeTockSubst]
                simpa [recursiveValuation] using hSourceComplete
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_union_left _
                    (Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩),
                  sourceResidual, hSourceRelated, hSourceSubst⟩
            have hAllowed : bodyState ∈ allowed :=
              completingBackClosure_subset_of_predecessor_closed bodyFragment
                seed allowed hSeed hClosed hClosure
            obtain ⟨residual, hRelated, hSubst⟩ :=
              (Finset.mem_filter.mp hAllowed).2
            refine ⟨residual.replaceVar binder (.recur binder body),
              TypeCompilationRelation.recur_body binder body residual
                bodyState hRelated, ?_⟩
            rw [PactType.replaceVar_canCompleteBeforeTock]
            simpa [PactType.CanCompleteBeforeTock] using hSubst
      | xoffer elseType branches =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hBranchFuel : typeBranchCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hTailFields : elseType.TailRecursive ∧
              PactType.TailRecursiveBranches branches := by
            simpa only [PactType.TailRecursive] using hTail
          have hHygienicFields : elseType.BinderHygienic bound ∧
              PactType.BinderHygienicBranches bound branches := by
            simpa only [PactType.BinderHygienic] using hHygienic
          let elseFragment := compileTypeFuel signature fuel elseType
          let branchAutomata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hCompleting
          rcases hCompleting with (hRoot | hElse) | hIndexed
          · have hCondition : elseFragment.initial ∈
                  elseFragment.completing ∨
                branches.any (fun branch =>
                  branch.2.CanCompleteBeforeTock) = true := by
              by_contra hNo
              rw [if_neg hNo] at hRoot
              simp at hRoot
            have hState : state = .root := by
              rw [if_pos hCondition] at hRoot
              simpa using hRoot
            subst state
            have hComplete :
                (PactType.xoffer elseType branches).CanCompleteBeforeTock =
                  true := by
              rcases hCondition with hElseInitial | hBranch
              · obtain ⟨residual, hRelated, hResidualComplete⟩ :=
                  ih bound elseType hElseFuel hTailFields.1 hHygienicFields.1
                    elseFragment.initial
                    (by simpa [elseFragment] using hElseInitial)
                have hResidual : residual = elseType :=
                  TypeCompilationRelation.residual_unique hRelated
                    (compileTypeFuel_initial_relation signature fuel elseType
                      hElseFuel)
                subst residual
                simp [PactType.CanCompleteBeforeTock,
                  branchCanCompleteBeforeTock_eq_any, hResidualComplete]
              · simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
                right
                simpa [branchCanCompleteBeforeTock_eq_any] using hBranch
            exact ⟨.xoffer elseType branches,
              TypeCompilationRelation.xoffer_source elseType branches,
                hComplete⟩
          · rcases Finset.mem_image.mp hElse with
              ⟨elseState, hElseCompleting, rfl⟩
            obtain ⟨residual, hRelated, hComplete⟩ :=
              ih bound elseType hElseFuel hTailFields.1 hHygienicFields.1
                elseState hElseCompleting
            exact ⟨residual,
              TypeCompilationRelation.xoffer_else elseType residual branches
                elseState hRelated, hComplete⟩
          · rw [indexedFragmentCompleting, mem_foldl_union_iff] at hIndexed
            rcases hIndexed with hEmpty |
              ⟨indexed, hIndexedEntry, hChildCompleting⟩
            · simp at hEmpty
            · simp only [childCompleting, Finset.mem_image] at hChildCompleting
              rcases hChildCompleting with
                ⟨childState', hChildCompleting, hState⟩
              have hFields := List.mem_zipIdx hIndexedEntry
              simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
                at hFields
              rcases hFields with ⟨hBound, hValue⟩
              have hAt : branchAutomata[indexed.2]? = some indexed.1 := by
                rw [List.getElem?_eq_getElem hBound, ← hValue]
              simp only [branchAutomata, List.getElem?_map] at hAt
              cases hOriginal : branches[indexed.2]? with
              | none => simp [hOriginal] at hAt
              | some branch =>
                  rcases branch with ⟨action, branchType⟩
                  simp only [hOriginal, Option.map_some, Option.some.injEq]
                    at hAt
                  have hMember : (action, branchType) ∈ branches :=
                    List.mem_of_getElem? hOriginal
                  have hFuelBranch : TypeCompilationFuelSufficient branchType
                      fuel := by
                    exact (typeCompilationFuel_le_typeBranchCompilationFuel
                      branches (action, branchType) hMember).trans hBranchFuel
                  have hTailBranch : branchType.TailRecursive :=
                    tailRecursive_branch_of_mem branches (action, branchType)
                      hTailFields.2 hMember
                  have hHygienicBranch : branchType.BinderHygienic bound :=
                    binderHygienic_branch_of_mem bound branches
                      (action, branchType) hHygienicFields.2 hMember
                  have hFragment : indexed.1.2 =
                      compileTypeFuel signature fuel branchType := by
                    simpa using (congrArg Prod.snd hAt).symm
                  rw [hFragment] at hChildCompleting
                  obtain ⟨residual, hRelated, hComplete⟩ :=
                    ih bound branchType hFuelBranch hTailBranch
                      hHygienicBranch childState' hChildCompleting
                  have hState' : state = childState (indexed.2 + 1)
                      childState' := hState.symm
                  subst state
                  exact ⟨residual,
                    TypeCompilationRelation.xoffer_branch elseType branchType
                      residual branches action indexed.2 childState' hOriginal
                        hRelated, hComplete⟩
      | offer elseType branches =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : elseType.TailRecursive ∧
              PactType.TailRecursiveBranches branches := by
            simpa only [PactType.TailRecursive] using hTail
          have hHygienicFields : elseType.BinderHygienic bound ∧
              PactType.BinderHygienicBranches bound branches := by
            simpa only [PactType.BinderHygienic] using hHygienic
          let elseFragment := compileTypeFuel signature fuel elseType
          let selectedConjunctions := branches.map fun selected =>
            (selected.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting selected branches))
          simp only [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hCompleting
          rcases hCompleting with (hRoot | hElse) | hIndexed
          · have hCondition : elseFragment.initial ∈
                  elseFragment.completing ∨
                branches.any (fun branch =>
                  branch.2.CanCompleteBeforeTock) = true := by
              by_contra hNo
              rw [if_neg hNo] at hRoot
              simp at hRoot
            have hState : state = .root := by
              rw [if_pos hCondition] at hRoot
              simpa using hRoot
            subst state
            have hComplete :
                (PactType.offer elseType branches).CanCompleteBeforeTock =
                  true := by
              rcases hCondition with hElseInitial | hBranch
              · obtain ⟨residual, hRelated, hResidualComplete⟩ :=
                  ih bound elseType hElseFuel hTailFields.1 hHygienicFields.1
                    elseFragment.initial
                    (by simpa [elseFragment] using hElseInitial)
                have hResidual : residual = elseType :=
                  TypeCompilationRelation.residual_unique hRelated
                    (compileTypeFuel_initial_relation signature fuel elseType
                      hElseFuel)
                subst residual
                simp [PactType.CanCompleteBeforeTock,
                  branchCanCompleteBeforeTock_eq_any, hResidualComplete]
              · simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
                right
                simpa [branchCanCompleteBeforeTock_eq_any] using hBranch
            exact ⟨.offer elseType branches,
              TypeCompilationRelation.offer_source elseType branches,
                hComplete⟩
          · rcases Finset.mem_image.mp hElse with
              ⟨elseState, hElseCompleting, rfl⟩
            obtain ⟨residual, hRelated, hComplete⟩ :=
              ih bound elseType hElseFuel hTailFields.1 hHygienicFields.1
                elseState hElseCompleting
            exact ⟨residual,
              TypeCompilationRelation.offer_else elseType residual branches
                elseState hRelated, hComplete⟩
          · rw [indexedFragmentCompleting, mem_foldl_union_iff] at hIndexed
            rcases hIndexed with hEmpty |
              ⟨indexed, hIndexedEntry, hChildCompleting⟩
            · simp at hEmpty
            · simp only [childCompleting, Finset.mem_image] at hChildCompleting
              rcases hChildCompleting with
                ⟨childState', hChildCompleting, hState⟩
              have hFields := List.mem_zipIdx hIndexedEntry
              simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
                at hFields
              rcases hFields with ⟨hBound, hValue⟩
              have hAt : selectedConjunctions[indexed.2]? =
                  some indexed.1 := by
                rw [List.getElem?_eq_getElem hBound, ← hValue]
              simp only [selectedConjunctions, List.getElem?_map] at hAt
              cases hOriginal : branches[indexed.2]? with
              | none => simp [hOriginal] at hAt
              | some selected =>
                  simp only [hOriginal, Option.map_some, Option.some.injEq]
                    at hAt
                  have hMember : selected ∈ branches :=
                    List.mem_of_getElem? hOriginal
                  have hFuelSelected : TypeCompilationFuelSufficient
                      (parallelTypeBranchesSelecting selected branches) fuel := by
                    rw [TypeCompilationFuelSufficient,
                      typeCompilationFuel_parallelTypeBranchesSelecting]
                    simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                      at hFuel
                    omega
                  have hTailSelected :=
                    tailRecursive_parallelTypeBranchesSelecting selected
                      branches hTailFields.2
                  have hHygienicSelected :=
                    binderHygienic_parallelTypeBranchesSelecting bound selected
                      branches hHygienicFields.2
                  have hFragment : indexed.1.2 = compileTypeFuel signature fuel
                      (parallelTypeBranchesSelecting selected branches) := by
                    simpa using (congrArg Prod.snd hAt).symm
                  rw [hFragment] at hChildCompleting
                  obtain ⟨residual, hRelated, hComplete⟩ :=
                    ih bound (parallelTypeBranchesSelecting selected branches)
                      hFuelSelected hTailSelected hHygienicSelected childState'
                        hChildCompleting
                  have hState' : state = childState (indexed.2 + 1)
                      childState' := hState.symm
                  subst state
                  exact ⟨residual,
                    TypeCompilationRelation.offer_branches elseType residual
                      branches selected indexed.2 childState' hOriginal
                        hRelated, hComplete⟩

  termination_by fuel
  decreasing_by all_goals omega

end

end

end Pact
