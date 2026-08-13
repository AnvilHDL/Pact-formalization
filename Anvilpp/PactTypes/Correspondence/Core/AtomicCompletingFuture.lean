import Anvilpp.PactTypes.Correspondence.Core.CompilationStateCorrect

/-!
# CompilationCompletingCorrect and CompilationFutureCorrect for the atomic constructors
-/

namespace Pact

noncomputable section

/-- The constructor metadata used only for optimistic future propagation is
exactly the syntax predicate saying that the represented residual may finish
before the next clock. -/
def CompilationCompletingCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  ∀ state residual,
    TypeCompilationRelation processType state residual →
      (state ∈ (compileTypeFuel signature
          (typeCompilationFuel processType) processType).completing ↔
        residual.CanCompleteBeforeTock = true)

theorem compilationCompletingCorrect_skip (signature : TypeAlphabet) :
    CompilationCompletingCorrect signature .skip := by
  intro state residual hRelated
  cases hRelated
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    PactType.CanCompleteBeforeTock]

theorem compilationCompletingCorrect_message
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CompilationCompletingCorrect signature (.message msg dir) := by
  intro state residual hRelated
  cases hRelated <;>
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      PactType.CanCompleteBeforeTock]

theorem compilationCompletingCorrect_tock (signature : TypeAlphabet) :
    CompilationCompletingCorrect signature .tock := by
  intro state residual hRelated
  cases hRelated <;>
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      PactType.CanCompleteBeforeTock]

theorem compilationCompletingCorrect_progress
    (signature : TypeAlphabet) (pid : ProcId) :
    CompilationCompletingCorrect signature (.progress pid) := by
  intro state residual hRelated
  cases hRelated <;>
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      PactType.CanCompleteBeforeTock]

theorem compilationCompletingCorrect_var
    (signature : TypeAlphabet) (name : String) :
    CompilationCompletingCorrect signature (.var name) := by
  intro state residual hRelated
  cases hRelated
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    PactType.CanCompleteBeforeTock]

/-- The raw constructor-fragment form of step correspondence.  It is the
compositional interface used before the public alphabet filter is applied. -/
def CompilationFragmentStepCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    TypeCompilationRelation processType state residual →
    env ∈ signature.localEnvironments →
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        fragment.HasResolvedEdge state env label offers state' ∧
        TypeCompilationRelation processType state' residual')

private theorem computeFuture_eq_empty_of_edges_empty
    (automaton : PendingAutomaton)
    (hEmpty : ∀ edge ∈ automaton.edges,
      edge.current = ∅ ∧ edge.future = .explicit ∅)
    (state : TypeAutomatonState) :
    computeFuture automaton state = ∅ := by
  have hExplicit : ∀ edge ∈ automaton.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    exact ⟨∅, (hEmpty edge hEdge).2⟩
  rw [computeFuture_eq_offersAt_of_all_explicit automaton hExplicit]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro action hAction
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter] at hAction
  rcases hAction with ⟨edge, ⟨hEdge, _⟩, hOffer⟩
  obtain ⟨hCurrent, hFuture⟩ := hEmpty edge hEdge
  simp [hCurrent, hFuture] at hOffer

/-- Future correctness for `skip`. -/
theorem compilationFutureCorrect_skip (signature : TypeAlphabet) :
    CompilationFutureCorrect signature .skip := by
  intro state residual hRelated
  cases hRelated
  let fragment := compileTypeFuel signature (typeCompilationFuel .skip) .skip
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  change computeFuture pending .root = typeFutureOffers .skip
  rw [computeFuture_eq_offersAt_of_all_explicit pending]
  · ext action
    simp [pending, fragment, PendingAutomaton.offersAt,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      typeFutureOffers, typeFutureOffersFuel]
  · intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with ⟨_, _, rfl⟩
    exact ⟨∅, rfl⟩

/-- Future correctness for an atomic progress marker. -/
theorem compilationFutureCorrect_progress
    (signature : TypeAlphabet) (pid : ProcId) :
    CompilationFutureCorrect signature (.progress pid) := by
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.progress pid)) (.progress pid)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hEmpty : ∀ state, computeFuture pending state = ∅ := by
    intro state
    apply computeFuture_eq_empty_of_edges_empty pending
    intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with hAction | hFinal
    · rcases hAction with ⟨_, _, rfl⟩
      exact ⟨rfl, rfl⟩
    · rcases hFinal with ⟨_, _, rfl⟩
      exact ⟨rfl, rfl⟩
  intro state residual hRelated
  change computeFuture pending state = typeFutureOffers residual
  cases hRelated <;>
    simpa [typeFutureOffers, typeFutureOffersFuel] using hEmpty _

/-- Future correctness for the clock constructor. -/
theorem compilationFutureCorrect_tock (signature : TypeAlphabet) :
    CompilationFutureCorrect signature .tock := by
  let fragment := compileTypeFuel signature
    (typeCompilationFuel .tock) .tock
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hEmpty : ∀ state, computeFuture pending state = ∅ := by
    intro state
    apply computeFuture_eq_empty_of_edges_empty pending
    intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with hAction | hFinal
    · rcases hAction with ⟨environment, _, rfl⟩
      by_cases hClock : environment.clock = true <;>
        simp [hClock]
    · rcases hFinal with ⟨_, _, rfl⟩
      exact ⟨rfl, rfl⟩
  intro state residual hRelated
  change computeFuture pending state = typeFutureOffers residual
  cases hRelated <;>
    simpa [typeFutureOffers, typeFutureOffersFuel] using hEmpty _

/-- Future correctness for an atomic message. -/
theorem compilationFutureCorrect_message
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CompilationFutureCorrect signature (.message msg dir) := by
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.message msg dir)) (.message msg dir)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hExplicit : ∀ edge ∈ pending.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with hFiring | hWaiting | hFinal
    · rcases hFiring with ⟨_, _, rfl⟩
      exact ⟨∅, rfl⟩
    · rcases hWaiting with ⟨_, _, rfl⟩
      exact ⟨∅, rfl⟩
    · rcases hFinal with ⟨_, _, rfl⟩
      exact ⟨∅, rfl⟩
  intro state residual hRelated
  change computeFuture pending state = typeFutureOffers residual
  rw [computeFuture_eq_offersAt_of_all_explicit pending hExplicit]
  cases hRelated with
  | message_source =>
      ext action
      constructor
      · intro hAction
        simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
          Finset.mem_filter] at hAction
        rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
        simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment] at hEdge
        rcases hEdge with hFiring | hWaiting | hFinal
        · rcases hFiring with ⟨_, _, rfl⟩
          simpa using hOffer
        · rcases hWaiting with ⟨_, _, rfl⟩
          simpa using hOffer
        · rcases hFinal with ⟨_, _, rfl⟩
          simp at hSource
      · intro hAction
        simp only [typeFutureOffers, typeFutureOffersFuel,
          Finset.mem_singleton] at hAction
        subst action
        simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
          Finset.mem_filter]
        let emptyEdge : PendingAutomatonEdge :=
          { source := .root
            environment := TypeEnvironment.empty
            label := .visible TypeLabel.silent
            current := {(msg, dir)}
            future := .explicit ∅
            target := .root }
        refine ⟨emptyEdge, ?_, ?_⟩
        · constructor
          · simp [pending, fragment, emptyEdge, typeCompilationFuel,
              compileTypeFuel, finishAutomatonFragment,
              TypeAlphabet.localEnvironments,
              TypeAlphabet.localEnvironmentActions,
              TypeEnvironment.empty, TypeEnvironment.hasNeed]
          · rfl
        · simp [emptyEdge, AutomatonConstructionLabel.semantic,
            TypeLabel.silent]
  | message_final =>
      change pending.offersAt .final = ∅
      rw [Finset.eq_empty_iff_forall_notMem]
      intro action hAction
      simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
        Finset.mem_filter] at hAction
      rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
      simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment] at hEdge
      rcases hEdge with hFiring | hWaiting | hFinal
      · rcases hFiring with ⟨_, _, rfl⟩
        simp at hSource
      · rcases hWaiting with ⟨_, _, rfl⟩
        simp at hSource
      · rcases hFinal with ⟨_, _, rfl⟩
        simp at hOffer

/-- Future correctness for a free-variable marker fragment. -/
theorem compilationFutureCorrect_var
    (signature : TypeAlphabet) (name : String) :
    CompilationFutureCorrect signature (.var name) := by
  intro state residual hRelated
  cases hRelated
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.var name)) (.var name)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  change computeFuture pending .root = typeFutureOffers (.var name)
  rw [computeFuture_eq_offersAt_of_all_explicit pending]
  · ext action
    simp [pending, fragment, PendingAutomaton.offersAt,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      typeFutureOffers, typeFutureOffersFuel]
  · intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with ⟨_, _, rfl⟩
    exact ⟨∅, rfl⟩

end

end Pact
