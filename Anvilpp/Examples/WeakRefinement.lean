import Mathlib.Logic.Relation
import Anvilpp.PactTypes.Proofs.Syntax.TypeTransitionSystemLemmas
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.TypeWellFormedIn
import Anvilpp.ProofHelpers.Honesty

namespace Pact

noncomputable section

open Classical

/-- A finite sequence of silent steps under one fixed environment. -/
abbrev TypeSilentSteps (env : TypeEnvironment) : PactType → PactType → Prop :=
  Relation.ReflTransGen (fun source target =>
    TypeTransition env source TypeLabel.silent target)

/-- Silent steps before and after one labelled step, all under the same environment. -/
def TypeWeakTransition (env : TypeEnvironment) (source : PactType)
    (label : TypeLabel) (target : PactType) : Prop :=
  (label = TypeLabel.silent ∧ TypeSilentSteps env source target) ∨
    ∃ before after,
      TypeSilentSteps env source before ∧
      TypeTransition env before label after ∧
      TypeSilentSteps env after target

/-- Every ordinary transition is a weak transition. -/
theorem TypeTransition.toWeak {env : TypeEnvironment} {source target : PactType}
    {label : TypeLabel} (step : TypeTransition env source label target) :
    TypeWeakTransition env source label target :=
  Or.inr ⟨source, target, .refl, step, .refl⟩

/-- A silent path cannot leave a source with no silent transition. -/
theorem TypeSilentSteps.eq_of_no_silent {env : TypeEnvironment}
    {source target : PactType}
    (noSilent : ∀ next, ¬ TypeTransition env source TypeLabel.silent next)
    (steps : TypeSilentSteps env source target) : target = source := by
  rcases steps.cases_head with hEq | ⟨next, step, _⟩
  · exact hEq.symm
  · exact (noSilent next step).elim

/-- With no initial silent step, a visible weak step starts with an ordinary matching step. -/
theorem TypeWeakTransition.first_of_no_silent {env : TypeEnvironment}
    {source target : PactType} {label : TypeLabel}
    (visible : label ≠ TypeLabel.silent)
    (noSilent : ∀ next, ¬ TypeTransition env source TypeLabel.silent next)
    (step : TypeWeakTransition env source label target) :
    ∃ next, TypeTransition env source label next := by
  rcases step with ⟨hSilent, _⟩ | ⟨before, after, hPrefix, step, _⟩
  · exact (visible hSilent).elim
  · have hEq := hPrefix.eq_of_no_silent noSilent
    subst before
    exact ⟨after, step⟩

/-- Keeping the environment after a silent step satisfies retained-offer honesty. -/
theorem TypeEnvironment.available_subset_silent_remainder (env : TypeEnvironment) :
    env.immediate ∪ env.future ⊆ env.honestyRemainder TypeLabel.silent := by
  rw [TypeEnvironment.honestyRemainder_silent, Finset.union_comm]

namespace WeakRefinement

def progress (pid : ProcId) : PactType := .progress PactTypeAlphabet.empty pid

def delayedProgress (pid : ProcId) : PactType :=
  .seq PactTypeAlphabet.empty (.skip PactTypeAlphabet.empty) (progress pid)

def progressPair : PactType :=
  .par PactTypeAlphabet.empty (progress 0) (progress 1) ∅

def delayedProgressPair : PactType :=
  .par PactTypeAlphabet.empty (delayedProgress 0) (progress 1) ∅

/-- Both products satisfy all type well-formedness conditions. -/
theorem progressPairs_wellFormed :
    TypeWellFormedIn [] delayedProgressPair ∧ TypeWellFormedIn [] progressPair := by
  have hAlphabet : PactTypeAlphabet.ParallelCompatible PactTypeAlphabet.empty
      PactTypeAlphabet.empty PactTypeAlphabet.empty ∅ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [PactTypeAlphabet.empty]
    · simp [PactTypeAlphabet.ComplementaryOn]
    · rfl
    · rfl
  simp [TypeWellFormedIn, delayedProgressPair, progressPair, delayedProgress,
    progress, PactType.AlphabetWellFormed, PactType.alphabet,
    PactTypeAlphabet.WellFormed, PactTypeAlphabet.OnePolarity, PactTypeAlphabet.empty,
    PactType.AllVariablesBound, PactType.BinderHygienic, PactType.TailClosed,
    PactType.TailOccurrences, PactType.ClockGuarded, PactType.TailRecursive,
    PactType.SameCycleMessageLinear, PactType.PrefixMessageIds, PactType.SuffixMessageIds,
    PactType.ProgressLinear, PactType.ProgressIds, PactType.FairChoiceLinear,
    PactType.FairChoiceIds, PactType.ParallelMessageOwnership, PactType.MessageIds,
    PactType.ParallelProgressOwnership, PactType.ParallelFairChoiceOwnership,
    PactType.InterfaceScoped, PactType.InterfaceAlphabetScoped,
    PactTypeAlphabet.messageIds, PactType.ParallelInterfaces,
    PactType.ConjunctiveMessageOwnership, OfferMenuLinear]
  exact hAlphabet

/-- The two products have the same alphabet, progress identifiers, and fair-choice identifiers. -/
theorem progressPairs_sameDeclarations :
    delayedProgressPair.alphabet = progressPair.alphabet ∧
    delayedProgressPair.ProgressIds = progressPair.ProgressIds ∧
    delayedProgressPair.FairChoiceIds = progressPair.FairChoiceIds := by
  simp [delayedProgressPair, progressPair, delayedProgress, progress,
    PactType.alphabet, PactType.ProgressIds, PactType.FairChoiceIds]

private theorem progress_transition_iff {env : TypeEnvironment}
    {alphabet : PactTypeAlphabet} {pid : ProcId} {label : TypeLabel} {target : PactType} :
    TypeTransition env (.progress alphabet pid) label target ↔
      env.WellFormed alphabet ∧ env.clock = false ∧
      label = TypeLabel.progress pid ∧ target = .skip alphabet := by
  constructor
  · intro step
    cases step with
    | progress _ _ _ hWF hClock => exact ⟨hWF, hClock, rfl, rfl⟩
  · rintro ⟨hWF, hClock, rfl, rfl⟩
    exact TypeTransition.progress _ _ _ hWF hClock

private theorem empty_wellFormed :
    TypeEnvironment.empty.WellFormed PactTypeAlphabet.empty := by
  simp [TypeEnvironment.WellFormed, TypeEnvironment.empty]

private theorem empty_local (source : PactType) :
    LocalTypeOfferEnvironment TypeEnvironment.empty ∅ source
      TypeEnvironment.empty ∅ ∅ TypeEnvironment.empty := by
  apply LocalTypeOfferEnvironment.ordinary <;>
    simp [TypeEnvironment.empty, restrictTypeOffers]

private theorem skip_prefix_step {env : TypeEnvironment} {pid : ProcId}
    (hWF : env.WellFormed PactTypeAlphabet.empty) (hClock : env.clock = false) :
    TypeTransition env (delayedProgress pid) TypeLabel.silent (progress pid) :=
  TypeTransition.seq_fuse _ _ _ _ _ _ (TypeTransition.skip _ _ ⟨hWF, hClock⟩)

/-- A leading skip can precede a progress step within a fixed-environment weak step. -/
theorem delayedProgress_weak_step {env : TypeEnvironment} (pid : ProcId)
    (hWF : env.WellFormed PactTypeAlphabet.empty) (hClock : env.clock = false) :
    TypeWeakTransition env (delayedProgress pid) (TypeLabel.progress pid)
      (.skip PactTypeAlphabet.empty) := by
  exact Or.inr ⟨progress pid, .skip PactTypeAlphabet.empty,
    .single (skip_prefix_step hWF hClock),
    TypeTransition.progress _ _ _ hWF hClock, .refl⟩

/-- The delayed product first emits only its right component's progress observation. -/
theorem delayedProgressPair_step :
    TypeTransition TypeEnvironment.empty delayedProgressPair (TypeLabel.progress 1)
      (.par PactTypeAlphabet.empty (progress 0) (.skip PactTypeAlphabet.empty) ∅) := by
  have leftOffers : TypeOffers TypeEnvironment.empty (delayedProgress 0)
      TypeLabel.silent (progress 0) ∅ ∅ := by
    simpa [delayedProgress, progress, sequenceRightMenu, typeFutureOffers,
      typeFutureOffersFuel] using
      TypeOffers.seq_fuse TypeEnvironment.empty PactTypeAlphabet.empty
        PactTypeAlphabet.empty (.skip PactTypeAlphabet.empty) (progress 0)
        TypeLabel.silent ∅ ∅
        (TypeOffers.skip _ _ ⟨empty_wellFormed, rfl⟩) (by simp [TypeLabel.silent])
  have rightOffers : TypeOffers TypeEnvironment.empty (progress 1)
      (TypeLabel.progress 1) (.skip PactTypeAlphabet.empty) ∅ ∅ := by
    simpa [progress, typeFutureOffers, typeFutureOffersFuel] using
      TypeOffers.progress TypeEnvironment.empty PactTypeAlphabet.empty 1
        ⟨empty_wellFormed, rfl⟩
  have step := TypeTransition.par TypeEnvironment.empty TypeEnvironment.empty
    TypeEnvironment.empty ∅ PactTypeAlphabet.empty
    (delayedProgress 0) (progress 0) (progress 1) (.skip PactTypeAlphabet.empty)
    TypeLabel.silent (TypeLabel.progress 1) ∅ ∅ ∅ ∅
    (by simp [delayedProgress]) (by simp [progress])
    (skip_prefix_step empty_wellFormed rfl) leftOffers
    (TypeTransition.progress _ _ _ empty_wellFormed rfl) rightOffers
    (by simp [progress])
    ⟨empty_wellFormed, empty_local _, empty_local _, by
      simp [TypeLabel.Sync, TypeLabel.silent, TypeLabel.progress, TypeLabel.isTock]⟩
  simpa [delayedProgressPair, TypeLabel.combine, TypeLabel.synced,
    TypeLabel.silent, TypeLabel.progress, TypeLabel.isRawSyncedMessage] using step

/-- Every step of the undelayed product emits both progress observations together. -/
theorem progressPair_step_label {env : TypeEnvironment} {label : TypeLabel}
    {target : PactType} (step : TypeTransition env progressPair label target) :
    label = .actions {TypeObservation.progress 0, TypeObservation.progress 1} := by
  change TypeTransition env (.par _ (progress 0) (progress 1) ∅) label target at step
  cases step <;>
    simp_all [progress_transition_iff, progress, PactType.alphabet,
      TypeLabel.combine, TypeLabel.synced, TypeLabel.progress,
      TypeLabel.isRawSyncedMessage]
  simp [Finset.filter_insert, Finset.filter_singleton, Finset.pair_comm]

/-- Silent padding cannot make the undelayed product emit only the right observation. -/
theorem progressPair_no_weak_right_step {env : TypeEnvironment} {target : PactType} :
    ¬ TypeWeakTransition env progressPair (TypeLabel.progress 1) target := by
  intro step
  have noSilent : ∀ next, ¬ TypeTransition env progressPair TypeLabel.silent next := by
    intro next hStep
    have hLabel := progressPair_step_label hStep
    have hContains := congrArg (fun label => label.contains (.progress 0)) hLabel
    simp [TypeLabel.contains, TypeLabel.silent] at hContains
  obtain ⟨next, hStep⟩ := step.first_of_no_silent
    (by simp [TypeLabel.progress, TypeLabel.silent]) noSilent
  have hLabel := progressPair_step_label hStep
  have hContains := congrArg (fun label => label.contains (.progress 0)) hLabel
  simp [TypeLabel.contains, TypeLabel.progress] at hContains

/-- The delayed product finishes in a second round containing the left observation. -/
theorem delayedProgressPair_finish :
    TypeTransition TypeEnvironment.empty
      (.par PactTypeAlphabet.empty (progress 0) (.skip PactTypeAlphabet.empty) ∅)
      (TypeLabel.progress 0) (.skip PactTypeAlphabet.empty) := by
  have hOffers : TypeOffers TypeEnvironment.empty (progress 0)
      (TypeLabel.progress 0) (.skip PactTypeAlphabet.empty) ∅ ∅ := by
    simpa [progress, typeFutureOffers, typeFutureOffersFuel] using
      TypeOffers.progress TypeEnvironment.empty PactTypeAlphabet.empty 0
        ⟨empty_wellFormed, rfl⟩
  have hSkipOffers : TypeOffers TypeEnvironment.empty (.skip PactTypeAlphabet.empty)
      TypeLabel.silent (.skip PactTypeAlphabet.empty) ∅ ∅ := by
    simpa [typeFutureOffers, typeFutureOffersFuel] using
      TypeOffers.skip TypeEnvironment.empty PactTypeAlphabet.empty ⟨empty_wellFormed, rfl⟩
  have hStep := TypeTransition.par_fuse TypeEnvironment.empty TypeEnvironment.empty
    TypeEnvironment.empty ∅ PactTypeAlphabet.empty (progress 0) (.skip PactTypeAlphabet.empty)
    (TypeLabel.progress 0) TypeLabel.silent ∅ ∅ ∅ ∅
    (TypeTransition.progress _ _ _ empty_wellFormed rfl) hOffers
    (TypeTransition.skip _ _ ⟨empty_wellFormed, rfl⟩) hSkipOffers
    ⟨empty_wellFormed, empty_local _, empty_local _, by
      simp [TypeLabel.Sync, TypeLabel.silent, TypeLabel.progress, TypeLabel.isTock]⟩
  simpa [TypeLabel.combine, TypeLabel.synced, TypeLabel.silent, TypeLabel.progress,
    TypeLabel.isRawSyncedMessage] using hStep

/-- The undelayed product emits both observations and finishes in one round. -/
theorem progressPair_step :
    TypeTransition TypeEnvironment.empty progressPair
      (.actions {TypeObservation.progress 0, TypeObservation.progress 1})
      (.skip PactTypeAlphabet.empty) := by
  have hOffers (pid : ProcId) : TypeOffers TypeEnvironment.empty (progress pid)
      (TypeLabel.progress pid) (.skip PactTypeAlphabet.empty) ∅ ∅ := by
    simpa [progress, typeFutureOffers, typeFutureOffersFuel] using
      TypeOffers.progress TypeEnvironment.empty PactTypeAlphabet.empty pid
        ⟨empty_wellFormed, rfl⟩
  have hStep := TypeTransition.par_fuse TypeEnvironment.empty TypeEnvironment.empty
    TypeEnvironment.empty ∅ PactTypeAlphabet.empty (progress 0) (progress 1)
    (TypeLabel.progress 0) (TypeLabel.progress 1) ∅ ∅ ∅ ∅
    (TypeTransition.progress _ _ _ empty_wellFormed rfl) (hOffers 0)
    (TypeTransition.progress _ _ _ empty_wellFormed rfl) (hOffers 1)
    ⟨empty_wellFormed, empty_local _, empty_local _, by
      simp [TypeLabel.Sync, TypeLabel.progress, TypeLabel.isTock]⟩
  simpa [progressPair, TypeLabel.combine, TypeLabel.synced, TypeLabel.progress,
    TypeLabel.isRawSyncedMessage, Finset.filter_insert, Finset.filter_singleton,
    Finset.pair_comm] using hStep

/-- Skip elimination and parallel congruence cannot both preserve weak responses with exact labels. -/
theorem no_skip_eliminating_parallel_refinement
    (relation : PactType → PactType → Prop)
    (eliminateSkip : relation (delayedProgress 0) (progress 0))
    (parallel : relation (delayedProgress 0) (progress 0) →
      relation delayedProgressPair progressPair)
    (response : ∀ {source abstract target env label},
      relation source abstract → TypeTransition env source label target →
      ∃ abstractTarget, TypeWeakTransition env abstract label abstractTarget ∧
        relation target abstractTarget) : False := by
  obtain ⟨_, hWeak, _⟩ := response (parallel eliminateSkip) delayedProgressPair_step
  exact progressPair_no_weak_right_step hWeak

end WeakRefinement

end

end Pact
