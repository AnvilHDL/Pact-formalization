import Anvilpp.PactTypes.Automata.TypeAlphabetDefs

namespace Pact

noncomputable section

namespace PactTypeAlphabet

  /-- `TypeEnvironment.tock` is the only clocked environment over one type's
  alphabet: every other member is built with `clock := false`. -/
  theorem eq_tock_of_mem_localEnvironments_of_clock
      {alphabet : PactTypeAlphabet} {environment : TypeEnvironment}
      (hEnvironment : environment ∈ alphabet.localEnvironments)
      (hClock : environment.clock = true) :
      environment = TypeEnvironment.tock := by
    simp only [localEnvironments, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
      at hEnvironment
    rcases hEnvironment with hTock | ⟨immediate, _, future, _, rfl⟩
    · exact hTock
    · exact absurd hClock (by simp)

  /-- A clocked environment over one type's alphabet offers nothing immediately. -/
  theorem immediate_eq_empty_of_mem_localEnvironments_of_clock
      {alphabet : PactTypeAlphabet} {environment : TypeEnvironment}
      (hEnvironment : environment ∈ alphabet.localEnvironments)
      (hClock : environment.clock = true) :
      environment.immediate = ∅ := by
    rw [eq_tock_of_mem_localEnvironments_of_clock hEnvironment hClock]
    rfl

  /-- Environments over one type's alphabet are well formed. -/
  theorem environment_wellFormed {alphabet : PactTypeAlphabet}
      {environment : TypeEnvironment}
      (hEnvironment : environment ∈ alphabet.localEnvironments) :
      environment.WellFormed alphabet := by
    simp only [localEnvironments, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
      at hEnvironment
    rcases hEnvironment with rfl | ⟨immediate, hImmediateSub, future, hFuture, rfl⟩
    · simp [TypeEnvironment.WellFormed, TypeEnvironment.tock]
    · refine ⟨by simp, ?_, hImmediateSub, hFuture.trans Finset.sdiff_subset⟩
      intro _
      change immediate ∩ future = ∅
      rw [← Finset.disjoint_iff_inter_eq_empty]
      apply Finset.disjoint_left.mpr
      intro action hImmediate hFutureMember
      have hAvailable := hFuture hFutureMember
      simp only [Finset.mem_sdiff] at hAvailable
      exact hAvailable.2 hImmediate

end PactTypeAlphabet

@[simp] theorem PactType.mem_transitionAlphabet_iff
    (processType : PactType) (environment : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    TypeAutomatonSymbol.mk environment label offers ∈
        processType.transitionAlphabet ↔
      environment ∈ processType.alphabet.localEnvironments ∧
      label ∈ processType.labels ∧
      offers ∈ processType.alphabet.localOfferSummaries := by
  classical
  simp [PactType.transitionAlphabet]

end

end Pact
