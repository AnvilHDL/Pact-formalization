import Anvilpp.ProofHelpers
import Anvilpp.PactTypes.NewCorrespondence.TypeAutoRelCore
import Anvilpp.PactTypes.NewCorrespondence.CasesTop
import Anvilpp.PactSafetyStructures

/-!
# Communication safety

Supporting definitions live in `Anvilpp/ProofHelpers.lean`.
-/

namespace Pact

noncomputable section

open Classical

/-! ## Type inference, refinement, and checking -/

/-- Lemma 4.1, "Strategy transfer": honest winning strategies transfer from
types to processes along conformance.

The proof follows `pactproofdetails.typ` step for step.  Build `S_P` from
`S_τ` by concretizing each chosen erased environment (Helper Lemma H3, using
the representative `γ` of Helper Lemma H2).  Take an arbitrary completed
process log `ℓ_P` under `S_P`; Helper Lemma H4 supplies a completed type log
`ℓ_τ` under `S_τ` with `Erase(ℓ_P) = ℓ_τ`.  Since `S_τ` ensures `Φ`, we get
`ℓ_τ ∈ Φ`, and since `Φ` is value-oblivious — membership depends only on the
erased log — also `ℓ_P ∈ Φ`.  Honesty of `ℓ_P` is Helper Lemma H5 applied to
the honest `ℓ_τ`.  As `ℓ_P` was arbitrary, `S_P` is honest and ensures `Φ`. -/
theorem strategy_transfer
    {process : Proc} {processType : PactType} {objective : ProcessObjective}
    (hConforms : Conforms process processType)
    (hOblivious : ValueOblivious objective)
    (hTypeStrategy :
      ∃ strategy : TypeStrategy,
        HonestTypeStrategy processType strategy ∧
        ∀ log, CompletedTypeLog processType strategy log →
          ErasedObjective objective log) :
    ∃ strategy : ProcessStrategy process,
      HonestProcessStrategy strategy ∧
      ∀ log, CompletedProcessLog strategy log → log ∈ objective := by
  obtain ⟨typeStrategy, hHonestType, hEnsures⟩ := hTypeStrategy
  -- Build `S_P` from `S_τ` by concretizing each chosen erased environment
  -- (Helper Lemma H3, via `helper_h2`'s representative `γ`).
  refine ⟨concretizingStrategy processType typeStrategy, ?_, ?_⟩
  · -- Honesty: the matching completed type log is honest (`S_τ` is honest),
    -- and honesty is preserved by concretization (Helper Lemmas H4, H5).
    intro log hCompleted
    obtain ⟨typeLog, hCompletedType, hErase⟩ :=
      helper_h4_completed_process_logs_erase hConforms.some typeStrategy hCompleted
    exact helper_h5_honesty_preserved_by_concretization hErase
      (hHonestType typeLog hCompletedType)
  · -- The objective: `S_τ` ensures `Φ` on the matching type log, and `Φ` is
    -- value-oblivious, so it depends only on the erased log (Helper Lemma H4).
    intro log hCompleted
    obtain ⟨typeLog, hCompletedType, hErase⟩ :=
      helper_h4_completed_process_logs_erase hConforms.some typeStrategy hCompleted
    obtain ⟨witnessLog, hWitnessErase, hWitnessMem⟩ := hEnsures typeLog hCompletedType
    exact (hOblivious log witnessLog (hErase.trans hWitnessErase.symm)).mpr hWitnessMem

/-- Lemma 4.2, "Soundness of inferred types": `WFProc(P) ⟹ P ⊧ abs(P)`. -/
theorem inferred_type_soundness {process : Proc} (hWF : WFProc process) :
    Conforms process (inferProcess process) := by
  induction hSize : sizeOf process using Nat.strong_induction_on
      generalizing process with
    | _ n ih =>
      cases process with
      | _ => sorry
/-- Lemma 4.3, "Conformance is closed under refinement". -/
theorem conformance_closed_under_refinement
    {process : Proc} {precise abstract : PactType}
    (hConforms : Conforms process precise)
    (hRefines : Refines precise abstract) :
    Conforms process abstract := by
    let witness_relation_fun :  Proc → PactType → Prop := fun p τ =>
      ∃ τ', hConforms.some.relation p τ' ∧ hRefines.some.relation τ' τ
    exact ⟨{
      relation := witness_relation_fun
      initial := by
        have hProcPreciseInitial := hConforms.some.initial
        have hPreciseAbsRefinesInitial := hRefines.some.initial
        refine ⟨precise, hProcPreciseInitial, hPreciseAbsRefinesInitial⟩
      readyReflect := by
        intro p τ hWitnessEnv hWitnessRel hTypeReady
        rcases hWitnessRel with ⟨τ', hConformRel, hRefineRel⟩
        have hPreciseReady : TypeReady (eraseEnvironment hWitnessEnv) τ' := by
          -- Ready abstract type gives us a transition
          rcases hTypeReady with ⟨label, target, hStep⟩
          -- H17 decorates that transition
          obtain ⟨offers, hDecoratedStep⟩ := helper_h17_every_type_step_has_decoration hStep
          -- Refinement availability transfers the transition
          -- from τ back to τ'
          obtain ⟨target', hDecoratedStep'⟩ :=
            hRefines.some.availability hRefineRel hDecoratedStep
          -- A decorated transition contains/is backed by an ordinary transition.
          -- Need to extract it and rebuild TypeReady here.
          exact ⟨label, target', hDecoratedStep'.1⟩
        exact hConforms.some.readyReflect
          hConformRel hPreciseReady
      matchStep := by
        intro p p' τ hWitnessEnv label hConformWitnessRel hProcessStep
        -- Given p ⊧ τ there exists τ₀ such that p ⊧ τ₀ and τ τ₀ in R
        rcases hConformWitnessRel with ⟨τₒ , hConformRel, hRefineRel⟩
        obtain ⟨τ₁, hPrecTypeStep, hPrecConformRel'⟩ :=
          helper_h9_one_step_conformance_match
          hConforms.some
          hConformRel hProcessStep
        -- Given τ τ₀ in R and τ₀ -> τ₁, then we can use h10 to
        --  obtain τ' such that τ -> τ' and τ₁ τ' in R
        obtain ⟨τ', hTypeTrans, hRefineRel'⟩ :=
          helper_h10_refinement_response_coherence
            hRefines.some hRefineRel hPrecTypeStep
        exact ⟨τ', hTypeTrans, ⟨τ₁, hPrecConformRel', hRefineRel'⟩⟩
    }
    ⟩


/-- Lemma 4.4, "Soundness of type checking":
`WFProc(P) ∧ checkdo(P,τ) ⟹ P ⊧ τ`. -/
theorem type_checking_soundness
    {process : Proc} {claimed : PactType} (hWF : WFProc process)
    (hChecks : DataObliviousChecks process claimed) :
    Conforms process claimed := by
  have hPreciseConfirms : Conforms process (inferProcess process) := by
    simpa using inferred_type_soundness hWF
  have hRefines : Refines (inferProcess process) claimed := by
    simpa using hChecks
  simpa using conformance_closed_under_refinement hPreciseConfirms hRefines

/-- Theorem 4.1, "Decidability and complexity of type inference and
checking": inference and checking are decidable; inference runs in `O(|P|)`
and checking (given explicit automata of sizes `m`, `n`) in `O(mn)`. -/
theorem inference_checking_decidable_and_efficient
    (process : Proc) (claimed : PactType) :
    (∃ answer : Bool, answer = true ↔ DataObliviousChecks process claimed) ∧
    RunsInLinearTime inferProcess ∧
    RunsInProductTime refinementChecker := by
  sorry

/-! ## Type compatibility checking -/

/-- Proposition 4.1, "Regularity of the log objective": `Ω_T` is
omega-regular. -/
theorem log_objective_regular
    (initial : PactType) (progress : Finset ProcId) :
    OmegaRegular initial progress := by
  sorry

/-- Lemma 4.5, "Type--automaton correspondence". -/
theorem type_automaton_correspondence
     {processType : PactType}
    (hAdmissible : AdmissibleType processType) :
    Nonempty
      (TypeAutomatonCorrespondence processType
        (compileType processType)) := by
  -- The automaton
  let typeAutomaton := compileType processType
  -- The relation set
  let relation_set : Finset (PactType × TypeAutomatonState) :=
    buildRelationSet processType typeAutomaton
  -- proof witness
  exact ⟨{
      relation := relationMembership relation_set
      initial := by
        simpa [relation_set, typeAutomaton] using
          buildRelationSet_initial processType typeAutomaton
      initial_mem := by
        have hInitialRelated :
            relationMembership
              (buildRelationSet processType (compileType processType))
              processType (compileType processType).initial := by
          simpa using
            buildRelationSet_initial processType
              (compileType processType)
        simpa [typeAutomaton] using
          helper_h12_compiled_state_shape hInitialRelated
      forward := by
        intro residual residual' state env label offers hRelated hStep
        exact (correspondence_steps processType hAdmissible).1
          (by simpa [relation_set, typeAutomaton] using hRelated) hStep
      backward := by
        intro residual state state' env label offers hRelated hEdge
        exact (correspondence_steps processType hAdmissible).2
          (by simpa [relation_set, typeAutomaton] using hRelated)
          (by simpa [typeAutomaton] using hEdge)
    }⟩

#print axioms type_automaton_correspondence
/-- Lemma 4.6, "Process--automaton correspondence": conforming processes
simulate into the type automaton. -/
theorem process_automaton_correspondence
     {process : Proc} {processType : PactType}
    (hAdmissible : AdmissibleType processType)
    (hConforms : Conforms process processType) :
    Nonempty
      (ProcessAutomatonCorrespondence
        process processType (compileType processType)) := by
  sorry

/-- Theorem 4.2, "Correctness of the game reduction": the honesty-aware
Rabin game exactly captures semantic compatibility. -/
theorem game_reduction_correctness
     (initial : PactType) (progress : Finset ProcId) :
    TypeCompatible initial progress ↔
      SemanticTypeCompatible initial progress := by
  sorry

/-- Theorem 4.3, "Soundness of type compatibility" (the main soundness
theorem): conformance of the fixed process composition plus compatibility of
the matching type composition implies communication safety of the processes. -/
theorem type_compatibility_soundness
     {process : Proc} {processType : PactType}
    {progress : Finset ProcId}
    (hConforms : Conforms process processType)
    (hCompatible : TypeCompatible processType progress) :
    ProcessCompatible process progress := by
  sorry

/-- Theorem 4.4, "Decidability and complexity of compatibility": for a
monitored game with `N` vertices, `M` edges, and `K = 1+2|cal(Eta)(Θ_0)|`
Rabin pairs, compatibility is decidable in `Õ(MN(K!)^{1+o(1)})` time. -/
theorem type_compatibility_decidable_and_efficient
     (processType : PactType) (progress : Finset ProcId) :
    (∃ answer : Bool,
      answer = true ↔ TypeCompatible processType progress) ∧
    CompatibilityGameComplexityBound processType progress := by
  sorry

/-! ## Optimality of inferred types -/

/-- Lemma 4.7, "Compatibility is monotone under type refinement". -/
theorem compatibility_monotone_under_refinement
     {precise abstract : List PactType}
    {interfaces : List Interface} {progress : Finset ProcId}
    (hRefines : ComponentwiseRefines precise abstract)
    (hCompatible : TypeTupleCompatible abstract interfaces progress) :
    TypeTupleCompatible precise interfaces progress := by
  sorry

/-- Theorem 4.5, "Optimality of inferred types". -/
theorem inferred_types_optimal
     (processes : List Proc) (interfaces : List Interface)
    (progress : Finset ProcId) :
    TypeTupleCompatible (processes.map inferProcess) interfaces progress ↔
      ∃ claimedTypes,
        List.Forall₂
          (fun process claimed => DataObliviousChecks process claimed)
          processes claimedTypes ∧
        TypeTupleCompatible claimedTypes interfaces progress := by
  sorry

/-- Corollary 4.1, "Failure rules out data-oblivious proofs". -/
theorem inferred_failure_rules_out_data_oblivious_proofs
     {processes : List Proc} {interfaces : List Interface}
    {progress : Finset ProcId}
    (hFailure :
      ¬ TypeTupleCompatible (processes.map inferProcess) interfaces
        progress) :
    ¬ ∃ claimedTypes,
        List.Forall₂
          (fun process claimed => DataObliviousChecks process claimed)
          processes claimedTypes ∧
        TypeTupleCompatible claimedTypes interfaces progress := by
  sorry

end

end Pact
