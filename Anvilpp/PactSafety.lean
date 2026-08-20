import Anvilpp.PactSafetyHelpers
import Anvilpp.PactTypes.NewCorrespondence.TypeAutoRelCore
import Anvilpp.PactTypes.NewCorrespondence.CasesTop
import Anvilpp.PactSafetyStructures

/-!
# Communication safety: the paper's theorem catalog

Redeveloped to match the current formalism in `pact.typ`, rather than the
earlier, now-superseded uppercase `Pact.pdf` scaffold. This file states the
numbered results exactly as they appear, in order, in `pactproofs.typ`
("Lemmas, Theorems, and Proofs"). All supporting definitions (histories,
strategies, honesty, the `pactcompat.typ` compatibility game, etc.) live in
`Anvilpp/PactSafetyHelpers.lean`. Theorems whose proofs constitute the
research development are intentionally closed with `sorry`.
-/

namespace Pact

noncomputable section

open Classical

/-! ## Type inference, refinement, and checking -/

/-- Lemma 4.1, "Strategy transfer": honest winning strategies transfer from
types to processes along conformance. -/
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
  sorry

/-- Lemma 4.2, "Soundness of inferred types": `WFProc(P) ⟹ P ⊧ abs(P)`. -/
theorem inferred_type_soundness {process : Proc} (hWF : WFProc process) :
    Conforms process (inferProcess process) := by
  sorry

/-- Lemma 4.3, "Conformance is closed under refinement". -/
theorem conformance_closed_under_refinement
    {process : Proc} {precise abstract : PactType}
    (hConforms : Conforms process precise)
    (hRefines : Refines precise abstract) :
    Conforms process abstract := by
  sorry

/-- Lemma 4.4, "Soundness of type checking":
`WFProc(P) ∧ checkdo(P,τ) ⟹ P ⊧ τ`. -/
theorem type_checking_soundness
    {process : Proc} {claimed : PactType} (hWF : WFProc process)
    (hChecks : DataObliviousChecks process claimed) :
    Conforms process claimed := by
  sorry

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

/-- Lemma 4.5 (`pactautomatonconstruction.typ`, "Correspondence theorem"):
operational types and their finite constructor automata correspond. Its proof
is `sorry` pending the supporting `Correspondence/*` development, which is
mid-redevelopment against the doc-accurate `computeFutureOf` automaton
construction. -/
theorem type_automaton_correspondence
    {signature : TypeAlphabet} {processType : PactType}
    (hAdmissible : AdmissibleType signature processType) :
    Nonempty
      (TypeAutomatonCorrespondence processType
        (compileType signature processType)) := by
  -- The automaton
  let typeAutomaton := compileType signature processType
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
              (buildRelationSet processType (compileType signature processType))
              processType (compileType signature processType).initial := by
          simpa using
            buildRelationSet_initial processType
              (compileType signature processType)
        simpa [typeAutomaton] using
          helper_h12_compiled_state_shape signature hInitialRelated
      stepIff := by
        intro residual residual' state env label offers hRelated hSymbol
        -- Now prove step correspondence by the Lemma 4.5 constructor induction.
        simpa [relation_set, typeAutomaton] using
          correspondence_stepIff signature processType hRelated hSymbol
    }⟩

/-- Lemma 4.6, "Process--automaton correspondence": conforming processes
simulate into the type automaton. -/
theorem process_automaton_correspondence
    {signature : TypeAlphabet} {process : Proc} {processType : PactType}
    (hAdmissible : AdmissibleType signature processType)
    (hConforms : Conforms process processType) :
    Nonempty
      (ProcessAutomatonCorrespondence
        process processType (compileType signature processType)) := by
  sorry

/-- Theorem 4.2, "Correctness of the game reduction": the honesty-aware
Rabin game exactly captures semantic compatibility. -/
theorem game_reduction_correctness
    {signature : TypeAlphabet} (initial : PactType) (progress : Finset ProcId) :
    TypeCompatible signature initial progress ↔
      SemanticTypeCompatible initial progress := by
  sorry

/-- Theorem 4.3, "Soundness of type compatibility" (the main soundness
theorem): conformance of the fixed process composition plus compatibility of
the matching type composition implies communication safety of the processes. -/
theorem type_compatibility_soundness
    {signature : TypeAlphabet} {process : Proc} {processType : PactType}
    {progress : Finset ProcId}
    (hConforms : Conforms process processType)
    (hCompatible : TypeCompatible signature processType progress) :
    ProcessCompatible process progress := by
  sorry

/-- Theorem 4.4, "Decidability and complexity of compatibility": for a
monitored game with `N` vertices, `M` edges, and `K = 1+2|cal(Eta)(Θ_0)|`
Rabin pairs, compatibility is decidable in `Õ(MN(K!)^{1+o(1)})` time. -/
theorem type_compatibility_decidable_and_efficient
    (signature : TypeAlphabet) (processType : PactType) (progress : Finset ProcId) :
    (∃ answer : Bool,
      answer = true ↔ TypeCompatible signature processType progress) ∧
    CompatibilityGameComplexityBound signature processType progress := by
  sorry

/-! ## Optimality of inferred types -/

/-- Lemma 4.7, "Compatibility is monotone under type refinement". -/
theorem compatibility_monotone_under_refinement
    {signature : TypeAlphabet} {precise abstract : List PactType}
    {interfaces : List Interface} {progress : Finset ProcId}
    (hRefines : ComponentwiseRefines precise abstract)
    (hCompatible : TypeTupleCompatible signature abstract interfaces progress) :
    TypeTupleCompatible signature precise interfaces progress := by
  sorry

/-- Theorem 4.5, "Optimality of inferred types". -/
theorem inferred_types_optimal
    (signature : TypeAlphabet) (processes : List Proc) (interfaces : List Interface)
    (progress : Finset ProcId) :
    TypeTupleCompatible signature (processes.map inferProcess) interfaces progress ↔
      ∃ claimedTypes,
        List.Forall₂
          (fun process claimed => DataObliviousChecks process claimed)
          processes claimedTypes ∧
        TypeTupleCompatible signature claimedTypes interfaces progress := by
  sorry

/-- Corollary 4.1, "Failure rules out data-oblivious proofs". -/
theorem inferred_failure_rules_out_data_oblivious_proofs
    {signature : TypeAlphabet} {processes : List Proc} {interfaces : List Interface}
    {progress : Finset ProcId}
    (hFailure :
      ¬ TypeTupleCompatible signature (processes.map inferProcess) interfaces
        progress) :
    ¬ ∃ claimedTypes,
        List.Forall₂
          (fun process claimed => DataObliviousChecks process claimed)
          processes claimedTypes ∧
        TypeTupleCompatible signature claimedTypes interfaces progress := by
  sorry

end

end Pact
