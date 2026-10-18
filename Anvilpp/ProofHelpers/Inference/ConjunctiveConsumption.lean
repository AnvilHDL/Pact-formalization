import Anvilpp.ProofHelpers.Inference.AbstractionSubstitution
import Anvilpp.PactTypes.Proofs.Syntax.ConjunctiveResiduals

namespace Pact

noncomputable section

open Classical

/-- Branch abstraction preserves list order and multiplicity. -/
theorem inferBranches_eq_map (branches : List ChoiceBranch) :
    inferBranches branches = branches.map inferBranch := by
  induction branches with
  | nil => simp [inferBranches]
  | cons branch rest ih => simp [inferBranches_action, inferBranch, ih]

/-- Erasure preserves the complete set of immediately enabled indices. -/
theorem typeEnabledBranches_inferBranches (env : Environment) (branches : List ChoiceBranch) :
    typeEnabledBranches (eraseEnvironment env) (inferBranches branches) =
      processEnabledBranches env branches := by
  rw [typeEnabledBranches, inferBranches_eq_map, branchIndices_map]
  rfl

/-- Payload erasure preserves the joint communication label. -/
theorem eraseLabel_processBranchBatchLabel (branches : List ChoiceBranch)
    (selected : Finset Nat) (values : Nat → Bool) :
    eraseLabel (processBranchBatchLabel branches selected values) =
      typeBranchBatchLabel (inferBranches branches) selected := by
  simp only [processBranchBatchLabel, typeBranchBatchLabel, eraseLabel]
  congr 1
  ext observation
  simp [Finset.mem_image, inferBranches_eq_map, List.zipIdx_map,
    List.filter_map, List.map_map, Function.comp_def, inferBranch,
    ChoiceBranch.action, eraseObservation]

/-- A consumed head erases to its continuation, not to another message prefix. -/
theorem inferProcess_consumedProcessBranchAt (alphabet : PactTypeAlphabet)
    (branch : ChoiceBranch) (value : Bool) :
    inferProcess (consumedProcessBranchAt alphabet branch value) =
      (inferBranch branch).2.reannotate alphabet := by
  cases branch <;>
    simp [consumedProcessBranchAt, inferProcess_reannotate, inferProcess_procExprReplace,
      inferBranch, ChoiceBranch.continuation]

/-- An unconsumed head erases to the corresponding optional singleton. -/
theorem inferProcess_optionalProcessBranchAt (alphabet : PactTypeAlphabet)
    (branch : ChoiceBranch) :
    inferProcess (optionalProcessBranchAt alphabet branch) =
      singletonTypeXOfferAt alphabet (inferBranch branch) := by
  cases branch <;>
    simp [optionalProcessBranchAt, Proc.reannotateBranches, inferProcess, inferBranches,
      inferProcess_reannotate, singletonTypeXOfferAt, inferBranch,
      ChoiceBranch.action, ChoiceBranch.getMessageId, ChoiceBranch.getDir,
      ChoiceBranch.continuation]

/-- Erasure commutes with construction of every subset residual. -/
theorem inferProcess_parallelProcessBranchesFiringFrom (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (values : Nat → Bool) (index : Nat)
    (branches : List ChoiceBranch) :
    inferProcess (parallelProcessBranchesFiringFrom alphabet selected values index branches) =
      parallelTypeBranchesFiringFrom alphabet selected index (inferBranches branches) := by
  induction branches generalizing index with
  | nil => simp [parallelProcessBranchesFiringFrom, parallelTypeBranchesFiringFrom,
      inferBranches, inferProcess]
  | cons branch rest ih =>
      cases rest with
      | nil =>
          simp only [inferBranches_action, inferBranches, parallelProcessBranchesFiringFrom,
            parallelTypeBranchesFiringFrom]
          split <;> simp [inferProcess_consumedProcessBranchAt,
            inferProcess_optionalProcessBranchAt, inferBranch]
      | cons next rest =>
          simp only [inferBranches_action, parallelProcessBranchesFiringFrom,
            parallelTypeBranchesFiringFrom, inferProcess]
          rw [ih]
          split <;> simp [inferProcess_consumedProcessBranchAt,
            inferProcess_optionalProcessBranchAt, inferBranch]

theorem inferProcess_parallelProcessBranchesFiring (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (values : Nat → Bool) (branches : List ChoiceBranch) :
    inferProcess (parallelProcessBranchesFiring alphabet selected values branches) =
      parallelTypeBranchesFiring alphabet selected (inferBranches branches) :=
  inferProcess_parallelProcessBranchesFiringFrom alphabet selected values 0 branches

/-- All payload fillings of a subset residual have the same future menu. -/
theorem procFutureOffers_parallelProcessBranchesFiring (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (values : Nat → Bool) (branches : List ChoiceBranch) :
    procFutureOffers (parallelProcessBranchesFiring alphabet selected values branches) =
      typeFutureOffers (parallelTypeBranchesFiring alphabet selected (inferBranches branches)) := by
  rw [procFutureOffers_inferProcess, inferProcess_parallelProcessBranchesFiring]

/-- An enabled head has a concrete communication whenever its send expression evaluates. -/
theorem branchCommunication_exists (env : Environment) (branch : ChoiceBranch)
    (hEnabled : BranchEnabled env branch)
    (hEval : ∀ msg expr process, branch = .send msg expr process →
      ∃ value, Semantics.ExprEval expr value) :
    ∃ value, BranchCommunication env branch value := by
  cases branch with
  | send msg expr process =>
      obtain ⟨value, hValue⟩ := hEval msg expr process rfl
      refine ⟨value, ?_, hValue⟩
      apply (hasNeed_send_iff env msg).mp
      exact hEnabled
  | recv msg name process =>
      exact (hasNeed_recv_iff env msg).mp hEnabled

/-- All enabled heads admit one joint payload assignment; unselected indices are unrestricted. -/
theorem conjunctiveValues_exist (env : Environment) (branches : List ChoiceBranch)
    (hEval : ∀ msg expr process, ChoiceBranch.send msg expr process ∈ branches →
      ∃ value, Semantics.ExprEval expr value) :
    ∃ values : Nat → Bool, ∀ entry ∈ branches.zipIdx,
      entry.2 ∈ processEnabledBranches env branches →
        BranchCommunication env entry.1 (values entry.2) := by
  have hEach : ∀ index, ∃ value, ∀ branch, (branch, index) ∈ branches.zipIdx →
      index ∈ processEnabledBranches env branches → BranchCommunication env branch value := by
    intro index
    by_cases hSelected : index ∈ processEnabledBranches env branches
    · obtain ⟨branch, hMem, hEnabled⟩ :=
        (mem_branchIndices (BranchEnabled env) branches index).mp hSelected
      obtain ⟨value, hValue⟩ := branchCommunication_exists env branch hEnabled
        (fun msg expr process hEq => hEval msg expr process
          (hEq ▸ List.fst_mem_of_mem_zipIdx hMem))
      refine ⟨value, fun other hOther _ => ?_⟩
      have hSame : other = branch := by
        have hFirst := List.mk_mem_zipIdx_iff_getElem?.mp hMem
        have hSecond := List.mk_mem_zipIdx_iff_getElem?.mp hOther
        exact Option.some.inj (hSecond.symm.trans hFirst)
      exact hSame ▸ hValue
    · exact ⟨false, fun _ _ h => False.elim (hSelected h)⟩
  choose values hValues using hEach
  exact ⟨values, fun entry hMem hSelected => hValues entry.2 entry.1 hMem hSelected⟩

end

end Pact
