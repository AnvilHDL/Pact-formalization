import Anvilpp.ProofHelpers.TypeSemantics
import Anvilpp.ProofHelpers.Inference.AbstractionMenus

namespace Pact

noncomputable section

open Classical

mutual
  /-- Abstraction preserves fair-choice identifiers. -/
  theorem typeFairIds_inferProcess (process : Proc) :
      typeFairIds (inferProcess process) = processFairIds process := by
    cases process with
    | send _ _ _ p | recv _ _ _ p | letp _ _ _ p =>
        simpa only [inferProcess, typeFairIds, processFairIds, Finset.empty_union] using typeFairIds_inferProcess p
    | var _ _ | skip _ | endp _ _ | cycle _ => simp only [inferProcess, typeFairIds, processFairIds]
    | recur _ _ body =>
        simpa only [inferProcess, typeFairIds, processFairIds] using typeFairIds_inferProcess body
    | par _ left right _ | seq _ left right | ifunfair _ _ left right
    | iffair _ _ _ left right =>
        simp only [inferProcess, typeFairIds, processFairIds, typeFairIds_inferProcess left,
          typeFairIds_inferProcess right]
    | xoffer _ other branches | offer _ other branches =>
        simp only [inferProcess, typeFairIds, processFairIds, typeFairIds_inferProcess other,
          typeBranchFairIds_inferBranches branches]
  termination_by sizeOf process

  /-- Abstraction preserves the fair-choice identifiers of a branch list. -/
  theorem typeBranchFairIds_inferBranches (branches : List ChoiceBranch) :
      typeBranchFairIds (inferBranches branches) = processBranchFairIds branches := by
    cases branches with
    | nil => simp only [inferBranches, typeBranchFairIds, processBranchFairIds]
    | cons branch rest =>
        rw [inferBranches_action, typeBranchFairIds, processBranchFairIds,
          typeFairIds_inferProcess, typeBranchFairIds_inferBranches]
  termination_by sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have := ChoiceBranch.continuation_sizeOf_lt branch; simp_wf; omega)
end

mutual
  /-- Abstraction preserves progress identifiers. -/
  theorem progressIds_inferProcess (process : Proc) :
      (inferProcess process).ProgressIds = processProgressIds process := by
    cases process with
    | send _ _ _ p | recv _ _ _ p | letp _ _ _ p =>
        simpa only [inferProcess, PactType.ProgressIds, processProgressIds, Finset.empty_union] using progressIds_inferProcess p
    | var _ _ | skip _ | endp _ _ | cycle _ => simp only [inferProcess, PactType.ProgressIds, processProgressIds]
    | recur _ _ body =>
        simpa only [inferProcess, PactType.ProgressIds, processProgressIds] using progressIds_inferProcess body
    | par _ left right _ | seq _ left right | ifunfair _ _ left right
    | iffair _ _ _ left right =>
        simp only [inferProcess, PactType.ProgressIds, processProgressIds, progressIds_inferProcess left,
          progressIds_inferProcess right]
    | xoffer _ other branches | offer _ other branches =>
        simp only [inferProcess, PactType.ProgressIds, processProgressIds, progressIds_inferProcess other,
          branchProgressIds_inferBranches branches]
  termination_by sizeOf process

  /-- Abstraction preserves the progress identifiers of a branch list. -/
  theorem branchProgressIds_inferBranches (branches : List ChoiceBranch) :
      PactType.BranchProgressIds (inferBranches branches) = processBranchProgressIds branches := by
    cases branches with
    | nil => simp only [inferBranches, PactType.BranchProgressIds, processBranchProgressIds]
    | cons branch rest =>
        rw [inferBranches_action, PactType.BranchProgressIds, processBranchProgressIds,
          progressIds_inferProcess, branchProgressIds_inferBranches]
  termination_by sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have := ChoiceBranch.continuation_sizeOf_lt branch; simp_wf; omega)
end

end

end Pact
