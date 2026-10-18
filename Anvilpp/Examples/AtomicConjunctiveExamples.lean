import Anvilpp.ProofHelpers.Inference.ConjunctiveConsumption
import Anvilpp.PactTypes.Proofs.Syntax.ConjunctiveResidualMenus
import Anvilpp.PactTypes.Proofs.Automata.AtomicConjunctiveOffer
import Anvilpp.PactTypes.Proofs.Automata.CompileTypeLemmas
import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.Offers

namespace Pact.AtomicConjunctiveExamples

noncomputable section

open Classical

private def alphabet : PactTypeAlphabet := ⟨{("a", .recv), ("b", .recv)}⟩

private def branches : List (BareMessage × PactType) :=
  [(("a", .recv), .skip alphabet), (("b", .recv), .tock alphabet)]

/-- A single available head is consumed; the other head remains optional. -/
theorem one_enabled :
    typeEnabledBranches ⟨{("a", .send)}, ∅, false⟩ branches = {0} ∧
    typeBranchBatchLabel branches {0} = .message "a" .recv ∧
    parallelTypeBranchesFiring alphabet {0} branches =
      .par alphabet (.skip alphabet)
        (.xoffer alphabet (.skip alphabet) [(("b", .recv), .tock alphabet)]) ∅ := by
  simp [typeEnabledBranches, branchIndices, TypeBranchEnabled, typeNeed,
    MessageDir.invert, branches, typeBranchBatchLabel, TypeLabel.message,
    parallelTypeBranchesFiring, parallelTypeBranchesFiringFrom,
    singletonTypeXOfferAt, PactType.reannotate]

/-- Two available heads communicate together and both leave their continuations. -/
theorem both_enabled :
    typeEnabledBranches ⟨{("a", .send), ("b", .send)}, ∅, false⟩ branches = {0, 1} ∧
    typeBranchBatchLabel branches {0, 1} =
      .actions {.message "a" .recv, .message "b" .recv} ∧
    parallelTypeBranchesFiring alphabet {0, 1} branches =
      .par alphabet (.skip alphabet) (.tock alphabet) ∅ := by
  simp [typeEnabledBranches, branchIndices, TypeBranchEnabled, typeNeed,
    MessageDir.invert, branches, typeBranchBatchLabel,
    parallelTypeBranchesFiring, parallelTypeBranchesFiringFrom, PactType.reannotate]

/-- An empty immediate menu yields no firing subset. -/
theorem none_enabled :
    typeEnabledBranches TypeEnvironment.empty branches = ∅ := by
  simp [typeEnabledBranches, branchIndices, TypeBranchEnabled, TypeEnvironment.empty, branches]

/-- Duplicate heads still denote distinct indices and are consumed together. -/
theorem duplicate_head_indices :
    typeEnabledBranches ⟨{("a", .send)}, ∅, false⟩
      [(("a", .recv), .skip alphabet), (("a", .recv), .tock alphabet)] = {0, 1} := by
  simp [typeEnabledBranches, branchIndices, TypeBranchEnabled, typeNeed, MessageDir.invert]

/-- Re-signing cannot remove subset copies, even if no head remains declared. -/
theorem selections_ignore_alphabet :
    conjunctiveSelections (PactType.reannotateBranches PactTypeAlphabet.empty branches).length =
      conjunctiveSelections branches.length ∧
    ({0, 1} : Finset Nat) ∈ conjunctiveSelections branches.length := by
  simp [branches, mem_conjunctiveSelections, Finset.subset_iff]

/-- A consumed receive substitutes its payload before its continuation runs. -/
theorem receive_substitution :
    parallelProcessBranchesFiring alphabet {0} (fun _ => true)
      [.recv "a" "x" (.send alphabet "b" (.var "x") (.skip alphabet))] =
      .send alphabet "b" (.val true) (.skip alphabet) := by
  simp [parallelProcessBranchesFiring, parallelProcessBranchesFiringFrom,
    consumedProcessBranchAt, Semantics.procExprReplace, Semantics.exprReplace,
    Proc.reannotate]

/-- An environment enabling both heads cannot select a single-head automaton edge. -/
theorem no_partial_batch (left right both : AutomatonFragment) (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ conjunctiveFiringEdges alphabet branches
      [({0}, left), ({1}, right), ({0, 1}, both)])
    (hEnv : edge.environment = ⟨{("a", .send), ("b", .send)}, ∅, false⟩) :
    edge.label = .visible (.actions {.message "a" .recv, .message "b" .recv}) := by
  obtain ⟨entry, _, env, _, _, hSelected, rfl⟩ :=
    (mem_conjunctiveFiringEdges alphabet branches _ edge).mp hEdge
  simp only at hEnv
  subst env
  rw [← hSelected, both_enabled.1, both_enabled.2.1]

/-- The active semantic rule consumes both enabled heads in one decorated step. -/
theorem active_type_step :
    TypeOffers ⟨{("a", .send), ("b", .send)}, ∅, false⟩
      (.offer alphabet (.skip alphabet) branches)
      (.actions {.message "a" .recv, .message "b" .recv})
      (.par alphabet (.skip alphabet) (.tock alphabet) ∅)
      (typeBranchActions branches ∩ alphabet.actions)
      (typeFutureOffers (.par alphabet (.skip alphabet) (.tock alphabet) ∅) \
        (typeBranchActions branches ∩ alphabet.actions)) := by
  have h := TypeOffers.offer_some ⟨{("a", .send), ("b", .send)}, ∅, false⟩
    alphabet (.skip alphabet) branches {0, 1}
    ⟨by simp [TypeEnvironment.WellFormed, alphabet, typeNeed, MessageDir.invert],
      by simp, both_enabled.1⟩
  simpa only [both_enabled.2.1, both_enabled.2.2] using h

/-- The active compiler contains the corresponding batch edge into the full-subset copy. -/
theorem active_compiler_step :
    ∃ edge ∈ (compileTypeFuel (typeCompilationFuel (.offer alphabet (.skip alphabet) branches))
        (.offer alphabet (.skip alphabet) branches)).edges,
      edge.source = .root ∧
      edge.environment = ⟨{("a", .send), ("b", .send)}, ∅, false⟩ ∧
      edge.label = .visible (.actions {.message "a" .recv, .message "b" .recv}) ∧
      edge.current = typeBranchActions branches ∩ alphabet.actions := by
  have hSelection : ({0, 1} : Finset Nat) ∈ conjunctiveSelections branches.length :=
    selections_ignore_alphabet.2
  obtain ⟨index, hGet⟩ := List.getElem?_of_mem (Finset.mem_toList.mpr hSelection)
  let residual := parallelTypeBranchesFiring alphabet {0, 1} branches
  let target := childState (index + 1)
    (compileTypeFuel (typeCompilationFuel residual) residual).initial
  refine ⟨{ source := .root,
            environment := ⟨{("a", .send), ("b", .send)}, ∅, false⟩,
            label := .visible (typeBranchBatchLabel branches {0, 1}),
            current := typeBranchActions branches ∩ alphabet.actions,
            future := .at target (typeBranchActions branches ∩ alphabet.actions),
            target := target }, ?_, rfl, rfl, ?_, rfl⟩
  · rw [compileTypeFuel_offer_eq]
    simp only [buildAtomicConjunctiveOfferAutomaton, finishAutomatonFragment, Finset.mem_union]
    refine Or.inl (Or.inl (Or.inr ?_))
    rw [mem_conjunctiveFiringEdges]
    refine ⟨(({0, 1}, compileTypeFuel (typeCompilationFuel residual) residual), index),
      ?_, _, ?_, by simp, both_enabled.1, rfl⟩
    · rw [List.mk_mem_zipIdx_iff_getElem?, List.getElem?_map, hGet]
      rfl
    · apply PactTypeAlphabet.mem_localEnvironments_of_wellFormed
      simp [TypeEnvironment.WellFormed, alphabet, typeNeed, MessageDir.invert]
  · rw [both_enabled.2.1]

private def payloadAlphabet : PactTypeAlphabet := ⟨{("a", .recv), ("b", .send)}⟩

private def payloadBranches : List ChoiceBranch :=
  [.recv "a" "x" (.send payloadAlphabet "b" (.var "x") (.skip payloadAlphabet))]

/-- The active process rule receives the payload and substitutes it in the surviving continuation. -/
theorem active_process_step :
    Offers ⟨{.send "a" true}, ∅, false⟩
      (.offer payloadAlphabet (.skip payloadAlphabet) payloadBranches)
      (.message "a" .recv true)
      (.send payloadAlphabet "b" (.val true) (.skip payloadAlphabet))
      (projectCurrent payloadAlphabet (branchOfferSet payloadBranches))
      (procFutureOffers (.send payloadAlphabet "b" (.val true) (.skip payloadAlphabet)) \
        (branchActions payloadBranches ∩ payloadAlphabet.actions)) := by
  have h := Offers.offer_some ⟨{.send "a" true}, ∅, false⟩ payloadAlphabet
    (.skip payloadAlphabet) payloadBranches {0} (fun _ => true)
    ⟨by simp [Environment.WellFormed, Environment.bareImmediate, Offer.bare,
        payloadAlphabet, bareNeed, MessageDir.invert],
      by simp,
      by simp [processEnabledBranches, branchIndices, BranchEnabled,
        payloadBranches, ChoiceBranch.need, ChoiceBranch.action,
        ChoiceBranch.getMessageId, ChoiceBranch.getDir,
        Environment.bareImmediate, Offer.bare, bareNeed, MessageDir.invert],
      by simp [payloadBranches, BranchCommunication, Environment.hasSend]⟩
  simpa [processBranchBatchLabel, Label.message, parallelProcessBranchesFiring,
    parallelProcessBranchesFiringFrom, consumedProcessBranchAt, payloadBranches,
    ChoiceBranch.getMessageId, ChoiceBranch.getDir, Semantics.procExprReplace,
    Semantics.exprReplace, Proc.reannotate] using h

end

end Pact.AtomicConjunctiveExamples
