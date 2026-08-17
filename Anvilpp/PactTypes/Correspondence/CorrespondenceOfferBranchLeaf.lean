import Anvilpp.PactTypes.Correspondence.CorrespondenceXOfferLeaf

/-!
# parallelTypeBranches / parallelTypeBranchesSelecting leaves
-/

namespace Pact

noncomputable section

/-- Bundle for the generated conjunction behind `.offer`, proved by induction
on the original branch list rather than by recursion on the larger generated
syntax tree. -/
private theorem compilationProofBundle_parallelTypeBranches_leaf
    (signature : TypeAlphabet) : ∀ branches,
    signature.WellFormed →
    signature.SupportsBranches branches →
    PactType.AllBranchVariablesBound [] branches →
    PactType.ClockGuardedBranches branches →
    PactType.TailRecursiveBranches branches →
    PactType.SameCycleMessageLinearBranches branches →
    PactType.InterfaceScopedBranches branches →
    (∀ (action : BareMessage) (branchType : PactType) (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) →
    CompilationProofBundle signature (parallelTypeBranches branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _ _ _ _ _ _ _ _
      simpa [parallelTypeBranches] using
        (show CompilationProofBundle signature PactType.skip from
          { future := compilationFutureCorrect_skip signature
            completing := compilationCompletingCorrect_skip signature
            scopedStep :=
              compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
                signature .skip
                  (compilationFragmentStepCorrect_skip_leaf signature)
            execution := compilationSequenceExecutionCorrect_skip signature })
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      intro hSignature hSupports hClosed hGuarded hTail hLinear hScoped
        hBranches
      simp only [TypeAlphabet.SupportsBranches] at hSupports
      simp only [PactType.AllBranchVariablesBound] at hClosed
      simp only [PactType.ClockGuardedBranches] at hGuarded
      simp only [PactType.TailRecursiveBranches] at hTail
      simp only [PactType.SameCycleMessageLinearBranches] at hLinear
      simp only [PactType.InterfaceScopedBranches] at hScoped
      have hBranchBundle : CompilationProofBundle signature branchType :=
        hBranches action branchType 0 (by simp)
      have hSkipBundle : CompilationProofBundle signature .skip :=
        { future := compilationFutureCorrect_skip signature
          completing := compilationCompletingCorrect_skip signature
          scopedStep :=
            compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
              signature .skip
                (compilationFragmentStepCorrect_skip_leaf signature)
          execution := compilationSequenceExecutionCorrect_skip signature }
      have hSingletonSupports : signature.Supports
          (singletonTypeXOffer (action, branchType)) := by
        simp [singletonTypeXOffer, TypeAlphabet.Supports,
          TypeAlphabet.SupportsBranches, hSupports.1, hSupports.2.1]
      have hSingletonClosed : PactType.AllVariablesBound []
          (singletonTypeXOffer (action, branchType)) := by
        simp [singletonTypeXOffer, PactType.AllVariablesBound,
          PactType.AllBranchVariablesBound, hClosed.1]
      have hSingletonGuarded : PactType.ClockGuarded
          (singletonTypeXOffer (action, branchType)) := by
        simp [singletonTypeXOffer, PactType.ClockGuarded,
          PactType.ClockGuardedBranches, hGuarded.1]
      have hSingletonTail : PactType.TailRecursive
          (singletonTypeXOffer (action, branchType)) := by
        simp [singletonTypeXOffer, PactType.TailRecursive,
          PactType.TailRecursiveBranches, hTail.1]
      have hSingletonLinear : PactType.SameCycleMessageLinear
          (singletonTypeXOffer (action, branchType)) := by
        simp [singletonTypeXOffer, PactType.SameCycleMessageLinear,
          PactType.SameCycleMessageLinearBranches, hLinear.1, hLinear.2.1]
      have hSingletonScoped : PactType.InterfaceScoped
          (singletonTypeXOffer (action, branchType)) := by
        simp [singletonTypeXOffer, PactType.InterfaceScoped,
          PactType.InterfaceScopedBranches, hScoped.1]
      have hSingletonBranches : ∀ (selected : BareMessage)
          (selectedType : PactType) (index : Nat),
          [(action, branchType)][index]? = some (selected, selectedType) →
            CompilationProofBundle signature selectedType := by
        intro selected selectedType index hEntry
        have hIndex : index = 0 := by
          simpa using (List.getElem?_eq_some_iff.mp hEntry).1
        subst index
        simp only [List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hEntry
        rcases hEntry with ⟨rfl, rfl⟩
        exact hBranchBundle
      have hSingletonBundle : CompilationProofBundle signature
          (singletonTypeXOffer (action, branchType)) :=
        compilationProofBundle_xoffer_leaf signature .skip
          [(action, branchType)] hSignature hSingletonSupports
          hSingletonGuarded hSingletonTail hSingletonLinear
          hSingletonScoped hSkipBundle hSingletonBranches
      have hRestBranches : ∀ (selected : BareMessage)
          (selectedType : PactType) (index : Nat),
          rest[index]? = some (selected, selectedType) →
            CompilationProofBundle signature selectedType := by
        intro selected selectedType index hEntry
        exact hBranches selected selectedType (index + 1) (by
          simpa using hEntry)
      have hRestBundle := ih hSignature hSupports.2.2 hClosed.2 hGuarded.2
        hTail.2 hLinear.2.2 hScoped.2 hRestBranches
      cases rest with
      | nil =>
          simpa [parallelTypeBranches] using hSingletonBundle
      | cons next tail =>
          simpa [parallelTypeBranches] using
            (show CompilationProofBundle signature
                (.par (singletonTypeXOffer (action, branchType))
                  (parallelTypeBranches (next :: tail)) ∅) from
              { future := compilationFutureCorrect_parallel signature
                  (singletonTypeXOffer (action, branchType))
                  (parallelTypeBranches (next :: tail)) ∅
                  hSingletonBundle.future hRestBundle.future
                completing := compilationCompletingCorrect_parallel signature
                  (singletonTypeXOffer (action, branchType))
                  (parallelTypeBranches (next :: tail)) ∅
                  hSingletonBundle.completing hRestBundle.completing
                scopedStep := compilationFragmentStepCorrect_parallel_leaf
                  signature (singletonTypeXOffer (action, branchType))
                  (parallelTypeBranches (next :: tail)) ∅ hSignature
                  (by simp)
                  (by
                    simp only [PactType.InterfaceScoped]
                    exact ⟨by simp, hSingletonScoped,
                      parallelTypeBranches_interfaceScoped (next :: tail)
                        hScoped.2⟩)
                  (by
                    simp only [PactType.AllVariablesBound]
                    exact ⟨hSingletonClosed,
                      allVariablesBound_parallelTypeBranches []
                        (next :: tail) hClosed.2⟩)
                  hSingletonBundle hRestBundle
                execution :=
                  compilationSequenceExecutionCorrect_parallel_regular_leaf
                    signature (singletonTypeXOffer (action, branchType))
                      (parallelTypeBranches (next :: tail)) ∅
                        hSingletonClosed
                        (allVariablesBound_parallelTypeBranches []
                          (next :: tail) hClosed.2)
                        hSingletonBundle hRestBundle })

/-- A forced conjunctive-offer branch is a mandatory action followed by its
continuation; compose the atomic message bundle with the child bundle through
the ordinary sequence combinators. -/
private theorem compilationProofBundle_selectedTypeBranch_leaf
    (signature : TypeAlphabet) (action : BareMessage) (branchType : PactType)
    (hBranch : CompilationProofBundle signature branchType) :
    CompilationProofBundle signature
      (selectedTypeBranch (action, branchType)) := by
  sorry -- TODO(redevelopment): proof broken by upstream EntryCanonical/TypeCompilationRelation changes; .

/-- Bundle for the generated selected conjunction behind an enabled `.offer`
branch, proved by induction on the original branch list.  At the selected
position the mandatory `selectedTypeBranch` replaces `singletonTypeXOffer`;
every other position keeps its synthetic else arm exactly as in
`compilationProofBundle_parallelTypeBranches_leaf`. -/
theorem compilationProofBundle_parallelTypeBranchesSelecting_leaf
    (signature : TypeAlphabet) (selected : BareMessage × PactType) :
    ∀ branches,
    signature.WellFormed →
    signature.SupportsBranches branches →
    PactType.AllBranchVariablesBound [] branches →
    PactType.ClockGuardedBranches branches →
    PactType.TailRecursiveBranches branches →
    PactType.SameCycleMessageLinearBranches branches →
    PactType.InterfaceScopedBranches branches →
    (∀ (action : BareMessage) (branchType : PactType) (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) →
    CompilationProofBundle signature
      (parallelTypeBranchesSelecting selected branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _ _ _ _ _ _ _ _
      simpa [parallelTypeBranchesSelecting] using
        (show CompilationProofBundle signature PactType.skip from
          { future := compilationFutureCorrect_skip signature
            completing := compilationCompletingCorrect_skip signature
            scopedStep :=
              compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
                signature .skip
                  (compilationFragmentStepCorrect_skip_leaf signature)
            execution := compilationSequenceExecutionCorrect_skip signature })
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      intro hSignature hSupports hClosed hGuarded hTail hLinear hScoped
        hBranches
      simp only [TypeAlphabet.SupportsBranches] at hSupports
      simp only [PactType.AllBranchVariablesBound] at hClosed
      simp only [PactType.ClockGuardedBranches] at hGuarded
      simp only [PactType.TailRecursiveBranches] at hTail
      simp only [PactType.SameCycleMessageLinearBranches] at hLinear
      simp only [PactType.InterfaceScopedBranches] at hScoped
      have hBranchBundle : CompilationProofBundle signature branchType :=
        hBranches action branchType 0 (by simp)
      have hSkipBundle : CompilationProofBundle signature .skip :=
        { future := compilationFutureCorrect_skip signature
          completing := compilationCompletingCorrect_skip signature
          scopedStep :=
            compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
              signature .skip
                (compilationFragmentStepCorrect_skip_leaf signature)
          execution := compilationSequenceExecutionCorrect_skip signature }
      have hSingletonSupports : signature.Supports
          (singletonTypeXOffer (action, branchType)) := by
        simp [singletonTypeXOffer, TypeAlphabet.Supports,
          TypeAlphabet.SupportsBranches, hSupports.1, hSupports.2.1]
      have hSingletonClosed : PactType.AllVariablesBound []
          (singletonTypeXOffer (action, branchType)) := by
        simp [singletonTypeXOffer, PactType.AllVariablesBound,
          PactType.AllBranchVariablesBound, hClosed.1]
      have hSingletonGuarded : PactType.ClockGuarded
          (singletonTypeXOffer (action, branchType)) := by
        simp [singletonTypeXOffer, PactType.ClockGuarded,
          PactType.ClockGuardedBranches, hGuarded.1]
      have hSingletonTail : PactType.TailRecursive
          (singletonTypeXOffer (action, branchType)) := by
        simp [singletonTypeXOffer, PactType.TailRecursive,
          PactType.TailRecursiveBranches, hTail.1]
      have hSingletonLinear : PactType.SameCycleMessageLinear
          (singletonTypeXOffer (action, branchType)) := by
        simp [singletonTypeXOffer, PactType.SameCycleMessageLinear,
          PactType.SameCycleMessageLinearBranches, hLinear.1, hLinear.2.1]
      have hSingletonScoped : PactType.InterfaceScoped
          (singletonTypeXOffer (action, branchType)) := by
        simp [singletonTypeXOffer, PactType.InterfaceScoped,
          PactType.InterfaceScopedBranches, hScoped.1]
      have hSingletonBranches : ∀ (selectedAction : BareMessage)
          (selectedType : PactType) (index : Nat),
          [(action, branchType)][index]? = some (selectedAction, selectedType) →
            CompilationProofBundle signature selectedType := by
        intro selectedAction selectedType index hEntry
        have hIndex : index = 0 := by
          simpa using (List.getElem?_eq_some_iff.mp hEntry).1
        subst index
        simp only [List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hEntry
        rcases hEntry with ⟨rfl, rfl⟩
        exact hBranchBundle
      have hSingletonBundle : CompilationProofBundle signature
          (singletonTypeXOffer (action, branchType)) :=
        compilationProofBundle_xoffer_leaf signature .skip
          [(action, branchType)] hSignature hSingletonSupports
          hSingletonGuarded hSingletonTail hSingletonLinear
          hSingletonScoped hSkipBundle hSingletonBranches
      have hSelectedBundle : CompilationProofBundle signature
          (selectedTypeBranch (action, branchType)) :=
        compilationProofBundle_selectedTypeBranch_leaf signature action
          branchType hBranchBundle
      have hRestBranches : ∀ (selectedAction : BareMessage)
          (selectedType : PactType) (index : Nat),
          rest[index]? = some (selectedAction, selectedType) →
            CompilationProofBundle signature selectedType := by
        intro selectedAction selectedType index hEntry
        exact hBranches selectedAction selectedType (index + 1) (by
          simpa using hEntry)
      have hRestBundle := ih hSignature hSupports.2.2 hClosed.2 hGuarded.2
        hTail.2 hLinear.2.2 hScoped.2 hRestBranches
      by_cases hEq : (action, branchType) = selected
      · cases rest with
        | nil =>
            simpa [parallelTypeBranchesSelecting, hEq] using hSelectedBundle
        | cons next tail =>
            have hRestFullBundle := compilationProofBundle_parallelTypeBranches_leaf
              signature (next :: tail) hSignature hSupports.2.2 hClosed.2
                hGuarded.2 hTail.2 hLinear.2.2 hScoped.2 hRestBranches
            simpa [parallelTypeBranchesSelecting, hEq] using
              (show CompilationProofBundle signature
                  (.par (selectedTypeBranch (action, branchType))
                    (parallelTypeBranches (next :: tail)) ∅) from
                { future := compilationFutureCorrect_parallel signature
                    (selectedTypeBranch (action, branchType))
                    (parallelTypeBranches (next :: tail)) ∅
                    hSelectedBundle.future hRestFullBundle.future
                  completing := compilationCompletingCorrect_parallel signature
                    (selectedTypeBranch (action, branchType))
                    (parallelTypeBranches (next :: tail)) ∅
                    hSelectedBundle.completing hRestFullBundle.completing
                  scopedStep := compilationFragmentStepCorrect_parallel_leaf
                    signature (selectedTypeBranch (action, branchType))
                    (parallelTypeBranches (next :: tail)) ∅ hSignature
                    (by simp)
                    (by
                      simp only [PactType.InterfaceScoped]
                      refine ⟨by simp, ?_,
                        parallelTypeBranches_interfaceScoped (next :: tail)
                          hScoped.2⟩
                      simpa [selectedTypeBranch, PactType.InterfaceScoped]
                        using hScoped.1)
                    (by
                      simp only [PactType.AllVariablesBound]
                      refine ⟨?_,
                        allVariablesBound_parallelTypeBranches []
                          (next :: tail) hClosed.2⟩
                      simpa [selectedTypeBranch, PactType.AllVariablesBound]
                        using hClosed.1)
                    hSelectedBundle hRestFullBundle
                  execution :=
                    compilationSequenceExecutionCorrect_parallel_regular_leaf
                      signature (selectedTypeBranch (action, branchType))
                        (parallelTypeBranches (next :: tail)) ∅
                          (by
                            simpa [selectedTypeBranch,
                              PactType.AllVariablesBound] using
                              hClosed.1)
                          (allVariablesBound_parallelTypeBranches []
                            (next :: tail) hClosed.2)
                          hSelectedBundle hRestFullBundle })
      · cases rest with
        | nil =>
            simpa [parallelTypeBranchesSelecting, hEq] using hSingletonBundle
        | cons next tail =>
            simpa [parallelTypeBranchesSelecting, hEq] using
              (show CompilationProofBundle signature
                  (.par (singletonTypeXOffer (action, branchType))
                    (parallelTypeBranchesSelecting selected (next :: tail)) ∅)
                  from
                { future := compilationFutureCorrect_parallel signature
                    (singletonTypeXOffer (action, branchType))
                    (parallelTypeBranchesSelecting selected (next :: tail)) ∅
                    hSingletonBundle.future hRestBundle.future
                  completing := compilationCompletingCorrect_parallel signature
                    (singletonTypeXOffer (action, branchType))
                    (parallelTypeBranchesSelecting selected (next :: tail)) ∅
                    hSingletonBundle.completing hRestBundle.completing
                  scopedStep := compilationFragmentStepCorrect_parallel_leaf
                    signature (singletonTypeXOffer (action, branchType))
                    (parallelTypeBranchesSelecting selected (next :: tail)) ∅
                    hSignature (by simp)
                    (by
                      simp only [PactType.InterfaceScoped]
                      exact ⟨by simp, hSingletonScoped,
                        parallelTypeBranchesSelecting_interfaceScoped selected
                          (next :: tail) hScoped.2⟩)
                    (by
                      simp only [PactType.AllVariablesBound]
                      exact ⟨hSingletonClosed,
                        allVariablesBound_parallelTypeBranchesSelecting []
                          selected (next :: tail) hClosed.2⟩)
                    hSingletonBundle hRestBundle
                  execution :=
                    compilationSequenceExecutionCorrect_parallel_regular_leaf
                      signature (singletonTypeXOffer (action, branchType))
                        (parallelTypeBranchesSelecting selected (next :: tail))
                          ∅ hSingletonClosed
                          (allVariablesBound_parallelTypeBranchesSelecting []
                            selected (next :: tail) hClosed.2)
                          hSingletonBundle hRestBundle })

end

end Pact
