import Anvilpp.PactTypes.Correspondence.CorrespondenceRecursionHeader

/-!
# Proof-bundle scaffolding: CompilationProofBundle, branch-regularity transport, nested-recursion vanilla completing correctness
-/

namespace Pact

noncomputable section

/-! ## Hierarchical closure of the compiler proof -/

theorem compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
    (signature : TypeAlphabet) (processType : PactType)
    (hStep : CompilationFragmentStepCorrect signature processType) :
    CompilationScopedFragmentStepCorrect signature processType := by
  intro residual residual' state environment label offers hRelated
    hEnvironment _
  exact hStep hRelated hEnvironment

private theorem mem_parallelBranchInterfaces_iff_exists
    (message : MessageId) : ∀ branches,
    message ∈ PactType.ParallelBranchInterfaces branches ↔
      ∃ entry ∈ branches, message ∈ entry.2.ParallelInterfaces := by
  intro branches
  induction branches with
  | nil => simp [PactType.ParallelBranchInterfaces]
  | cons entry rest ih =>
      rcases entry with ⟨action, processType⟩
      simp [PactType.ParallelBranchInterfaces, ih]

theorem supports_branch_of_mem (signature : TypeAlphabet) :
    ∀ branches entry, signature.SupportsBranches branches →
      entry ∈ branches → signature.Supports entry.2 := by
  intro branches
  induction branches with
  | nil => simp
  | cons head rest ih =>
      rcases head with ⟨action, processType⟩
      intro entry hSupports hEntry
      simp only [TypeAlphabet.SupportsBranches] at hSupports
      simp only [List.mem_cons] at hEntry
      rcases hEntry with rfl | hRest
      · exact hSupports.2.1
      · exact ih entry hSupports.2.2 hRest

theorem allVariablesBound_branch_of_mem (bound : List String) :
    ∀ branches entry, PactType.AllBranchVariablesBound bound branches →
      entry ∈ branches → PactType.AllVariablesBound bound entry.2 := by
  intro branches
  induction branches with
  | nil => simp
  | cons head rest ih =>
      rcases head with ⟨action, processType⟩
      intro entry hAll hEntry
      simp only [PactType.AllBranchVariablesBound] at hAll
      simp only [List.mem_cons] at hEntry
      rcases hEntry with rfl | hRest
      · exact hAll.1
      · exact ih entry hAll.2 hRest

theorem allVariablesBound_parallelTypeBranches
    (bound : List String) (branches : List (BareMessage × PactType))
    (hBound : PactType.AllBranchVariablesBound bound branches) :
    PactType.AllVariablesBound bound (parallelTypeBranches branches) := by
  induction branches with
  | nil =>
      simp [parallelTypeBranches, PactType.AllVariablesBound]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      simp only [PactType.AllBranchVariablesBound] at hBound
      cases rest with
      | nil =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.AllVariablesBound, PactType.AllBranchVariablesBound]
            using hBound.1
      | cons next tail =>
          simp only [parallelTypeBranches, PactType.AllVariablesBound]
          constructor
          · simpa [singletonTypeXOffer, PactType.AllVariablesBound,
              PactType.AllBranchVariablesBound] using hBound.1
          · exact ih hBound.2

theorem allVariablesBound_parallelTypeBranchesSelecting
    (bound : List String) (selected : BareMessage × PactType) :
    ∀ branches,
      PactType.AllBranchVariablesBound bound branches →
      PactType.AllVariablesBound bound
        (parallelTypeBranchesSelecting selected branches) := by
  intro branches hBound
  induction branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.AllVariablesBound]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      simp only [PactType.AllBranchVariablesBound] at hBound
      cases rest with
      | nil =>
          by_cases hEq : (action, processType) = selected
          · simp [parallelTypeBranchesSelecting, hEq, selectedTypeBranch,
              PactType.AllVariablesBound, hBound.1]
          · simp [parallelTypeBranchesSelecting, hEq, singletonTypeXOffer,
              PactType.AllVariablesBound, PactType.AllBranchVariablesBound,
              hBound.1]
      | cons next tail =>
          by_cases hEq : (action, processType) = selected
          · subst selected
            simp [parallelTypeBranchesSelecting, selectedTypeBranch,
              PactType.AllVariablesBound, hBound.1,
              allVariablesBound_parallelTypeBranches bound
                (next :: tail) hBound.2]
          · simp [parallelTypeBranchesSelecting, hEq, singletonTypeXOffer,
              PactType.AllVariablesBound, PactType.AllBranchVariablesBound,
              hBound.1, ih hBound.2]

theorem clockGuarded_branch_of_mem :
    ∀ branches entry, PactType.ClockGuardedBranches branches →
      entry ∈ branches → PactType.ClockGuarded entry.2 := by
  intro branches
  induction branches with
  | nil => simp
  | cons head rest ih =>
      rcases head with ⟨action, processType⟩
      intro entry hAll hEntry
      simp only [PactType.ClockGuardedBranches] at hAll
      simp only [List.mem_cons] at hEntry
      rcases hEntry with rfl | hRest
      · exact hAll.1
      · exact ih entry hAll.2 hRest

theorem tailRecursive_branch_of_mem :
    ∀ branches entry, PactType.TailRecursiveBranches branches →
      entry ∈ branches → PactType.TailRecursive entry.2 := by
  intro branches
  induction branches with
  | nil => simp
  | cons head rest ih =>
      rcases head with ⟨action, processType⟩
      intro entry hAll hEntry
      simp only [PactType.TailRecursiveBranches] at hAll
      simp only [List.mem_cons] at hEntry
      rcases hEntry with rfl | hRest
      · exact hAll.1
      · exact ih entry hAll.2 hRest

theorem sameCycleMessageLinear_branch_of_mem :
    ∀ branches entry, PactType.SameCycleMessageLinearBranches branches →
      entry ∈ branches → PactType.SameCycleMessageLinear entry.2 := by
  intro branches
  induction branches with
  | nil => simp
  | cons head rest ih =>
      rcases head with ⟨action, processType⟩
      intro entry hAll hEntry
      simp only [PactType.SameCycleMessageLinearBranches] at hAll
      simp only [List.mem_cons] at hEntry
      rcases hEntry with rfl | hRest
      · exact hAll.1
      · exact ih entry hAll.2.2 hRest

theorem binderHygienic_branch_of_mem (bound : List String) :
    ∀ branches entry, PactType.BinderHygienicBranches bound branches →
      entry ∈ branches → PactType.BinderHygienic bound entry.2 := by
  intro branches entry hHygienic hMember
  induction branches with
  | nil => simp at hMember
  | cons head rest ih =>
      rcases head with ⟨action, processType⟩
      simp only [PactType.BinderHygienicBranches] at hHygienic
      rcases hHygienic with ⟨hHead, hRest⟩
      simp only [List.mem_cons] at hMember
      rcases hMember with rfl | hMember
      · exact hHead
      · exact ih hRest hMember

theorem interfaceScoped_branch_of_mem :
    ∀ branches entry, PactType.InterfaceScopedBranches branches →
      entry ∈ branches → PactType.InterfaceScoped entry.2 := by
  intro branches
  induction branches with
  | nil => simp
  | cons head rest ih =>
      rcases head with ⟨action, processType⟩
      intro entry hAll hEntry
      simp only [PactType.InterfaceScopedBranches] at hAll
      simp only [List.mem_cons] at hEntry
      rcases hEntry with rfl | hRest
      · exact hAll.1
      · exact ih entry hAll.2 hRest

/- Supporting syntax declares every synchronization interface it contains. -/
/-! ### Vanilla (unsubstituted) completion correctness

Every completion combinator proved above (`compilationCompletingCorrect_choice`,
`_fairChoice`, `_sequence`, `_parallel`, `_xoffer`, `_offer`) consumes
completion correctness of its *children* as a hypothesis and composes it; none
of them requires closedness, clock guarding, tail recursion, message linearity
or interface scoping of its own.  Therefore
`CompilationCompletingCorrect signature processType` can be established by an
independent structural induction over `processType`, reusing those combinators
unchanged.

Only two cases are not already available.  The `.var` leaf is
`compilationCompletingCorrect_var`: the compiler's `.var` clause produces a
fragment whose `completing` set is empty, matching
`PactType.CanCompleteBeforeTock (.var _) = false` unconditionally.  A nested
recursion binder is exactly one application of the (still open) recursion
completion leaf; rather than duplicating that argument here, it is taken as an
explicit hypothesis in the style of `compilationCompletingCorrect_choice`'s
`hLeft`/`hRight`, phrased against `sizeOf` so that a well-founded proof of
`compilationCompletingCorrect_recursion_regular_leaf` can discharge it directly
from its own recursive-call hypothesis.

The nested-recursion hypothesis is guarded by `PactType.ClockGuarded` and
`PactType.TailRecursive` premises on the nested binder, matching the side
conditions of `compilationCompletingCorrect_recursion_regular_leaf` exactly.
Both predicates are purely structural and hold of every subterm, so they are
threaded through the induction; if that leaf is later restated without them,
the hypothesis becomes correspondingly easier to supply.  Crucially, no
*closedness* premise appears anywhere: `PactType.AllVariablesBound []` is false
for the body of a binder, and no completion combinator needs it. -/

/-- Completion correctness for the generated *selected* conjunction used by
`.offer`.  This is the `parallelTypeBranchesSelecting` analogue of
`compilationCompletingCorrect_parallelTypeBranches`, proved directly over the
branch list.  Like every other completion combinator it consumes only the
per-branch completion facts and no closedness or regularity hypothesis. -/
theorem compilationCompletingCorrect_parallelTypeBranchesSelecting
    (signature : TypeAlphabet) (selected : BareMessage × PactType) :
    ∀ branches,
    (∀ (action : BareMessage) (branchType : PactType) (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationCompletingCorrect signature branchType) →
    CompilationCompletingCorrect signature
      (parallelTypeBranchesSelecting selected branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _
      simpa [parallelTypeBranchesSelecting] using
        (compilationCompletingCorrect_skip signature)
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      intro hBranches
      have hHead : CompilationCompletingCorrect signature branchType :=
        hBranches action branchType 0 (by simp)
      have hSingleton : CompilationCompletingCorrect signature
          (singletonTypeXOffer (action, branchType)) := by
        apply compilationCompletingCorrect_xoffer signature .skip
          [(action, branchType)]
        · exact compilationCompletingCorrect_skip signature
        · intro selectedAction selectedType index hEntry
          have hIndex : index = 0 := by
            simpa using (List.getElem?_eq_some_iff.mp hEntry).1
          subst index
          simp only [List.getElem?_cons_zero, Option.some.injEq,
            Prod.mk.injEq] at hEntry
          rcases hEntry with ⟨rfl, rfl⟩
          exact hHead
      have hSelectedBranch : CompilationCompletingCorrect signature
          (selectedTypeBranch (action, branchType)) := by
        have hSeq := compilationCompletingCorrect_sequence signature
          (.message action.1 action.2) branchType
          (compilationCompletingCorrect_message signature action.1 action.2)
          hHead
        simpa [selectedTypeBranch] using hSeq
      have hRestBranches : ∀ (selectedAction : BareMessage)
          (selectedType : PactType) (index : Nat),
          rest[index]? = some (selectedAction, selectedType) →
            CompilationCompletingCorrect signature selectedType := by
        intro selectedAction selectedType index hEntry
        exact hBranches selectedAction selectedType (index + 1) (by
          simpa using hEntry)
      have hRest := ih hRestBranches
      by_cases hEq : (action, branchType) = selected
      · cases rest with
        | nil =>
            simpa [parallelTypeBranchesSelecting, hEq] using hSelectedBranch
        | cons next tail =>
            have hRestFull := compilationCompletingCorrect_parallelTypeBranches
              signature (next :: tail) hRestBranches
            simpa [parallelTypeBranchesSelecting, hEq] using
              (compilationCompletingCorrect_parallel signature
                (selectedTypeBranch (action, branchType))
                (parallelTypeBranches (next :: tail)) ∅ hSelectedBranch
                  hRestFull)
      · cases rest with
        | nil =>
            simpa [parallelTypeBranchesSelecting, hEq] using hSingleton
        | cons next tail =>
            simpa [parallelTypeBranchesSelecting, hEq] using
              (compilationCompletingCorrect_parallel signature
                (singletonTypeXOffer (action, branchType))
                (parallelTypeBranchesSelecting selected (next :: tail)) ∅
                  hSingleton hRest)

/-- Structural completion correctness for an arbitrary type, given completion
correctness for every clock-guarded, tail-recursive recursion binder of size at
most `processType`.

This is deliberately independent of closedness: `PactType.AllVariablesBound []`
is false for the body of a binder, and no completion combinator needs it.  The
structural premises `hGuarded`/`hTail` are carried only so that the nested
recursion hypothesis can be stated with exactly the side conditions of
`compilationCompletingCorrect_recursion_regular_leaf`; every composition step is
one of the already proved completion combinators, none of which needs them.  A
`.recur` node is discharged by applying `hNestedRecursion` to itself
(`le_rfl`). -/
theorem compilationCompletingCorrect_of_nestedRecursion
    (signature : TypeAlphabet) : ∀ processType : PactType,
    signature.Supports processType →
    PactType.ClockGuarded processType →
    PactType.TailRecursive processType →
    PactType.BinderHygienic [] processType →
    (∀ (nestedName : String) (nestedBody : PactType),
      sizeOf (PactType.recur nestedName nestedBody) ≤ sizeOf processType →
      signature.Supports (.recur nestedName nestedBody) →
      PactType.ClockGuarded (.recur nestedName nestedBody) →
      PactType.TailRecursive (.recur nestedName nestedBody) →
      PactType.BinderHygienic [] (.recur nestedName nestedBody) →
        CompilationCompletingCorrect signature (.recur nestedName nestedBody)) →
    CompilationCompletingCorrect signature processType := by
  intro processType
  cases processType with
  | message msg dir =>
      intro _ _ _ _ _
      exact compilationCompletingCorrect_message signature msg dir
  | progress pid =>
      intro _ _ _ _ _
      exact compilationCompletingCorrect_progress signature pid
  | tock =>
      intro _ _ _ _ _
      exact compilationCompletingCorrect_tock signature
  | skip =>
      intro _ _ _ _ _
      exact compilationCompletingCorrect_skip signature
  | var name =>
      intro _ _ _ _ _
      exact compilationCompletingCorrect_var signature name
  | recur nestedName nestedBody =>
      intro hSupports hGuarded hTail hHygienic hNestedRecursion
      exact hNestedRecursion nestedName nestedBody le_rfl hSupports hGuarded
        hTail hHygienic
  | choice left right =>
      intro hSupports hGuarded hTail hHygienic hNestedRecursion
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.BinderHygienic] at hHygienic
      have hLeftSize : sizeOf left < sizeOf (PactType.choice left right) := by
        simp_wf
        omega
      have hRightSize : sizeOf right < sizeOf (PactType.choice left right) := by
        simp_wf
        omega
      have hLeft := compilationCompletingCorrect_of_nestedRecursion signature
        left hSupports.1 hGuarded.1 hTail.1 hHygienic.1
        (fun nestedName nestedBody hSize hNestedSupports hNestedGuarded
            hNestedTail hNestedHygienic =>
          hNestedRecursion nestedName nestedBody
            (le_trans hSize (le_of_lt hLeftSize)) hNestedSupports
              hNestedGuarded hNestedTail hNestedHygienic)
      have hRight := compilationCompletingCorrect_of_nestedRecursion signature
        right hSupports.2 hGuarded.2 hTail.2 hHygienic.2
        (fun nestedName nestedBody hSize hNestedSupports hNestedGuarded
            hNestedTail hNestedHygienic =>
          hNestedRecursion nestedName nestedBody
            (le_trans hSize (le_of_lt hRightSize)) hNestedSupports
              hNestedGuarded hNestedTail hNestedHygienic)
      exact compilationCompletingCorrect_choice signature left right hLeft
        hRight
  | fairChoice bid left right =>
      intro hSupports hGuarded hTail hHygienic hNestedRecursion
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.BinderHygienic] at hHygienic
      have hLeftSize : sizeOf left <
          sizeOf (PactType.fairChoice bid left right) := by
        simp_wf
        omega
      have hRightSize : sizeOf right <
          sizeOf (PactType.fairChoice bid left right) := by
        simp_wf
        omega
      have hLeft := compilationCompletingCorrect_of_nestedRecursion signature
        left hSupports.2.1 hGuarded.1 hTail.1 hHygienic.1
        (fun nestedName nestedBody hSize hNestedSupports hNestedGuarded
            hNestedTail hNestedHygienic =>
          hNestedRecursion nestedName nestedBody
            (le_trans hSize (le_of_lt hLeftSize)) hNestedSupports
              hNestedGuarded hNestedTail hNestedHygienic)
      have hRight := compilationCompletingCorrect_of_nestedRecursion signature
        right hSupports.2.2 hGuarded.2 hTail.2 hHygienic.2
        (fun nestedName nestedBody hSize hNestedSupports hNestedGuarded
            hNestedTail hNestedHygienic =>
          hNestedRecursion nestedName nestedBody
            (le_trans hSize (le_of_lt hRightSize)) hNestedSupports
              hNestedGuarded hNestedTail hNestedHygienic)
      exact compilationCompletingCorrect_fairChoice signature bid left right
        hLeft hRight
  | seq left right =>
      intro hSupports hGuarded hTail hHygienic hNestedRecursion
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.BinderHygienic] at hHygienic
      have hLeftSize : sizeOf left < sizeOf (PactType.seq left right) := by
        simp_wf
        omega
      have hRightSize : sizeOf right < sizeOf (PactType.seq left right) := by
        simp_wf
        omega
      have hLeft := compilationCompletingCorrect_of_nestedRecursion signature
        left hSupports.1 hGuarded.1 hTail.1 hHygienic.1
        (fun nestedName nestedBody hSize hNestedSupports hNestedGuarded
            hNestedTail hNestedHygienic =>
          hNestedRecursion nestedName nestedBody
            (le_trans hSize (le_of_lt hLeftSize)) hNestedSupports
              hNestedGuarded hNestedTail hNestedHygienic)
      have hRight := compilationCompletingCorrect_of_nestedRecursion signature
        right hSupports.2 hGuarded.2 hTail.2 hHygienic.2
        (fun nestedName nestedBody hSize hNestedSupports hNestedGuarded
            hNestedTail hNestedHygienic =>
          hNestedRecursion nestedName nestedBody
            (le_trans hSize (le_of_lt hRightSize)) hNestedSupports
              hNestedGuarded hNestedTail hNestedHygienic)
      exact compilationCompletingCorrect_sequence signature left right hLeft
        hRight
  | par left right interface =>
      intro hSupports hGuarded hTail hHygienic hNestedRecursion
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.BinderHygienic] at hHygienic
      have hLeftSize : sizeOf left <
          sizeOf (PactType.par left right interface) := by
        simp_wf
        omega
      have hRightSize : sizeOf right <
          sizeOf (PactType.par left right interface) := by
        simp_wf
        omega
      have hLeft := compilationCompletingCorrect_of_nestedRecursion signature
        left hSupports.2.1 hGuarded.1 hTail.1 hHygienic.1
        (fun nestedName nestedBody hSize hNestedSupports hNestedGuarded
            hNestedTail hNestedHygienic =>
          hNestedRecursion nestedName nestedBody
            (le_trans hSize (le_of_lt hLeftSize)) hNestedSupports
              hNestedGuarded hNestedTail hNestedHygienic)
      have hRight := compilationCompletingCorrect_of_nestedRecursion signature
        right hSupports.2.2 hGuarded.2 hTail.2 hHygienic.2
        (fun nestedName nestedBody hSize hNestedSupports hNestedGuarded
            hNestedTail hNestedHygienic =>
          hNestedRecursion nestedName nestedBody
            (le_trans hSize (le_of_lt hRightSize)) hNestedSupports
              hNestedGuarded hNestedTail hNestedHygienic)
      exact compilationCompletingCorrect_parallel signature left right interface
        hLeft hRight
  | xoffer elseType branches =>
      intro hSupports hGuarded hTail hHygienic hNestedRecursion
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.BinderHygienic] at hHygienic
      have hElseSize : sizeOf elseType <
          sizeOf (PactType.xoffer elseType branches) := by
        simp_wf
        omega
      have hElse := compilationCompletingCorrect_of_nestedRecursion signature
        elseType hSupports.1 hGuarded.1 hTail.1 hHygienic.1
        (fun nestedName nestedBody hSize hNestedSupports hNestedGuarded
            hNestedTail hNestedHygienic =>
          hNestedRecursion nestedName nestedBody
            (le_trans hSize (le_of_lt hElseSize)) hNestedSupports
              hNestedGuarded hNestedTail hNestedHygienic)
      have hBranches : ∀ (action : BareMessage) (branchType : PactType)
          (index : Nat), branches[index]? = some (action, branchType) →
            CompilationCompletingCorrect signature branchType := by
        intro action branchType index hEntry
        have hMember : (action, branchType) ∈ branches := by
          rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
          have hAt := List.getElem_mem hBound
          simpa [hValue] using hAt
        have hBranchSize : sizeOf branchType <
            sizeOf (PactType.xoffer elseType branches) := by
          have hPair := List.sizeOf_lt_of_mem hMember
          have hComponent : sizeOf branchType <
              sizeOf (action, branchType) := by
            simp_wf
            omega
          have hList : sizeOf branches <
              sizeOf (PactType.xoffer elseType branches) := by
            simp_wf
            omega
          omega
        exact compilationCompletingCorrect_of_nestedRecursion signature
          branchType (supports_branch_of_mem signature branches
            (action, branchType) hSupports.2 hMember)
          (clockGuarded_branch_of_mem branches (action, branchType)
            hGuarded.2 hMember)
          (tailRecursive_branch_of_mem branches (action, branchType)
            hTail.2 hMember)
          (binderHygienic_branch_of_mem [] branches (action, branchType)
            hHygienic.2 hMember)
          (fun nestedName nestedBody hSize hNestedSupports hNestedGuarded
              hNestedTail hNestedHygienic =>
            hNestedRecursion nestedName nestedBody
              (le_trans hSize (le_of_lt hBranchSize)) hNestedSupports
                hNestedGuarded hNestedTail hNestedHygienic)
      exact compilationCompletingCorrect_xoffer signature elseType branches
        hElse hBranches
  | offer elseType branches =>
      intro hSupports hGuarded hTail hHygienic hNestedRecursion
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.BinderHygienic] at hHygienic
      have hElseSize : sizeOf elseType <
          sizeOf (PactType.offer elseType branches) := by
        simp_wf
        omega
      have hElse := compilationCompletingCorrect_of_nestedRecursion signature
        elseType hSupports.1 hGuarded.1 hTail.1 hHygienic.1
        (fun nestedName nestedBody hSize hNestedSupports hNestedGuarded
            hNestedTail hNestedHygienic =>
          hNestedRecursion nestedName nestedBody
            (le_trans hSize (le_of_lt hElseSize)) hNestedSupports
              hNestedGuarded hNestedTail hNestedHygienic)
      have hBranches : ∀ (action : BareMessage) (branchType : PactType)
          (index : Nat), branches[index]? = some (action, branchType) →
            CompilationCompletingCorrect signature branchType := by
        intro action branchType index hEntry
        have hMember : (action, branchType) ∈ branches := by
          rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
          have hAt := List.getElem_mem hBound
          simpa [hValue] using hAt
        have hBranchSize : sizeOf branchType <
            sizeOf (PactType.offer elseType branches) := by
          have hPair := List.sizeOf_lt_of_mem hMember
          have hComponent : sizeOf branchType <
              sizeOf (action, branchType) := by
            simp_wf
            omega
          have hList : sizeOf branches <
              sizeOf (PactType.offer elseType branches) := by
            simp_wf
            omega
          omega
        exact compilationCompletingCorrect_of_nestedRecursion signature
          branchType (supports_branch_of_mem signature branches
            (action, branchType) hSupports.2 hMember)
          (clockGuarded_branch_of_mem branches (action, branchType)
            hGuarded.2 hMember)
          (tailRecursive_branch_of_mem branches (action, branchType)
            hTail.2 hMember)
          (binderHygienic_branch_of_mem [] branches (action, branchType)
            hHygienic.2 hMember)
          (fun nestedName nestedBody hSize hNestedSupports hNestedGuarded
              hNestedTail hNestedHygienic =>
            hNestedRecursion nestedName nestedBody
              (le_trans hSize (le_of_lt hBranchSize)) hNestedSupports
                hNestedGuarded hNestedTail hNestedHygienic)
      have hConjunction : ∀ (selected : BareMessage × PactType) (index : Nat),
          branches[index]? = some selected →
            CompilationCompletingCorrect signature
              (parallelTypeBranchesSelecting selected branches) := by
        intro selected _ _
        exact compilationCompletingCorrect_parallelTypeBranchesSelecting
          signature selected branches hBranches
      exact compilationCompletingCorrect_offer signature elseType branches
        hElse hConjunction
termination_by processType => sizeOf processType
decreasing_by all_goals assumption

/-- "Vanilla" completion correctness for a recursion body: the *unsubstituted*
body of `.recur name body`, compared against its own standalone compiled
fragment.  A state representing a bare `.var other` residual is compared
against `PactType.CanCompleteBeforeTock (.var other) = false`; no substitution
of the enclosing binder takes place.  This is the fact
`compilationCompletingCorrect_recursion_regular_leaf` cannot obtain from
`PactType.guardedOccurrences_replace_canCompleteBeforeTock`, because a
body-embedded state past a tock generally fails
`body.GuardedOccurrences name False`.

`hGuarded`/`hTail` are the two conjuncts of `ClockGuarded (.recur name body)`
and `TailRecursive (.recur name body)` that survive to the body, and
`hNestedRecursion` is exactly the recursive-call hypothesis available to a
well-founded proof of `compilationCompletingCorrect_recursion_regular_leaf`
measured by `sizeOf`.  No closedness premise is required or available.

Intended use, inside a `termination_by name body => sizeOf (.recur name body)`
proof of that leaf (checked to elaborate):
```
have hGuardedFields : PactType.GuardedOccurrences name False body ∧
    PactType.ClockGuarded body := by
  simpa only [PactType.ClockGuarded] using hGuarded
have hTailFields : PactType.TailOccurrences name True body ∧
    PactType.TailRecursive body := by
  simpa only [PactType.TailRecursive] using hTail
have hVanilla := recursionBodyCompletingCorrect_vanilla signature name body
  hGuardedFields.2 hTailFields.2
  (fun n b _ hNestedGuarded hNestedTail =>
    compilationCompletingCorrect_recursion_regular_leaf signature n b
      hNestedGuarded hNestedTail)
```
The `_` argument is the `sizeOf` decrease consumed by `decreasing_by`. -/
theorem recursionBodyCompletingCorrect_vanilla
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hSupports : signature.Supports body)
    (hGuarded : PactType.ClockGuarded body)
    (hTail : PactType.TailRecursive body)
    (hHygienic : PactType.BinderHygienic [] body)
    (hNestedRecursion : ∀ (nestedName : String) (nestedBody : PactType),
      sizeOf (PactType.recur nestedName nestedBody) <
          sizeOf (PactType.recur name body) →
      signature.Supports (.recur nestedName nestedBody) →
      PactType.ClockGuarded (.recur nestedName nestedBody) →
      PactType.TailRecursive (.recur nestedName nestedBody) →
      PactType.BinderHygienic [] (.recur nestedName nestedBody) →
        CompilationCompletingCorrect signature (.recur nestedName nestedBody)) :
    CompilationCompletingCorrect signature body := by
  have hBodySize : sizeOf body < sizeOf (PactType.recur name body) := by
    simp_wf
    omega
  exact compilationCompletingCorrect_of_nestedRecursion signature body hSupports
    hGuarded hTail hHygienic
    (fun nestedName nestedBody hSize hNestedSupports hNestedGuarded hNestedTail
        hNestedHygienic =>
      hNestedRecursion nestedName nestedBody
        (lt_of_le_of_lt hSize hBodySize) hNestedSupports hNestedGuarded
          hNestedTail hNestedHygienic)

/-- Corollary fixing the constant `v := body.CanCompleteBeforeTock` at the
body's own compiled fragment: the entry state of the standalone compilation of
`body` is `completing` exactly when the unsubstituted syntax predicate holds. -/
theorem recursionBodyCompletingCorrect_vanilla_initial
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hSupports : signature.Supports body)
    (hGuarded : PactType.ClockGuarded body)
    (hTail : PactType.TailRecursive body)
    (hHygienic : PactType.BinderHygienic [] body)
    (hNestedRecursion : ∀ (nestedName : String) (nestedBody : PactType),
      sizeOf (PactType.recur nestedName nestedBody) <
          sizeOf (PactType.recur name body) →
      signature.Supports (.recur nestedName nestedBody) →
      PactType.ClockGuarded (.recur nestedName nestedBody) →
      PactType.TailRecursive (.recur nestedName nestedBody) →
      PactType.BinderHygienic [] (.recur nestedName nestedBody) →
        CompilationCompletingCorrect signature (.recur nestedName nestedBody)) :
    ((compileTypeFuel signature (typeCompilationFuel body) body).initial ∈
        (compileTypeFuel signature (typeCompilationFuel body) body).completing ↔
      body.CanCompleteBeforeTock = true) := by
  have hVanilla := recursionBodyCompletingCorrect_vanilla signature name body
    hSupports hGuarded hTail hHygienic hNestedRecursion
  have hCanonical := hVanilla _ body
    (compileType_initial_relation signature body)
  simpa [compileType] using hCanonical

/-- Fuel-general form of the previous corollary.  `buildRecursionAutomaton` is
applied to `compileTypeFuel signature fuel body` for the enclosing binder's
remaining fuel, so this is the shape actually met at a recursion node. -/
private theorem recursionBodyCompletingCorrect_vanilla_initial_of_sufficient
    (signature : TypeAlphabet) (name : String) (body : PactType) (fuel : Nat)
    (hFuel : TypeCompilationFuelSufficient body fuel)
    (hSupports : signature.Supports body)
    (hGuarded : PactType.ClockGuarded body)
    (hTail : PactType.TailRecursive body)
    (hHygienic : PactType.BinderHygienic [] body)
    (hNestedRecursion : ∀ (nestedName : String) (nestedBody : PactType),
      sizeOf (PactType.recur nestedName nestedBody) <
          sizeOf (PactType.recur name body) →
      signature.Supports (.recur nestedName nestedBody) →
      PactType.ClockGuarded (.recur nestedName nestedBody) →
      PactType.TailRecursive (.recur nestedName nestedBody) →
      PactType.BinderHygienic [] (.recur nestedName nestedBody) →
        CompilationCompletingCorrect signature (.recur nestedName nestedBody)) :
    ((compileTypeFuel signature fuel body).initial ∈
        (compileTypeFuel signature fuel body).completing ↔
      body.CanCompleteBeforeTock = true) := by
  have hStable : compileTypeFuel signature fuel body =
      compileTypeFuel signature (typeCompilationFuel body) body :=
    compileTypeFuel_eq_of_sufficient signature body hFuel
      (typeCompilationFuel_sufficient body)
  rw [hStable]
  exact recursionBodyCompletingCorrect_vanilla_initial signature name body
    hSupports hGuarded hTail hHygienic hNestedRecursion

private theorem parallelInterfaces_subset_of_supports_leaf
    (signature : TypeAlphabet) (processType : PactType)
    (hSupports : signature.Supports processType) :
    processType.ParallelInterfaces ⊆ signature.interface := by
  intro message hMessage
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | h n ih =>
      cases processType with
      | message msg dir => simp [PactType.ParallelInterfaces] at hMessage
      | progress pid => simp [PactType.ParallelInterfaces] at hMessage
      | tock => simp [PactType.ParallelInterfaces] at hMessage
      | skip => simp [PactType.ParallelInterfaces] at hMessage
      | var name => simp [PactType.ParallelInterfaces] at hMessage
      | recur name body =>
          apply ih (sizeOf body) (by rw [← hSize]; simp_wf; omega) body
            (by simpa [TypeAlphabet.Supports] using hSupports)
            (by simpa [PactType.ParallelInterfaces] using hMessage) rfl
      | choice left right | seq left right =>
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.ParallelInterfaces, Finset.mem_union] at hMessage
          rcases hMessage with hLeft | hRight
          · exact ih (sizeOf left) (by rw [← hSize]; simp_wf; omega) left
              hSupports.1 hLeft rfl
          · exact ih (sizeOf right) (by rw [← hSize]; simp_wf; omega) right
              hSupports.2 hRight rfl
      | fairChoice bid left right =>
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.ParallelInterfaces, Finset.mem_union] at hMessage
          rcases hMessage with hLeft | hRight
          · exact ih (sizeOf left) (by rw [← hSize]; simp_wf; omega) left
              hSupports.2.1 hLeft rfl
          · exact ih (sizeOf right) (by rw [← hSize]; simp_wf; omega) right
              hSupports.2.2 hRight rfl
      | par left right interface =>
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.ParallelInterfaces, Finset.mem_union] at hMessage
          rcases hMessage with (hInterface | hLeft) | hRight
          · exact hSupports.1 hInterface
          · exact ih (sizeOf left) (by rw [← hSize]; simp_wf; omega) left
              hSupports.2.1 hLeft rfl
          · exact ih (sizeOf right) (by rw [← hSize]; simp_wf; omega) right
              hSupports.2.2 hRight rfl
      | xoffer elseType branches | offer elseType branches =>
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.ParallelInterfaces, Finset.mem_union] at hMessage
          rcases hMessage with hElse | hBranches
          · exact ih (sizeOf elseType) (by rw [← hSize]; simp_wf; omega)
              elseType hSupports.1 hElse rfl
          · rcases (mem_parallelBranchInterfaces_iff_exists message branches).mp
                hBranches with ⟨entry, hEntry, hEntryMessage⟩
            have hSupported : signature.Supports entry.2 :=
              supports_branch_of_mem signature branches entry hSupports.2 hEntry
            have hPairSize := List.sizeOf_lt_of_mem hEntry
            have hComponentSize : sizeOf entry.2 < sizeOf entry := by
              rcases entry
              simp_wf
              omega
            exact ih (sizeOf entry.2) (by rw [← hSize]; simp_wf; omega)
              entry.2 hSupported hEntryMessage rfl

/-- Export a scoped constructor theorem through the public alphabet filter. -/
theorem compilationStepCorrect_of_scopedFragmentStepCorrect
    (signature : TypeAlphabet) (processType : PactType)
    (hAlphabet : signature.WellFormed)
    (hSupports : signature.Supports processType)
    (hStep : CompilationScopedFragmentStepCorrect signature processType) :
    CompilationStepCorrect signature processType := by
  intro residual residual' state environment label offers hRelated hSymbol
  have hSignatureSymbol : TypeAutomatonSymbol.mk environment label offers ∈
      signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hFields : environment ∈ signature.environments ∧
      label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
    simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
  have hAvoids := signature.environment_avoids_subinterface hAlphabet
    hFields.1 (parallelInterfaces_subset_of_supports_leaf signature processType
      hSupports)
  have hRaw := hStep (residual := residual) (residual' := residual')
    (state := state) (environment := environment) (label := label)
    (offers := offers) hRelated
    (signature.environments_subset_localEnvironments hFields.1) hAvoids
  constructor
  · intro hSemantic
    rcases hRaw.mp hSemantic with ⟨target, hEdge, hTarget⟩
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature processType state
        target environment label offers hSignatureSymbol).mpr hEdge,
      hTarget⟩
  · rintro ⟨target, hEdge, hTarget⟩
    apply hRaw.mpr
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature processType state
        target environment label offers hSignatureSymbol).mp hEdge,
      hTarget⟩

/-- The extra same-cycle observable required when a compiled type is placed
on the left of sequencing.  Besides the ordinary future menu, sequencing must
know whether following non-clock execution targets reaches either literal
completion or optimistic completion metadata. -/
def CompilationSequenceExecutionCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  let execution := sequenceExecutionAutomaton fragment
  ∀ state residual,
    TypeCompilationRelation processType state residual →
      computeFuture execution state = typeFutureOffers residual ∧
        ((∃ completed ∈ execution.futureReachable state,
              completed ∈ fragment.skipping ∨
                completed ∈ fragment.completing) ↔
          residual.CanCompleteBeforeTock = true)

/-- The mutually supporting invariants needed by the structural compiler
proof.  Public step correspondence is derived uniformly from the raw fragment
field, while `execution` retains precisely the same-cycle closure information
needed by an enclosing sequence. -/
structure CompilationProofBundle
    (signature : TypeAlphabet) (processType : PactType) : Prop where
  future : CompilationFutureCorrect signature processType
  completing : CompilationCompletingCorrect signature processType
  scopedStep : CompilationScopedFragmentStepCorrect signature processType
  execution : CompilationSequenceExecutionCorrect signature processType

end

end Pact
