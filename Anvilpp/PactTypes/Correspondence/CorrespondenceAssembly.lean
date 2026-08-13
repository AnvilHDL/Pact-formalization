import Anvilpp.PactTypes.Correspondence.CorrespondenceOfferLeaf

/-!
# Top-level proof-bundle assembly and ProcessAutomatonCorrespondence
-/

namespace Pact

noncomputable section

private theorem allBranchVariablesBound_nil_of_bound (bound : List String) :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.AllBranchVariablesBound bound branches →
      (∀ m ∈ bound, PactType.TailBranchOccurrences m False branches) →
        PactType.AllBranchVariablesBound [] branches := by
  intro branches
  induction branches with
  | nil => intro _ _; simp [PactType.AllBranchVariablesBound]
  | cons branch rest ih =>
      obtain ⟨action, branchType⟩ := branch
      intro hBound hTail
      simp only [PactType.AllBranchVariablesBound] at hBound ⊢
      refine ⟨?_, ih hBound.2 (fun m hm => by
        have hEntry := hTail m hm
        simp only [PactType.TailBranchOccurrences] at hEntry
        exact hEntry.2)⟩
      apply PactType.allVariablesBound_drop_of_allTailOccurrences_false bound []
        branchType (fun m hm => by
          have hEntry := hTail m hm
          simp only [PactType.TailBranchOccurrences] at hEntry
          exact hEntry.1)
      simpa using hBound.1

/-- Top-down structural assembly of all compiler invariants, against an
ambient list of enclosing binder names.  Carrying `bound` is what lets a
recursion body be compiled *open*: the `.recur` case descends into `body` with
`binder :: bound` rather than demanding closedness, and closedness is recovered
only where a constructor genuinely needs it (below a product, and in the
generated conjunctions of an `offer`), using the fact that a bound name cannot
occur there. -/
theorem compilationProofBundle_of_boundedRegular
    (signature : TypeAlphabet) : ∀ processType (bound : List String),
    signature.WellFormed →
    signature.Supports processType →
    PactType.AllTailOccurrences bound True processType →
    PactType.AllVariablesBound bound processType →
    PactType.BinderHygienic bound processType →
    PactType.ClockGuarded processType →
    PactType.TailRecursive processType →
    PactType.SameCycleMessageLinear processType →
    PactType.InterfaceScoped processType →
    CompilationProofBundle signature processType := by
  intro processType bound
  cases processType with
  | message msg dir =>
      intro _ _ _ _ _ _ _ _ _
      exact
        { future := compilationFutureCorrect_message signature msg dir
          completing := compilationCompletingCorrect_message signature msg dir
          scopedStep := compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
            signature (.message msg dir)
              (compilationFragmentStepCorrect_message_leaf signature msg dir)
          execution := compilationSequenceExecutionCorrect_message signature
            msg dir }
  | progress pid =>
      intro _ _ _ _ _ _ _ _ _
      exact
        { future := compilationFutureCorrect_progress signature pid
          completing := compilationCompletingCorrect_progress signature pid
          scopedStep := compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
            signature (.progress pid)
              (compilationFragmentStepCorrect_progress_leaf signature pid)
          execution := compilationSequenceExecutionCorrect_progress signature
            pid }
  | tock =>
      intro _ _ _ _ _ _ _ _ _
      exact
        { future := compilationFutureCorrect_tock signature
          completing := compilationCompletingCorrect_tock signature
          scopedStep := compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
            signature .tock
              (compilationFragmentStepCorrect_tock_leaf signature)
          execution := compilationSequenceExecutionCorrect_tock signature }
  | skip =>
      intro _ _ _ _ _ _ _ _ _
      exact
        { future := compilationFutureCorrect_skip signature
          completing := compilationCompletingCorrect_skip signature
          scopedStep := compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
            signature .skip
              (compilationFragmentStepCorrect_skip_leaf signature)
          execution := compilationSequenceExecutionCorrect_skip signature }
  | var markerName =>
      intro _ _ _ _ _ _ _ _ _
      exact
        { future := compilationFutureCorrect_var signature markerName
          completing := compilationCompletingCorrect_var signature markerName
          scopedStep := compilationScopedFragmentStepCorrect_var signature
            markerName
          execution := compilationSequenceExecutionCorrect_var signature
            markerName }
  | recur binder body =>
      intro hSignature hSupports hAllTail hClosed hHygienic hGuarded hTail
        hLinear hScoped
      have hSupportBody : signature.Supports body := by
        simpa only [TypeAlphabet.Supports] using hSupports
      have hHygienicFields : binder ∉ bound ∧
          PactType.BinderHygienic (binder :: bound) body := by
        simpa only [PactType.BinderHygienic] using hHygienic
      have hBoundBody : PactType.AllVariablesBound (binder :: bound) body := by
        simpa only [PactType.AllVariablesBound] using hClosed
      have hGuardedFields : body.GuardedOccurrences binder False ∧
          body.ClockGuarded := by
        simpa only [PactType.ClockGuarded] using hGuarded
      have hTailFields : body.TailOccurrences binder True ∧
          body.TailRecursive := by
        simpa only [PactType.TailRecursive] using hTail
      have hLinearFields : body.SameCycleMessageLinear ∧
          Disjoint (PactType.SuffixMessageIds body)
            (PactType.PrefixMessageIds body) := by
        simpa only [PactType.SameCycleMessageLinear] using hLinear
      have hScopedBody : body.InterfaceScoped := by
        simpa only [PactType.InterfaceScoped] using hScoped
      have hAllTailBody : PactType.AllTailOccurrences (binder :: bound) True
          body := by
        intro m hm
        rcases List.mem_cons.mp hm with rfl | hRest
        · exact hTailFields.1
        · have hNe : ¬ binder = m := by
            intro hEq
            exact hHygienicFields.1 (hEq ▸ hRest)
          have hEntry := hAllTail m hRest
          simpa only [PactType.TailOccurrences, if_neg hNe] using hEntry
      have hBodyBundle := compilationProofBundle_of_boundedRegular signature
        body (binder :: bound) hSignature hSupportBody hAllTailBody hBoundBody
          hHygienicFields.2 hGuardedFields.2 hTailFields.2 hLinearFields.1
            hScopedBody
      have hMarker := compilationMarkerReachable_iff signature
        (binder :: bound) binder body List.mem_cons_self hAllTailBody
          hSignature hSupportBody hBoundBody hHygienicFields.2
            hGuardedFields.2 hTailFields.2 hLinearFields.1 hScopedBody
        (fun child hChildSize hChildSupports hChildClosed hChildHygienic
            hChildGuarded hChildTail hChildLinear hChildScoped =>
          compilationProofBundle_of_boundedRegular signature child []
            hSignature hChildSupports (by intro m hm; simp at hm) hChildClosed
              hChildHygienic hChildGuarded hChildTail hChildLinear
                hChildScoped)
      exact compilationProofBundle_recursion_bounded_leaf signature bound
        binder body hSignature hSupports hHygienic hGuarded hTail hLinear
          hScoped hBodyBundle hMarker
  | choice left right =>
      intro hSignature hSupports hAllTail hClosed hHygienic hGuarded hTail
        hLinear hScoped
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.AllVariablesBound] at hClosed
      simp only [PactType.BinderHygienic] at hHygienic
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.SameCycleMessageLinear] at hLinear
      simp only [PactType.InterfaceScoped] at hScoped
      have hAllTailLeft : PactType.AllTailOccurrences bound True left := by
        intro m hm
        have hEntry := hAllTail m hm
        simp only [PactType.TailOccurrences] at hEntry
        exact hEntry.1
      have hAllTailRight : PactType.AllTailOccurrences bound True right := by
        intro m hm
        have hEntry := hAllTail m hm
        simp only [PactType.TailOccurrences] at hEntry
        exact hEntry.2
      have hLeft := compilationProofBundle_of_boundedRegular signature
        left bound hSignature hSupports.1 hAllTailLeft hClosed.1 hHygienic.1
          hGuarded.1 hTail.1 hLinear.1 hScoped.1
      have hRight := compilationProofBundle_of_boundedRegular signature
        right bound hSignature hSupports.2 hAllTailRight hClosed.2 hHygienic.2
          hGuarded.2 hTail.2 hLinear.2 hScoped.2
      exact
        { future := compilationFutureCorrect_choice signature left right
            hLeft.future hRight.future
          completing := compilationCompletingCorrect_choice signature left right
            hLeft.completing hRight.completing
          scopedStep := compilationFragmentStepCorrect_choice_leaf signature
            left right hLeft hRight
          execution := compilationSequenceExecutionCorrect_choice signature
            left right hLeft.execution hRight.execution }
  | fairChoice bid left right =>
      intro hSignature hSupports hAllTail hClosed hHygienic hGuarded hTail
        hLinear hScoped
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.AllVariablesBound] at hClosed
      simp only [PactType.BinderHygienic] at hHygienic
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.SameCycleMessageLinear] at hLinear
      simp only [PactType.InterfaceScoped] at hScoped
      have hAllTailLeft : PactType.AllTailOccurrences bound True left := by
        intro m hm
        have hEntry := hAllTail m hm
        simp only [PactType.TailOccurrences] at hEntry
        exact hEntry.1
      have hAllTailRight : PactType.AllTailOccurrences bound True right := by
        intro m hm
        have hEntry := hAllTail m hm
        simp only [PactType.TailOccurrences] at hEntry
        exact hEntry.2
      have hLeft := compilationProofBundle_of_boundedRegular signature
        left bound hSignature hSupports.2.1 hAllTailLeft hClosed.1 hHygienic.1
          hGuarded.1 hTail.1 hLinear.1 hScoped.1
      have hRight := compilationProofBundle_of_boundedRegular signature
        right bound hSignature hSupports.2.2 hAllTailRight hClosed.2 hHygienic.2
          hGuarded.2 hTail.2 hLinear.2 hScoped.2
      exact
        { future := compilationFutureCorrect_fairChoice signature bid left right
            hLeft.future hRight.future
          completing := compilationCompletingCorrect_fairChoice signature bid
            left right hLeft.completing hRight.completing
          scopedStep := compilationFragmentStepCorrect_fairChoice_leaf
            signature bid left right hLeft hRight
          execution := compilationSequenceExecutionCorrect_fairChoice signature
            bid left right hLeft.execution hRight.execution }
  | seq left right =>
      intro hSignature hSupports hAllTail hClosed hHygienic hGuarded hTail
        hLinear hScoped
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.AllVariablesBound] at hClosed
      simp only [PactType.BinderHygienic] at hHygienic
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.SameCycleMessageLinear] at hLinear
      simp only [PactType.InterfaceScoped] at hScoped
      have hAllTailLeftFalse : PactType.AllTailOccurrences bound False left := by
        intro m hm
        have hEntry := hAllTail m hm
        simp only [PactType.TailOccurrences] at hEntry
        exact hEntry.1
      have hAllTailLeft : PactType.AllTailOccurrences bound True left :=
        fun m hm => PactType.tailOccurrences_mono m (fun h => h.elim) left
          (hAllTailLeftFalse m hm)
      have hAllTailRight : PactType.AllTailOccurrences bound True right := by
        intro m hm
        have hEntry := hAllTail m hm
        simp only [PactType.TailOccurrences] at hEntry
        exact hEntry.2
      have hLeft := compilationProofBundle_of_boundedRegular signature
        left bound hSignature hSupports.1 hAllTailLeft hClosed.1 hHygienic.1
          hGuarded.1 hTail.1 hLinear.1 hScoped.1
      have hRight := compilationProofBundle_of_boundedRegular signature
        right bound hSignature hSupports.2 hAllTailRight hClosed.2 hHygienic.2
          hGuarded.2 hTail.2 hLinear.2.1 hScoped.2
      have hFuture := compilationFutureCorrect_sequence signature left right
        hLeft hRight hLeft.execution
      exact
        { future := hFuture
          completing := compilationCompletingCorrect_sequence signature left
            right hLeft.completing hRight.completing
          scopedStep := compilationScopedFragmentStepCorrect_sequence_leaf
            signature left right hLeft hRight hFuture
          execution := compilationSequenceExecutionCorrect_sequence signature
            left right hLeft.execution hRight.execution }
  | par left right interface =>
      intro hSignature hSupports hAllTail hClosed hHygienic hGuarded hTail
        hLinear hScoped
      have hScopedWhole : PactType.InterfaceScoped (.par left right interface) :=
        hScoped
      have hAllTailWhole : PactType.AllTailOccurrences bound False
          (.par left right interface) := by
        intro m hm
        have hEntry := hAllTail m hm
        simp only [PactType.TailOccurrences] at hEntry ⊢
        exact hEntry
      have hClosedWhole : PactType.AllVariablesBound []
          (.par left right interface) := by
        apply PactType.allVariablesBound_drop_of_allTailOccurrences_false bound
          [] (.par left right interface) hAllTailWhole
        simpa using hClosed
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.AllVariablesBound] at hClosed
      simp only [PactType.BinderHygienic] at hHygienic
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.SameCycleMessageLinear] at hLinear
      simp only [PactType.InterfaceScoped] at hScoped
      have hAllTailLeft : PactType.AllTailOccurrences bound True left := by
        intro m hm
        have hEntry := hAllTail m hm
        simp only [PactType.TailOccurrences] at hEntry
        exact PactType.tailOccurrences_mono m (fun h => h.elim) left hEntry.1
      have hAllTailRight : PactType.AllTailOccurrences bound True right := by
        intro m hm
        have hEntry := hAllTail m hm
        simp only [PactType.TailOccurrences] at hEntry
        exact PactType.tailOccurrences_mono m (fun h => h.elim) right hEntry.2
      have hLeft := compilationProofBundle_of_boundedRegular signature
        left bound hSignature hSupports.2.1 hAllTailLeft hClosed.1 hHygienic.1
          hGuarded.1 hTail.1 hLinear.1 hScoped.2.1
      have hRight := compilationProofBundle_of_boundedRegular signature
        right bound hSignature hSupports.2.2 hAllTailRight hClosed.2 hHygienic.2
          hGuarded.2 hTail.2 hLinear.2 hScoped.2.2
      exact
        { future := compilationFutureCorrect_parallel signature left right
            interface hLeft.future hRight.future
          completing := compilationCompletingCorrect_parallel signature left
            right interface hLeft.completing hRight.completing
          scopedStep := compilationFragmentStepCorrect_parallel_leaf
            signature left right interface hSignature hSupports.1 hScopedWhole
              hClosedWhole hLeft hRight
          execution :=
            compilationSequenceExecutionCorrect_parallel_regular_leaf
              signature left right interface
                (by
                  have hFields := hClosedWhole
                  simp only [PactType.AllVariablesBound] at hFields
                  exact hFields.1)
                (by
                  have hFields := hClosedWhole
                  simp only [PactType.AllVariablesBound] at hFields
                  exact hFields.2) hLeft hRight }
  | xoffer elseType branches =>
      intro hSignature hSupports hAllTail hClosed hHygienic hGuarded hTail
        hLinear hScoped
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.AllVariablesBound] at hClosed
      simp only [PactType.BinderHygienic] at hHygienic
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.SameCycleMessageLinear] at hLinear
      simp only [PactType.InterfaceScoped] at hScoped
      have hAllTailElse : PactType.AllTailOccurrences bound True elseType := by
        intro m hm
        have hEntry := hAllTail m hm
        simp only [PactType.TailOccurrences] at hEntry
        exact hEntry.1
      have hElse := compilationProofBundle_of_boundedRegular signature
        elseType bound hSignature hSupports.1 hAllTailElse hClosed.1
          hHygienic.1 hGuarded.1 hTail.1 hLinear.1 hScoped.1
      have hBranches : ∀ (action : BareMessage) (branchType : PactType)
          (index : Nat), branches[index]? = some (action, branchType) →
            CompilationProofBundle signature branchType := by
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
        exact compilationProofBundle_of_boundedRegular signature
          branchType bound hSignature
          (supports_branch_of_mem signature branches (action, branchType)
            hSupports.2 hMember)
          (by
            intro m hm
            have hEntry := hAllTail m hm
            simp only [PactType.TailOccurrences] at hEntry
            exact tailOccurrences_branch_of_mem m True branches hEntry.2
              (action, branchType) hMember)
          (allVariablesBound_branch_of_mem bound branches (action, branchType)
            hClosed.2 hMember)
          (binderHygienic_branch_of_mem bound branches (action, branchType)
            hHygienic.2 hMember)
          (clockGuarded_branch_of_mem branches (action, branchType)
            hGuarded.2 hMember)
          (tailRecursive_branch_of_mem branches (action, branchType)
            hTail.2 hMember)
          (sameCycleMessageLinear_branch_of_mem branches
            (action, branchType) hLinear.2 hMember)
          (interfaceScoped_branch_of_mem branches (action, branchType)
            hScoped.2 hMember)
      exact compilationProofBundle_xoffer_leaf signature elseType branches
        hSignature (by simpa [TypeAlphabet.Supports] using hSupports)
        (by simpa [PactType.ClockGuarded] using hGuarded)
        (by simpa [PactType.TailRecursive] using hTail)
        (by simpa [PactType.SameCycleMessageLinear] using hLinear)
        (by simpa [PactType.InterfaceScoped] using hScoped) hElse hBranches
  | offer elseType branches =>
      intro hSignature hSupports hAllTail hClosed hHygienic hGuarded hTail
        hLinear hScoped
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.AllVariablesBound] at hClosed
      simp only [PactType.BinderHygienic] at hHygienic
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.SameCycleMessageLinear] at hLinear
      simp only [PactType.InterfaceScoped] at hScoped
      have hAllTailElse : PactType.AllTailOccurrences bound True elseType := by
        intro m hm
        have hEntry := hAllTail m hm
        simp only [PactType.TailOccurrences] at hEntry
        exact hEntry.1
      have hElse := compilationProofBundle_of_boundedRegular signature
        elseType bound hSignature hSupports.1 hAllTailElse hClosed.1
          hHygienic.1 hGuarded.1 hTail.1 hLinear.1 hScoped.1
      have hBranches : ∀ (action : BareMessage) (branchType : PactType)
          (index : Nat), branches[index]? = some (action, branchType) →
            CompilationProofBundle signature branchType := by
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
        exact compilationProofBundle_of_boundedRegular signature
          branchType bound hSignature
          (supports_branch_of_mem signature branches (action, branchType)
            hSupports.2 hMember)
          (by
            intro m hm
            have hEntry := hAllTail m hm
            simp only [PactType.TailOccurrences] at hEntry
            exact PactType.tailOccurrences_mono m (fun h => h.elim) branchType
              (tailOccurrences_branch_of_mem m _ branches hEntry.2
                (action, branchType) hMember))
          (allVariablesBound_branch_of_mem bound branches (action, branchType)
            hClosed.2 hMember)
          (binderHygienic_branch_of_mem bound branches (action, branchType)
            hHygienic.2 hMember)
          (clockGuarded_branch_of_mem branches (action, branchType)
            hGuarded.2 hMember)
          (tailRecursive_branch_of_mem branches (action, branchType)
            hTail.2 hMember)
          (sameCycleMessageLinear_branch_of_mem branches
            (action, branchType) hLinear.2 hMember)
          (interfaceScoped_branch_of_mem branches (action, branchType)
            hScoped.2 hMember)
      exact compilationProofBundle_offer_leaf signature elseType branches
        hSignature (by simpa [TypeAlphabet.Supports] using hSupports)
        (allBranchVariablesBound_nil_of_bound bound branches hClosed.2
          (fun m hm => by
            have hEntry := hAllTail m hm
            simp only [PactType.TailOccurrences] at hEntry
            exact hEntry.2))
        (by simpa [PactType.ClockGuarded] using hGuarded)
        (by simpa [PactType.TailRecursive] using hTail)
        (by simpa [PactType.SameCycleMessageLinear] using hLinear)
        (by simpa [PactType.InterfaceScoped] using hScoped) hElse hBranches
termination_by processType bound => sizeOf processType
decreasing_by
  all_goals

    first
    | assumption
    | (simp_wf; omega)

/-- Closed instance of the bounded assembly: at the top level no binder is
open, so the ambient tail-occurrence premise is vacuous. -/
theorem compilationProofBundle_of_closedGuardedRegular
    (signature : TypeAlphabet) : ∀ processType,
    signature.WellFormed →
    signature.Supports processType →
    PactType.AllVariablesBound [] processType →
    PactType.BinderHygienic [] processType →
    PactType.ClockGuarded processType →
    PactType.TailRecursive processType →
    PactType.SameCycleMessageLinear processType →
    PactType.InterfaceScoped processType →
    CompilationProofBundle signature processType :=
  fun processType hSignature hSupports hClosed hHygienic hGuarded hTail
      hLinear hScoped =>
    compilationProofBundle_of_boundedRegular signature processType []
      hSignature hSupports (by intro m hm; simp at hm) hClosed hHygienic
        hGuarded hTail hLinear hScoped

/-- Public one-step bisimulation follows immediately from the hierarchical
bundle and the uniform fragment-to-public exporter. -/
theorem compilationStepCorrect_of_closedGuardedRegular
    (signature : TypeAlphabet) (processType : PactType)
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports processType)
    (hClosed : PactType.AllVariablesBound [] processType)
    (hHygienic : PactType.BinderHygienic [] processType)
    (hGuarded : PactType.ClockGuarded processType)
    (hTail : PactType.TailRecursive processType)
    (hLinear : PactType.SameCycleMessageLinear processType)
    (hScoped : PactType.InterfaceScoped processType) :
    CompilationStepCorrect signature processType := by
  have hBundle := compilationProofBundle_of_closedGuardedRegular signature
    processType hSignature hSupports hClosed hHygienic hGuarded hTail hLinear
      hScoped
  intro residual residual' state env label offers hRelated hSymbol
  exact (compilationStepCorrect_of_scopedFragmentStepCorrect signature
    processType hSignature hSupports hBundle.scopedStep) hRelated hSymbol

/-- The process-to-automaton simulation of Lemma 4.6. -/
structure ProcessAutomatonCorrespondence
    (process : Proc) (processType : PactType) (automaton : TypeAutomaton) : Type where
  relation : Proc → TypeAutomatonState → Prop
  initial : relation process automaton.initial
  matchStep :
    ∀ {p₀ p₁ : Proc} {state : TypeAutomatonState}
      {env : Environment} {label : Label},
      relation p₀ state →
      ProcessTransition env p₀ label p₁ →
      ∃ state' offers,
        automaton.HasEdge state (eraseEnvironment env) (eraseLabel label) offers state' ∧
        relation p₁ state'

end

end Pact
