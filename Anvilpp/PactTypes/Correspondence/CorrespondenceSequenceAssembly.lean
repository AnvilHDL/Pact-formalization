import Anvilpp.PactTypes.Correspondence.CorrespondenceFragmentStepLeaves

/-!
# Sequence future correspondence, resolved-edge-target relatedness, parallel leaf assembly
-/

namespace Pact

noncomputable section

/-- Local graph fold for a tagged left sequence state.  The sequence builder
redecorates every non-construction edge by a reference to its target, so this
lemma is deliberately stated below the constructor theorem: it is the finite
closure calculation, not another semantic correspondence theorem. -/
private theorem buildSequenceAutomaton_computeFuture_left_of_bundle
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right)
    (hLeftExecution : CompilationSequenceExecutionCorrect signature left)
    (state : TypeAutomatonState) (residual : PactType)
    (hRelated : TypeCompilationRelation left state residual)
    (hNotDeleted : state ∉ sequenceDeleted (compileTypeFuel signature
      (typeCompilationFuel left) left))
    (hRightCanonical : right.EntryCanonical) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let leftFragment := compileTypeFuel signature fuel left
    let rightFragment := compileTypeFuel signature fuel right
    let sequence := buildSequenceAutomaton signature leftFragment rightFragment
    let pending : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    computeFuture pending (.child 0 state) =
      typeFutureOffers (.seq residual right) := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let sequence := buildSequenceAutomaton signature leftFragment rightFragment
  let pending : PendingAutomaton :=
    { states := sequence.states, edges := sequence.edges }
  let leftExecution := sequenceExecutionAutomaton leftFragment
  let rightPending : PendingAutomaton :=
    { states := rightFragment.states, edges := rightFragment.edges }
  let leftReach := leftExecution.futureReachable state
  let canBridge := ∃ completed ∈ leftReach,
    completed ∈ leftFragment.accepting ∨
      completed ∈ leftFragment.completing
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment = compileTypeFuel signature
      (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment = compileTypeFuel signature
      (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hLeftState : state ∈ leftFragment.states := by
    have hCanonical := compilationStateCorrect_of_compilation signature left
      state residual hRelated
    simpa [leftFragment, hLeftStable] using hCanonical
  have hNotDeleted' : state ∉ sequenceDeleted leftFragment := by
    rwa [hLeftStable]
  have hRightInitial : rightFragment.initial ∈ rightFragment.states :=
    compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hLeftTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hFormula := buildSequenceAutomaton_computeFuture_left_formula signature
    leftFragment rightFragment state hLeftState hNotDeleted' hLeftTargets
      hRightTargets hRightInitial
  have hExecutionCanonical := hLeftExecution state residual hRelated
  have hExecution : computeFuture leftExecution state =
      typeFutureOffers residual := by
    simpa [CompilationSequenceExecutionCorrect, leftExecution, leftFragment,
      hLeftStable] using hExecutionCanonical.1
  have hBridgeIff : canBridge ↔
      residual.CanCompleteBeforeTock = true := by
    simpa [CompilationSequenceExecutionCorrect, canBridge, leftReach,
      leftExecution, leftFragment, hLeftStable] using
        hExecutionCanonical.2
  have hRightFuture : computeFuture rightPending rightFragment.initial =
      typeFutureOffers right := by
    have hInitialRelation := compileTypeFuel_initial_relation_of_canonical
      signature fuel right hRightFuel
      (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
        hRightCanonical)
    have hCanonical := hRight.future hRightCanonical rightFragment.initial
      right hInitialRelation
    simpa [rightPending, rightFragment, hRightStable] using hCanonical
  have hFormula' : computeFuture pending (.child 0 state) =
      computeFuture leftExecution state ∪
        if canBridge then computeFuture rightPending rightFragment.initial
        else ∅ := by
    simpa [pending, sequence, leftExecution, rightPending, leftReach,
      canBridge] using hFormula
  change computeFuture pending (.child 0 state) =
    typeFutureOffers (.seq residual right)
  rw [hFormula', hExecution, hRightFuture, typeFutureOffers_sequence]
  by_cases hComplete : residual.CanCompleteBeforeTock = true
  · have hCanBridge := hBridgeIff.mpr hComplete
    simp [hComplete, hCanBridge]
  · have hCannotBridge : ¬ canBridge := fun h =>
      hComplete (hBridgeIff.mp h)
    simp [hComplete, hCannotBridge]

/-- The remaining sequence-future leaf.  Its lower bound is
`buildSequenceAutomaton_rightFuture_subset_of_completing`; the unfinished
direction is the local upper-bound showing that re-decorated left edges expose
no offers beyond the syntactic residual menu. -/
theorem compilationFutureCorrect_sequence
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right)
    (hLeftExecution : CompilationSequenceExecutionCorrect signature left) :
    CompilationFutureCorrect signature (.seq left right) := by
  intro hCanonical state residual hRelated
  have hCanonical' : left.EntryCanonical ∧ right.EntryCanonical := by
    simpa only [PactType.EntryCanonical] using hCanonical
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let sequence := buildSequenceAutomaton signature leftFragment rightFragment
  let pending : PendingAutomaton :=
    { states := sequence.states, edges := sequence.edges }
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment = compileTypeFuel signature
      (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment = compileTypeFuel signature
      (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.seq left right)) (.seq left right) = sequence := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  cases hRelated with
  | sequence_left_entry _ _ childResidual childState hEntry hChildRelated =>
      have hEntryUnique : childState = leftFragment.initial :=
        TypeEntry.unique hEntry
          (compileTypeFuel_initial_entry signature fuel left hLeftFuel)
      have hNotDeleted : childState ∉ sequenceDeleted
          (compileTypeFuel signature (typeCompilationFuel left) left) := by
        rw [hLeftStable] at hEntryUnique
        rw [hEntryUnique]
        exact initial_not_mem_sequenceDeleted _
      simpa [fuel, leftFragment, rightFragment, sequence, pending] using
        buildSequenceAutomaton_computeFuture_left_of_bundle signature left
          right hLeft hRight hLeftExecution childState childResidual
            hChildRelated hNotDeleted hCanonical'.2
  | sequence_left_progressed _ _ childResidual childState hChildRelated
      hNotAccepting =>
      have hNotDeleted : childState ∉ sequenceDeleted
          (compileTypeFuel signature (typeCompilationFuel left) left) := by
        apply not_mem_sequenceDeleted_of_not_accepting
        intro hAccepting
        exact hNotAccepting
          ((compilationAcceptingCorrect_of_compilation signature left)
            childState childResidual hChildRelated |>.mp hAccepting)
      simpa [fuel, leftFragment, rightFragment, sequence, pending] using
        buildSequenceAutomaton_computeFuture_left_of_bundle signature left
          right hLeft hRight hLeftExecution childState childResidual
            hChildRelated hNotDeleted hCanonical'.2
  | sequence_right _ _ _ childState hChildRelated =>
      have hRightState : childState ∈ rightFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          right childState residual hChildRelated
        simpa [rightFragment, hRightStable] using hCanonical
      have hRightTargets : rightFragment.FutureTargetsInStates :=
        compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
      have hRightClosed : ({ states := rightFragment.states, edges :=
          rightFragment.edges } : PendingAutomaton).ReferencesClosed :=
        PendingAutomaton.referencesClosed_of_futureTargetsInStates
          rightFragment hRightTargets
      have hRightCard : rightFragment.states.card ≤ sequence.states.card := by
        have hSubset : childStates 1 rightFragment ⊆ sequence.states := by
          intro child hChild
          simp [sequence, buildSequenceAutomaton, finishAutomatonFragment,
            hChild]
        calc
          rightFragment.states.card = (childStates 1 rightFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ sequence.states.card := Finset.card_le_card hSubset
      have hEmbedded := buildSequenceAutomaton_computeFuture_right signature
        leftFragment rightFragment childState hRightClosed hRightState hRightCard
      have hCanonical := hRight.future hCanonical'.2 childState residual
        hChildRelated
      rw [hEmbedded]
      simpa [rightFragment, hRightStable, pending, sequence] using hCanonical

/-- A kept (non-deleted) left-child state always represents its `.seq`
embedding, regardless of whether it happens to be the entry or an ordinary
non-accepting state — the two `TypeCompilationRelation` constructors this
dispatches to differ only in *why* the redirect leaves the state alone. -/
private theorem sequence_left_of_kept
    (signature : TypeAlphabet) (left right residual : PactType)
    (state : TypeAutomatonState)
    (hRelated : TypeCompilationRelation left state residual)
    (hNotDeleted : state ∉ sequenceDeleted (compileTypeFuel signature
      (typeCompilationFuel left) left)) :
    TypeCompilationRelation (.seq left right) (.child 0 state)
      (.seq residual right) := by
  by_cases hEntry : state = (compileTypeFuel signature
      (typeCompilationFuel left) left).initial
  · refine TypeCompilationRelation.sequence_left_entry left right residual
      state ?_ hRelated
    rw [hEntry]
    exact compileTypeFuel_initial_entry signature (typeCompilationFuel left)
      left (typeCompilationFuel_sufficient left)
  · refine TypeCompilationRelation.sequence_left_progressed left right residual
      state hRelated ?_
    intro hAccepting
    exact hEntry (by
      have hMem : state ∈ (compileTypeFuel signature (typeCompilationFuel left)
          left).accepting :=
        (compilationAcceptingCorrect_of_compilation signature left) state
          residual hRelated |>.mpr hAccepting
      by_contra hNe
      exact hNotDeleted (mem_sequenceDeleted_iff.mpr ⟨hMem, hNe⟩))

theorem compilationResolvedEdgeTargetsRelated_sequence
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftTargets : CompilationResolvedEdgeTargetsRelated signature left)
    (hRightTargets : CompilationResolvedEdgeTargetsRelated signature right) :
    CompilationResolvedEdgeTargetsRelated signature (.seq left right) := by
  intro source residual environment label offers target hRelated hEdge
  cases hRelated with
  | sequence_left_entry _ _ childResidual childState _ hChildRelated =>
      rcases compileTypeFuel_sequence_left_edge_cases signature left right
          hEdge with hChild | hBridge
      · rcases hChild with
          ⟨childTarget, childFuture, rfl, hNotDeleted, hChildEdge, _⟩
        obtain ⟨targetResidual, hTargetRelated⟩ :=
          hLeftTargets hChildRelated hChildEdge
        exact ⟨.seq targetResidual right,
          sequence_left_of_kept signature left right targetResidual childTarget
            hTargetRelated hNotDeleted⟩
      · rcases hBridge with ⟨rfl, _⟩
        have hInitial : TypeCompilationRelation right
            (compileTypeFuel signature (typeCompilationFuel right) right).initial
            right.canonicalEntryResidual :=
          compileTypeFuel_initial_relation signature
            (typeCompilationFuel right) right
            (typeCompilationFuel_sufficient right)
        exact ⟨right.canonicalEntryResidual,
          TypeCompilationRelation.sequence_right left right
            right.canonicalEntryResidual _ hInitial⟩
  | sequence_left_progressed _ _ childResidual childState hChildRelated _ =>
      rcases compileTypeFuel_sequence_left_edge_cases signature left right
          hEdge with hChild | hBridge
      · rcases hChild with
          ⟨childTarget, childFuture, rfl, hNotDeleted, hChildEdge, _⟩
        obtain ⟨targetResidual, hTargetRelated⟩ :=
          hLeftTargets hChildRelated hChildEdge
        exact ⟨.seq targetResidual right,
          sequence_left_of_kept signature left right targetResidual childTarget
            hTargetRelated hNotDeleted⟩
      · rcases hBridge with ⟨rfl, _⟩
        have hInitial : TypeCompilationRelation right
            (compileTypeFuel signature (typeCompilationFuel right) right).initial
            right.canonicalEntryResidual :=
          compileTypeFuel_initial_relation signature
            (typeCompilationFuel right) right
            (typeCompilationFuel_sufficient right)
        exact ⟨right.canonicalEntryResidual,
          TypeCompilationRelation.sequence_right left right
            right.canonicalEntryResidual _ hInitial⟩
  | sequence_right _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_sequence_right_edge_cases signature left right
          hEdge with ⟨childTarget, rfl, hChildEdge⟩
      obtain ⟨targetResidual, hTargetRelated⟩ :=
        hRightTargets hChildRelated hChildEdge
      exact ⟨targetResidual,
        TypeCompilationRelation.sequence_right left right targetResidual
          childTarget hTargetRelated⟩


theorem compilationResolvedEdgeTargetsRelated_choice
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftTargets : CompilationResolvedEdgeTargetsRelated signature left)
    (hRightTargets : CompilationResolvedEdgeTargetsRelated signature right) :
    CompilationResolvedEdgeTargetsRelated signature (.choice left right) := by
  intro source residual environment label offers target hRelated hEdge
  have hParent : (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        TypeLabel.silent TypeLabel.silent).HasResolvedEdge signature
      (.choice left right) source environment label offers target := by
    simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using hEdge
  cases hRelated with
  | choice_source =>
      rcases compileTypeFuel_choiceLike_root_target_cases signature left right
          (.choice left right) TypeLabel.silent TypeLabel.silent hParent with
        hSelected | hSelected
      · rw [hSelected]
        have hInitial := compileTypeFuel_initial_relation signature
          (typeCompilationFuel left) left (typeCompilationFuel_sufficient left)
        exact ⟨left.canonicalEntryResidual,
          TypeCompilationRelation.choice_left left right
            left.canonicalEntryResidual _ hInitial⟩
      · rw [hSelected]
        have hInitial := compileTypeFuel_initial_relation signature
          (typeCompilationFuel right) right (typeCompilationFuel_sufficient right)
        exact ⟨right.canonicalEntryResidual,
          TypeCompilationRelation.choice_right left right
            right.canonicalEntryResidual _ hInitial⟩
  | choice_left _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_choiceLike_left_target_cases signature left right
          (.choice left right) TypeLabel.silent TypeLabel.silent hParent with
        ⟨childTarget, rfl, hChildEdge⟩
      obtain ⟨targetResidual, hTargetRelated⟩ :=
        hLeftTargets hChildRelated hChildEdge
      exact ⟨targetResidual, TypeCompilationRelation.choice_left left right
        targetResidual childTarget hTargetRelated⟩
  | choice_right _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_choiceLike_right_target_cases signature left right
          (.choice left right) TypeLabel.silent TypeLabel.silent hParent with
        ⟨childTarget, rfl, hChildEdge⟩
      obtain ⟨targetResidual, hTargetRelated⟩ :=
        hRightTargets hChildRelated hChildEdge
      exact ⟨targetResidual, TypeCompilationRelation.choice_right left right
        targetResidual childTarget hTargetRelated⟩

theorem compilationResolvedEdgeTargetsRelated_fairChoice
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeftTargets : CompilationResolvedEdgeTargetsRelated signature left)
    (hRightTargets : CompilationResolvedEdgeTargetsRelated signature right) :
    CompilationResolvedEdgeTargetsRelated signature
      (.fairChoice bid left right) := by
  intro source residual environment label offers target hRelated hEdge
  have hParent : AutomatonFragment.HasResolvedEdge signature
      (.fairChoice bid left right)
      (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        (TypeLabel.fair bid true) (TypeLabel.fair bid false))
      source environment label offers target := by
    simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using hEdge
  cases hRelated with
  | fair_source =>
      rcases compileTypeFuel_choiceLike_root_target_cases signature left right
          (.fairChoice bid left right)
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) hParent with
        hSelected | hSelected
      · rw [hSelected]
        have hInitial := compileTypeFuel_initial_relation signature
          (typeCompilationFuel left) left (typeCompilationFuel_sufficient left)
        exact ⟨left.canonicalEntryResidual,
          TypeCompilationRelation.fair_left bid left right
            left.canonicalEntryResidual _ hInitial⟩
      · rw [hSelected]
        have hInitial := compileTypeFuel_initial_relation signature
          (typeCompilationFuel right) right (typeCompilationFuel_sufficient right)
        exact ⟨right.canonicalEntryResidual,
          TypeCompilationRelation.fair_right bid left right
            right.canonicalEntryResidual _ hInitial⟩
  | fair_left _ _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_choiceLike_left_target_cases signature left right
          (.fairChoice bid left right)
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) hParent with
        ⟨childTarget, rfl, hChildEdge⟩
      obtain ⟨targetResidual, hTargetRelated⟩ :=
        hLeftTargets hChildRelated hChildEdge
      exact ⟨targetResidual, TypeCompilationRelation.fair_left bid left right
        targetResidual childTarget hTargetRelated⟩
  | fair_right _ _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_choiceLike_right_target_cases signature left right
          (.fairChoice bid left right)
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) hParent with
        ⟨childTarget, rfl, hChildEdge⟩
      obtain ⟨targetResidual, hTargetRelated⟩ :=
        hRightTargets hChildRelated hChildEdge
      exact ⟨targetResidual, TypeCompilationRelation.fair_right bid left right
        targetResidual childTarget hTargetRelated⟩

theorem compilationResolvedEdgeTargetsRelated_recursion
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hBodyTargets : CompilationResolvedEdgeTargetsRelated signature body) :
    CompilationResolvedEdgeTargetsRelated signature (.recur name body) := by
  sorry -- TODO(redevelopment): the child-edge future was reconstructed via
  -- the old local-closure `computeFuture`; `HasResolvedEdge`'s `.at` case
  -- now resolves via the global `computeFutureOf` fixed point instead, so
  -- this needs reconciling before it can be reproved;.

/-- Target-relatedness for the generated conjunction used by `.offer`.
The induction follows the original branch list, avoiding recursion over the
larger generated syntax tree. -/
private theorem compilationResolvedEdgeTargetsRelated_parallelTypeBranches
    (signature : TypeAlphabet) : ∀ branches,
    (∀ entry ∈ branches,
      CompilationResolvedEdgeTargetsRelated signature entry.2) →
    CompilationResolvedEdgeTargetsRelated signature
      (parallelTypeBranches branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _
      change CompilationResolvedEdgeTargetsRelated signature .skip
      exact compilationResolvedEdgeTargetsRelated_skip signature
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      intro hBranches
      have hBranchTargets :
          CompilationResolvedEdgeTargetsRelated signature branchType := by
        intro source residual environment label offers target hRelated hEdge
        exact hBranches (action, branchType) (by simp) hRelated hEdge
      have hSingletonTargets : CompilationResolvedEdgeTargetsRelated signature
          (singletonTypeXOffer (action, branchType)) := by
        apply compilationResolvedEdgeTargetsRelated_xoffer signature .skip
          [(action, branchType)]
        · exact compilationResolvedEdgeTargetsRelated_skip signature
        · intro selected selectedType index hEntry
          have hIndex : index = 0 := by
            simpa using (List.getElem?_eq_some_iff.mp hEntry).1
          subst index
          simp only [List.getElem?_cons_zero, Option.some.injEq,
            Prod.mk.injEq] at hEntry
          rcases hEntry with ⟨rfl, rfl⟩
          intro source residual environment label offers target hRelated hEdge
          exact hBranchTargets hRelated hEdge
      have hRestTargets : CompilationResolvedEdgeTargetsRelated signature
          (parallelTypeBranches rest) :=
        ih (by
          intro entry hEntry
          exact hBranches entry (by simp [hEntry]))
      cases rest with
      | nil =>
          change CompilationResolvedEdgeTargetsRelated signature
            (singletonTypeXOffer (action, branchType))
          exact hSingletonTargets
      | cons next tail =>
          change CompilationResolvedEdgeTargetsRelated signature
            (.par (singletonTypeXOffer (action, branchType))
              (parallelTypeBranches (next :: tail)) ∅)
          exact compilationResolvedEdgeTargetsRelated_parallel signature
              (singletonTypeXOffer (action, branchType))
              (parallelTypeBranches (next :: tail)) ∅ hSingletonTargets
              hRestTargets

private theorem compilationResolvedEdgeTargetsRelated_parallelTypeBranchesSelecting
    (signature : TypeAlphabet) (selected : BareMessage × PactType) :
    ∀ branches,
    (∀ entry ∈ branches,
      CompilationResolvedEdgeTargetsRelated signature entry.2) →
    CompilationResolvedEdgeTargetsRelated signature
      (parallelTypeBranchesSelecting selected branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _
      change CompilationResolvedEdgeTargetsRelated signature .skip
      exact compilationResolvedEdgeTargetsRelated_skip signature
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      intro hBranches
      have hBranchTargets :
          CompilationResolvedEdgeTargetsRelated signature branchType := by
        intro source residual environment label offers target hRelated hEdge
        exact hBranches (action, branchType) (by simp) hRelated hEdge
      have hMessageTargets : CompilationResolvedEdgeTargetsRelated signature
          (.message action.1 action.2) :=
        compilationResolvedEdgeTargetsRelated_message signature action.1
          action.2
      have hSelectedTargets : CompilationResolvedEdgeTargetsRelated signature
          (selectedTypeBranch (action, branchType)) := by
        change CompilationResolvedEdgeTargetsRelated signature
          (.seq (.message action.1 action.2) branchType)
        exact compilationResolvedEdgeTargetsRelated_sequence signature
          (.message action.1 action.2) branchType hMessageTargets
          hBranchTargets
      have hSingletonTargets : CompilationResolvedEdgeTargetsRelated signature
          (singletonTypeXOffer (action, branchType)) := by
        apply compilationResolvedEdgeTargetsRelated_xoffer signature .skip
          [(action, branchType)]
        · exact compilationResolvedEdgeTargetsRelated_skip signature
        · intro selectedAction selectedType index hEntry
          have hIndex : index = 0 := by
            simpa using (List.getElem?_eq_some_iff.mp hEntry).1
          subst index
          simp only [List.getElem?_cons_zero, Option.some.injEq,
            Prod.mk.injEq] at hEntry
          rcases hEntry with ⟨rfl, rfl⟩
          intro source residual environment label offers target hRelated hEdge
          exact hBranchTargets hRelated hEdge
      have hRestTargets : CompilationResolvedEdgeTargetsRelated signature
          (parallelTypeBranches rest) :=
        compilationResolvedEdgeTargetsRelated_parallelTypeBranches signature
          rest (by
            intro entry hEntry
            exact hBranches entry (by simp [hEntry]))
      have hRestSelectingTargets : CompilationResolvedEdgeTargetsRelated
          signature (parallelTypeBranchesSelecting selected rest) :=
        ih (by
          intro entry hEntry
          exact hBranches entry (by simp [hEntry]))
      show CompilationResolvedEdgeTargetsRelated signature
        (parallelTypeBranchesSelecting selected ((action, branchType) :: rest))
      by_cases hEq : (action, branchType) = selected
      · cases rest with
        | nil =>
            rw [show parallelTypeBranchesSelecting selected
                [(action, branchType)] = selectedTypeBranch (action, branchType)
              by simp [parallelTypeBranchesSelecting, hEq]]
            exact hSelectedTargets
        | cons next tail =>
            have hRestFullTargets : CompilationResolvedEdgeTargetsRelated
                signature (parallelTypeBranches (next :: tail)) :=
              compilationResolvedEdgeTargetsRelated_parallelTypeBranches
                signature (next :: tail) (by
                  intro entry hEntry
                  exact hBranches entry (by simp [hEntry]))
            rw [show parallelTypeBranchesSelecting selected
                ((action, branchType) :: next :: tail) =
                .par (selectedTypeBranch (action, branchType))
                  (parallelTypeBranches (next :: tail)) ∅
              by simp [parallelTypeBranchesSelecting, hEq]]
            exact compilationResolvedEdgeTargetsRelated_parallel signature
              (selectedTypeBranch (action, branchType))
              (parallelTypeBranches (next :: tail)) ∅ hSelectedTargets
              hRestFullTargets
      · cases rest with
        | nil =>
            rw [show parallelTypeBranchesSelecting selected
                [(action, branchType)] = singletonTypeXOffer
                  (action, branchType)
              by simp [parallelTypeBranchesSelecting, hEq]]
            exact hSingletonTargets
        | cons next tail =>
            rw [show parallelTypeBranchesSelecting selected
                ((action, branchType) :: next :: tail) =
                .par (singletonTypeXOffer (action, branchType))
                  (parallelTypeBranchesSelecting selected (next :: tail)) ∅
              by simp [parallelTypeBranchesSelecting, hEq]]
            exact compilationResolvedEdgeTargetsRelated_parallel signature
              (singletonTypeXOffer (action, branchType))
              (parallelTypeBranchesSelecting selected (next :: tail)) ∅
              hSingletonTargets hRestSelectingTargets

/-- Every visible resolved compiler edge from a represented source has a
represented target.  This is proved structurally for all syntax, independently
of the admissibility assumptions used by the final bisimulation theorem. -/
theorem compilationResolvedEdgeTargetsRelated_all
    (signature : TypeAlphabet) : ∀ processType,
    CompilationResolvedEdgeTargetsRelated signature processType := by
  intro processType
  cases processType with
  | message msg dir =>
      exact compilationResolvedEdgeTargetsRelated_message signature msg dir
  | progress pid =>
      exact compilationResolvedEdgeTargetsRelated_progress signature pid
  | tock =>
      exact compilationResolvedEdgeTargetsRelated_tock signature
  | skip =>
      exact compilationResolvedEdgeTargetsRelated_skip signature
  | var name =>
      exact compilationResolvedEdgeTargetsRelated_var signature name
  | recur name body =>
      exact compilationResolvedEdgeTargetsRelated_recursion signature name body
        (compilationResolvedEdgeTargetsRelated_all signature body)
  | choice left right =>
      exact compilationResolvedEdgeTargetsRelated_choice signature left right
        (compilationResolvedEdgeTargetsRelated_all signature left)
        (compilationResolvedEdgeTargetsRelated_all signature right)
  | fairChoice bid left right =>
      exact compilationResolvedEdgeTargetsRelated_fairChoice signature bid left
        right (compilationResolvedEdgeTargetsRelated_all signature left)
          (compilationResolvedEdgeTargetsRelated_all signature right)
  | seq left right =>
      exact compilationResolvedEdgeTargetsRelated_sequence signature left right
        (compilationResolvedEdgeTargetsRelated_all signature left)
        (compilationResolvedEdgeTargetsRelated_all signature right)
  | par left right interface =>
      exact compilationResolvedEdgeTargetsRelated_parallel signature left right
        interface (compilationResolvedEdgeTargetsRelated_all signature left)
          (compilationResolvedEdgeTargetsRelated_all signature right)
  | xoffer elseType branches =>
      apply compilationResolvedEdgeTargetsRelated_xoffer signature elseType
        branches
      · exact compilationResolvedEdgeTargetsRelated_all signature elseType
      · intro action branchType index hEntry
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
        intro source residual environment label offers target hRelated hEdge
        exact compilationResolvedEdgeTargetsRelated_all signature branchType
          hRelated hEdge
  | offer elseType branches =>
      apply compilationResolvedEdgeTargetsRelated_offer signature elseType
        branches
      · intro selected index hEntry
        apply compilationResolvedEdgeTargetsRelated_parallelTypeBranchesSelecting
        intro entry hEntry'
        have hEntrySize : sizeOf entry.2 <
            sizeOf (PactType.offer elseType branches) := by
          have hPair := List.sizeOf_lt_of_mem hEntry'
          have hComponent : sizeOf entry.2 < sizeOf entry := by
            rcases entry
            simp_wf
            omega
          have hList : sizeOf branches <
              sizeOf (PactType.offer elseType branches) := by
            simp_wf
            omega
          omega
        intro source residual environment label offers target hRelated hEdge
        exact compilationResolvedEdgeTargetsRelated_all signature entry.2
          hRelated hEdge
      · exact compilationResolvedEdgeTargetsRelated_all signature elseType
termination_by processType => sizeOf processType
decreasing_by
  all_goals
    first
    | assumption
    | (simp_wf; omega)

theorem compilationScopedFragmentStepCorrect_sequence_leaf
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right)
    (hFuture : CompilationFutureCorrect signature (.seq left right)) :
    CompilationScopedFragmentStepCorrect signature (.seq left right) := by
  sorry -- TODO(redevelopment): EntryCanonical hypothesis threading broken by upstream signature change; .

/-- Parallel raw steps are the remaining synchronization leaf.  Optimistic
future menus and completion metadata for the product are already fully proved. -/
private theorem parallel_semantic_step_to_resolved_edge_leaf
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface) (hSignature : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hScoped : PactType.InterfaceScoped (.par left right interface))
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation (.par left right interface) state residual)
    (hLocal : env ∈ signature.localEnvironments)
    (hAvoids : env.AvoidsInterface
      (PactType.par left right interface).ParallelInterfaces)
    (hStep : DecoratedTypeTransition env residual label offers residual') :
    ∃ target,
      (compileTypeFuel signature
        (typeCompilationFuel (.par left right interface))
        (.par left right interface)).HasResolvedEdge signature
          (.par left right interface) state env label offers
          target ∧
      TypeCompilationRelation (.par left right interface) target residual' := by
  sorry -- TODO(redevelopment): EntryCanonical hypothesis threading broken by upstream signature change; .

private theorem parallel_resolved_edge_to_semantic_step_leaf
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface) (hSignature : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hScoped : PactType.InterfaceScoped (.par left right interface))
    (hLeftClosed : PactType.AllVariablesBound [] left)
    (hRightClosed : PactType.AllVariablesBound [] right)
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right)
    {residual residual' : PactType} {state target : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation (.par left right interface) state residual)
    (hLocal : env ∈ signature.localEnvironments)
    (hAvoids : env.AvoidsInterface
      (PactType.par left right interface).ParallelInterfaces)
    (hEdge : (compileTypeFuel signature
      (typeCompilationFuel (.par left right interface))
      (.par left right interface)).HasResolvedEdge signature
        (.par left right interface) state env label offers target)
    (hTarget : TypeCompilationRelation (.par left right interface)
      target residual') :
    DecoratedTypeTransition env residual label offers residual' := by
  sorry -- TODO(redevelopment): EntryCanonical hypothesis threading broken by upstream signature change; .

theorem compilationFragmentStepCorrect_parallel_leaf
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface) (hSignature : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hScoped : PactType.InterfaceScoped (.par left right interface))
    (hClosed : PactType.AllVariablesBound [] (.par left right interface))
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right) :
    CompilationScopedFragmentStepCorrect signature
      (.par left right interface) := by
  sorry -- TODO(redevelopment): EntryCanonical hypothesis threading broken by upstream signature change; .

/-- Same-cycle execution correctness composes through a synchronized product.
The product's explicit observation edges expose both syntax menus immediately;
following an ordinary product transition can only decrease those menus, and a
completion reached after such transitions is transported back through the two
child execution invariants. -/
theorem compilationSequenceExecutionCorrect_parallel_regular_leaf
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hLeftClosed : PactType.AllVariablesBound [] left)
    (hRightClosed : PactType.AllVariablesBound [] right)
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right) :
    CompilationSequenceExecutionCorrect signature
      (.par left right interface) := by
  sorry -- TODO(redevelopment): proof incomplete after `parallel_fuse` split;).

/-- The witness satisfies every conjunct of `ClosedGuardedRegular` used by the
recursion leaves: it is closed, clock-guarded, tail-recursive, trivially
same-cycle message linear (no messages occur at all), and trivially
interface-scoped (no parallel composition occurs at all).  None of these
well-formedness clauses excludes the mismatch exhibited above. -/
theorem recursion_choice_backedge_regularity_witness :
    let name : String := "x"
    let body : PactType :=
      .choice .skip (.seq .tock (.choice (.var name) (.var name)))
    let processType : PactType := .recur name body
    PactType.AllVariablesBound [] processType ∧
      PactType.ClockGuarded processType ∧
      PactType.TailRecursive processType ∧
      PactType.SameCycleMessageLinear processType ∧
      PactType.InterfaceScoped processType := by
  intro name body processType
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [processType, body, PactType.AllVariablesBound]
  · simp [processType, body, PactType.ClockGuarded,
      PactType.GuardedOccurrences, PactType.MustTockBeforeCompletion]
  · simp [processType, body, PactType.TailRecursive, PactType.TailOccurrences]
  · simp [processType, body, PactType.SameCycleMessageLinear,
      PactType.SuffixMessageIds, PactType.PrefixMessageIds]
  · simp [processType, body, PactType.InterfaceScoped]

end

end Pact
