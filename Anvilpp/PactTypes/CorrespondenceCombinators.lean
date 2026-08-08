import Anvilpp.PactTypes.CorrespondenceCore

/-!
# Composite-constructor type-automaton correspondence
-/

namespace Pact

noncomputable section

/-! ### Ordinary choice correspondence -/

/-- The two graph-future calculations needed to decorate the fresh selection
edges of an ordinary choice.  This isolates the graph/syntax future theorem
from the otherwise structural correspondence argument. -/
def ChoiceFutureCorrect
    (signature : TypeAlphabet) (left right : PactType) : Prop :=
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    TypeLabel.silent TypeLabel.silent
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  computeFuture pending (.child 0 leftFragment.initial) =
      typeFutureOffers left ∧
    computeFuture pending (.child 1 rightFragment.initial) =
      typeFutureOffers right

private theorem buildChoiceAutomaton_hasResolvedEdge_left_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hTargets : left.FutureTargetsInStates) :
    AutomatonFragment.HasResolvedEdge
        (buildChoiceAutomaton signature left right selectionLeft selectionRight)
        (.child 0 source) env label offers (.child 0 target) ↔
      AutomatonFragment.HasResolvedEdge left source env label offers target := by
  classical
  let choice := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  have hClosed : ({ states := left.states, edges := left.edges } :
      PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates left hTargets
  have hCard : left.states.card ≤ choice.states.card := by
    have hSubset : childStates 0 left ⊆ choice.states := by
      intro state hState
      simp [choice, buildChoiceAutomaton, finishAutomatonFragment, hState]
    calc
      left.states.card = (childStates 0 left).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ choice.states.card := Finset.card_le_card hSubset
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    have hOutgoing :=
      (buildChoiceAutomaton_outgoing_left signature left right
        selectionLeft selectionRight source edge).mp ⟨hEdge, hSource⟩
    rcases hOutgoing with ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    simp only [childPendingEdge] at hEnvironment hLabel hCurrent hTarget
    have hChildTarget : childEdge.target = target := by
      injection hTarget
    refine ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, ?_, hChildTarget⟩
    cases hSpec : childEdge.future with
    | explicit future =>
        simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
    | «at» referenced removed =>
        have hReferenced := hTargets childEdge hChildEdge referenced removed hSpec
        have hEmbedding := buildChoiceAutomaton_computeFuture_left signature
          left right selectionLeft selectionRight referenced hClosed
          hReferenced hCard
        simp only [hSpec]
        simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          at hFuture
        rw [hEmbedding] at hFuture
        exact hFuture
  · rintro ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, hFuture, hChildTarget⟩
    have hOutgoing :=
      (buildChoiceAutomaton_outgoing_left signature left right
        selectionLeft selectionRight source (childPendingEdge 0 childEdge)).mpr
        ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    refine ⟨childPendingEdge 0 childEdge, hOutgoing.1, hOutgoing.2,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [childPendingEdge] using hEnvironment
    · simpa [childPendingEdge] using hLabel
    · simpa [childPendingEdge] using hCurrent
    · cases hSpec : childEdge.future with
      | explicit future =>
          simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
      | «at» referenced removed =>
          have hReferenced := hTargets childEdge hChildEdge referenced removed hSpec
          have hEmbedding := buildChoiceAutomaton_computeFuture_left signature
            left right selectionLeft selectionRight referenced hClosed
            hReferenced hCard
          simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          rw [hEmbedding]
          simp only [hSpec] at hFuture
          exact hFuture
    · simp [childPendingEdge, childState, hChildTarget]

private theorem buildChoiceAutomaton_hasResolvedEdge_right_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hTargets : right.FutureTargetsInStates) :
    AutomatonFragment.HasResolvedEdge
        (buildChoiceAutomaton signature left right selectionLeft selectionRight)
        (.child 1 source) env label offers (.child 1 target) ↔
      AutomatonFragment.HasResolvedEdge right source env label offers target := by
  classical
  let choice := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  have hClosed : ({ states := right.states, edges := right.edges } :
      PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates right hTargets
  have hCard : right.states.card ≤ choice.states.card := by
    have hSubset : childStates 1 right ⊆ choice.states := by
      intro state hState
      simp [choice, buildChoiceAutomaton, finishAutomatonFragment, hState]
    calc
      right.states.card = (childStates 1 right).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ choice.states.card := Finset.card_le_card hSubset
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    have hOutgoing :=
      (buildChoiceAutomaton_outgoing_right signature left right
        selectionLeft selectionRight source edge).mp ⟨hEdge, hSource⟩
    rcases hOutgoing with ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    simp only [childPendingEdge] at hEnvironment hLabel hCurrent hTarget
    have hChildTarget : childEdge.target = target := by
      injection hTarget
    refine ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, ?_, hChildTarget⟩
    cases hSpec : childEdge.future with
    | explicit future =>
        simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
    | «at» referenced removed =>
        have hReferenced := hTargets childEdge hChildEdge referenced removed hSpec
        have hEmbedding := buildChoiceAutomaton_computeFuture_right signature
          left right selectionLeft selectionRight referenced hClosed
          hReferenced hCard
        simp only
        simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          at hFuture
        rw [hEmbedding] at hFuture
        exact hFuture
  · rintro ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, hFuture, hChildTarget⟩
    have hOutgoing :=
      (buildChoiceAutomaton_outgoing_right signature left right
        selectionLeft selectionRight source (childPendingEdge 1 childEdge)).mpr
        ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    refine ⟨childPendingEdge 1 childEdge, hOutgoing.1, hOutgoing.2,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [childPendingEdge] using hEnvironment
    · simpa [childPendingEdge] using hLabel
    · simpa [childPendingEdge] using hCurrent
    · cases hSpec : childEdge.future with
      | explicit future =>
          simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
      | «at» referenced removed =>
          have hReferenced := hTargets childEdge hChildEdge referenced removed hSpec
          have hEmbedding := buildChoiceAutomaton_computeFuture_right signature
            left right selectionLeft selectionRight referenced hClosed
            hReferenced hCard
          simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          rw [hEmbedding]
          simp only [hSpec] at hFuture
          exact hFuture
    · simp [childPendingEdge, childState, hChildTarget]

private theorem buildChoiceAutomaton_root_hasResolvedEdge_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : TypeAutomatonState) :
    let fragment := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    AutomatonFragment.HasResolvedEdge fragment .root env label offers target ↔
      (env ∈ signature.localEnvironments ∧ label = selectionLeft ∧
        offers.current = ∅ ∧
        computeFuture pending (.child 0 left.initial) = offers.future ∧
        target = .child 0 left.initial) ∨
      (env ∈ signature.localEnvironments ∧ label = selectionRight ∧
        offers.current = ∅ ∧
        computeFuture pending (.child 1 right.initial) = offers.future ∧
        target = .child 1 right.initial) := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge, buildChoiceAutomaton,
    finishAutomatonFragment, childPendingEdges, Finset.mem_union,
    Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨edge, ((hLeft | hRight) | hSelection), hSource,
      hEnvironment, hLabel, hCurrent, hFuture, hTarget⟩
    · rcases hLeft with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · rcases hRight with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · rcases hSelection with ⟨edgeEnvironment, hLocal, hEdge | hEdge⟩
      · rw [hEdge] at hSource hEnvironment hLabel hCurrent hFuture hTarget
        simp only [Finset.sdiff_empty, childState] at hFuture
        left
        simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
        aesop
      · rw [hEdge] at hSource hEnvironment hLabel hCurrent hFuture hTarget
        simp only [Finset.sdiff_empty, childState] at hFuture
        right
        simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
        aesop
  · rintro (hLeft | hRight)
    · rcases hLeft with ⟨hLocal, hLabel, hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible selectionLeft
          current := ∅
          future := .at (.child 0 left.initial) ∅
          target := .child 0 left.initial }, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · right
        exact ⟨env, hLocal, Or.inl rfl⟩
      · simp [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm
    · rcases hRight with ⟨hLocal, hLabel, hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible selectionRight
          current := ∅
          future := .at (.child 1 right.initial) ∅
          target := .child 1 right.initial }, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · right
        exact ⟨env, hLocal, Or.inr rfl⟩
      · simp [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm

private theorem choiceFutureCorrect_core
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (hLeftCorrect : CompilationFutureCorrect signature left)
    (hRightCorrect : CompilationFutureCorrect signature right)
    (hLeftClosed :
      let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
      let fragment := compileTypeFuel signature fuel left
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).ReferencesClosed)
    (hRightClosed :
      let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
      let fragment := compileTypeFuel signature fuel right
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).ReferencesClosed) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let leftFragment := compileTypeFuel signature fuel left
    let rightFragment := compileTypeFuel signature fuel right
    let fragment := buildChoiceAutomaton signature leftFragment rightFragment
      selectionLeft selectionRight
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    computeFuture pending (.child 0 leftFragment.initial) =
        typeFutureOffers left ∧
      computeFuture pending (.child 1 rightFragment.initial) =
        typeFutureOffers right := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    selectionLeft selectionRight
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftState : leftFragment.initial ∈ leftFragment.states := by
    exact compileTypeFuel_initial_mem signature fuel left hLeftFuel
  have hRightState : rightFragment.initial ∈ rightFragment.states := by
    exact compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hLeftCard : leftFragment.states.card ≤ fragment.states.card := by
    have hSubset : childStates 0 leftFragment ⊆ fragment.states := by
      intro state hState
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment, hState]
    calc
      leftFragment.states.card = (childStates 0 leftFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hRightCard : rightFragment.states.card ≤ fragment.states.card := by
    have hSubset : childStates 1 rightFragment ⊆ fragment.states := by
      intro state hState
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment, hState]
    calc
      rightFragment.states.card = (childStates 1 rightFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hLeftSemantic : computeFuture
      { states := leftFragment.states, edges := leftFragment.edges }
      leftFragment.initial = typeFutureOffers left := by
    unfold CompilationFutureCorrect at hLeftCorrect
    have hRelation := compileTypeFuel_initial_relation signature fuel left
      hLeftFuel
    have hResult := hLeftCorrect leftFragment.initial left hRelation
    have hStable := compileTypeFuel_eq_of_sufficient signature left
      hLeftFuel (typeCompilationFuel_sufficient left)
    simpa [leftFragment, hStable] using hResult
  have hRightSemantic : computeFuture
      { states := rightFragment.states, edges := rightFragment.edges }
      rightFragment.initial = typeFutureOffers right := by
    unfold CompilationFutureCorrect at hRightCorrect
    have hRelation := compileTypeFuel_initial_relation signature fuel right
      hRightFuel
    have hResult := hRightCorrect rightFragment.initial right hRelation
    have hStable := compileTypeFuel_eq_of_sufficient signature right
      hRightFuel (typeCompilationFuel_sufficient right)
    simpa [rightFragment, hStable] using hResult
  constructor
  · rw [buildChoiceAutomaton_computeFuture_left signature leftFragment
      rightFragment selectionLeft selectionRight leftFragment.initial
      hLeftClosed hLeftState hLeftCard]
    exact hLeftSemantic
  · rw [buildChoiceAutomaton_computeFuture_right signature leftFragment
      rightFragment selectionLeft selectionRight rightFragment.initial
      hRightClosed hRightState hRightCard]
    exact hRightSemantic

/-- Choice-root future correctness follows compositionally from correctness
of both compiled children; reference closure is now supplied by the compiler
invariant rather than exposed as a separate hypothesis. -/
theorem choiceFutureCorrect_of_compilation
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftCorrect : CompilationFutureCorrect signature left)
    (hRightCorrect : CompilationFutureCorrect signature right) :
    ChoiceFutureCorrect signature left right := by
  apply choiceFutureCorrect_core signature left right
    TypeLabel.silent TypeLabel.silent hLeftCorrect hRightCorrect
  · apply compileTypeFuel_referencesClosed
    simp [TypeCompilationFuelSufficient]
  · apply compileTypeFuel_referencesClosed
    simp [TypeCompilationFuelSufficient]

/-- Visible edges inside the left tagged child of a compiled choice are
exactly the standalone child's visible edges. -/
theorem compileType_choice_left_child_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature (.choice left right)).HasEdge
        (.child 0 source) env label offers (.child 0 target) ↔
      (compileType signature left).HasEdge source env label offers target := by
  rw [compileType_hasEdge_iff_hasResolvedEdge signature (.choice left right)
      (.child 0 source) (.child 0 target) env label offers hSymbol,
    compileType_hasEdge_iff_hasResolvedEdge signature left source target env
      label offers hSymbol]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hTargets : leftFragment.FutureTargetsInStates := by
    exact compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          TypeLabel.silent TypeLabel.silent := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment,
    buildChoiceAutomaton_hasResolvedEdge_left_iff signature leftFragment
      rightFragment TypeLabel.silent TypeLabel.silent source target env label
      offers hTargets]
  have hStable := compileTypeFuel_eq_of_sufficient signature left hLeftFuel
    (typeCompilationFuel_sufficient left)
  simpa only [leftFragment, hStable]

/-- Visible edges inside the right tagged child of a compiled choice are
exactly the standalone child's visible edges. -/
theorem compileType_choice_right_child_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature (.choice left right)).HasEdge
        (.child 1 source) env label offers (.child 1 target) ↔
      (compileType signature right).HasEdge source env label offers target := by
  rw [compileType_hasEdge_iff_hasResolvedEdge signature (.choice left right)
      (.child 1 source) (.child 1 target) env label offers hSymbol,
    compileType_hasEdge_iff_hasResolvedEdge signature right source target env
      label offers hSymbol]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hTargets : rightFragment.FutureTargetsInStates := by
    exact compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          TypeLabel.silent TypeLabel.silent := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment,
    buildChoiceAutomaton_hasResolvedEdge_right_iff signature leftFragment
      rightFragment TypeLabel.silent TypeLabel.silent source target env label
      offers hTargets]
  have hStable := compileTypeFuel_eq_of_sufficient signature right hRightFuel
    (typeCompilationFuel_sufficient right)
  simpa only [rightFragment, hStable]

theorem compileType_choice_left_child_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet)
    (hEdge : (compileType signature (.choice left right)).HasEdge
      (.child 0 source) env label offers target) :
    ∃ childTarget,
      target = .child 0 childTarget ∧
      (compileType signature left).HasEdge source env label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          TypeLabel.silent TypeLabel.silent := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature (.choice left right)
      (.child 0 source) target env label offers hSymbol).mp hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPendingEdge, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildChoiceAutomaton_outgoing_left signature leftFragment rightFragment
      TypeLabel.silent TypeLabel.silent source pendingEdge).mp
      ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPending⟩
  have hTargetEq : target = .child 0 childEdge.target := by
    rw [hPending] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEq, ?_⟩
  apply (compileType_choice_left_child_edge_iff signature left right source
    childEdge.target env label offers hSymbol).mp
  simpa [hTargetEq] using hEdge

theorem compileType_choice_right_child_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet)
    (hEdge : (compileType signature (.choice left right)).HasEdge
      (.child 1 source) env label offers target) :
    ∃ childTarget,
      target = .child 1 childTarget ∧
      (compileType signature right).HasEdge source env label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          TypeLabel.silent TypeLabel.silent := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature (.choice left right)
      (.child 1 source) target env label offers hSymbol).mp hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPendingEdge, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildChoiceAutomaton_outgoing_right signature leftFragment rightFragment
      TypeLabel.silent TypeLabel.silent source pendingEdge).mp
      ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPending⟩
  have hTargetEq : target = .child 1 childEdge.target := by
    rw [hPending] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEq, ?_⟩
  apply (compileType_choice_right_child_edge_iff signature left right source
    childEdge.target env label offers hSymbol).mp
  simpa [hTargetEq] using hEdge

/-- Every public edge leaving an ordinary-choice root is one of its two
selection edges, with the graph-resolved child future. -/
theorem compileType_choice_root_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary} {target : TypeAutomatonState}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet)
    (hFuture : ChoiceFutureCorrect signature left right)
    (hEdge : (compileType signature (.choice left right)).HasEdge
      .root env label offers target) :
    (label = TypeLabel.silent ∧ offers.current = ∅ ∧
        offers.future = typeFutureOffers left ∧
        target = .child 0 (compileType signature left).initial) ∨
      (label = TypeLabel.silent ∧ offers.current = ∅ ∧
        offers.future = typeFutureOffers right ∧
        target = .child 1 (compileType signature right).initial) := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    TypeLabel.silent TypeLabel.silent
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable := compileTypeFuel_eq_of_sufficient signature left
    hLeftFuel (typeCompilationFuel_sufficient left)
  have hRightStable := compileTypeFuel_eq_of_sufficient signature right
    hRightFuel (typeCompilationFuel_sufficient right)
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature (.choice left right)
      .root target env label offers hSymbol).mp hEdge
  rw [hFragment] at hResolved
  have hCases :=
    (buildChoiceAutomaton_root_hasResolvedEdge_iff signature leftFragment
      rightFragment TypeLabel.silent TypeLabel.silent env label offers
      target).mp hResolved
  unfold ChoiceFutureCorrect at hFuture
  rcases hCases with hLeft | hRight
  · left
    rcases hLeft with ⟨_, hLabel, hCurrent, hComputed, hTarget⟩
    refine ⟨hLabel, hCurrent, ?_, ?_⟩
    · exact (hFuture.1.symm.trans hComputed).symm
    · simpa [leftFragment, compileType, hLeftStable] using hTarget
  · right
    rcases hRight with ⟨_, hLabel, hCurrent, hComputed, hTarget⟩
    refine ⟨hLabel, hCurrent, ?_, ?_⟩
    · exact (hFuture.2.symm.trans hComputed).symm
    · simpa [rightFragment, compileType, hRightStable] using hTarget

/-- The left selection edge of an ordinary choice, conditional only on the
graph-future equality used in its decoration. -/
theorem compileType_choice_left_selection_edge
    (signature : TypeAlphabet) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : ChoiceFutureCorrect signature left right)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ (typeFutureOffers left)) ∈
        signature.transitionAlphabet) :
    (compileType signature (.choice left right)).HasEdge .root env
      TypeLabel.silent (TypeOfferSummary.mk ∅ (typeFutureOffers left))
      (.child 0 (compileType signature left).initial) := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    TypeLabel.silent TypeLabel.silent
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hInitial : leftFragment.initial =
      (compileTypeFuel signature (typeCompilationFuel left) left).initial := by
    exact congrArg AutomatonFragment.initial
      (compileTypeFuel_eq_of_sufficient signature left
        (by simpa [leftFragment] using hLeftFuel)
        (typeCompilationFuel_sufficient left))
  have hComputed : computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 0 leftFragment.initial) = typeFutureOffers left := by
    simpa [pending] using hFuture.1
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := typeFutureOffers left
      target := .child 0 leftFragment.initial }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (.child 0 leftFragment.initial) ∅
        target := .child 0 leftFragment.initial }, ?_, ?_⟩
    · rw [hFragment]
      change _ ∈ fragment.edges
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment,
        hLocalEnvironment]
      right
      right
      exact ⟨env, hLocalEnvironment, Or.inl ⟨rfl, rfl⟩⟩
    · rw [hFragment]
      simp [hComputed]
  · simp [hSymbol, hInitial]

/-- The right selection edge of an ordinary choice. -/
theorem compileType_choice_right_selection_edge
    (signature : TypeAlphabet) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : ChoiceFutureCorrect signature left right)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ (typeFutureOffers right)) ∈
        signature.transitionAlphabet) :
    (compileType signature (.choice left right)).HasEdge .root env
      TypeLabel.silent (TypeOfferSummary.mk ∅ (typeFutureOffers right))
      (.child 1 (compileType signature right).initial) := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    TypeLabel.silent TypeLabel.silent
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hInitial : rightFragment.initial =
      (compileTypeFuel signature (typeCompilationFuel right) right).initial := by
    exact congrArg AutomatonFragment.initial
      (compileTypeFuel_eq_of_sufficient signature right
        (by simpa [rightFragment] using hRightFuel)
        (typeCompilationFuel_sufficient right))
  have hComputed : computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 1 rightFragment.initial) = typeFutureOffers right := by
    simpa [pending] using hFuture.2
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := typeFutureOffers right
      target := .child 1 rightFragment.initial }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (.child 1 rightFragment.initial) ∅
        target := .child 1 rightFragment.initial }, ?_, ?_⟩
    · rw [hFragment]
      change _ ∈ fragment.edges
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment,
        hLocalEnvironment]
      right
      right
      exact ⟨env, hLocalEnvironment, Or.inr ⟨rfl, rfl⟩⟩
    · rw [hFragment]
      simp [hComputed]
  · simp [hSymbol, hInitial]

private theorem TypeOffers.choice_left_fields
    {env : TypeEnvironment} {left right : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.choice left right) TypeLabel.silent left
      current future) :
    current = ∅ ∧ future = typeFutureOffers left := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers <;> simp_all

private theorem TypeOffers.choice_right_fields
    {env : TypeEnvironment} {left right : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.choice left right) TypeLabel.silent right
      current future) :
    current = ∅ ∧ future = typeFutureOffers right := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers <;> simp_all

/-- Root-state step correspondence for the left selection of an ordinary
choice.  Child-state lifting is deliberately not needed here. -/
theorem compileType_choice_left_selection_step_iff
    (signature : TypeAlphabet) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : ChoiceFutureCorrect signature left right)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ (typeFutureOffers left)) ∈
        signature.transitionAlphabet) :
    DecoratedTypeTransition env (.choice left right) TypeLabel.silent
        (TypeOfferSummary.mk ∅ (typeFutureOffers left)) left ↔
      ∃ state',
        (compileType signature (.choice left right)).HasEdge .root env
            TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers left)) state' ∧
          TypeCompilationRelation (.choice left right) state' left := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro _
    refine ⟨.child 0 (compileType signature left).initial, ?_, ?_⟩
    · exact compileType_choice_left_selection_edge signature left right
        hEnvironment hFuture hSymbol
    · exact TypeCompilationRelation.choice_left left right left _
        (compileType_initial_relation signature left)
  · intro _
    exact ⟨TypeTransition.choice_left env left right hWellFormed,
      TypeOffers.choice_left env left right hWellFormed⟩

/-- Root-state step correspondence for the right selection of an ordinary
choice. -/
theorem compileType_choice_right_selection_step_iff
    (signature : TypeAlphabet) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : ChoiceFutureCorrect signature left right)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ (typeFutureOffers right)) ∈
        signature.transitionAlphabet) :
    DecoratedTypeTransition env (.choice left right) TypeLabel.silent
        (TypeOfferSummary.mk ∅ (typeFutureOffers right)) right ↔
      ∃ state',
        (compileType signature (.choice left right)).HasEdge .root env
            TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers right)) state' ∧
          TypeCompilationRelation (.choice left right) state' right := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro _
    refine ⟨.child 1 (compileType signature right).initial, ?_, ?_⟩
    · exact compileType_choice_right_selection_edge signature left right
        hEnvironment hFuture hSymbol
    · exact TypeCompilationRelation.choice_right left right right _
        (compileType_initial_relation signature right)
  · intro _
    exact ⟨TypeTransition.choice_right env left right hWellFormed,
      TypeOffers.choice_right env left right hWellFormed⟩

/-- Ordinary choice preserves full step correspondence once both closed child
compilations and their graph futures are correct. -/
theorem compilationStepCorrect_choice
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftStep : CompilationStepCorrect signature left)
    (hRightStep : CompilationStepCorrect signature right)
    (hLeftFuture : CompilationFutureCorrect signature left)
    (hRightFuture : CompilationFutureCorrect signature right) :
    CompilationStepCorrect signature (.choice left right) := by
  intro residual residual' state env label offers hRelated hSymbol
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label { current := current, future := future } ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧
        ({ current := current, future := future } : TypeOfferSummary) ∈
          signature.offerSummaries := by
      simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
    exact hParts.1
  have hChoiceFuture := choiceFutureCorrect_of_compilation signature left right
    hLeftFuture hRightFuture
  cases hRelated with
  | choice_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | choice_left =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.choice_left_fields hOffers
            refine ⟨.child 0 (compileType signature left).initial, ?_, ?_⟩
            · exact compileType_choice_left_selection_edge signature left right
                hEnvironment hChoiceFuture hSignatureSymbol
            · exact TypeCompilationRelation.choice_left left right left _
                (compileType_initial_relation signature left)
        | choice_right =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.choice_right_fields hOffers
            refine ⟨.child 1 (compileType signature right).initial, ?_, ?_⟩
            · exact compileType_choice_right_selection_edge signature left right
                hEnvironment hChoiceFuture hSignatureSymbol
            · exact TypeCompilationRelation.choice_right left right right _
                (compileType_initial_relation signature right)
      · rintro ⟨target, hEdge, hTarget⟩
        have hCases := compileType_choice_root_edge_cases signature left right
          hSignatureSymbol hChoiceFuture hEdge
        rcases hCases with hLeft | hRight
        · rcases hLeft with ⟨rfl, hCurrent, hFuture, hState⟩
          cases hCurrent
          cases hFuture
          cases hState
          cases hTarget with
          | choice_left _ _ _ _ hChildTarget =>
              have hResidual := TypeCompilationRelation.residual_unique
                hChildTarget (compileType_initial_relation signature left)
              cases hResidual
              exact ⟨TypeTransition.choice_left env left right
                  (TypeAlphabet.environment_wellFormed hEnvironment),
                TypeOffers.choice_left env left right
                  (TypeAlphabet.environment_wellFormed hEnvironment)⟩
        · rcases hRight with ⟨rfl, hCurrent, hFuture, hState⟩
          cases hCurrent
          cases hFuture
          cases hState
          cases hTarget with
          | choice_right _ _ _ _ hChildTarget =>
              have hResidual := TypeCompilationRelation.residual_unique
                hChildTarget (compileType_initial_relation signature right)
              cases hResidual
              exact ⟨TypeTransition.choice_right env left right
                  (TypeAlphabet.environment_wellFormed hEnvironment),
                TypeOffers.choice_right env left right
                  (TypeAlphabet.environment_wellFormed hEnvironment)⟩
  | choice_left _ _ childResidual childState hChildRelated =>
      have hChildSymbol :
          TypeAutomatonSymbol.mk env label
              { current := current, future := future } ∈
            (compileType signature left).alphabet := by
        simpa [compileType] using hSignatureSymbol
      constructor
      · intro hStep
        rcases (hLeftStep hChildRelated hChildSymbol).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨.child 0 childTarget, ?_, ?_⟩
        · exact (compileType_choice_left_child_edge_iff signature left right
              childState childTarget env label
              { current := current, future := future } hSignatureSymbol).mpr
            hChildEdge
        · exact TypeCompilationRelation.choice_left left right residual'
            childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileType_choice_left_child_edge_cases signature left right
          hSignatureSymbol hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | choice_left _ _ _ _ hChildTarget =>
            exact (hLeftStep hChildRelated hChildSymbol).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | choice_right _ _ childResidual childState hChildRelated =>
      have hChildSymbol :
          TypeAutomatonSymbol.mk env label
              { current := current, future := future } ∈
            (compileType signature right).alphabet := by
        simpa [compileType] using hSignatureSymbol
      constructor
      · intro hStep
        rcases (hRightStep hChildRelated hChildSymbol).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨.child 1 childTarget, ?_, ?_⟩
        · exact (compileType_choice_right_child_edge_iff signature left right
              childState childTarget env label
              { current := current, future := future } hSignatureSymbol).mpr
            hChildEdge
        · exact TypeCompilationRelation.choice_right left right residual'
            childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileType_choice_right_child_edge_cases signature left right
          hSignatureSymbol hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | choice_right _ _ _ _ hChildTarget =>
            exact (hRightStep hChildRelated hChildSymbol).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

/-! ### Fair-choice selection edges -/

/-- Graph-future correctness for the two fair-choice selection edges. -/
def FairChoiceFutureCorrect
    (signature : TypeAlphabet) (bid : BranchId)
    (left right : PactType) : Prop :=
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    (TypeLabel.fair bid true) (TypeLabel.fair bid false)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  computeFuture pending (.child 0 leftFragment.initial) =
      typeFutureOffers left ∧
    computeFuture pending (.child 1 rightFragment.initial) =
      typeFutureOffers right

/-- Fair-choice selection futures are the same tagged-child graph calculation
as ordinary choice, with observable branch labels on the two root edges. -/
theorem fairChoiceFutureCorrect_of_compilation
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeftCorrect : CompilationFutureCorrect signature left)
    (hRightCorrect : CompilationFutureCorrect signature right) :
    FairChoiceFutureCorrect signature bid left right := by
  apply choiceFutureCorrect_core signature left right
    (TypeLabel.fair bid true) (TypeLabel.fair bid false)
    hLeftCorrect hRightCorrect
  · apply compileTypeFuel_referencesClosed
    simp [TypeCompilationFuelSufficient]
  · apply compileTypeFuel_referencesClosed
    simp [TypeCompilationFuelSufficient]

/-- Visible edges inside the left tagged child of a compiled fair choice are
exactly the standalone child's visible edges. -/
theorem compileType_fairChoice_left_child_edge_iff
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature (.fairChoice bid left right)).HasEdge
        (.child 0 source) env label offers (.child 0 target) ↔
      (compileType signature left).HasEdge source env label offers target := by
  rw [compileType_hasEdge_iff_hasResolvedEdge signature
      (.fairChoice bid left right) (.child 0 source) (.child 0 target) env
      label offers hSymbol,
    compileType_hasEdge_iff_hasResolvedEdge signature left source target env
      label offers hSymbol]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment,
    buildChoiceAutomaton_hasResolvedEdge_left_iff signature leftFragment
      rightFragment (TypeLabel.fair bid true) (TypeLabel.fair bid false)
      source target env label offers hTargets]
  have hStable := compileTypeFuel_eq_of_sufficient signature left hLeftFuel
    (typeCompilationFuel_sufficient left)
  simpa only [leftFragment, hStable]

/-- Visible edges inside the right tagged child of a compiled fair choice are
exactly the standalone child's visible edges. -/
theorem compileType_fairChoice_right_child_edge_iff
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature (.fairChoice bid left right)).HasEdge
        (.child 1 source) env label offers (.child 1 target) ↔
      (compileType signature right).HasEdge source env label offers target := by
  rw [compileType_hasEdge_iff_hasResolvedEdge signature
      (.fairChoice bid left right) (.child 1 source) (.child 1 target) env
      label offers hSymbol,
    compileType_hasEdge_iff_hasResolvedEdge signature right source target env
      label offers hSymbol]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment,
    buildChoiceAutomaton_hasResolvedEdge_right_iff signature leftFragment
      rightFragment (TypeLabel.fair bid true) (TypeLabel.fair bid false)
      source target env label offers hTargets]
  have hStable := compileTypeFuel_eq_of_sufficient signature right hRightFuel
    (typeCompilationFuel_sufficient right)
  simpa only [rightFragment, hStable]

/-- Every edge from a left-tagged fair-choice state remains in the left
tagged child. -/
theorem compileType_fairChoice_left_child_edge_cases
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet)
    (hEdge : (compileType signature (.fairChoice bid left right)).HasEdge
      (.child 0 source) env label offers target) :
    ∃ childTarget,
      target = .child 0 childTarget ∧
      (compileType signature left).HasEdge source env label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature
      (.fairChoice bid left right) (.child 0 source) target env label offers
      hSymbol).mp hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPendingEdge, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildChoiceAutomaton_outgoing_left signature leftFragment rightFragment
      (TypeLabel.fair bid true) (TypeLabel.fair bid false) source
      pendingEdge).mp ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPending⟩
  have hTargetEq : target = .child 0 childEdge.target := by
    rw [hPending] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEq, ?_⟩
  apply (compileType_fairChoice_left_child_edge_iff signature bid left right
    source childEdge.target env label offers hSymbol).mp
  simpa [hTargetEq] using hEdge

/-- Every edge from a right-tagged fair-choice state remains in the right
tagged child. -/
theorem compileType_fairChoice_right_child_edge_cases
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet)
    (hEdge : (compileType signature (.fairChoice bid left right)).HasEdge
      (.child 1 source) env label offers target) :
    ∃ childTarget,
      target = .child 1 childTarget ∧
      (compileType signature right).HasEdge source env label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature
      (.fairChoice bid left right) (.child 1 source) target env label offers
      hSymbol).mp hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPendingEdge, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildChoiceAutomaton_outgoing_right signature leftFragment rightFragment
      (TypeLabel.fair bid true) (TypeLabel.fair bid false) source
      pendingEdge).mp ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPending⟩
  have hTargetEq : target = .child 1 childEdge.target := by
    rw [hPending] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEq, ?_⟩
  apply (compileType_fairChoice_right_child_edge_iff signature bid left right
    source childEdge.target env label offers hSymbol).mp
  simpa [hTargetEq] using hEdge

/-- Every public edge leaving a fair-choice root is one of its two labelled
selection edges, with the graph-resolved child future. -/
theorem compileType_fairChoice_root_edge_cases
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary} {target : TypeAutomatonState}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet)
    (hFuture : FairChoiceFutureCorrect signature bid left right)
    (hEdge : (compileType signature (.fairChoice bid left right)).HasEdge
      .root env label offers target) :
    (label = TypeLabel.fair bid true ∧ offers.current = ∅ ∧
        offers.future = typeFutureOffers left ∧
        target = .child 0 (compileType signature left).initial) ∨
      (label = TypeLabel.fair bid false ∧ offers.current = ∅ ∧
        offers.future = typeFutureOffers right ∧
        target = .child 1 (compileType signature right).initial) := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    (TypeLabel.fair bid true) (TypeLabel.fair bid false)
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable := compileTypeFuel_eq_of_sufficient signature left
    hLeftFuel (typeCompilationFuel_sufficient left)
  have hRightStable := compileTypeFuel_eq_of_sufficient signature right
    hRightFuel (typeCompilationFuel_sufficient right)
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature
      (.fairChoice bid left right) .root target env label offers hSymbol).mp
      hEdge
  rw [hFragment] at hResolved
  have hCases :=
    (buildChoiceAutomaton_root_hasResolvedEdge_iff signature leftFragment
      rightFragment (TypeLabel.fair bid true) (TypeLabel.fair bid false) env
      label offers target).mp hResolved
  unfold FairChoiceFutureCorrect at hFuture
  rcases hCases with hLeft | hRight
  · left
    rcases hLeft with ⟨_, hLabel, hCurrent, hComputed, hTarget⟩
    refine ⟨hLabel, hCurrent, ?_, ?_⟩
    · exact (hFuture.1.symm.trans hComputed).symm
    · simpa [leftFragment, compileType, hLeftStable] using hTarget
  · right
    rcases hRight with ⟨_, hLabel, hCurrent, hComputed, hTarget⟩
    refine ⟨hLabel, hCurrent, ?_, ?_⟩
    · exact (hFuture.2.symm.trans hComputed).symm
    · simpa [rightFragment, compileType, hRightStable] using hTarget

/-- The left selection edge of a fair choice. -/
theorem compileType_fairChoice_left_selection_edge
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : FairChoiceFutureCorrect signature bid left right)
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.fair bid true)
      (TypeOfferSummary.mk ∅ (typeFutureOffers left)) ∈
        signature.transitionAlphabet) :
    (compileType signature (.fairChoice bid left right)).HasEdge .root env
      (TypeLabel.fair bid true)
      (TypeOfferSummary.mk ∅ (typeFutureOffers left))
      (.child 0 (compileType signature left).initial) := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    (TypeLabel.fair bid true) (TypeLabel.fair bid false)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hInitial : leftFragment.initial =
      (compileTypeFuel signature (typeCompilationFuel left) left).initial := by
    exact congrArg AutomatonFragment.initial
      (compileTypeFuel_eq_of_sufficient signature left
        (by simpa [leftFragment] using hLeftFuel)
        (typeCompilationFuel_sufficient left))
  have hComputed : computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 0 leftFragment.initial) = typeFutureOffers left := by
    simpa [pending] using hFuture.1
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  refine ⟨
    { source := .root
      environment := env
      label := .visible (TypeLabel.fair bid true)
      current := ∅
      future := typeFutureOffers left
      target := .child 0 leftFragment.initial }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible (TypeLabel.fair bid true)
        current := ∅
        future := .at (.child 0 leftFragment.initial) ∅
        target := .child 0 leftFragment.initial }, ?_, ?_⟩
    · rw [hFragment]
      change _ ∈ fragment.edges
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment,
        hLocalEnvironment]
      right
      right
      exact ⟨env, hLocalEnvironment, Or.inl ⟨rfl, rfl⟩⟩
    · rw [hFragment]
      simp [hComputed]
  · simp [hSymbol, hInitial]

/-- The right selection edge of a fair choice. -/
theorem compileType_fairChoice_right_selection_edge
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : FairChoiceFutureCorrect signature bid left right)
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.fair bid false)
      (TypeOfferSummary.mk ∅ (typeFutureOffers right)) ∈
        signature.transitionAlphabet) :
    (compileType signature (.fairChoice bid left right)).HasEdge .root env
      (TypeLabel.fair bid false)
      (TypeOfferSummary.mk ∅ (typeFutureOffers right))
      (.child 1 (compileType signature right).initial) := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    (TypeLabel.fair bid true) (TypeLabel.fair bid false)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hInitial : rightFragment.initial =
      (compileTypeFuel signature (typeCompilationFuel right) right).initial := by
    exact congrArg AutomatonFragment.initial
      (compileTypeFuel_eq_of_sufficient signature right
        (by simpa [rightFragment] using hRightFuel)
        (typeCompilationFuel_sufficient right))
  have hComputed : computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 1 rightFragment.initial) = typeFutureOffers right := by
    simpa [pending] using hFuture.2
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  refine ⟨
    { source := .root
      environment := env
      label := .visible (TypeLabel.fair bid false)
      current := ∅
      future := typeFutureOffers right
      target := .child 1 rightFragment.initial }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible (TypeLabel.fair bid false)
        current := ∅
        future := .at (.child 1 rightFragment.initial) ∅
        target := .child 1 rightFragment.initial }, ?_, ?_⟩
    · rw [hFragment]
      change _ ∈ fragment.edges
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment,
        hLocalEnvironment]
      right
      right
      exact ⟨env, hLocalEnvironment, Or.inr ⟨rfl, rfl⟩⟩
    · rw [hFragment]
      simp [hComputed]
  · simp [hSymbol, hInitial]

private theorem TypeOffers.fair_left_fields
    {env : TypeEnvironment} {bid : BranchId} {left right : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.fairChoice bid left right)
      (TypeLabel.fair bid true) left current future) :
    current = ∅ ∧ future = typeFutureOffers left := by
  generalize hLabel : TypeLabel.fair bid true = actualLabel at hOffers
  cases hOffers <;> simp_all

private theorem TypeOffers.fair_right_fields
    {env : TypeEnvironment} {bid : BranchId} {left right : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.fairChoice bid left right)
      (TypeLabel.fair bid false) right current future) :
    current = ∅ ∧ future = typeFutureOffers right := by
  generalize hLabel : TypeLabel.fair bid false = actualLabel at hOffers
  cases hOffers <;> simp_all

/-- Root-state step correspondence for the taken-left fair branch. -/
theorem compileType_fairChoice_left_selection_step_iff
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : FairChoiceFutureCorrect signature bid left right)
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.fair bid true)
      (TypeOfferSummary.mk ∅ (typeFutureOffers left)) ∈
        signature.transitionAlphabet) :
    DecoratedTypeTransition env (.fairChoice bid left right)
        (TypeLabel.fair bid true)
        (TypeOfferSummary.mk ∅ (typeFutureOffers left)) left ↔
      ∃ state',
        (compileType signature (.fairChoice bid left right)).HasEdge .root env
            (TypeLabel.fair bid true)
            (TypeOfferSummary.mk ∅ (typeFutureOffers left)) state' ∧
          TypeCompilationRelation (.fairChoice bid left right) state' left := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro _
    refine ⟨.child 0 (compileType signature left).initial, ?_, ?_⟩
    · exact compileType_fairChoice_left_selection_edge signature bid left right
        hEnvironment hFuture hSymbol
    · exact TypeCompilationRelation.fair_left bid left right left _
        (compileType_initial_relation signature left)
  · intro _
    exact ⟨TypeTransition.fair_left env bid left right hWellFormed,
      TypeOffers.fair_left env bid left right hWellFormed⟩

/-- Root-state step correspondence for the taken-right fair branch. -/
theorem compileType_fairChoice_right_selection_step_iff
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : FairChoiceFutureCorrect signature bid left right)
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.fair bid false)
      (TypeOfferSummary.mk ∅ (typeFutureOffers right)) ∈
        signature.transitionAlphabet) :
    DecoratedTypeTransition env (.fairChoice bid left right)
        (TypeLabel.fair bid false)
        (TypeOfferSummary.mk ∅ (typeFutureOffers right)) right ↔
      ∃ state',
        (compileType signature (.fairChoice bid left right)).HasEdge .root env
            (TypeLabel.fair bid false)
            (TypeOfferSummary.mk ∅ (typeFutureOffers right)) state' ∧
          TypeCompilationRelation (.fairChoice bid left right) state' right := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro _
    refine ⟨.child 1 (compileType signature right).initial, ?_, ?_⟩
    · exact compileType_fairChoice_right_selection_edge signature bid left right
        hEnvironment hFuture hSymbol
    · exact TypeCompilationRelation.fair_right bid left right right _
        (compileType_initial_relation signature right)
  · intro _
    exact ⟨TypeTransition.fair_right env bid left right hWellFormed,
      TypeOffers.fair_right env bid left right hWellFormed⟩

/-- Fair choice preserves full step correspondence once both closed child
compilations and their graph futures are correct. -/
theorem compilationStepCorrect_fairChoice
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeftStep : CompilationStepCorrect signature left)
    (hRightStep : CompilationStepCorrect signature right)
    (hLeftFuture : CompilationFutureCorrect signature left)
    (hRightFuture : CompilationFutureCorrect signature right) :
    CompilationStepCorrect signature (.fairChoice bid left right) := by
  intro residual residual' state env label offers hRelated hSymbol
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label { current := current, future := future } ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment : env ∈ signature.environments := by
    have hFields : env ∈ signature.environments ∧
        label ∈ signature.labels ∧
        ({ current := current, future := future } : TypeOfferSummary) ∈
          signature.offerSummaries := by
      simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
    exact hFields.1
  have hFairFuture := fairChoiceFutureCorrect_of_compilation signature bid
    left right hLeftFuture hRightFuture
  cases hRelated with
  | fair_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | fair_left =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.fair_left_fields hOffers
            refine ⟨.child 0 (compileType signature left).initial, ?_, ?_⟩
            · exact compileType_fairChoice_left_selection_edge signature bid
                left right hEnvironment hFairFuture hSignatureSymbol
            · exact TypeCompilationRelation.fair_left bid left right left _
                (compileType_initial_relation signature left)
        | fair_right =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.fair_right_fields hOffers
            refine ⟨.child 1 (compileType signature right).initial, ?_, ?_⟩
            · exact compileType_fairChoice_right_selection_edge signature bid
                left right hEnvironment hFairFuture hSignatureSymbol
            · exact TypeCompilationRelation.fair_right bid left right right _
                (compileType_initial_relation signature right)
      · rintro ⟨target, hEdge, hTarget⟩
        have hCases := compileType_fairChoice_root_edge_cases signature bid
          left right hSignatureSymbol hFairFuture hEdge
        rcases hCases with hLeft | hRight
        · rcases hLeft with ⟨rfl, hCurrent, hFuture, hState⟩
          cases hCurrent
          cases hFuture
          cases hState
          cases hTarget with
          | fair_left _ _ _ _ _ hChildTarget =>
              have hResidual := TypeCompilationRelation.residual_unique
                hChildTarget (compileType_initial_relation signature left)
              cases hResidual
              exact ⟨TypeTransition.fair_left env bid left right
                  (TypeAlphabet.environment_wellFormed hEnvironment),
                TypeOffers.fair_left env bid left right
                  (TypeAlphabet.environment_wellFormed hEnvironment)⟩
        · rcases hRight with ⟨rfl, hCurrent, hFuture, hState⟩
          cases hCurrent
          cases hFuture
          cases hState
          cases hTarget with
          | fair_right _ _ _ _ _ hChildTarget =>
              have hResidual := TypeCompilationRelation.residual_unique
                hChildTarget (compileType_initial_relation signature right)
              cases hResidual
              exact ⟨TypeTransition.fair_right env bid left right
                  (TypeAlphabet.environment_wellFormed hEnvironment),
                TypeOffers.fair_right env bid left right
                  (TypeAlphabet.environment_wellFormed hEnvironment)⟩
  | fair_left _ _ _ childResidual childState hChildRelated =>
      have hChildSymbol :
          TypeAutomatonSymbol.mk env label
              { current := current, future := future } ∈
            (compileType signature left).alphabet := by
        simpa [compileType] using hSignatureSymbol
      constructor
      · intro hStep
        rcases (hLeftStep hChildRelated hChildSymbol).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨.child 0 childTarget, ?_, ?_⟩
        · exact (compileType_fairChoice_left_child_edge_iff signature bid
              left right childState childTarget env label
              { current := current, future := future } hSignatureSymbol).mpr
            hChildEdge
        · exact TypeCompilationRelation.fair_left bid left right residual'
            childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileType_fairChoice_left_child_edge_cases signature bid
          left right hSignatureSymbol hEdge with
          ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | fair_left _ _ _ _ _ hChildTarget =>
            exact (hLeftStep hChildRelated hChildSymbol).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | fair_right _ _ _ childResidual childState hChildRelated =>
      have hChildSymbol :
          TypeAutomatonSymbol.mk env label
              { current := current, future := future } ∈
            (compileType signature right).alphabet := by
        simpa [compileType] using hSignatureSymbol
      constructor
      · intro hStep
        rcases (hRightStep hChildRelated hChildSymbol).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨.child 1 childTarget, ?_, ?_⟩
        · exact (compileType_fairChoice_right_child_edge_iff signature bid
              left right childState childTarget env label
              { current := current, future := future } hSignatureSymbol).mpr
            hChildEdge
        · exact TypeCompilationRelation.fair_right bid left right residual'
            childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileType_fairChoice_right_child_edge_cases signature bid
          left right hSignatureSymbol hEdge with
          ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | fair_right _ _ _ _ _ hChildTarget =>
            exact (hRightStep hChildRelated hChildSymbol).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

/-! ### Sequence entry and literal-skip bridge -/

/-- The compiled entry of a sequence is the tagged entry of its left child. -/
theorem compileType_sequence_initial_eq
    (signature : TypeAlphabet) (left right : PactType) :
    (compileType signature (.seq left right)).initial =
      .child 0 (compileType signature left).initial := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hInitial : leftFragment.initial =
      (compileTypeFuel signature (typeCompilationFuel left) left).initial := by
    exact congrArg AutomatonFragment.initial
      (compileTypeFuel_eq_of_sufficient signature left
        (by simpa [leftFragment] using hLeftFuel)
        (typeCompilationFuel_sufficient left))
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  simp only [compileType]
  rw [hFragment]
  simp [fragment, buildSequenceAutomaton, finishAutomatonFragment,
    childState, hInitial]

private theorem buildSequenceAutomaton_outgoing_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let sequence := buildSequenceAutomaton signature left right
    edge ∈ sequence.edges ∧ edge.source = .child 0 state ↔
      (∃ childEdge ∈ left.edges,
        childEdge.source = state ∧
        edge =
          { source := childState 0 childEdge.source
            environment := childEdge.environment
            label := childEdge.label
            current := childEdge.current
            future := .at (childState 0 childEdge.target) childEdge.current
            target := childState 0 childEdge.target }) ∨
      (state ∈ left.skipping ∧
        ∃ environment ∈ signature.localEnvironments,
          edge =
            { source := childState 0 state
              environment := environment
              label := .visible TypeLabel.silent
              current := ∅
              future := .at (childState 1 right.initial) ∅
              target := childState 1 right.initial }) := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSequenceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at hEdge
    rcases hEdge with (hLeft | hRight) | hBridge
    · rcases hLeft with ⟨childEdge, hChildEdge, hEdge⟩
      have hChildSource := hSource
      rw [← hEdge] at hChildSource
      have hChildSource' : childEdge.source = state := by
        simpa [childState] using hChildSource
      left
      exact ⟨childEdge, hChildEdge, hChildSource', hEdge.symm⟩
    · rcases hRight with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childPendingEdge, childState] at hSource
    · rcases hBridge with ⟨bridgeState, hSkipping, environment,
        hEnvironment, hEdge⟩
      have hBridgeSource := hSource
      rw [← hEdge] at hBridgeSource
      have hState : bridgeState = state := by
        simpa [childState] using hBridgeSource
      subst bridgeState
      right
      exact ⟨hSkipping, environment, hEnvironment, hEdge.symm⟩
  · rintro (hLeft | hBridge)
    · rcases hLeft with ⟨childEdge, hChildEdge, hChildSource, rfl⟩
      constructor
      · simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image]
        exact Or.inl (Or.inl ⟨childEdge, hChildEdge, rfl⟩)
      · simp [childState, hChildSource]
    · rcases hBridge with ⟨hSkipping, environment, hEnvironment, rfl⟩
      constructor
      · simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
        right
        exact ⟨state, hSkipping, environment, hEnvironment, rfl⟩
      · rfl

private theorem buildSequenceAutomaton_outgoing_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let sequence := buildSequenceAutomaton signature left right
    edge ∈ sequence.edges ∧ edge.source = .child 1 state ↔
      ∃ childEdge ∈ right.edges,
        childEdge.source = state ∧ edge = childPendingEdge 1 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSequenceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at hEdge
    rcases hEdge with (hLeft | hRight) | hBridge
    · rcases hLeft with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childState] at hSource
    · rcases hRight with ⟨childEdge, hChildEdge, hEdge⟩
      have hChildSource := hSource
      rw [← hEdge] at hChildSource
      have hChildSource' : childEdge.source = state := by
        simpa [childPendingEdge, childState] using hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource', hEdge.symm⟩
    · rcases hBridge with ⟨bridgeState, _, environment, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childState] at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildSequenceAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inr ⟨childEdge, hChildEdge, rfl⟩)
    · simp [childPendingEdge, childState, hChildSource]

private theorem buildSequenceAutomaton_referencedStates_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    parent.referencedStates (.child 1 state) =
      (child.referencedStates state).image (.child 1) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [buildSequenceAutomaton_outgoing_right signature left right]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem buildSequenceAutomaton_offersAt_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    parent.offersAt (.child 1 state) = child.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [buildSequenceAutomaton_outgoing_right signature left right]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem buildSequenceAutomaton_computeFuture_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hClosed : ({ states := right.states, edges := right.edges } :
      PendingAutomaton).ReferencesClosed)
    (hState : state ∈ right.states)
    (hCard : right.states.card ≤
      (buildSequenceAutomaton signature left right).states.card) :
    computeFuture
        { states := (buildSequenceAutomaton signature left right).states
          edges := (buildSequenceAutomaton signature left right).edges }
        (.child 1 state) =
      computeFuture { states := right.states, edges := right.edges } state := by
  let sequence := buildSequenceAutomaton signature left right
  let parent : PendingAutomaton :=
    { states := sequence.states, edges := sequence.edges }
  let child : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  apply computeFuture_eq_of_embedding child parent (.child 1)
  · exact buildSequenceAutomaton_referencedStates_right signature left right
  · exact buildSequenceAutomaton_offersAt_right signature left right
  · exact hClosed
  · exact hState
  · exact hCard

/-- Right-child resolved edges are preserved by the one-way sequence
embedding. -/
private theorem buildSequenceAutomaton_hasResolvedEdge_right_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hTargets : right.FutureTargetsInStates) :
    AutomatonFragment.HasResolvedEdge
        (buildSequenceAutomaton signature left right)
        (.child 1 source) env label offers (.child 1 target) ↔
      AutomatonFragment.HasResolvedEdge right source env label offers target := by
  classical
  let sequence := buildSequenceAutomaton signature left right
  have hClosed : ({ states := right.states, edges := right.edges } :
      PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates right hTargets
  have hCard : right.states.card ≤ sequence.states.card := by
    have hSubset : childStates 1 right ⊆ sequence.states := by
      intro state hState
      simp [sequence, buildSequenceAutomaton, finishAutomatonFragment, hState]
    calc
      right.states.card = (childStates 1 right).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ sequence.states.card := Finset.card_le_card hSubset
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_right signature left right
        source edge).mp ⟨hEdge, hSource⟩
    rcases hOutgoing with ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    simp only [childPendingEdge] at hEnvironment hLabel hCurrent hTarget
    have hChildTarget : childEdge.target = target := by
      simpa [childState] using hTarget
    refine ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, ?_, hChildTarget⟩
    cases hSpec : childEdge.future with
    | explicit future =>
        simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
    | «at» referenced removed =>
        have hReferenced := hTargets childEdge hChildEdge referenced removed hSpec
        have hEmbedding := buildSequenceAutomaton_computeFuture_right signature
          left right referenced hClosed hReferenced hCard
        simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          at hFuture
        rw [hEmbedding] at hFuture
        exact hFuture
  · rintro ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, hFuture, hChildTarget⟩
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_right signature left right source
        (childPendingEdge 1 childEdge)).mpr
        ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    refine ⟨childPendingEdge 1 childEdge, hOutgoing.1, hOutgoing.2,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [childPendingEdge] using hEnvironment
    · simpa [childPendingEdge] using hLabel
    · simpa [childPendingEdge] using hCurrent
    · cases hSpec : childEdge.future with
      | explicit future =>
          simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
      | «at» referenced removed =>
          have hReferenced := hTargets childEdge hChildEdge referenced removed hSpec
          have hEmbedding := buildSequenceAutomaton_computeFuture_right signature
            left right referenced hClosed hReferenced hCard
          simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          rw [hEmbedding]
          simp only [hSpec] at hFuture
          exact hFuture
    · simp [childPendingEdge, childState, hChildTarget]

/-- A left-child edge is re-decorated from the future menu at its tagged
target.  Its original resolved future remains existentially available for the
child fragment correspondence, while its current offers are preserved. -/
private theorem buildSequenceAutomaton_hasResolvedEdge_left_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    let sequence := buildSequenceAutomaton signature left right
    let pending : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    sequence.HasResolvedEdge (.child 0 source) env label offers
        (.child 0 target) ↔
      ∃ childFuture,
        left.HasResolvedEdge source env label
            { current := offers.current, future := childFuture } target ∧
          computeFuture pending (.child 0 target) \ offers.current =
            offers.future := by
  classical
  dsimp only
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_left signature left right
        source edge).mp ⟨hEdge, hSource⟩
    rcases hOutgoing with hChild | hBridge
    · rcases hChild with ⟨childEdge, hChildEdge, hChildSource, rfl⟩
      have hChildTarget : childEdge.target = target := by
        simpa [childState] using hTarget
      let childFuture : Finset BareMessage :=
        match childEdge.future with
        | .explicit future => future
        | .at state removed =>
            computeFuture { states := left.states, edges := left.edges }
              state \ removed
      refine ⟨childFuture, ?_, ?_⟩
      · refine ⟨childEdge, hChildEdge, hChildSource, hEnvironment,
          hLabel, hCurrent, ?_, hChildTarget⟩
        rfl
      · rw [hCurrent] at hFuture
        simpa [childState, hChildTarget] using hFuture
    · rcases hBridge with ⟨_, _, _, _, rfl⟩
      simp [childState] at hTarget
  · rintro ⟨childFuture,
      ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
        hCurrent, _, hChildTarget⟩, hFuture⟩
    let lifted : PendingAutomatonEdge :=
      { source := childState 0 childEdge.source
        environment := childEdge.environment
        label := childEdge.label
        current := childEdge.current
        future := .at (childState 0 childEdge.target) childEdge.current
        target := childState 0 childEdge.target }
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_left signature left right source
        lifted).mpr (Or.inl
          ⟨childEdge, hChildEdge, hChildSource, rfl⟩)
    refine ⟨lifted, hOutgoing.1, hOutgoing.2, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [lifted] using hEnvironment
    · simpa [lifted] using hLabel
    · simpa [lifted] using hCurrent
    · simpa [lifted, childState, hChildTarget, hCurrent] using hFuture
    · simp [lifted, childState, hChildTarget]

/-- Exact classification of an administrative sequence bridge. -/
private theorem buildSequenceAutomaton_hasResolvedEdge_bridge_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (source : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    let sequence := buildSequenceAutomaton signature left right
    let pending : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    sequence.HasResolvedEdge (.child 0 source) env label offers
        (.child 1 right.initial) ↔
      source ∈ left.skipping ∧ env ∈ signature.localEnvironments ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture pending (.child 1 right.initial) = offers.future := by
  classical
  dsimp only
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_left signature left right
        source edge).mp ⟨hEdge, hSource⟩
    rcases hOutgoing with hChild | hBridge
    · rcases hChild with ⟨childEdge, _, _, rfl⟩
      simp [childState] at hTarget
    · rcases hBridge with ⟨hSkipping, bridgeEnvironment,
        hBridgeEnvironment, rfl⟩
      simp only at hEnvironment hLabel hCurrent hFuture hTarget
      have hEnvironmentEq : bridgeEnvironment = env := hEnvironment
      subst bridgeEnvironment
      refine ⟨hSkipping, hBridgeEnvironment, ?_, ?_, ?_⟩
      · simpa using hLabel.symm
      · simpa using hCurrent.symm
      · simpa using hFuture
  · rintro ⟨hSkipping, hEnvironment, rfl, hCurrent, hFuture⟩
    let bridge : PendingAutomatonEdge :=
      { source := childState 0 source
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 1 right.initial) ∅
        target := childState 1 right.initial }
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_left signature left right source
        bridge).mpr (Or.inr ⟨hSkipping, env, hEnvironment, rfl⟩)
    refine ⟨bridge, hOutgoing.1, hOutgoing.2, rfl, rfl, ?_, ?_, rfl⟩
    · simpa [bridge] using hCurrent.symm
    · simpa [bridge] using hFuture

/-- Canonical raw-fragment form of a lifted left sequence edge.  The parent
recomputes the future at the represented target, while preserving the child's
current offer set. -/
theorem compileTypeFuel_sequence_left_child_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right))
        (.child 0 source) env label offers (.child 0 target) ↔
      ∃ childFuture,
        AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature (typeCompilationFuel left) left)
            source env label
              { current := offers.current, future := childFuture } target ∧
          computeFuture
              { states :=
                  (compileTypeFuel signature
                    (typeCompilationFuel (.seq left right))
                    (.seq left right)).states
                edges :=
                  (compileTypeFuel signature
                    (typeCompilationFuel (.seq left right))
                    (.seq left right)).edges }
              (.child 0 target) \ offers.current = offers.future := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  have hCore :=
    buildSequenceAutomaton_hasResolvedEdge_left_iff signature leftFragment
      rightFragment source target env label offers
  simpa only [fragment, hLeftStable, hFragment] using hCore

/-- Canonical raw-fragment form of an embedded right sequence edge. -/
theorem compileTypeFuel_sequence_right_child_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right))
        (.child 1 source) env label offers (.child 1 target) ↔
      AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel right) right)
        source env label offers target := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  have hCore :=
    buildSequenceAutomaton_hasResolvedEdge_right_iff signature leftFragment
      rightFragment source target env label offers hRightTargets
  simpa only [fragment, hRightStable] using hCore

/-- Canonical raw-fragment classification of the administrative bridge from a
skipping left state to the right entry. -/
theorem compileTypeFuel_sequence_bridge_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right))
        (.child 0 source) env label offers
        (.child 1 (compileTypeFuel signature
          (typeCompilationFuel right) right).initial) ↔
      source ∈ (compileTypeFuel signature
          (typeCompilationFuel left) left).skipping ∧
        env ∈ signature.localEnvironments ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture
            { states :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).states
              edges :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).edges }
            (.child 1 (compileTypeFuel signature
              (typeCompilationFuel right) right).initial) = offers.future := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment, ← hRightStable]
  have hCore :=
    buildSequenceAutomaton_hasResolvedEdge_bridge_iff signature leftFragment
      rightFragment source env label offers
  simpa only [fragment, hFragment, hLeftStable, hRightStable] using hCore

/-- Exact target-shape classification for every raw edge leaving a tagged left
sequence state. -/
theorem compileTypeFuel_sequence_left_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : AutomatonFragment.HasResolvedEdge
      (compileTypeFuel signature (typeCompilationFuel (.seq left right))
        (.seq left right))
      (.child 0 source) env label offers target) :
    (∃ childTarget childFuture,
        target = .child 0 childTarget ∧
        AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature (typeCompilationFuel left) left)
            source env label
              { current := offers.current, future := childFuture }
              childTarget ∧
        computeFuture
            { states :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).states
              edges :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).edges }
            (.child 0 childTarget) \ offers.current = offers.future) ∨
      (source ∈ (compileTypeFuel signature
          (typeCompilationFuel left) left).skipping ∧
        env ∈ signature.localEnvironments ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture
            { states :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).states
              edges :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).edges }
            (.child 1 (compileTypeFuel signature
              (typeCompilationFuel right) right).initial) = offers.future ∧
        target = .child 1 (compileTypeFuel signature
          (typeCompilationFuel right) right).initial) := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment] at hEdge
  rcases hEdge with ⟨pendingEdge, hPendingEdge, hSource, hEnvironment,
    hLabel, hCurrent, hResolvedFuture, hTarget⟩
  have hOutgoing :=
    (buildSequenceAutomaton_outgoing_left signature leftFragment rightFragment
      source pendingEdge).mp ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with hChild | hBridge
  · rcases hChild with ⟨childEdge, _, _, hPending⟩
    have hTargetEq : target = .child 0 childEdge.target := by
      rw [hPending] at hTarget
      simpa [childState] using hTarget.symm
    have hFixed : AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right))
        (.child 0 source) env label offers (.child 0 childEdge.target) := by
      rw [hFragment]
      simpa [hTargetEq] using (show fragment.HasResolvedEdge
        (.child 0 source) env label offers target from
          ⟨pendingEdge, hPendingEdge, hSource, hEnvironment, hLabel,
            hCurrent, hResolvedFuture, hTarget⟩)
    rcases (compileTypeFuel_sequence_left_child_edge_iff signature left right
      source childEdge.target env label offers).mp hFixed with
      ⟨childFuture, hChildResolved, hFuture⟩
    left
    exact ⟨childEdge.target, childFuture, hTargetEq, hChildResolved, hFuture⟩
  · rcases hBridge with ⟨_, _, _, hPending⟩
    have hTargetEq : target = .child 1 rightFragment.initial := by
      rw [hPending] at hTarget
      simpa [childState] using hTarget.symm
    have hFixed : AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right))
        (.child 0 source) env label offers
          (.child 1 (compileTypeFuel signature
            (typeCompilationFuel right) right).initial) := by
      rw [hFragment]
      simpa [hTargetEq, hRightStable] using (show fragment.HasResolvedEdge
        (.child 0 source) env label offers target from
          ⟨pendingEdge, hPendingEdge, hSource, hEnvironment, hLabel,
            hCurrent, hResolvedFuture, hTarget⟩)
    have hFields :=
      (compileTypeFuel_sequence_bridge_edge_iff signature left right source env
        label offers).mp hFixed
    right
    exact ⟨hFields.1, hFields.2.1, hFields.2.2.1,
      hFields.2.2.2.1, hFields.2.2.2.2,
      by simpa [hRightStable] using hTargetEq⟩

/-- Exact target-shape classification for every raw edge leaving a tagged right
sequence state. -/
theorem compileTypeFuel_sequence_right_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : AutomatonFragment.HasResolvedEdge
      (compileTypeFuel signature (typeCompilationFuel (.seq left right))
        (.seq left right))
      (.child 1 source) env label offers target) :
    ∃ childTarget,
      target = .child 1 childTarget ∧
      AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel right) right)
        source env label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment] at hEdge
  rcases hEdge with ⟨pendingEdge, hPendingEdge, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  have hOutgoing :=
    (buildSequenceAutomaton_outgoing_right signature leftFragment rightFragment
      source pendingEdge).mp ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPending⟩
  have hTargetEq : target = .child 1 childEdge.target := by
    rw [hPending] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEq, ?_⟩
  apply (compileTypeFuel_sequence_right_child_edge_iff signature left right
    source childEdge.target env label offers).mp
  rw [hFragment]
  simpa [hTargetEq] using (show fragment.HasResolvedEdge
    (.child 1 source) env label offers target from
      ⟨pendingEdge, hPendingEdge, hSource, hEnvironment, hLabel, hCurrent,
        hFuture, hTarget⟩)


/-- The graph-future equality used to decorate the administrative bridge of
`skip ; right`. -/
def SequenceSkipBridgeFutureCorrect
    (signature : TypeAlphabet) (right : PactType) : Prop :=
  let fuel := max (typeCompilationFuel .skip) (typeCompilationFuel right)
  let skipFragment := compileTypeFuel signature fuel .skip
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature skipFragment rightFragment
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  computeFuture pending (.child 1 rightFragment.initial) =
    typeFutureOffers right

/-- The administrative bridge from the completed literal `skip` child to the
right entry is present with its exact offer decoration. -/
theorem compileType_sequence_skip_bridge_edge
    (signature : TypeAlphabet) (right : PactType) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : SequenceSkipBridgeFutureCorrect signature right)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ (typeFutureOffers right)) ∈
        signature.transitionAlphabet) :
    (compileType signature (.seq .skip right)).HasEdge
      (.child 0 (compileType signature .skip).initial) env TypeLabel.silent
      (TypeOfferSummary.mk ∅ (typeFutureOffers right))
      (.child 1 (compileType signature right).initial) := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  let fuel := max (typeCompilationFuel .skip) (typeCompilationFuel right)
  let skipFragment := compileTypeFuel signature fuel .skip
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature skipFragment rightFragment
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hSkipFuel : TypeCompilationFuelSufficient .skip fuel := by
    simp [TypeCompilationFuelSufficient, typeCompilationFuel, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hSkipFragment : skipFragment =
      compileTypeFuel signature (typeCompilationFuel .skip) .skip :=
    compileTypeFuel_eq_of_sufficient signature .skip hSkipFuel
      (typeCompilationFuel_sufficient .skip)
  have hRightFragment : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hSkipping : skipFragment.initial ∈ skipFragment.skipping := by
    rw [hSkipFragment]
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
  have hComputed : computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 1 rightFragment.initial) = typeFutureOffers right := by
    simpa [pending] using hFuture
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq .skip right))
          (.seq .skip right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    simp [fragment, skipFragment, rightFragment, fuel, typeCompilationFuel]
  refine ⟨
    { source := .child 0 skipFragment.initial
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := typeFutureOffers right
      target := .child 1 rightFragment.initial }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .child 0 skipFragment.initial
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (.child 1 rightFragment.initial) ∅
        target := .child 1 rightFragment.initial }, ?_, ?_⟩
    · rw [hFragment]
      change _ ∈ fragment.edges
      simp only [fragment, buildSequenceAutomaton,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_image]
      right
      exact ⟨skipFragment.initial, hSkipping, env, hLocalEnvironment, rfl⟩
    · rw [hFragment]
      simp [hComputed]
  · simp [hSymbol, hSkipFragment, hRightFragment]

private theorem TypeOffers.skip_sequence_fields
    {env : TypeEnvironment} {right : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.seq .skip right) TypeLabel.silent right
      current future) :
    current = ∅ ∧ future = typeFutureOffers right := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers <;> simp_all

/-- Complete root-equivalent correspondence for the literal-skip sequence
bridge. -/
theorem compileType_sequence_skip_bridge_step_iff
    (signature : TypeAlphabet) (right : PactType) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : SequenceSkipBridgeFutureCorrect signature right)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ (typeFutureOffers right)) ∈
        signature.transitionAlphabet) :
    DecoratedTypeTransition env (.seq .skip right) TypeLabel.silent
        (TypeOfferSummary.mk ∅ (typeFutureOffers right)) right ↔
      ∃ state',
        (compileType signature (.seq .skip right)).HasEdge
            (.child 0 (compileType signature .skip).initial) env
            TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers right)) state' ∧
          TypeCompilationRelation (.seq .skip right) state' right := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro _
    refine ⟨.child 1 (compileType signature right).initial, ?_, ?_⟩
    · exact compileType_sequence_skip_bridge_edge signature right
        hEnvironment hFuture hSymbol
    · exact TypeCompilationRelation.sequence_right .skip right right _
        (compileType_initial_relation signature right)
  · intro _
    exact ⟨TypeTransition.skip_seq env right hWellFormed,
      TypeOffers.skip_seq env right hWellFormed⟩

private theorem TypeOffers.sequence_fields
    {env : TypeEnvironment} {left left' right : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.seq left right) label (.seq left' right)
      current future) :
    ∃ childFuture,
      TypeOffers env left label left' current childFuture ∧
        future = typeFutureOffers (.seq left' right) \ current := by
  generalize hLabel : label = actualLabel at hOffers
  cases hOffers with
  | seq _ _ _ _ _ _ childFuture hChild =>
      subst actualLabel
      exact ⟨childFuture, hChild, rfl⟩
  | _ => simp_all

/-- Sequence preserves raw constructor-fragment step correspondence.  The
proof uses child fragment correspondence (not exported edges), exact parent
future correctness for re-decoration, and exact left skipping correctness for
the administrative bridge. -/
theorem compilationFragmentStepCorrect_sequence
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftStep : CompilationFragmentStepCorrect signature left)
    (hRightStep : CompilationFragmentStepCorrect signature right)
    (hSequenceFuture : CompilationFutureCorrect signature (.seq left right))
    (hLeftSkipping : CompilationSkippingCorrect signature left) :
    CompilationFragmentStepCorrect signature (.seq left right) := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
  cases hRelated with
  | sequence_left _ _ childResidual childState hChildRelated =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | skip_seq =>
            obtain ⟨hCurrent, hOfferFuture⟩ :=
              TypeOffers.skip_sequence_fields hOffers
            have hSkipping : childState ∈
                (compileTypeFuel signature (typeCompilationFuel left) left).skipping :=
              (hLeftSkipping childState .skip hChildRelated).mpr rfl
            have hRightInitial : TypeCompilationRelation right
                (compileTypeFuel signature (typeCompilationFuel right) right).initial
                right := by
              simpa [compileType] using
                (compileType_initial_relation signature right)
            have hTarget : TypeCompilationRelation (.seq left right)
                (.child 1 (compileTypeFuel signature
                  (typeCompilationFuel right) right).initial) right :=
              TypeCompilationRelation.sequence_right left right right _
                hRightInitial
            have hComputed := hSequenceFuture _ _ hTarget
            refine ⟨.child 1 (compileTypeFuel signature
                (typeCompilationFuel right) right).initial, ?_, hTarget⟩
            apply (compileTypeFuel_sequence_bridge_edge_iff signature left right
              childState env TypeLabel.silent offers).mpr
            exact ⟨hSkipping, hLocalEnvironment, rfl, hCurrent,
              hComputed.trans hOfferFuture.symm⟩
        | seq _ _ childTarget _ _ hChildTransition =>
            obtain ⟨childFuture, hChildOffers, hOfferFuture⟩ :=
              TypeOffers.sequence_fields hOffers
            rcases (hLeftStep (residual' := childTarget) (label := label)
                (offers := { current := offers.current, future := childFuture })
                hChildRelated hLocalEnvironment).mp
                ⟨hChildTransition, hChildOffers⟩ with
              ⟨childState', hChildEdge, hChildTarget⟩
            have hTarget : TypeCompilationRelation (.seq left right)
                (.child 0 childState') (.seq childTarget right) :=
              TypeCompilationRelation.sequence_left left right childTarget _
                hChildTarget
            have hComputed := hSequenceFuture _ _ hTarget
            refine ⟨.child 0 childState', ?_, hTarget⟩
            apply (compileTypeFuel_sequence_left_child_edge_iff signature left
              right childState childState' env label offers).mpr
            refine ⟨childFuture, hChildEdge, ?_⟩
            rw [hComputed]
            exact hOfferFuture.symm
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_sequence_left_edge_cases signature left right
          hEdge with hChild | hBridge
        · rcases hChild with
            ⟨childTarget, childFuture, rfl, hChildEdge, hComputed⟩
          cases hTarget with
          | sequence_left _ _ targetResidual _ hChildTarget =>
              rcases (hLeftStep hChildRelated hLocalEnvironment).mpr
                  ⟨childTarget, hChildEdge, hChildTarget⟩ with
                ⟨hChildTransition, hChildOffers⟩
              refine ⟨TypeTransition.seq env childResidual targetResidual right
                  label hChildTransition, ?_⟩
              have hParentTarget : TypeCompilationRelation (.seq left right)
                  (.child 0 childTarget) (.seq targetResidual right) :=
                TypeCompilationRelation.sequence_left left right targetResidual _
                  hChildTarget
              have hTargetFuture := hSequenceFuture _ _ hParentTarget
              have hSemanticFuture :
                  typeFutureOffers (.seq targetResidual right) \
                      offers.current = offers.future :=
                (congrArg (fun available => available \ offers.current)
                  hTargetFuture).symm.trans hComputed
              simpa only [hSemanticFuture] using
                (TypeOffers.seq env childResidual targetResidual right label
                  offers.current childFuture hChildOffers)
        · rcases hBridge with
            ⟨hSkipping, _, hLabel, hCurrent, hComputed, rfl⟩
          cases hTarget with
          | sequence_right _ _ targetResidual _ hChildTarget =>
              have hRightInitial : TypeCompilationRelation right
                  (compileTypeFuel signature
                    (typeCompilationFuel right) right).initial right := by
                simpa [compileType] using
                  (compileType_initial_relation signature right)
              have hResidual := TypeCompilationRelation.residual_unique
                hChildTarget hRightInitial
              cases hResidual
              have hChildResidual : childResidual = .skip :=
                (hLeftSkipping childState childResidual hChildRelated).mp
                  hSkipping
              subst childResidual
              have hParentTarget : TypeCompilationRelation (.seq left right)
                  (.child 1 (compileTypeFuel signature
                    (typeCompilationFuel right) right).initial) right :=
                TypeCompilationRelation.sequence_right left right right _
                  hChildTarget
              have hTargetFuture := hSequenceFuture _ _ hParentTarget
              have hOfferFuture : offers.future = typeFutureOffers right :=
                hComputed.symm.trans hTargetFuture
              subst label
              refine ⟨TypeTransition.skip_seq env right
                  (TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment),
                ?_⟩
              simpa only [hCurrent, hOfferFuture] using
                (TypeOffers.skip_seq env right
                  (TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment))
  | sequence_right _ _ childResidual childState hChildRelated =>
      constructor
      · intro hStep
        rcases (hRightStep hChildRelated hLocalEnvironment).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨.child 1 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_sequence_right_child_edge_iff signature left
              right childState childTarget env label offers).mpr hChildEdge
        · exact TypeCompilationRelation.sequence_right left right residual'
            childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_sequence_right_edge_cases signature left right
          hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | sequence_right _ _ _ _ hChildTarget =>
            exact (hRightStep hChildRelated hLocalEnvironment).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

/-- Exported sequence step correspondence follows from the raw constructor
theorem once the source symbol passes the fixed public alphabet filter. -/
theorem compilationStepCorrect_sequence
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftStep : CompilationFragmentStepCorrect signature left)
    (hRightStep : CompilationFragmentStepCorrect signature right)
    (hSequenceFuture : CompilationFutureCorrect signature (.seq left right)) :
    CompilationStepCorrect signature (.seq left right) := by
  intro residual residual' state env label offers hRelated hSymbol
  have hSignatureSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hLocalEnvironment : env ∈ signature.localEnvironments := by
    have hFields : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
    exact signature.environments_subset_localEnvironments hFields.1
  have hRaw := compilationFragmentStepCorrect_sequence signature left right
    hLeftStep hRightStep hSequenceFuture
      (compilationSkippingCorrect_of_compilation signature left)
    (residual := residual) (residual' := residual') (state := state)
    (env := env) (label := label) (offers := offers) hRelated hLocalEnvironment
  constructor
  · intro hStep
    rcases hRaw.mp hStep with ⟨target, hEdge, hTarget⟩
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature (.seq left right)
        state target env label offers hSignatureSymbol).mpr hEdge,
      hTarget⟩
  · rintro ⟨target, hEdge, hTarget⟩
    apply hRaw.mpr
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature (.seq left right)
        state target env label offers hSignatureSymbol).mp hEdge,
      hTarget⟩


/-! ### Recursion header correspondence -/

/-- The graph-future equality used to decorate the explicit silent edge from
a recursion binder header into its body.  The semantic target is the usual
capture-avoiding unfolding of the body. -/
def RecursionHeaderFutureCorrect
    (signature : TypeAlphabet) (name : String) (body : PactType) : Prop :=
  let bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
  let fragment := buildRecursionAutomaton signature name bodyFragment
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  computeFuture pending (.child 0 bodyFragment.initial) =
    typeFutureOffers (body.replaceVar name (.recur name body))

/-- The recursion binder's explicit header edge is present with the exact
decoration of the unfolded body. -/
theorem compileType_recursion_header_edge
    (signature : TypeAlphabet) (name : String) (body : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : RecursionHeaderFutureCorrect signature name body)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅
        (typeFutureOffers (body.replaceVar name (.recur name body)))) ∈
          signature.transitionAlphabet) :
    (compileType signature (.recur name body)).HasEdge .root env
      TypeLabel.silent
      (TypeOfferSummary.mk ∅
        (typeFutureOffers (body.replaceVar name (.recur name body))))
      (.child 0 (compileType signature body).initial) := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  let bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
  let fragment := buildRecursionAutomaton signature name bodyFragment
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hComputed : computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 0 bodyFragment.initial) =
        typeFutureOffers (body.replaceVar name (.recur name body)) := by
    simpa [pending, fragment, bodyFragment] using hFuture
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.recur name body))
          (.recur name body) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := typeFutureOffers (body.replaceVar name (.recur name body))
      target := .child 0 bodyFragment.initial }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (.child 0 bodyFragment.initial) ∅
        target := .child 0 bodyFragment.initial }, ?_, ?_⟩
    · rw [hFragment]
      simp [fragment, buildRecursionAutomaton, finishAutomatonFragment,
        hLocalEnvironment]
      left
      rfl
    · rw [hFragment]
      simp [hComputed]
  · simp [hSymbol, bodyFragment]

/-- Complete root-state correspondence for the explicit recursion-unfolding
step. -/
theorem compileType_recursion_header_step_iff
    (signature : TypeAlphabet) (name : String) (body : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : RecursionHeaderFutureCorrect signature name body)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅
        (typeFutureOffers (body.replaceVar name (.recur name body)))) ∈
          signature.transitionAlphabet) :
    DecoratedTypeTransition env (.recur name body) TypeLabel.silent
        (TypeOfferSummary.mk ∅
          (typeFutureOffers (body.replaceVar name (.recur name body))))
        (body.replaceVar name (.recur name body)) ↔
      ∃ state',
        (compileType signature (.recur name body)).HasEdge .root env
            TypeLabel.silent
            (TypeOfferSummary.mk ∅
              (typeFutureOffers (body.replaceVar name (.recur name body))))
            state' ∧
          TypeCompilationRelation (.recur name body) state'
            (body.replaceVar name (.recur name body)) := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro _
    refine ⟨.child 0 (compileType signature body).initial, ?_, ?_⟩
    · exact compileType_recursion_header_edge signature name body
        hEnvironment hFuture hSymbol
    · exact TypeCompilationRelation.recur_body name body body _
        (compileType_initial_relation signature body)
  · intro _
    exact ⟨TypeTransition.recur env name body hWellFormed,
      TypeOffers.recur env name body hWellFormed⟩

/-- Every compiled parallel edge hides immediate interface actions. -/
theorem compileType_parallel_edge_hides_immediate_interface
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileType signature (.par left right interface)).HasEdge
      source env label offers target) :
    ∀ action ∈ env.immediate, action.1 ∉ interface := by
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion] at hEdge
  rcases hEdge with ⟨resolvedEdge, hResolvedEdge, hOutput⟩
  cases hLabel : resolvedEdge.label with
  | «variable» name => simp [hLabel] at hOutput
  | visible visibleLabel =>
      simp only [hLabel] at hOutput
      split at hOutput
      · simp only [Finset.mem_singleton] at hOutput
        have hEnvironment := congrArg
          (fun edge : TypeAutomatonEdge => edge.symbol.environment) hOutput
        simp only at hEnvironment
        simp only [resolvedAutomatonEdges, Finset.mem_image] at hResolvedEdge
        rcases hResolvedEdge with ⟨pendingEdge, hPendingEdge, rfl⟩
        change env = pendingEdge.environment at hEnvironment
        have hFuel :
            typeCompilationFuel (.par left right interface) =
              Nat.succ (max (typeCompilationFuel left)
                (typeCompilationFuel right)) := by
          rw [typeCompilationFuel]
          omega
        rw [hFuel] at hPendingEdge
        simp only [compileTypeFuel] at hPendingEdge
        change pendingEdge ∈
            (buildParallelAutomaton interface
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right)).edges
          at hPendingEdge
        simp only [buildParallelAutomaton, finishAutomatonFragment]
          at hPendingEdge
        have hProductEdge := hPendingEdge
        simp only [Finset.mem_biUnion, Finset.mem_image,
          Finset.mem_filter] at hProductEdge
        rcases hProductEdge with ⟨leftEdge, _, rightEdge, ⟨_, _⟩, rfl⟩
        intro action hAction hInterface
        rw [hEnvironment] at hAction
        unfold combineAutomatonEnvironment at hAction
        split at hAction
        · simp [TypeEnvironment.tock] at hAction
        · exact (Finset.mem_filter.mp hAction).2 hInterface
      · simp at hOutput

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

