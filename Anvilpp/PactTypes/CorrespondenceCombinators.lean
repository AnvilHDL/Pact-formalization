import Anvilpp.PactTypes.CorrespondenceOffers
import Anvilpp.PactTypes.CorrespondenceParallel

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

/-- At a fresh choice root, future resolution is exactly the union of the
two child-entry futures.  The theorem applies to ordinary and fair selection
labels because neither selection crosses a clock boundary. -/
private theorem buildChoiceAutomaton_computeFuture_root
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    let fragment := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    computeFuture pending .root =
      computeFuture { states := left.states, edges := left.edges }
          left.initial ∪
        computeFuture { states := right.states, edges := right.edges }
          right.initial := by
  classical
  let fragment := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hClosed : pending.ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_of_futureTargetsInStates fragment
    exact buildChoiceAutomaton_futureTargetsInStates signature left right
      selectionLeft selectionRight hLeftTargets hRightTargets hLeftInitial
      hRightInitial
  have hRoot : (.root : TypeAutomatonState) ∈ pending.states := by
    simp [pending, fragment, buildChoiceAutomaton, finishAutomatonFragment]
  have hOffers : pending.offersAt .root = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro action hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hAction
    rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
    simp only [pending, fragment, buildChoiceAutomaton,
      finishAutomatonFragment, childPendingEdges, Finset.mem_union,
      Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
      Finset.mem_singleton] at hEdge
    rcases hEdge with (hLeft | hRight) | hSelection
    · rcases hLeft with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · rcases hRight with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · rcases hSelection with ⟨environment, _, hEdge | hEdge⟩
      · rw [hEdge] at hOffer
        simp [AutomatonConstructionLabel.semantic] at hOffer
      · rw [hEdge] at hOffer
        simp [AutomatonConstructionLabel.semantic] at hOffer
  have hReferences : pending.referencedStates .root =
      {.child 0 left.initial, .child 1 right.initial} := by
    ext state
    constructor
    · intro hState
      simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
        Finset.mem_filter] at hState
      rcases hState with ⟨edge, ⟨hEdge, hSource⟩, hReference⟩
      simp only [pending, fragment, buildChoiceAutomaton,
        finishAutomatonFragment, childPendingEdges, Finset.mem_union,
        Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
        Finset.mem_singleton] at hEdge
      rcases hEdge with (hLeft | hRight) | hSelection
      · rcases hLeft with ⟨childEdge, _, rfl⟩
        simp [childPendingEdge, childState] at hSource
      · rcases hRight with ⟨childEdge, _, rfl⟩
        simp [childPendingEdge, childState] at hSource
      · rcases hSelection with ⟨environment, _, hEdge | hEdge⟩
        · rw [hEdge] at hReference
          simp [AutomatonConstructionLabel.semantic, hSelectionLeft]
            at hReference
          simp [childState, hReference]
        · rw [hEdge] at hReference
          simp [AutomatonConstructionLabel.semantic, hSelectionRight]
            at hReference
          simp [childState, hReference]
    · intro hState
      simp only [Finset.mem_insert, Finset.mem_singleton] at hState
      rcases hState with rfl | rfl
      · let edge : PendingAutomatonEdge :=
          { source := .root
            environment := TypeEnvironment.tock
            label := .visible selectionLeft
            current := ∅
            future := .at (.child 0 left.initial) ∅
            target := .child 0 left.initial }
        simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
          Finset.mem_filter]
        refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
        · simp only [pending, fragment, buildChoiceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
            Finset.mem_singleton]
          right
          exact ⟨TypeEnvironment.tock,
            by simp [TypeAlphabet.localEnvironments], Or.inl rfl⟩
        · simp [edge, AutomatonConstructionLabel.semantic,
            hSelectionLeft]
      · let edge : PendingAutomatonEdge :=
          { source := .root
            environment := TypeEnvironment.tock
            label := .visible selectionRight
            current := ∅
            future := .at (.child 1 right.initial) ∅
            target := .child 1 right.initial }
        simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
          Finset.mem_filter]
        refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
        · simp only [pending, fragment, buildChoiceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
            Finset.mem_singleton]
          right
          exact ⟨TypeEnvironment.tock,
            by simp [TypeAlphabet.localEnvironments], Or.inr rfl⟩
        · simp [edge, AutomatonConstructionLabel.semantic,
            hSelectionRight]
  have hLeftClosed :
      ({ states := left.states, edges := left.edges } :
        PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates left
      hLeftTargets
  have hRightClosed :
      ({ states := right.states, edges := right.edges } :
        PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates right
      hRightTargets
  have hLeftCard : left.states.card ≤ fragment.states.card := by
    have hSubset : childStates 0 left ⊆ fragment.states := by
      intro state hState
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment, hState]
    calc
      left.states.card = (childStates 0 left).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hRightCard : right.states.card ≤ fragment.states.card := by
    have hSubset : childStates 1 right ⊆ fragment.states := by
      intro state hState
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment, hState]
    calc
      right.states.card = (childStates 1 right).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  change computeFuture pending .root = _
  rw [computeFuture_unfold pending .root hClosed hRoot, hOffers, hReferences]
  simp only [Finset.empty_union, Finset.biUnion_insert,
    Finset.biUnion_singleton]
  have hLeftEmbedding := buildChoiceAutomaton_computeFuture_left signature
    left right selectionLeft selectionRight left.initial hLeftClosed
    hLeftInitial hLeftCard
  have hRightEmbedding := buildChoiceAutomaton_computeFuture_right signature
    left right selectionLeft selectionRight right.initial hRightClosed
    hRightInitial hRightCard
  refine congrArg₂ (fun first second => first ∪ second)
    hLeftEmbedding ?_
  simpa using hRightEmbedding

private theorem compiledChoiceRootFuture_eq_union
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftCorrect : CompilationFutureCorrect signature left)
    (hRightCorrect : CompilationFutureCorrect signature right) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let leftFragment := compileTypeFuel signature fuel left
    let rightFragment := compileTypeFuel signature fuel right
    let fragment := buildChoiceAutomaton signature leftFragment rightFragment
      selectionLeft selectionRight
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    computeFuture pending .root =
      typeFutureOffers left ∪ typeFutureOffers right := by
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
  have hLeftInitial : leftFragment.initial ∈ leftFragment.states :=
    compileTypeFuel_initial_mem signature fuel left hLeftFuel
  have hRightInitial : rightFragment.initial ∈ rightFragment.states :=
    compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hRoot := buildChoiceAutomaton_computeFuture_root signature leftFragment
    rightFragment selectionLeft selectionRight hSelectionLeft hSelectionRight
    (compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel)
    (compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel)
    hLeftInitial hRightInitial
  have hLeftRelation : TypeCompilationRelation left leftFragment.initial left :=
    compileTypeFuel_initial_relation signature fuel left hLeftFuel
  have hRightRelation :
      TypeCompilationRelation right rightFragment.initial right :=
    compileTypeFuel_initial_relation signature fuel right hRightFuel
  have hLeftSemantic : computeFuture
      { states := leftFragment.states, edges := leftFragment.edges }
      leftFragment.initial = typeFutureOffers left := by
    have hResult := hLeftCorrect leftFragment.initial left hLeftRelation
    have hStable := compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
    simpa [leftFragment, hStable] using hResult
  have hRightSemantic : computeFuture
      { states := rightFragment.states, edges := rightFragment.edges }
      rightFragment.initial = typeFutureOffers right := by
    have hResult := hRightCorrect rightFragment.initial right hRightRelation
    have hStable := compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
    simpa [rightFragment, hStable] using hResult
  exact hRoot.trans (congrArg₂ (fun first second => first ∪ second)
    hLeftSemantic hRightSemantic)

private theorem compiledChoiceLeftFuture_eq
    (signature : TypeAlphabet) (left right residual : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState)
    (hRelated : TypeCompilationRelation left state residual)
    (hFuture : CompilationFutureCorrect signature left)
    (hStateCorrect : CompilationStateCorrect signature left) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let leftFragment := compileTypeFuel signature fuel left
    let rightFragment := compileTypeFuel signature fuel right
    let fragment := buildChoiceAutomaton signature leftFragment rightFragment
      selectionLeft selectionRight
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    computeFuture pending (.child 0 state) = typeFutureOffers residual := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    selectionLeft selectionRight
  have hFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hStable := compileTypeFuel_eq_of_sufficient signature left hFuel
    (typeCompilationFuel_sufficient left)
  have hState : state ∈ leftFragment.states := by
    have hExact := hStateCorrect state residual hRelated
    simpa [leftFragment, hStable] using hExact
  have hClosed :
      ({ states := leftFragment.states, edges := leftFragment.edges } :
        PendingAutomaton).ReferencesClosed := by
    apply compileTypeFuel_referencesClosed
    exact hFuel
  have hCard : leftFragment.states.card ≤ fragment.states.card := by
    have hSubset : childStates 0 leftFragment ⊆ fragment.states := by
      intro child hChild
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment, hChild]
    calc
      leftFragment.states.card = (childStates 0 leftFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hEmbedding := buildChoiceAutomaton_computeFuture_left signature
    leftFragment rightFragment selectionLeft selectionRight state hClosed
    hState hCard
  have hSemantic := hFuture state residual hRelated
  have hSemanticShared : computeFuture
      { states := leftFragment.states, edges := leftFragment.edges }
      state = typeFutureOffers residual := by
    simpa [leftFragment, hStable] using hSemantic
  change computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 0 state) = typeFutureOffers residual
  exact hEmbedding.trans hSemanticShared

private theorem compiledChoiceRightFuture_eq
    (signature : TypeAlphabet) (left right residual : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState)
    (hRelated : TypeCompilationRelation right state residual)
    (hFuture : CompilationFutureCorrect signature right)
    (hStateCorrect : CompilationStateCorrect signature right) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let leftFragment := compileTypeFuel signature fuel left
    let rightFragment := compileTypeFuel signature fuel right
    let fragment := buildChoiceAutomaton signature leftFragment rightFragment
      selectionLeft selectionRight
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    computeFuture pending (.child 1 state) = typeFutureOffers residual := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    selectionLeft selectionRight
  have hFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hStable := compileTypeFuel_eq_of_sufficient signature right hFuel
    (typeCompilationFuel_sufficient right)
  have hState : state ∈ rightFragment.states := by
    have hExact := hStateCorrect state residual hRelated
    simpa [rightFragment, hStable] using hExact
  have hClosed :
      ({ states := rightFragment.states, edges := rightFragment.edges } :
        PendingAutomaton).ReferencesClosed := by
    apply compileTypeFuel_referencesClosed
    exact hFuel
  have hCard : rightFragment.states.card ≤ fragment.states.card := by
    have hSubset : childStates 1 rightFragment ⊆ fragment.states := by
      intro child hChild
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment, hChild]
    calc
      rightFragment.states.card = (childStates 1 rightFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hEmbedding := buildChoiceAutomaton_computeFuture_right signature
    leftFragment rightFragment selectionLeft selectionRight state hClosed
    hState hCard
  have hSemantic := hFuture state residual hRelated
  have hSemanticShared : computeFuture
      { states := rightFragment.states, edges := rightFragment.edges }
      state = typeFutureOffers residual := by
    simpa [rightFragment, hStable] using hSemantic
  change computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 1 state) = typeFutureOffers residual
  exact hEmbedding.trans hSemanticShared

/-- Whole-fragment future correctness composes through ordinary choice while
the semantic future menu remains the syntax-derived union of its branches. -/
theorem compilationFutureCorrect_choice
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftFuture : CompilationFutureCorrect signature left)
    (hRightFuture : CompilationFutureCorrect signature right) :
    CompilationFutureCorrect signature (.choice left right) := by
  intro state residual hRelated
  cases hRelated with
  | choice_source =>
      have hRoot := compiledChoiceRootFuture_eq_union signature left right
        TypeLabel.silent TypeLabel.silent (by simp [TypeLabel.silent])
        (by simp [TypeLabel.silent]) hLeftFuture hRightFuture
      have hSyntax := typeFutureOffers_choice left right
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
        hRoot.trans hSyntax.symm
  | choice_left _ _ childResidual childState hChildRelated =>
      have hChild := compiledChoiceLeftFuture_eq signature left right
        residual TypeLabel.silent TypeLabel.silent childState
        hChildRelated hLeftFuture
        (compilationStateCorrect_of_compilation signature left)
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
        hChild
  | choice_right _ _ childResidual childState hChildRelated =>
      have hChild := compiledChoiceRightFuture_eq signature left right
        residual TypeLabel.silent TypeLabel.silent childState
        hChildRelated hRightFuture
        (compilationStateCorrect_of_compilation signature right)
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
        hChild

/-- Whole-fragment future correctness composes through fair choice; its
selection labels do not alter the syntax-derived branch union. -/
theorem compilationFutureCorrect_fairChoice
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeftFuture : CompilationFutureCorrect signature left)
    (hRightFuture : CompilationFutureCorrect signature right) :
    CompilationFutureCorrect signature (.fairChoice bid left right) := by
  intro state residual hRelated
  cases hRelated with
  | fair_source =>
      have hRoot := compiledChoiceRootFuture_eq_union signature left right
        (TypeLabel.fair bid true) (TypeLabel.fair bid false)
        (by simp [TypeLabel.fair]) (by simp [TypeLabel.fair])
        hLeftFuture hRightFuture
      have hSyntax := typeFutureOffers_fairChoice bid left right
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
        hRoot.trans hSyntax.symm
  | fair_left _ _ _ childResidual childState hChildRelated =>
      have hChild := compiledChoiceLeftFuture_eq signature left right
        residual (TypeLabel.fair bid true) (TypeLabel.fair bid false)
        childState hChildRelated hLeftFuture
        (compilationStateCorrect_of_compilation signature left)
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
        hChild
  | fair_right _ _ _ childResidual childState hChildRelated =>
      have hChild := compiledChoiceRightFuture_eq signature left right
        residual (TypeLabel.fair bid true) (TypeLabel.fair bid false)
        childState hChildRelated hRightFuture
        (compilationStateCorrect_of_compilation signature right)
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
        hChild

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
            future := match childEdge.label with
              | .future => childFutureSpec 0 childEdge.future
              | _ => .at (childState 0 childEdge.target) childEdge.current
            target := childState 0 childEdge.target }) ∨
      (state ∈ left.skipping ∧
        ∃ environment ∈ signature.localEnvironments,
          edge =
            { source := childState 0 state
              environment := environment
              label := .visible TypeLabel.silent
              current := ∅
              future := .at (childState 1 right.initial) ∅
              target := childState 1 right.initial }) ∨
      (state ∈ left.completing ∧
        edge =
          { source := childState 0 state
            environment := .empty
            label := .future
            current := ∅
            future := .at (childState 1 right.initial) ∅
            target := childState 0 state }) := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSequenceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at hEdge
    rcases hEdge with ((hLeft | hRight) | hBridge) | hFutureBridge
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
      left
      exact ⟨hSkipping, environment, hEnvironment, hEdge.symm⟩
    · rcases hFutureBridge with ⟨bridgeState, hCompleting, hEdge⟩
      have hBridgeSource := hSource
      rw [← hEdge] at hBridgeSource
      have hState : bridgeState = state := by
        simpa [childState] using hBridgeSource
      subst bridgeState
      right
      right
      exact ⟨hCompleting, hEdge.symm⟩
  · rintro (hLeft | hBridge | hFutureBridge)
    · rcases hLeft with ⟨childEdge, hChildEdge, hChildSource, rfl⟩
      constructor
      · simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image]
        exact Or.inl (Or.inl (Or.inl ⟨childEdge, hChildEdge, rfl⟩))
      · simp [childState, hChildSource]
    · rcases hBridge with ⟨hSkipping, environment, hEnvironment, rfl⟩
      constructor
      · simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
        left
        right
        exact ⟨state, hSkipping, environment, hEnvironment, rfl⟩
      · rfl
    · rcases hFutureBridge with ⟨hCompleting, rfl⟩
      constructor
      · simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image]
        right
        exact ⟨state, hCompleting, rfl⟩
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
    rcases hEdge with ((hLeft | hRight) | hBridge) | hFutureBridge
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
    · rcases hFutureBridge with ⟨bridgeState, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childState] at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildSequenceAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inr ⟨childEdge, hChildEdge, rfl⟩))
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

/-- A syntactically completing left state exposes the entire right-entry menu
through its construction-only future bridge.  This is the crucial lower-bound
half of optimistic sequence future correctness; it does not create a public
transition. -/
private theorem buildSequenceAutomaton_rightFuture_subset_of_completing
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hCompleting : state ∈ left.completing)
    (hLeftState : state ∈ left.states)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    computeFuture { states := right.states, edges := right.edges } right.initial ⊆
      computeFuture
        { states := (buildSequenceAutomaton signature left right).states
          edges := (buildSequenceAutomaton signature left right).edges }
        (.child 0 state) := by
  classical
  let sequence := buildSequenceAutomaton signature left right
  let parent : PendingAutomaton :=
    { states := sequence.states, edges := sequence.edges }
  let rightPending : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  have hClosed : parent.ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_of_futureTargetsInStates sequence
    exact buildSequenceAutomaton_futureTargetsInStates signature left right
      hLeftTargets hRightTargets hRightInitial
  have hSource : childState 0 state ∈ parent.states := by
    simp [parent, sequence, buildSequenceAutomaton,
      finishAutomatonFragment, childStates, childState, hLeftState]
  have hRightCard : right.states.card ≤ sequence.states.card := by
    have hSubset : childStates 1 right ⊆ sequence.states := by
      intro child hChild
      simp only [sequence, buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      exact Or.inr hChild
    calc
      right.states.card = (childStates 1 right).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ sequence.states.card := Finset.card_le_card hSubset
  have hRightEmbedding := buildSequenceAutomaton_computeFuture_right signature
    left right right.initial
    (PendingAutomaton.referencesClosed_of_futureTargetsInStates right
      hRightTargets)
    hRightInitial hRightCard
  have hReference : childState 1 right.initial ∈
      parent.referencedStates (childState 0 state) := by
    let bridge : PendingAutomatonEdge :=
      { source := childState 0 state
        environment := .empty
        label := .future
        current := ∅
        future := .at (childState 1 right.initial) ∅
        target := childState 0 state }
    simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
      Finset.mem_filter]
    refine ⟨bridge, ⟨?_, rfl⟩, ?_⟩
    · simp only [bridge, parent, sequence, buildSequenceAutomaton,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
      right
      exact ⟨state, hCompleting, rfl⟩
    · simp [bridge, AutomatonConstructionLabel.semantic, TypeLabel.silent]
  change computeFuture rightPending right.initial ⊆
    computeFuture parent (childState 0 state)
  rw [computeFuture_unfold parent (childState 0 state) hClosed hSource]
  intro action hAction
  simp only [Finset.mem_union, Finset.mem_biUnion]
  right
  refine ⟨childState 1 right.initial, hReference, ?_⟩
  have hRightEmbedding' :
      computeFuture parent (childState 1 right.initial) =
        computeFuture rightPending right.initial := by
    simpa [parent, sequence, rightPending] using hRightEmbedding
  rw [hRightEmbedding']
  exact hAction

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
    rcases hOutgoing with hChild | hBridge | hFutureBridge
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
        have hChildVisible : childEdge.label = .visible label := hLabel
        simpa [hChildVisible, childState, hChildTarget] using hFuture
    · rcases hBridge with ⟨_, _, _, _, rfl⟩
      simp [childState] at hTarget
    · rcases hFutureBridge with ⟨_, rfl⟩
      simp at hLabel
  · rintro ⟨childFuture,
      ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
        hCurrent, _, hChildTarget⟩, hFuture⟩
    let lifted : PendingAutomatonEdge :=
      { source := childState 0 childEdge.source
        environment := childEdge.environment
        label := childEdge.label
        current := childEdge.current
        future := match childEdge.label with
          | .future => childFutureSpec 0 childEdge.future
          | _ => .at (childState 0 childEdge.target) childEdge.current
        target := childState 0 childEdge.target }
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_left signature left right source
        lifted).mpr (Or.inl
          ⟨childEdge, hChildEdge, hChildSource, rfl⟩)
    refine ⟨lifted, hOutgoing.1, hOutgoing.2, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [lifted] using hEnvironment
    · simpa [lifted] using hLabel
    · simpa [lifted] using hCurrent
    · simpa [lifted, hLabel, childState, hChildTarget, hCurrent] using hFuture
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
    rcases hOutgoing with hChild | hBridge | hFutureBridge
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
    · rcases hFutureBridge with ⟨_, rfl⟩
      simp at hLabel
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
        bridge).mpr (Or.inr (Or.inl
          ⟨hSkipping, env, hEnvironment, rfl⟩))
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
  rcases hOutgoing with hChild | hBridge | hFutureBridge
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
  · rcases hFutureBridge with ⟨_, hPending⟩
    rw [hPending] at hLabel
    simp at hLabel

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
      left
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

/-- Optimistic completion metadata composes pointwise through sequencing.
The left tagged state completes exactly when both its represented residual and
the right entry complete; a right tagged state simply inherits the right
child's predicate. -/
theorem compilationCompletingCorrect_sequence
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationCompletingCorrect signature left)
    (hRight : CompilationCompletingCorrect signature right) :
    CompilationCompletingCorrect signature (.seq left right) := by
  intro state residual hRelated
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
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
  have hRightInitial : rightFragment.initial ∈ rightFragment.completing ↔
      right.CanCompleteBeforeTock = true := by
    have hInitialRelation := compileType_initial_relation signature right
    have hCanonical := hRight _ right hInitialRelation
    simpa [rightFragment, hRightStable, compileType] using hCanonical
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) =
        buildSequenceAutomaton signature leftFragment rightFragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  cases hRelated with
  | sequence_left _ _ childResidual childQ hChildRelated =>
      have hLeftChild : childQ ∈ leftFragment.completing ↔
          childResidual.CanCompleteBeforeTock = true := by
        have hCanonical := hLeft childQ childResidual hChildRelated
        simpa [leftFragment, hLeftStable] using hCanonical
      change childState 0 childQ ∈
          (buildSequenceAutomaton signature leftFragment rightFragment).completing ↔
        (PactType.seq childResidual right).CanCompleteBeforeTock = true
      by_cases hRightComplete : right.CanCompleteBeforeTock = true
      · simp [buildSequenceAutomaton, finishAutomatonFragment, childCompleting,
          childState, hLeftChild, hRightInitial, hRightComplete,
          PactType.CanCompleteBeforeTock]
      · simp [buildSequenceAutomaton, finishAutomatonFragment, childCompleting,
          childState, hRightInitial, hRightComplete,
          PactType.CanCompleteBeforeTock]
  | sequence_right _ _ _ childQ hChildRelated =>
      have hNotLeft : childState 1 childQ ∉
          (if rightFragment.initial ∈ rightFragment.completing then
            childCompleting 0 leftFragment
          else ∅) := by
        split <;> simp [childCompleting, childState]
      have hCanonical := hRight childQ _ hChildRelated
      constructor
      · intro hCompleting
        simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union] at hCompleting
        rcases hCompleting with hImpossible | hChild
        · exact (hNotLeft hImpossible).elim
        · apply hCanonical.mp
          simpa [childCompleting, childState, rightFragment,
            hRightStable] using hChild
      · intro hResidual
        simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union]
        right
        have hChild := hCanonical.mpr hResidual
        simpa [childCompleting, childState, rightFragment,
          hRightStable] using hChild

private theorem buildChoiceAutomaton_root_mem_completing_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (leftLabel rightLabel : TypeLabel) :
    TypeAutomatonState.root ∈
        (buildChoiceAutomaton signature left right leftLabel rightLabel).completing ↔
      left.initial ∈ left.completing ∨ right.initial ∈ right.completing := by
  classical
  by_cases hComplete : left.initial ∈ left.completing ∨
      right.initial ∈ right.completing <;>
    simp [buildChoiceAutomaton, finishAutomatonFragment, childCompleting,
      childState, hComplete]

private theorem buildChoiceAutomaton_left_mem_completing_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (leftLabel rightLabel : TypeLabel) (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildChoiceAutomaton signature left right leftLabel rightLabel).completing ↔
      state ∈ left.completing := by
  classical
  by_cases hComplete : left.initial ∈ left.completing ∨
      right.initial ∈ right.completing <;>
    simp [buildChoiceAutomaton, finishAutomatonFragment, childCompleting,
      childState, hComplete]

private theorem buildChoiceAutomaton_right_mem_completing_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (leftLabel rightLabel : TypeLabel) (state : TypeAutomatonState) :
    childState 1 state ∈
        (buildChoiceAutomaton signature left right leftLabel rightLabel).completing ↔
      state ∈ right.completing := by
  classical
  by_cases hComplete : left.initial ∈ left.completing ∨
      right.initial ∈ right.completing <;>
    simp [buildChoiceAutomaton, finishAutomatonFragment, childCompleting,
      childState, hComplete]

/-- Ordinary choice completes optimistically when either branch completes. -/
theorem compilationCompletingCorrect_choice
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationCompletingCorrect signature left)
    (hRight : CompilationCompletingCorrect signature right) :
    CompilationCompletingCorrect signature (.choice left right) := by
  intro state residual hRelated
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
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
  have hLeftInitial : leftFragment.initial ∈ leftFragment.completing ↔
      left.CanCompleteBeforeTock = true := by
    have hCanonical := hLeft _ left
      (compileType_initial_relation signature left)
    simpa [leftFragment, hLeftStable, compileType] using hCanonical
  have hRightInitial : rightFragment.initial ∈ rightFragment.completing ↔
      right.CanCompleteBeforeTock = true := by
    have hCanonical := hRight _ right
      (compileType_initial_relation signature right)
    simpa [rightFragment, hRightStable, compileType] using hCanonical
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          TypeLabel.silent TypeLabel.silent := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  cases hRelated with
  | choice_source =>
      rw [buildChoiceAutomaton_root_mem_completing_iff]
      simpa [PactType.CanCompleteBeforeTock] using
        (or_congr hLeftInitial hRightInitial)
  | choice_left _ _ _ childQ hChildRelated =>
      have hCanonical := hLeft childQ _ hChildRelated
      have hChild : childQ ∈ leftFragment.completing ↔
          residual.CanCompleteBeforeTock = true := by
        simpa [leftFragment, hLeftStable] using hCanonical
      exact (by simpa [childState] using
        ((buildChoiceAutomaton_left_mem_completing_iff signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent childQ).trans
            hChild))
  | choice_right _ _ _ childQ hChildRelated =>
      have hCanonical := hRight childQ _ hChildRelated
      have hChild : childQ ∈ rightFragment.completing ↔
          residual.CanCompleteBeforeTock = true := by
        simpa [rightFragment, hRightStable] using hCanonical
      exact (by simpa [childState] using
        ((buildChoiceAutomaton_right_mem_completing_iff signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent childQ).trans
            hChild))

/-- Fair choice has the same completion predicate as ordinary choice; its
selection labels do not affect same-cycle completion. -/
theorem compilationCompletingCorrect_fairChoice
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeft : CompilationCompletingCorrect signature left)
    (hRight : CompilationCompletingCorrect signature right) :
    CompilationCompletingCorrect signature (.fairChoice bid left right) := by
  intro state residual hRelated
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
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
  have hLeftInitial : leftFragment.initial ∈ leftFragment.completing ↔
      left.CanCompleteBeforeTock = true := by
    have hCanonical := hLeft _ left
      (compileType_initial_relation signature left)
    simpa [leftFragment, hLeftStable, compileType] using hCanonical
  have hRightInitial : rightFragment.initial ∈ rightFragment.completing ↔
      right.CanCompleteBeforeTock = true := by
    have hCanonical := hRight _ right
      (compileType_initial_relation signature right)
    simpa [rightFragment, hRightStable, compileType] using hCanonical
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  cases hRelated with
  | fair_source =>
      rw [buildChoiceAutomaton_root_mem_completing_iff]
      simpa [PactType.CanCompleteBeforeTock] using
        (or_congr hLeftInitial hRightInitial)
  | fair_left _ _ _ _ childQ hChildRelated =>
      have hCanonical := hLeft childQ _ hChildRelated
      have hChild : childQ ∈ leftFragment.completing ↔
          residual.CanCompleteBeforeTock = true := by
        simpa [leftFragment, hLeftStable] using hCanonical
      exact (by simpa [childState] using
        ((buildChoiceAutomaton_left_mem_completing_iff signature
          leftFragment rightFragment (TypeLabel.fair bid true)
            (TypeLabel.fair bid false) childQ).trans hChild))
  | fair_right _ _ _ _ childQ hChildRelated =>
      have hCanonical := hRight childQ _ hChildRelated
      have hChild : childQ ∈ rightFragment.completing ↔
          residual.CanCompleteBeforeTock = true := by
        simpa [rightFragment, hRightStable] using hCanonical
      exact (by simpa [childState] using
        ((buildChoiceAutomaton_right_mem_completing_iff signature
          leftFragment rightFragment (TypeLabel.fair bid true)
            (TypeLabel.fair bid false) childQ).trans hChild))

/-- Parallel completion is the conjunction of the represented child
completion predicates, matching the syntax-level optimistic analysis. -/
theorem compilationCompletingCorrect_parallel
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hLeft : CompilationCompletingCorrect signature left)
    (hRight : CompilationCompletingCorrect signature right) :
    CompilationCompletingCorrect signature (.par left right interface) := by
  intro state residual hRelated
  cases hRelated with
  | parallel _ _ leftResidual rightResidual _ leftQ rightQ
      hLeftRelated hRightRelated =>
      let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
      let leftFragment := compileTypeFuel signature fuel left
      let rightFragment := compileTypeFuel signature fuel right
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
      have hLeftChild : leftQ ∈ leftFragment.completing ↔
          leftResidual.CanCompleteBeforeTock = true := by
        have hCanonical := hLeft leftQ leftResidual hLeftRelated
        simpa [leftFragment, hLeftStable] using hCanonical
      have hRightChild : rightQ ∈ rightFragment.completing ↔
          rightResidual.CanCompleteBeforeTock = true := by
        have hCanonical := hRight rightQ rightResidual hRightRelated
        simpa [rightFragment, hRightStable] using hCanonical
      simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
      simpa [buildParallelAutomaton, finishAutomatonFragment,
        leftFragment, rightFragment, PactType.CanCompleteBeforeTock] using
          (and_congr hLeftChild hRightChild)

/-! ### Offer completion correspondence -/

private theorem branchCanCompleteBeforeTock_eq_any
    (branches : List (BareMessage × PactType)) :
    PactType.BranchCanCompleteBeforeTock branches =
      branches.any (fun branch => branch.2.CanCompleteBeforeTock) := by
  induction branches with
  | nil => simp [PactType.BranchCanCompleteBeforeTock]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      simp [PactType.BranchCanCompleteBeforeTock, ih]

private theorem childState_mem_indexedFragmentCompleting_iff
    (automata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : automata[index]? = some entry)
    (state : TypeAutomatonState) :
    childState (index + 1) state ∈ indexedFragmentCompleting automata ↔
      state ∈ entry.2.completing := by
  classical
  rw [indexedFragmentCompleting, mem_foldl_union_iff]
  constructor
  · rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
    · simp at hEmpty
    simp only [childCompleting, Finset.mem_image] at hChild
    rcases hChild with ⟨child, hChildCompleting, hState⟩
    have hIndex : indexed.2 = index := by
      injection hState with hTag _
      omega
    have hInner : child = state := by
      injection hState
    subst child
    have hIndexedFields := List.mem_zipIdx hIndexed
    simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
      at hIndexedFields
    rcases hIndexedFields with ⟨hBound, hValue⟩
    have hIndexedEntry : automata[indexed.2]? = some indexed.1 := by
      rw [List.getElem?_eq_getElem hBound, ← hValue]
    have hEntryEq : indexed.1 = entry := by
      have hOptions := congrArg (fun position => automata[position]?) hIndex
      change automata[indexed.2]? = automata[index]? at hOptions
      rw [hIndexedEntry, hEntry] at hOptions
      exact Option.some.inj hOptions
    simpa [hEntryEq] using hChildCompleting
  · intro hCompleting
    rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
    have hZipBound : index < automata.zipIdx.length := by
      simpa using hBound
    have hIndexed : (entry, index) ∈ automata.zipIdx := by
      have hMember := List.getElem_mem hZipBound
      have hAt := List.getElem_zipIdx (l := automata) (i := index)
        (j := 0) hZipBound
      simp only [zero_add] at hAt
      rw [hAt, hValue] at hMember
      exact hMember
    right
    refine ⟨(entry, index), hIndexed, ?_⟩
    simp [childCompleting, childState, hCompleting]

private theorem root_not_mem_indexedFragmentCompleting
    (automata : List (BareMessage × AutomatonFragment)) :
    TypeAutomatonState.root ∉ indexedFragmentCompleting automata := by
  rw [indexedFragmentCompleting, mem_foldl_union_iff]
  rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
  · simp at hEmpty
  · simp only [childCompleting, Finset.mem_image] at hChild
    rcases hChild with ⟨state, hState, hImpossible⟩
    cases hImpossible

private theorem child_zero_not_mem_indexedFragmentCompleting
    (automata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) :
    childState 0 state ∉ indexedFragmentCompleting automata := by
  rw [indexedFragmentCompleting, mem_foldl_union_iff]
  rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
  · simp at hEmpty
  · simp only [childCompleting, Finset.mem_image] at hChild
    rcases hChild with ⟨other, hOther, hEquality⟩
    have hIndex : indexed.2 + 1 = 0 := by
      injection hEquality
    omega

/-- Exclusive offers inherit optimistic completion from the else continuation
or any branch continuation, and tagged continuation states inherit the exact
child predicate. -/
theorem compilationCompletingCorrect_xoffer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElse : CompilationCompletingCorrect signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
        (index : Nat), branches[index]? = some (action, branchType) →
          CompilationCompletingCorrect signature branchType) :
    CompilationCompletingCorrect signature (.xoffer elseType branches) := by
  intro state residual hRelated
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hElseStable : elseFragment = compileTypeFuel signature
      (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hElseInitial : elseFragment.initial ∈ elseFragment.completing ↔
      elseType.CanCompleteBeforeTock = true := by
    have hCanonical := hElse _ elseType
      (compileType_initial_relation signature elseType)
    simpa [elseFragment, hElseStable, compileType] using hCanonical
  simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
  change state ∈
      (buildExclusiveOfferAutomaton signature branches elseFragment
        branchAutomata).completing ↔ residual.CanCompleteBeforeTock = true
  cases hRelated with
  | xoffer_source =>
      simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      have hNotElse : TypeAutomatonState.root ∉
          childCompleting 0 elseFragment := by
        rintro hMember
        simp only [childCompleting, Finset.mem_image] at hMember
        rcases hMember with ⟨child, _, hEquality⟩
        cases hEquality
      have hNotIndexed := root_not_mem_indexedFragmentCompleting branchAutomata
      have hCondition :
          (elseFragment.initial ∈ elseFragment.completing ∨
              branches.any (fun branch => branch.2.CanCompleteBeforeTock) = true) ↔
            (PactType.xoffer elseType branches).CanCompleteBeforeTock = true := by
        simp only [PactType.CanCompleteBeforeTock]
        rw [branchCanCompleteBeforeTock_eq_any branches]
        simp [hElseInitial]
      constructor
      · rintro ((hHeader | hElseMember) | hIndexed)
        · by_cases hConditionValue :
              elseFragment.initial ∈ elseFragment.completing ∨
                branches.any (fun branch =>
                  branch.2.CanCompleteBeforeTock) = true
          · exact hCondition.mp hConditionValue
          · rw [if_neg hConditionValue] at hHeader
            have hFalse : False := by simpa using hHeader
            exact hFalse.elim
        · exact (hNotElse hElseMember).elim
        · exact (hNotIndexed hIndexed).elim
      · intro hResidual
        left
        left
        have hConditionValue := hCondition.mpr hResidual
        rw [if_pos hConditionValue]
        exact Finset.mem_singleton_self _
  | xoffer_else _ _ _ childQ hChildRelated =>
      have hChild : childQ ∈ elseFragment.completing ↔
          residual.CanCompleteBeforeTock = true := by
        have hCanonical := hElse childQ residual hChildRelated
        simpa [elseFragment, hElseStable] using hCanonical
      have hNotHeader : childState 0 childQ ∉
          (if elseFragment.initial ∈ elseFragment.completing ∨
              branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
            {TypeAutomatonState.root}
          else (∅ : Finset TypeAutomatonState)) := by
        split <;> simp [childState]
      have hNotIndexed := child_zero_not_mem_indexedFragmentCompleting
        branchAutomata childQ
      simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      constructor
      · rintro ((hHeader | hElseMember) | hIndexed)
        · exact (hNotHeader hHeader).elim
        · apply hChild.mp
          simpa [childCompleting, childState] using hElseMember
        · exact (hNotIndexed hIndexed).elim
      · intro hResidual
        left
        right
        simpa [childCompleting, childState] using hChild.mpr hResidual
  | xoffer_branch _ branchType _ _ action index childQ hEntry hChildRelated =>
      have hBranchMem : (action, branchType) ∈ branches := by
        rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
        have hMember := List.getElem_mem hBound
        simpa [hValue] using hMember
      have hBranchFuel : TypeCompilationFuelSufficient branchType fuel := by
        apply le_trans
        · exact typeCompilationFuel_le_typeBranchCompilationFuel branches
            (action, branchType) hBranchMem
        · simp [fuel]
      have hBranchStable : compileTypeFuel signature fuel branchType =
          compileTypeFuel signature (typeCompilationFuel branchType)
            branchType :=
        compileTypeFuel_eq_of_sufficient signature branchType hBranchFuel
          (typeCompilationFuel_sufficient branchType)
      have hChild : childQ ∈
          (compileTypeFuel signature fuel branchType).completing ↔
          residual.CanCompleteBeforeTock = true := by
        have hCanonical := hBranches action branchType index hEntry
          childQ residual hChildRelated
        simpa [hBranchStable] using hCanonical
      have hAutomatonEntry : branchAutomata[index]? =
          some (action, compileTypeFuel signature fuel branchType) := by
        simp [branchAutomata, hEntry]
      have hIndexed := childState_mem_indexedFragmentCompleting_iff
        branchAutomata index
          (action, compileTypeFuel signature fuel branchType)
          hAutomatonEntry childQ
      simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      have hNotHeader : childState (index + 1) childQ ∉
          (if elseFragment.initial ∈ elseFragment.completing ∨
              branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
            {TypeAutomatonState.root}
          else (∅ : Finset TypeAutomatonState)) := by
        split <;> simp [childState]
      have hNotElse : childState (index + 1) childQ ∉
          childCompleting 0 elseFragment := by
        intro hMember
        simp only [childCompleting, Finset.mem_image] at hMember
        rcases hMember with ⟨other, hOther, hEquality⟩
        have hImpossible : 0 = index + 1 := by injection hEquality
        omega
      constructor
      · rintro ((hHeader | hElseMember) | hIndexedMember)
        · exact (hNotHeader hHeader).elim
        · exact (hNotElse hElseMember).elim
        · exact hChild.mp (hIndexed.mp hIndexedMember)
      · intro hResidual
        right
        exact hIndexed.mpr (hChild.mpr hResidual)

/-- Completion correctness for the generated conjunction used by `.offer`.
This is proved directly over the branch list, avoiding a non-structural
recursive call on `parallelTypeBranches`. -/
theorem compilationCompletingCorrect_parallelTypeBranches
    (signature : TypeAlphabet) : ∀ branches,
    (∀ (action : BareMessage) (branchType : PactType) (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationCompletingCorrect signature branchType) →
    CompilationCompletingCorrect signature (parallelTypeBranches branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _
      simpa [parallelTypeBranches] using
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
        · intro selected selectedType index hEntry
          have hIndex : index = 0 := by
            simpa using (List.getElem?_eq_some_iff.mp hEntry).1
          subst index
          simp only [List.getElem?_cons_zero, Option.some.injEq,
            Prod.mk.injEq] at hEntry
          rcases hEntry with ⟨rfl, rfl⟩
          exact hHead
      cases rest with
      | nil =>
          simpa [parallelTypeBranches] using hSingleton
      | cons next tail =>
          have hRest : ∀ (selected : BareMessage) (selectedType : PactType)
              (index : Nat),
              (next :: tail)[index]? = some (selected, selectedType) →
                CompilationCompletingCorrect signature selectedType := by
            intro selected selectedType index hEntry
            exact hBranches selected selectedType (index + 1) (by
              simpa using hEntry)
          have hTail := ih hRest
          simpa [parallelTypeBranches] using
            (compilationCompletingCorrect_parallel signature
              (singletonTypeXOffer (action, branchType))
              (parallelTypeBranches (next :: tail)) ∅ hSingleton hTail)

/-- Conjunctive offers inherit optimistic completion from the else
continuation or any branch continuation.  Tagged states inherit the exact
completion predicate of the generated conjunction or else child. -/
theorem compilationCompletingCorrect_offer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElse : CompilationCompletingCorrect signature elseType)
    (hConjunction : CompilationCompletingCorrect signature
      (parallelTypeBranches branches)) :
    CompilationCompletingCorrect signature (.offer elseType branches) := by
  intro state residual hRelated
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hConjunctionFuel : TypeCompilationFuelSufficient conjunctionType fuel := by
    rw [TypeCompilationFuelSufficient,
      typeCompilationFuel_parallelTypeBranches]
    simp [fuel, conjunctionType]
  have hElseStable : elseFragment = compileTypeFuel signature
      (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hConjunctionStable : conjunction = compileTypeFuel signature
      (typeCompilationFuel conjunctionType) conjunctionType :=
    compileTypeFuel_eq_of_sufficient signature conjunctionType
      hConjunctionFuel (typeCompilationFuel_sufficient conjunctionType)
  have hElseInitial : elseFragment.initial ∈ elseFragment.completing ↔
      elseType.CanCompleteBeforeTock = true := by
    have hCanonical := hElse _ elseType
      (compileType_initial_relation signature elseType)
    simpa [elseFragment, hElseStable, compileType] using hCanonical
  simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
  change state ∈
      (buildConjunctiveOfferAutomaton signature branches elseFragment
        conjunction).completing ↔ residual.CanCompleteBeforeTock = true
  cases hRelated with
  | offer_source =>
      have hNotConjunction : TypeAutomatonState.root ∉
          childCompleting 0 conjunction := by
        rintro hMember
        simp only [childCompleting, Finset.mem_image] at hMember
        rcases hMember with ⟨child, _, hEquality⟩
        cases hEquality
      have hNotElse : TypeAutomatonState.root ∉
          childCompleting 1 elseFragment := by
        rintro hMember
        simp only [childCompleting, Finset.mem_image] at hMember
        rcases hMember with ⟨child, _, hEquality⟩
        cases hEquality
      have hCondition :
          (elseFragment.initial ∈ elseFragment.completing ∨
              branches.any (fun branch =>
                branch.2.CanCompleteBeforeTock) = true) ↔
            (PactType.offer elseType branches).CanCompleteBeforeTock = true := by
        simp only [PactType.CanCompleteBeforeTock]
        rw [branchCanCompleteBeforeTock_eq_any branches]
        simp [hElseInitial]
      simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      constructor
      · rintro ((hHeader | hConjunctionMember) | hElseMember)
        · by_cases hValue :
              elseFragment.initial ∈ elseFragment.completing ∨
                branches.any (fun branch =>
                  branch.2.CanCompleteBeforeTock) = true
          · exact hCondition.mp hValue
          · rw [if_neg hValue] at hHeader
            simp at hHeader
        · exact (hNotConjunction hConjunctionMember).elim
        · exact (hNotElse hElseMember).elim
      · intro hResidual
        left
        have hValue := hCondition.mpr hResidual
        rw [if_pos hValue]
        exact Or.inl (Finset.mem_singleton_self _)
  | offer_branches _ childResidual _ childQ hChildRelated =>
      have hChild : childQ ∈ conjunction.completing ↔
          residual.CanCompleteBeforeTock = true := by
        have hCanonical := hConjunction childQ residual hChildRelated
        simpa [conjunction, conjunctionType, hConjunctionStable]
          using hCanonical
      have hNotHeader : childState 0 childQ ∉
          (if elseFragment.initial ∈ elseFragment.completing ∨
              branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
            {TypeAutomatonState.root}
          else (∅ : Finset TypeAutomatonState)) := by
        split <;> simp [childState]
      have hNotElse : childState 0 childQ ∉ childCompleting 1 elseFragment := by
        rintro hMember
        simp only [childCompleting, Finset.mem_image] at hMember
        rcases hMember with ⟨other, _, hEquality⟩
        have hImpossible : 1 = 0 := by injection hEquality
        omega
      simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      constructor
      · rintro ((hHeader | hConjunctionMember) | hElseMember)
        · exact (hNotHeader hHeader).elim
        · apply hChild.mp
          simpa [childCompleting, childState] using hConjunctionMember
        · exact (hNotElse hElseMember).elim
      · intro hResidual
        left
        right
        simpa [childCompleting, childState] using hChild.mpr hResidual
  | offer_else _ childResidual _ childQ hChildRelated =>
      have hChild : childQ ∈ elseFragment.completing ↔
          residual.CanCompleteBeforeTock = true := by
        have hCanonical := hElse childQ residual hChildRelated
        simpa [elseFragment, hElseStable] using hCanonical
      have hNotHeader : childState 1 childQ ∉
          (if elseFragment.initial ∈ elseFragment.completing ∨
              branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
            {TypeAutomatonState.root}
          else (∅ : Finset TypeAutomatonState)) := by
        split <;> simp [childState]
      have hNotConjunction : childState 1 childQ ∉
          childCompleting 0 conjunction := by
        rintro hMember
        simp only [childCompleting, Finset.mem_image] at hMember
        rcases hMember with ⟨other, _, hEquality⟩
        have hImpossible : 0 = 1 := by injection hEquality
        omega
      simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      constructor
      · rintro ((hHeader | hConjunctionMember) | hElseMember)
        · exact (hNotHeader hHeader).elim
        · exact (hNotConjunction hConjunctionMember).elim
        · apply hChild.mp
          simpa [childCompleting, childState] using hElseMember
      · intro hResidual
        right
        simpa [childCompleting, childState] using hChild.mpr hResidual

/-! ### Parallel future correspondence -/

/-- The optimistic product observations make parallel future correctness
compose directly from the two child future invariants.  Operational future
offers remain syntax-derived; the automaton equation is proved against
`typeFutureOffers_parallel`. -/
theorem compilationFutureCorrect_parallel
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hLeftFuture : CompilationFutureCorrect signature left)
    (hRightFuture : CompilationFutureCorrect signature right) :
    CompilationFutureCorrect signature (.par left right interface) := by
  intro state residual hRelated
  cases hRelated with
  | parallel _ _ leftResidual rightResidual _ leftState rightState
      hLeftRelated hRightRelated =>
      let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
      let leftFragment := compileTypeFuel signature fuel left
      let rightFragment := compileTypeFuel signature fuel right
      have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
        simp [TypeCompilationFuelSufficient, fuel]
      have hRightFuel : TypeCompilationFuelSufficient right fuel := by
        simp [TypeCompilationFuelSufficient, fuel]
      have hLeftStable := compileTypeFuel_eq_of_sufficient signature left
        hLeftFuel (typeCompilationFuel_sufficient left)
      have hRightStable := compileTypeFuel_eq_of_sufficient signature right
        hRightFuel (typeCompilationFuel_sufficient right)
      have hLeftState : leftState ∈ leftFragment.states := by
        have hState := compilationStateCorrect_of_compilation signature left
          leftState leftResidual hLeftRelated
        simpa [leftFragment, hLeftStable] using hState
      have hRightState : rightState ∈ rightFragment.states := by
        have hState := compilationStateCorrect_of_compilation signature right
          rightState rightResidual hRightRelated
        simpa [rightFragment, hRightStable] using hState
      have hFormula := buildParallelAutomaton_computeFuture interface
        leftFragment rightFragment leftState rightState hLeftState hRightState
        (compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel)
        (compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel)
      have hLeftSemantic : computeFuture
          { states := leftFragment.states, edges := leftFragment.edges }
          leftState = typeFutureOffers leftResidual := by
        have hExact := hLeftFuture leftState leftResidual hLeftRelated
        simpa [leftFragment, hLeftStable] using hExact
      have hRightSemantic : computeFuture
          { states := rightFragment.states, edges := rightFragment.edges }
          rightState = typeFutureOffers rightResidual := by
        have hExact := hRightFuture rightState rightResidual hRightRelated
        simpa [rightFragment, hRightStable] using hExact
      simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
      rw [hFormula, hLeftSemantic, hRightSemantic,
        typeFutureOffers_parallel]
      rfl


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

/-! ### Closed recursion-fragment correspondence -/

/-- Exact classifier for resolved edges leaving the fresh recursion header,
before the public alphabet filter. -/
private theorem buildRecursionAutomaton_root_hasResolvedEdge_iff
    (signature : TypeAlphabet) (name : String)
    (body : AutomatonFragment) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (target : TypeAutomatonState) :
    let recursion := buildRecursionAutomaton signature name body
    let pending : PendingAutomaton :=
      { states := recursion.states, edges := recursion.edges }
    recursion.HasResolvedEdge .root env label offers target ↔
      env ∈ signature.localEnvironments ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture pending (.child 0 body.initial) = offers.future ∧
        target = .child 0 body.initial := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge, buildRecursionAutomaton,
    finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    rcases hEdge with hHeader | hBody
    · rcases hHeader with ⟨edgeEnvironment, hLocal, rfl⟩
      simp only [Finset.sdiff_empty] at hFuture
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      aesop
    · rcases hBody with ⟨bodyEdge, hBodyEdge, rfl⟩
      by_cases hVariable : bodyEdge.label = .variable name
      · simp [hVariable, childState] at hSource
      · simp [hVariable, childState] at hSource
  · rintro ⟨hLocal, rfl, hCurrent, hFuture, rfl⟩
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (.child 0 body.initial) ∅
        target := .child 0 body.initial }, ?_, rfl, rfl, rfl, ?_, ?_, rfl⟩
    · left
      exact ⟨env, hLocal, rfl⟩
    · exact hCurrent.symm
    · simpa using hFuture

/-- A matching variable marker in the body is installed as a silent backedge
to the tagged body entry, and is resolved only in the closed recursion graph. -/
private theorem buildRecursionAutomaton_variable_marker_hasResolvedEdge
    (signature : TypeAlphabet) (name : String)
    (body : AutomatonFragment) (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ body.edges)
    (hVariable : edge.label = .variable name) :
    let recursion := buildRecursionAutomaton signature name body
    let pending : PendingAutomaton :=
      { states := recursion.states, edges := recursion.edges }
    recursion.HasResolvedEdge (.child 0 edge.source) edge.environment
      TypeLabel.silent
      { current := ∅,
        future := computeFuture pending (.child 0 body.initial) }
      (.child 0 body.initial) := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge]
  refine ⟨
    { source := .child 0 edge.source
      environment := edge.environment
      label := .visible TypeLabel.silent
      current := ∅
      future := .at (.child 0 body.initial) ∅
      target := .child 0 body.initial }, ?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · simp only [buildRecursionAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image]
    right
    refine ⟨edge, hEdge, ?_⟩
    simp [hVariable, childState]
  · simp

/-- Every resolved edge from a tagged recursion-body state is either the
installed matching-variable backedge or an unchanged non-matching body edge.
The latter's symbolic future is resolved in the enclosing recursion graph. -/
private theorem buildRecursionAutomaton_body_hasResolvedEdge_iff
    (signature : TypeAlphabet) (name : String)
    (body : AutomatonFragment) (source : TypeAutomatonState)
    (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : TypeAutomatonState) :
    let recursion := buildRecursionAutomaton signature name body
    let pending : PendingAutomaton :=
      { states := recursion.states, edges := recursion.edges }
    recursion.HasResolvedEdge (.child 0 source) env label offers target ↔
      (∃ edge ∈ body.edges,
        edge.source = source ∧ edge.label = .variable name ∧
          edge.environment = env ∧ label = TypeLabel.silent ∧
          offers.current = ∅ ∧
          computeFuture pending (.child 0 body.initial) = offers.future ∧
          target = .child 0 body.initial) ∨
      (∃ edge ∈ body.edges,
        edge.source = source ∧ edge.label ≠ .variable name ∧
          edge.environment = env ∧ edge.label = .visible label ∧
          edge.current = offers.current ∧
          (match edge.future with
            | .explicit future => future
            | .at state removed =>
                computeFuture pending (.child 0 state) \ removed) =
              offers.future ∧
          target = .child 0 edge.target) := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge, buildRecursionAutomaton,
    finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨lifted, hLifted, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    rcases hLifted with hHeader | hBody
    · rcases hHeader with ⟨headerEnvironment, hLocal, rfl⟩
      simp at hSource
    · rcases hBody with ⟨edge, hEdge, rfl⟩
      by_cases hVariable : edge.label = .variable name
      · simp only [hVariable, if_true, Finset.sdiff_empty, childState]
          at hSource hEnvironment hLabel hCurrent hFuture hTarget
        have hEdgeSource : edge.source = source := by
          injection hSource
        have hVisibleLabel : label = TypeLabel.silent := by
          injection hLabel with hEquality
          exact hEquality.symm
        left
        exact ⟨edge, hEdge, hEdgeSource, hVariable, hEnvironment,
          hVisibleLabel, hCurrent.symm, hFuture, hTarget.symm⟩
      · simp only [hVariable, if_false, childState]
          at hSource hEnvironment hLabel hCurrent hTarget
        have hEdgeSource : edge.source = source := by
          injection hSource
        have hEdgeTarget : target = .child 0 edge.target := hTarget.symm
        right
        refine ⟨edge, hEdge, hEdgeSource, hVariable, hEnvironment,
          hLabel, hCurrent, ?_, hEdgeTarget⟩
        cases hSpec : edge.future with
        | explicit future =>
            simpa [hVariable, hSpec, childFutureSpec] using hFuture
        | «at» state removed =>
            simpa [hVariable, hSpec, childFutureSpec, childState]
              using hFuture
  · rintro (hMarker | hBody)
    · rcases hMarker with ⟨edge, hEdge, hSource, hVariable,
        hEnvironment, hLabel, hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .child 0 edge.source
          environment := edge.environment
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (.child 0 body.initial) ∅
          target := .child 0 body.initial }, ?_, ?_, hEnvironment, ?_,
            hCurrent.symm, ?_, hTarget.symm⟩
      · right
        refine ⟨edge, hEdge, ?_⟩
        simp [hVariable, childState]
      · simpa [hSource]
      · simpa [hLabel]
      · simpa using hFuture
    · rcases hBody with ⟨edge, hEdge, hSource, hVariable,
        hEnvironment, hLabel, hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .child 0 edge.source
          environment := edge.environment
          label := edge.label
          current := edge.current
          future := childFutureSpec 0 edge.future
          target := .child 0 edge.target }, ?_, ?_, hEnvironment,
            hLabel, hCurrent, ?_, ?_⟩
      · right
        exact ⟨edge, hEdge, by simp [hVariable, childState]⟩
      · simpa [hSource, childState]
      · cases hSpec : edge.future with
        | explicit future =>
            simpa [hSpec, childFutureSpec] using hFuture
        | «at» state removed =>
            simpa [hSpec, childFutureSpec, childState] using hFuture
      · simpa [hTarget, childState]

/-- Ambient syntax-future invariant required by recursion.  The left side is
computed in the closed binder graph, while the right side remains the
syntax-derived future menu of the unfolded residual. -/
def RecursionBodyFutureCorrect
    (signature : TypeAlphabet) (name : String) (body : PactType) : Prop :=
  let bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
  let recursion := buildRecursionAutomaton signature name bodyFragment
  let pending : PendingAutomaton :=
    { states := recursion.states, edges := recursion.edges }
  ∀ state residual,
    TypeCompilationRelation body state residual →
      computeFuture pending (.child 0 state) =
        typeFutureOffers (residual.replaceVar name (.recur name body))

/-- The fresh recursion header contributes no offers of its own and has one
same-cycle reference, to the tagged body entry. -/
private theorem buildRecursionAutomaton_computeFuture_root
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment)
    (hBodyTargets : body.FutureTargetsInStates)
    (hBodyInitial : body.initial ∈ body.states) :
    let recursion := buildRecursionAutomaton signature name body
    let pending : PendingAutomaton :=
      { states := recursion.states, edges := recursion.edges }
    computeFuture pending .root =
      computeFuture pending (.child 0 body.initial) := by
  classical
  let recursion := buildRecursionAutomaton signature name body
  let pending : PendingAutomaton :=
    { states := recursion.states, edges := recursion.edges }
  have hClosed : pending.ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_of_futureTargetsInStates recursion
    exact buildRecursionAutomaton_futureTargetsInStates signature name body
      hBodyTargets hBodyInitial
  have hRoot : (.root : TypeAutomatonState) ∈ pending.states := by
    simp [pending, recursion, buildRecursionAutomaton,
      finishAutomatonFragment]
  have hOffers : pending.offersAt .root = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro action hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hAction
    rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
    simp only [pending, recursion, buildRecursionAutomaton,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with hHeader | hBody
    · rcases hHeader with ⟨environment, _, rfl⟩
      simp [AutomatonConstructionLabel.semantic] at hOffer
    · rcases hBody with ⟨bodyEdge, _, rfl⟩
      by_cases hVariable : bodyEdge.label = .variable name
      · simp [hVariable, childState] at hSource
      · simp [hVariable, childState] at hSource
  have hReferences : pending.referencedStates .root =
      {.child 0 body.initial} := by
    ext state
    constructor
    · intro hState
      simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
        Finset.mem_filter] at hState
      rcases hState with ⟨edge, ⟨hEdge, hSource⟩, hReference⟩
      simp only [pending, recursion, buildRecursionAutomaton,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_image] at hEdge
      rcases hEdge with hHeader | hBody
      · rcases hHeader with ⟨environment, _, rfl⟩
        simp [AutomatonConstructionLabel.semantic] at hReference
        simpa [TypeLabel.silent] using hReference
      · rcases hBody with ⟨bodyEdge, _, rfl⟩
        by_cases hVariable : bodyEdge.label = .variable name
        · simp [hVariable, childState] at hSource
        · simp [hVariable, childState] at hSource
    · intro hState
      simp only [Finset.mem_singleton] at hState
      subst state
      let edge : PendingAutomatonEdge :=
        { source := .root
          environment := TypeEnvironment.tock
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (.child 0 body.initial) ∅
          target := .child 0 body.initial }
      simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
        Finset.mem_filter]
      refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
      · simp only [pending, recursion, buildRecursionAutomaton,
          finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
        left
        exact ⟨TypeEnvironment.tock,
          by simp [TypeAlphabet.localEnvironments], rfl⟩
      · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.silent]
  change computeFuture pending .root =
    computeFuture pending (.child 0 body.initial)
  rw [computeFuture_unfold pending .root hClosed hRoot, hOffers, hReferences]
  simp

/-- Whole-fragment future correctness supplies the ambient tagged-body
invariant required by the recursion constructor. -/
theorem recursionBodyFutureCorrect_of_compilationFutureCorrect
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hFuture : CompilationFutureCorrect signature (.recur name body)) :
    RecursionBodyFutureCorrect signature name body := by
  intro state residual hRelated
  simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
    hFuture (.child 0 state)
      (residual.replaceVar name (.recur name body))
      (TypeCompilationRelation.recur_body name body residual state hRelated)

/-- A clock-guarded binder's whole-fragment future correctness follows from
the closed tagged-body invariant.  The semantic menu on the right remains
the syntax-derived `typeFutureOffers`; the graph is used only to verify the
compiled constructor implements that menu. -/
theorem compilationFutureCorrect_recursion
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hGuarded : body.GuardedOccurrences name False)
    (hBodyFuture : RecursionBodyFutureCorrect signature name body) :
    CompilationFutureCorrect signature (.recur name body) := by
  intro state residual hRelated
  cases hRelated with
  | recur_source =>
      let bodyFragment := compileTypeFuel signature
        (typeCompilationFuel body) body
      let recursion := buildRecursionAutomaton signature name bodyFragment
      let pending : PendingAutomaton :=
        { states := recursion.states, edges := recursion.edges }
      have hFuel := typeCompilationFuel_sufficient body
      have hInitial : bodyFragment.initial ∈ bodyFragment.states :=
        compileTypeFuel_initial_mem signature (typeCompilationFuel body) body
          hFuel
      have hTargets : bodyFragment.FutureTargetsInStates :=
        compileTypeFuel_futureTargetsInStates signature
          (typeCompilationFuel body) body hFuel
      have hRoot : computeFuture pending .root =
          computeFuture pending (.child 0 bodyFragment.initial) := by
        simpa [pending, recursion] using
          buildRecursionAutomaton_computeFuture_root signature name
            bodyFragment hTargets hInitial
      have hInitialRelation : TypeCompilationRelation body
          bodyFragment.initial body :=
        compileTypeFuel_initial_relation signature
          (typeCompilationFuel body) body hFuel
      have hEntry : computeFuture pending (.child 0 bodyFragment.initial) =
          typeFutureOffers (body.replaceVar name (.recur name body)) := by
        simpa [RecursionBodyFutureCorrect, bodyFragment, recursion, pending]
          using hBodyFuture bodyFragment.initial body hInitialRelation
      have hUnfold := guardedOccurrences_replace_typeFutureOffers_recur
        name body body hGuarded
      have hSyntax := typeFutureOffers_recur name body
      have hResult : computeFuture pending .root =
          typeFutureOffers (.recur name body) :=
        hRoot.trans (hEntry.trans (hUnfold.trans hSyntax.symm))
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        bodyFragment, recursion, pending] using hResult
  | recur_body _ _ childResidual childState hChildRelated =>
      have hBody := hBodyFuture childState childResidual hChildRelated
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
        hBody

/-- The recursion-specific tagged-body obligation.  It interprets matching
variable markers as calls of the surrounding binder and resolves symbolic
futures after the binder installs its backedges. -/
def RecursionBodyStepCorrect
    (signature : TypeAlphabet) (name : String) (body : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.recur name body)) (.recur name body)
  ∀ {state : TypeAutomatonState} {residual residual' : PactType}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    TypeCompilationRelation body state residual →
    env ∈ signature.localEnvironments →
    (DecoratedTypeTransition env
        (residual.replaceVar name (.recur name body)) label offers residual' ↔
      ∃ target,
        fragment.HasResolvedEdge (.child 0 state) env label offers target ∧
        TypeCompilationRelation (.recur name body) target residual')

/-- Inversion of a decorated recursion-header transition. -/
private theorem TypeTransition.recur_fields
    {env : TypeEnvironment} {name : String} {body target : PactType}
    {label : TypeLabel}
    (hTransition : TypeTransition env (.recur name body) label target) :
    env.WellFormed ∧ label = TypeLabel.silent ∧
      target = body.replaceVar name (.recur name body) := by
  cases hTransition <;> simp_all

private theorem TypeOffers.recur_fields
    {env : TypeEnvironment} {name : String} {body target : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.recur name body) label target current future) :
    label = TypeLabel.silent ∧
      target = body.replaceVar name (.recur name body) ∧
      current = ∅ ∧
      future = typeFutureOffers
        (body.replaceVar name (.recur name body)) := by
  cases hOffers <;> simp_all

private theorem decoratedTypeTransition_recur_iff
    (env : TypeEnvironment) (name : String) (body target : PactType)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    DecoratedTypeTransition env (.recur name body) label offers target ↔
      env.WellFormed ∧ label = TypeLabel.silent ∧
        target = body.replaceVar name (.recur name body) ∧
        offers.current = ∅ ∧
        offers.future =
          typeFutureOffers (body.replaceVar name (.recur name body)) := by
  constructor
  · rintro ⟨hTransition, hOffers⟩
    have hTransitionFields := TypeTransition.recur_fields hTransition
    have hOfferFields := TypeOffers.recur_fields hOffers
    exact ⟨hTransitionFields.1, hTransitionFields.2.1,
      hTransitionFields.2.2, hOfferFields.2.2.1,
      hOfferFields.2.2.2⟩
  · rintro ⟨hWellFormed, rfl, rfl, hCurrent, hFuture⟩
    cases offers
    simp only at hCurrent hFuture
    subst_vars
    exact ⟨TypeTransition.recur env name body hWellFormed,
      TypeOffers.recur env name body hWellFormed⟩

/-- The root-state branch of raw recursion correspondence.  Guardedness and
tail-recursiveness enter later, when the two body invariants are established. -/
theorem compilationFragmentStepCorrect_recursion_root
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    {residual' : PactType} {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hLocalEnvironment : env ∈ signature.localEnvironments) :
    DecoratedTypeTransition env (.recur name body) label offers residual' ↔
      ∃ state',
        (compileTypeFuel signature
          (typeCompilationFuel (.recur name body))
          (.recur name body)).HasResolvedEdge .root env label offers state' ∧
        TypeCompilationRelation (.recur name body) state' residual' := by
  let bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
  let recursion := buildRecursionAutomaton signature name bodyFragment
  let pending : PendingAutomaton :=
    { states := recursion.states, edges := recursion.edges }
  have hBodyInitial : TypeCompilationRelation body bodyFragment.initial body := by
    exact compileTypeFuel_initial_relation signature
      (typeCompilationFuel body) body
      (typeCompilationFuel_sufficient body)
  have hComputed : computeFuture pending (.child 0 bodyFragment.initial) =
      typeFutureOffers (body.replaceVar name (.recur name body)) := by
    have hAmbient := hFuture bodyFragment.initial body hBodyInitial
    simpa [RecursionBodyFutureCorrect, bodyFragment, recursion, pending]
      using hAmbient
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.recur name body)) (.recur name body) =
        recursion := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hTargetRelation : TypeCompilationRelation (.recur name body)
      (.child 0 bodyFragment.initial)
      (body.replaceVar name (.recur name body)) :=
    TypeCompilationRelation.recur_body name body body _ hBodyInitial
  constructor
  · intro hStep
    rcases (decoratedTypeTransition_recur_iff env name body residual'
      label offers).mp hStep with
      ⟨hWellFormed, hLabel, hResidual, hCurrent, hOfferFuture⟩
    subst residual'
    refine ⟨.child 0 bodyFragment.initial, ?_, hTargetRelation⟩
    rw [hFragment]
    apply (buildRecursionAutomaton_root_hasResolvedEdge_iff signature name
      bodyFragment env label offers (.child 0 bodyFragment.initial)).mpr
    exact ⟨hLocalEnvironment, hLabel, hCurrent, hComputed.trans
      hOfferFuture.symm, rfl⟩
  · rintro ⟨target, hEdge, hTarget⟩
    rw [hFragment] at hEdge
    rcases (buildRecursionAutomaton_root_hasResolvedEdge_iff signature name
      bodyFragment env label offers target).mp hEdge with
      ⟨_, hLabel, hCurrent, hEdgeFuture, hTargetState⟩
    subst target
    have hResidual : residual' =
        body.replaceVar name (.recur name body) :=
      TypeCompilationRelation.residual_unique hTarget hTargetRelation
    apply (decoratedTypeTransition_recur_iff env name body residual'
      label offers).mpr
    exact ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
      hLabel, hResidual, hCurrent,
      (hComputed.symm.trans hEdgeFuture).symm⟩

/-- The header and tagged-body branches compose into raw recursion step
correspondence once their two closed-graph invariants are available. -/
theorem compilationFragmentStepCorrect_recursion
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    (hBodyStep : RecursionBodyStepCorrect signature name body) :
    CompilationFragmentStepCorrect signature (.recur name body) := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
  cases hRelated with
  | recur_source =>
      exact compilationFragmentStepCorrect_recursion_root signature name body
        hFuture hLocalEnvironment
  | recur_body _ _ childResidual childState hChildRelated =>
      exact hBodyStep hChildRelated hLocalEnvironment

/-- Raw fragment correspondence exports uniformly through the fixed public
alphabet filter. -/
theorem compilationStepCorrect_of_fragmentStepCorrect
    (signature : TypeAlphabet) (processType : PactType)
    (hRaw : CompilationFragmentStepCorrect signature processType) :
    CompilationStepCorrect signature processType := by
  intro residual residual' state env label offers hRelated hSymbol
  have hSignatureSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hLocalEnvironment : env ∈ signature.localEnvironments := by
    have hFields : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
    exact signature.environments_subset_localEnvironments hFields.1
  have hFragment := hRaw (residual' := residual') (label := label)
    (offers := offers) hRelated hLocalEnvironment
  constructor
  · intro hStep
    rcases hFragment.mp hStep with ⟨target, hEdge, hTarget⟩
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature processType
        state target env label offers hSignatureSymbol).mpr hEdge,
      hTarget⟩
  · rintro ⟨target, hEdge, hTarget⟩
    apply hFragment.mpr
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature processType
        state target env label offers hSignatureSymbol).mp hEdge,
      hTarget⟩

/-- Public recursion correspondence follows from the two closed-graph
recursion invariants. -/
theorem compilationStepCorrect_recursion
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    (hBodyStep : RecursionBodyStepCorrect signature name body) :
    CompilationStepCorrect signature (.recur name body) :=
  compilationStepCorrect_of_fragmentStepCorrect signature (.recur name body)
    (compilationFragmentStepCorrect_recursion signature name body
      hFuture hBodyStep)

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
  | future => simp [hLabel] at hOutput
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
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
          Finset.mem_filter] at hProductEdge
        rcases hProductEdge with hTransition | hFuture
        · rcases hTransition with
            ⟨leftEdge, _, rightEdge, ⟨_, _⟩, rfl⟩
          intro action hAction hInterface
          rw [hEnvironment] at hAction
          unfold combineAutomatonEnvironment at hAction
          split at hAction
          · simp [TypeEnvironment.tock] at hAction
          · exact (Finset.mem_filter.mp hAction).2 hInterface
        · rcases hFuture with hLeftFuture | hRightFuture
          · rcases hLeftFuture with
              ⟨leftState, _, rightState, _, hEdge⟩
            rw [← hEdge] at hLabel
            simp at hLabel
          · rcases hRightFuture with
              ⟨leftState, _, rightState, _, hEdge⟩
            rw [← hEdge] at hLabel
            simp at hLabel
      · simp at hOutput

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

private theorem supports_branch_of_mem (signature : TypeAlphabet) :
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

private theorem allVariablesBound_branch_of_mem (bound : List String) :
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

private theorem clockGuarded_branch_of_mem :
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

private theorem tailRecursive_branch_of_mem :
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

private theorem sameCycleMessageLinear_branch_of_mem :
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

private theorem interfaceScoped_branch_of_mem :
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

/-- The three mutually supporting invariants needed by the structural
compiler proof.  Public step correspondence is derived uniformly from the raw
fragment field, so constructor cases do not repeat alphabet-filter plumbing. -/
structure CompilationProofBundle
    (signature : TypeAlphabet) (processType : PactType) : Prop where
  future : CompilationFutureCorrect signature processType
  completing : CompilationCompletingCorrect signature processType
  scopedStep : CompilationScopedFragmentStepCorrect signature processType

/- The following raw atomic/selection obligations are deliberately exposed as
small leaves.  Their public counterparts and all edge classifications are
already proved above; these leaves only remove the public alphabet filter. -/
private theorem compilationFragmentStepCorrect_skip_leaf
    (signature : TypeAlphabet) :
    CompilationFragmentStepCorrect signature .skip := by
  sorry

private theorem compilationFragmentStepCorrect_message_leaf
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CompilationFragmentStepCorrect signature (.message msg dir) := by
  sorry

private theorem compilationFragmentStepCorrect_tock_leaf
    (signature : TypeAlphabet) :
    CompilationFragmentStepCorrect signature .tock := by
  sorry

private theorem compilationFragmentStepCorrect_progress_leaf
    (signature : TypeAlphabet) (pid : ProcId) :
    CompilationFragmentStepCorrect signature (.progress pid) := by
  sorry

private theorem compilationFragmentStepCorrect_choice_leaf
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right) :
    CompilationScopedFragmentStepCorrect signature (.choice left right) := by
  sorry

private theorem compilationFragmentStepCorrect_fairChoice_leaf
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right) :
    CompilationScopedFragmentStepCorrect signature
      (.fairChoice bid left right) := by
  sorry

/-- Local graph fold for a tagged left sequence state.  The sequence builder
redecorates every non-construction edge by a reference to its target, so this
lemma is deliberately stated below the constructor theorem: it is the finite
closure calculation, not another semantic correspondence theorem. -/
private theorem buildSequenceAutomaton_computeFuture_left_of_bundle
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right)
    (state : TypeAutomatonState) (residual : PactType)
    (hRelated : TypeCompilationRelation left state residual) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let leftFragment := compileTypeFuel signature fuel left
    let rightFragment := compileTypeFuel signature fuel right
    let sequence := buildSequenceAutomaton signature leftFragment rightFragment
    let pending : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    computeFuture pending (.child 0 state) =
      typeFutureOffers (.seq residual right) := by
  sorry

/-- The remaining sequence-future leaf.  Its lower bound is
`buildSequenceAutomaton_rightFuture_subset_of_completing`; the unfinished
direction is the local upper-bound showing that re-decorated left edges expose
no offers beyond the syntactic residual menu. -/
theorem compilationFutureCorrect_sequence
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right) :
    CompilationFutureCorrect signature (.seq left right) := by
  intro state residual hRelated
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
  | sequence_left _ _ childResidual childState hChildRelated =>
      simpa [fuel, leftFragment, rightFragment, sequence, pending] using
        buildSequenceAutomaton_computeFuture_left_of_bundle signature left
          right hLeft hRight childState childResidual hChildRelated
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
      have hCanonical := hRight.future childState residual hChildRelated
      rw [hEmbedded]
      simpa [rightFragment, hRightStable, pending, sequence] using hCanonical

private theorem compilationScopedFragmentStepCorrect_sequence_leaf
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right)
    (hFuture : CompilationFutureCorrect signature (.seq left right)) :
    CompilationScopedFragmentStepCorrect signature (.seq left right) := by
  intro residual residual' state env label offers hRelated hLocal hAvoids
  have hAvoidsLeft : env.AvoidsInterface left.ParallelInterfaces :=
    hAvoids.mono (by simp [PactType.ParallelInterfaces])
  have hAvoidsRight : env.AvoidsInterface right.ParallelInterfaces :=
    hAvoids.mono (by simp [PactType.ParallelInterfaces])
  have hLeftSkipping := compilationSkippingCorrect_of_compilation signature left
  cases hRelated with
  | sequence_left _ _ childResidual childState hChildRelated =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | skip_seq =>
            obtain ⟨hCurrent, hOfferFuture⟩ :=
              TypeOffers.skip_sequence_fields hOffers
            have hSkipping : childState ∈
                (compileTypeFuel signature
                  (typeCompilationFuel left) left).skipping :=
              (hLeftSkipping childState .skip hChildRelated).mpr rfl
            have hRightInitial : TypeCompilationRelation right
                (compileTypeFuel signature
                  (typeCompilationFuel right) right).initial right := by
              simpa [compileType] using
                (compileType_initial_relation signature right)
            have hTarget : TypeCompilationRelation (.seq left right)
                (.child 1 (compileTypeFuel signature
                  (typeCompilationFuel right) right).initial) right :=
              TypeCompilationRelation.sequence_right left right right _
                hRightInitial
            have hComputed := hFuture _ _ hTarget
            refine ⟨.child 1 (compileTypeFuel signature
                (typeCompilationFuel right) right).initial, ?_, hTarget⟩
            apply (compileTypeFuel_sequence_bridge_edge_iff signature left right
              childState env TypeLabel.silent offers).mpr
            exact ⟨hSkipping, hLocal, rfl, hCurrent,
              hComputed.trans hOfferFuture.symm⟩
        | seq _ _ childTarget _ _ hChildTransition =>
            obtain ⟨childFuture, hChildOffers, hOfferFuture⟩ :=
              TypeOffers.sequence_fields hOffers
            rcases (hLeft.scopedStep (residual' := childTarget)
                (label := label)
                (offers := { current := offers.current, future := childFuture })
                hChildRelated hLocal hAvoidsLeft).mp
                ⟨hChildTransition, hChildOffers⟩ with
              ⟨childState', hChildEdge, hChildTarget⟩
            have hTarget : TypeCompilationRelation (.seq left right)
                (.child 0 childState') (.seq childTarget right) :=
              TypeCompilationRelation.sequence_left left right childTarget _
                hChildTarget
            have hComputed := hFuture _ _ hTarget
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
              rcases (hLeft.scopedStep hChildRelated hLocal hAvoidsLeft).mpr
                  ⟨childTarget, hChildEdge, hChildTarget⟩ with
                ⟨hChildTransition, hChildOffers⟩
              refine ⟨TypeTransition.seq env childResidual targetResidual right
                  label hChildTransition, ?_⟩
              have hParentTarget : TypeCompilationRelation (.seq left right)
                  (.child 0 childTarget) (.seq targetResidual right) :=
                TypeCompilationRelation.sequence_left left right targetResidual _
                  hChildTarget
              have hTargetFuture := hFuture _ _ hParentTarget
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
              have hTargetFuture := hFuture _ _ hParentTarget
              have hOfferFuture : offers.future = typeFutureOffers right :=
                hComputed.symm.trans hTargetFuture
              subst label
              refine ⟨TypeTransition.skip_seq env right
                  (TypeAlphabet.localEnvironment_wellFormed hLocal), ?_⟩
              simpa only [hCurrent, hOfferFuture] using
                (TypeOffers.skip_seq env right
                  (TypeAlphabet.localEnvironment_wellFormed hLocal))
  | sequence_right _ _ childResidual childState hChildRelated =>
      constructor
      · intro hStep
        rcases (hRight.scopedStep hChildRelated hLocal hAvoidsRight).mp hStep with
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
            exact (hRight.scopedStep hChildRelated hLocal hAvoidsRight).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

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
        (.par left right interface)).HasResolvedEdge state env label offers
          target ∧
      TypeCompilationRelation (.par left right interface) target residual' := by
  exact parallel_semantic_step_to_resolved_edge signature left right interface
    hInterface hScoped hLeft.scopedStep hRight.scopedStep hRelated hLocal
      hAvoids hStep

private theorem parallel_resolved_edge_to_semantic_step_leaf
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface) (hSignature : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
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
      (.par left right interface)).HasResolvedEdge state env label offers target)
    (hTarget : TypeCompilationRelation (.par left right interface)
      target residual') :
    DecoratedTypeTransition env residual label offers residual' := by
  sorry

private theorem compilationFragmentStepCorrect_parallel_leaf
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface) (hSignature : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hScoped : PactType.InterfaceScoped (.par left right interface))
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right) :
    CompilationScopedFragmentStepCorrect signature
      (.par left right interface) := by
  intro residual residual' state env label offers hRelated hLocal hAvoids
  constructor
  · exact parallel_semantic_step_to_resolved_edge_leaf signature left right
      interface hSignature hInterface hScoped hLeft hRight hRelated hLocal
        hAvoids
  · rintro ⟨target, hEdge, hTarget⟩
    exact parallel_resolved_edge_to_semantic_step_leaf signature left right
      interface hSignature hInterface hLeft hRight hRelated hLocal hAvoids
      hEdge hTarget

/-- The binder-local future fold.  This is the remaining variable-marker
calculation: matching markers are interpreted in the graph after the enclosing
backedge has been installed. -/
private theorem recursionBodyFutureCorrect_regular_leaf
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.recur name body))
    (hClosed : PactType.AllVariablesBound [] (.recur name body))
    (hGuarded : PactType.ClockGuarded (.recur name body))
    (hTail : PactType.TailRecursive (.recur name body))
    (hLinear : PactType.SameCycleMessageLinear (.recur name body)) :
    RecursionBodyFutureCorrect signature name body := by
  sorry

/-- Completion metadata for a guarded binder.  Guarded calls cannot complete
before the next tock, so the root and tagged-body clauses reduce to the body
predicate and guarded substitution. -/
private theorem compilationCompletingCorrect_recursion_regular_leaf
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hGuarded : PactType.ClockGuarded (.recur name body))
    (hTail : PactType.TailRecursive (.recur name body)) :
    CompilationCompletingCorrect signature (.recur name body) := by
  sorry

private theorem compilationScopedFragmentStepCorrect_recursion_regular_leaf
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.recur name body))
    (hClosed : PactType.AllVariablesBound [] (.recur name body))
    (hGuarded : PactType.ClockGuarded (.recur name body))
    (hTail : PactType.TailRecursive (.recur name body))
    (hLinear : PactType.SameCycleMessageLinear (.recur name body))
    (hScoped : PactType.InterfaceScoped (.recur name body))
    (hFuture : RecursionBodyFutureCorrect signature name body) :
    CompilationScopedFragmentStepCorrect signature (.recur name body) := by
  sorry

/-- Guarded/tail recursion is kept as one closed-graph leaf: it must establish
the body future and step packages against the graph after backedges are
installed.  Header composition itself is already proved above. -/
private theorem compilationProofBundle_recursion_leaf
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.recur name body))
    (hClosed : PactType.AllVariablesBound [] (.recur name body))
    (hGuarded : PactType.ClockGuarded (.recur name body))
    (hTail : PactType.TailRecursive (.recur name body))
    (hLinear : PactType.SameCycleMessageLinear (.recur name body))
    (hScoped : PactType.InterfaceScoped (.recur name body)) :
    CompilationProofBundle signature (.recur name body) := by
  have hBodyFuture := recursionBodyFutureCorrect_regular_leaf signature name
    body hSignature hSupports hClosed hGuarded hTail hLinear
  have hGuardedOccurrences : body.GuardedOccurrences name False := by
    have hFields : body.GuardedOccurrences name False ∧ body.ClockGuarded := by
      simpa only [PactType.ClockGuarded] using hGuarded
    exact hFields.1
  exact
    { future := compilationFutureCorrect_recursion signature name body
        hGuardedOccurrences hBodyFuture
      completing := compilationCompletingCorrect_recursion_regular_leaf
        signature name body hGuarded hTail
      scopedStep := compilationScopedFragmentStepCorrect_recursion_regular_leaf
        signature name body hSignature hSupports hClosed hGuarded hTail hLinear
          hScoped hBodyFuture }

/-- Exclusive-offer closure packages its indexed branch/else/wait
classifiers.  Completion is supplied by the strong-induction hypotheses for
the else continuation and every indexed branch. -/

private theorem compilationFutureCorrect_xoffer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hClosed : PactType.AllVariablesBound [] (.xoffer elseType branches))
    (hGuarded : PactType.ClockGuarded (.xoffer elseType branches))
    (hTail : PactType.TailRecursive (.xoffer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.xoffer elseType branches)) :
    CompilationFutureCorrect signature (.xoffer elseType branches) := by
  sorry

private theorem compilationFragmentStepCorrect_xoffer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hClosed : PactType.AllVariablesBound [] (.xoffer elseType branches))
    (hGuarded : PactType.ClockGuarded (.xoffer elseType branches))
    (hTail : PactType.TailRecursive (.xoffer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.xoffer elseType branches))
    (hScoped : PactType.InterfaceScoped (.xoffer elseType branches))
    (hFuture : CompilationFutureCorrect signature
      (.xoffer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationScopedFragmentStepCorrect signature
      (.xoffer elseType branches) := by
  exact compilationScopedFragmentStepCorrect_xoffer signature elseType
    branches hElse.scopedStep
      (fun action branchType index hEntry =>
        (hBranches action branchType index hEntry).scopedStep)
      hFuture

private theorem compilationProofBundle_xoffer_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hClosed : PactType.AllVariablesBound [] (.xoffer elseType branches))
    (hGuarded : PactType.ClockGuarded (.xoffer elseType branches))
    (hTail : PactType.TailRecursive (.xoffer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.xoffer elseType branches))
    (hScoped : PactType.InterfaceScoped (.xoffer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationProofBundle signature (.xoffer elseType branches) := by
  have hFuture := compilationFutureCorrect_xoffer_regular_leaf signature
    elseType branches hSignature hSupports hClosed hGuarded hTail hLinear
  have hBranchCompleting : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationCompletingCorrect signature branchType := by
    intro action branchType index hEntry
    exact (hBranches action branchType index hEntry).completing
  exact
    { future := hFuture
      completing := compilationCompletingCorrect_xoffer signature elseType
        branches hElse.completing hBranchCompleting
      scopedStep := compilationFragmentStepCorrect_xoffer_regular_leaf
        signature elseType branches hSignature hSupports hClosed hGuarded hTail
          hLinear hScoped hFuture hElse hBranches }

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
                  (compilationFragmentStepCorrect_skip_leaf signature) })
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
                (compilationFragmentStepCorrect_skip_leaf signature) }
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
          hSingletonClosed hSingletonGuarded hSingletonTail hSingletonLinear
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
                  hSingletonBundle hRestBundle })

/-- Conjunctive-offer closure packages the generated branch product and its
enabled/else/wait root classifiers. -/
private theorem compilationFutureCorrect_offer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.offer elseType branches))
    (hClosed : PactType.AllVariablesBound [] (.offer elseType branches))
    (hGuarded : PactType.ClockGuarded (.offer elseType branches))
    (hTail : PactType.TailRecursive (.offer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.offer elseType branches)) :
    CompilationFutureCorrect signature (.offer elseType branches) := by
  sorry

private theorem compilationCompletingCorrect_offer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationCompletingCorrect signature (.offer elseType branches) := by
  have hBranchCompleting : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationCompletingCorrect signature branchType := by
    intro action branchType index hEntry
    exact (hBranches action branchType index hEntry).completing
  have hConjunction := compilationCompletingCorrect_parallelTypeBranches
    signature branches hBranchCompleting
  exact compilationCompletingCorrect_offer signature elseType branches
    hElse.completing hConjunction

private theorem compilationFragmentStepCorrect_offer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.offer elseType branches))
    (hClosed : PactType.AllVariablesBound [] (.offer elseType branches))
    (hGuarded : PactType.ClockGuarded (.offer elseType branches))
    (hTail : PactType.TailRecursive (.offer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.offer elseType branches))
    (hScoped : PactType.InterfaceScoped (.offer elseType branches))
    (hFuture : CompilationFutureCorrect signature (.offer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationScopedFragmentStepCorrect signature
      (.offer elseType branches) := by
  have hSupportFields := hSupports
  have hClosedFields := hClosed
  have hGuardedFields := hGuarded
  have hTailFields := hTail
  have hLinearFields := hLinear
  have hScopedFields := hScoped
  simp only [TypeAlphabet.Supports] at hSupportFields
  simp only [PactType.AllVariablesBound] at hClosedFields
  simp only [PactType.ClockGuarded] at hGuardedFields
  simp only [PactType.TailRecursive] at hTailFields
  simp only [PactType.SameCycleMessageLinear] at hLinearFields
  simp only [PactType.InterfaceScoped] at hScopedFields
  have hConjunction := compilationProofBundle_parallelTypeBranches_leaf
    signature branches hSignature hSupportFields.2 hClosedFields.2
      hGuardedFields.2 hTailFields.2 hLinearFields.2 hScopedFields.2 hBranches
  intro residual residual' state environment label offers hRelated hLocal
    hAvoids
  exact compilationScopedFragmentStepCorrect_offer signature elseType branches
    hConjunction.scopedStep hElse.scopedStep hFuture hRelated hLocal hAvoids

private theorem compilationProofBundle_offer_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.offer elseType branches))
    (hClosed : PactType.AllVariablesBound [] (.offer elseType branches))
    (hGuarded : PactType.ClockGuarded (.offer elseType branches))
    (hTail : PactType.TailRecursive (.offer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.offer elseType branches))
    (hScoped : PactType.InterfaceScoped (.offer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationProofBundle signature (.offer elseType branches) := by
  have hFuture := compilationFutureCorrect_offer_regular_leaf signature
    elseType branches hSignature hSupports hClosed hGuarded hTail hLinear
  exact
    { future := hFuture
      completing := compilationCompletingCorrect_offer_regular_leaf signature
        elseType branches hElse hBranches
      scopedStep := compilationFragmentStepCorrect_offer_regular_leaf
        signature elseType branches hSignature hSupports hClosed hGuarded hTail
          hLinear hScoped hFuture hElse hBranches }

/-- Top-down structural assembly of all compiler invariants.  The proof is
complete at the hierarchy level: every unfinished fact is now a named local
constructor leaf above, rather than an undifferentiated hole in `stepIff`. -/
theorem compilationProofBundle_of_closedGuardedRegular
    (signature : TypeAlphabet) : ∀ processType,
    signature.WellFormed →
    signature.Supports processType →
    PactType.AllVariablesBound [] processType →
    PactType.ClockGuarded processType →
    PactType.TailRecursive processType →
    PactType.SameCycleMessageLinear processType →
    PactType.InterfaceScoped processType →
    CompilationProofBundle signature processType := by
  intro processType
  cases processType with
  | message msg dir =>
      intro _ _ _ _ _ _ _
      exact
        { future := compilationFutureCorrect_message signature msg dir
          completing := compilationCompletingCorrect_message signature msg dir
          scopedStep := compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
            signature (.message msg dir)
              (compilationFragmentStepCorrect_message_leaf signature msg dir) }
  | progress pid =>
      intro _ _ _ _ _ _ _
      exact
        { future := compilationFutureCorrect_progress signature pid
          completing := compilationCompletingCorrect_progress signature pid
          scopedStep := compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
            signature (.progress pid)
              (compilationFragmentStepCorrect_progress_leaf signature pid) }
  | tock =>
      intro _ _ _ _ _ _ _
      exact
        { future := compilationFutureCorrect_tock signature
          completing := compilationCompletingCorrect_tock signature
          scopedStep := compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
            signature .tock
              (compilationFragmentStepCorrect_tock_leaf signature) }
  | skip =>
      intro _ _ _ _ _ _ _
      exact
        { future := compilationFutureCorrect_skip signature
          completing := compilationCompletingCorrect_skip signature
          scopedStep := compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
            signature .skip
              (compilationFragmentStepCorrect_skip_leaf signature) }
  | var name =>
      intro _ _ hClosed _ _ _ _
      simp [PactType.AllVariablesBound] at hClosed
  | recur name body =>
      intro hSignature hSupports hClosed hGuarded hTail hLinear hScoped
      exact compilationProofBundle_recursion_leaf signature name body
        hSignature hSupports hClosed hGuarded hTail hLinear hScoped
  | choice left right =>
      intro hSignature hSupports hClosed hGuarded hTail hLinear hScoped
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.AllVariablesBound] at hClosed
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.SameCycleMessageLinear] at hLinear
      simp only [PactType.InterfaceScoped] at hScoped
      have hLeft := compilationProofBundle_of_closedGuardedRegular signature
        left hSignature hSupports.1 hClosed.1 hGuarded.1 hTail.1 hLinear.1
          hScoped.1
      have hRight := compilationProofBundle_of_closedGuardedRegular signature
        right hSignature hSupports.2 hClosed.2 hGuarded.2 hTail.2 hLinear.2
          hScoped.2
      exact
        { future := compilationFutureCorrect_choice signature left right
            hLeft.future hRight.future
          completing := compilationCompletingCorrect_choice signature left right
            hLeft.completing hRight.completing
          scopedStep := compilationFragmentStepCorrect_choice_leaf signature
            left right hLeft hRight }
  | fairChoice bid left right =>
      intro hSignature hSupports hClosed hGuarded hTail hLinear hScoped
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.AllVariablesBound] at hClosed
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.SameCycleMessageLinear] at hLinear
      simp only [PactType.InterfaceScoped] at hScoped
      have hLeft := compilationProofBundle_of_closedGuardedRegular signature
        left hSignature hSupports.2.1 hClosed.1 hGuarded.1 hTail.1 hLinear.1
          hScoped.1
      have hRight := compilationProofBundle_of_closedGuardedRegular signature
        right hSignature hSupports.2.2 hClosed.2 hGuarded.2 hTail.2 hLinear.2
          hScoped.2
      exact
        { future := compilationFutureCorrect_fairChoice signature bid left right
            hLeft.future hRight.future
          completing := compilationCompletingCorrect_fairChoice signature bid
            left right hLeft.completing hRight.completing
          scopedStep := compilationFragmentStepCorrect_fairChoice_leaf
            signature bid left right hLeft hRight }
  | seq left right =>
      intro hSignature hSupports hClosed hGuarded hTail hLinear hScoped
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.AllVariablesBound] at hClosed
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.SameCycleMessageLinear] at hLinear
      simp only [PactType.InterfaceScoped] at hScoped
      have hLeft := compilationProofBundle_of_closedGuardedRegular signature
        left hSignature hSupports.1 hClosed.1 hGuarded.1 hTail.1 hLinear.1
          hScoped.1
      have hRight := compilationProofBundle_of_closedGuardedRegular signature
        right hSignature hSupports.2 hClosed.2 hGuarded.2 hTail.2 hLinear.2.1
          hScoped.2
      have hFuture := compilationFutureCorrect_sequence signature left right
        hLeft hRight
      exact
        { future := hFuture
          completing := compilationCompletingCorrect_sequence signature left
            right hLeft.completing hRight.completing
          scopedStep := compilationScopedFragmentStepCorrect_sequence_leaf
            signature left right hLeft hRight hFuture }
  | par left right interface =>
      intro hSignature hSupports hClosed hGuarded hTail hLinear hScoped
      have hScopedWhole : PactType.InterfaceScoped (.par left right interface) :=
        hScoped
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.AllVariablesBound] at hClosed
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.SameCycleMessageLinear] at hLinear
      simp only [PactType.InterfaceScoped] at hScoped
      have hLeft := compilationProofBundle_of_closedGuardedRegular signature
        left hSignature hSupports.2.1 hClosed.1 hGuarded.1 hTail.1 hLinear.1
          hScoped.2.1
      have hRight := compilationProofBundle_of_closedGuardedRegular signature
        right hSignature hSupports.2.2 hClosed.2 hGuarded.2 hTail.2 hLinear.2
          hScoped.2.2
      exact
        { future := compilationFutureCorrect_parallel signature left right
            interface hLeft.future hRight.future
          completing := compilationCompletingCorrect_parallel signature left
            right interface hLeft.completing hRight.completing
          scopedStep := compilationFragmentStepCorrect_parallel_leaf
            signature left right interface hSignature hSupports.1 hScopedWhole
              hLeft hRight }
  | xoffer elseType branches =>
      intro hSignature hSupports hClosed hGuarded hTail hLinear hScoped
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.AllVariablesBound] at hClosed
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.SameCycleMessageLinear] at hLinear
      simp only [PactType.InterfaceScoped] at hScoped
      have hElse := compilationProofBundle_of_closedGuardedRegular signature
        elseType hSignature hSupports.1 hClosed.1 hGuarded.1 hTail.1
          hLinear.1 hScoped.1
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
        exact compilationProofBundle_of_closedGuardedRegular signature
          branchType hSignature
          (supports_branch_of_mem signature branches (action, branchType)
            hSupports.2 hMember)
          (allVariablesBound_branch_of_mem [] branches (action, branchType)
            hClosed.2 hMember)
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
        (by simpa [PactType.AllVariablesBound] using hClosed)
        (by simpa [PactType.ClockGuarded] using hGuarded)
        (by simpa [PactType.TailRecursive] using hTail)
        (by simpa [PactType.SameCycleMessageLinear] using hLinear)
        (by simpa [PactType.InterfaceScoped] using hScoped) hElse hBranches
  | offer elseType branches =>
      intro hSignature hSupports hClosed hGuarded hTail hLinear hScoped
      simp only [TypeAlphabet.Supports] at hSupports
      simp only [PactType.AllVariablesBound] at hClosed
      simp only [PactType.ClockGuarded] at hGuarded
      simp only [PactType.TailRecursive] at hTail
      simp only [PactType.SameCycleMessageLinear] at hLinear
      simp only [PactType.InterfaceScoped] at hScoped
      have hElse := compilationProofBundle_of_closedGuardedRegular signature
        elseType hSignature hSupports.1 hClosed.1 hGuarded.1 hTail.1
          hLinear.1 hScoped.1
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
        exact compilationProofBundle_of_closedGuardedRegular signature
          branchType hSignature
          (supports_branch_of_mem signature branches (action, branchType)
            hSupports.2 hMember)
          (allVariablesBound_branch_of_mem [] branches (action, branchType)
            hClosed.2 hMember)
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
        (by simpa [PactType.AllVariablesBound] using hClosed)
        (by simpa [PactType.ClockGuarded] using hGuarded)
        (by simpa [PactType.TailRecursive] using hTail)
        (by simpa [PactType.SameCycleMessageLinear] using hLinear)
        (by simpa [PactType.InterfaceScoped] using hScoped) hElse hBranches
termination_by processType => sizeOf processType
decreasing_by
  all_goals
    first
    | assumption
    | (simp_wf; omega)

/-- Public one-step bisimulation follows immediately from the hierarchical
bundle and the uniform fragment-to-public exporter. -/
theorem compilationStepCorrect_of_closedGuardedRegular
    (signature : TypeAlphabet) (processType : PactType)
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports processType)
    (hClosed : PactType.AllVariablesBound [] processType)
    (hGuarded : PactType.ClockGuarded processType)
    (hTail : PactType.TailRecursive processType)
    (hLinear : PactType.SameCycleMessageLinear processType)
    (hScoped : PactType.InterfaceScoped processType) :
    CompilationStepCorrect signature processType := by
  have hBundle := compilationProofBundle_of_closedGuardedRegular signature
    processType hSignature hSupports hClosed hGuarded hTail hLinear hScoped
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
