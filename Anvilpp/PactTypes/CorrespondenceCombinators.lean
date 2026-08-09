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

private def sequenceExecutionEdge
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  { source := edge.source
    environment := edge.environment
    label := edge.label
    current := edge.current
    future := match edge.label with
      | .future => edge.future
      | _ => .at edge.target edge.current
    target := edge.target }

@[simp] private theorem sequenceExecutionEdge_source
    (edge : PendingAutomatonEdge) :
    (sequenceExecutionEdge edge).source = edge.source := rfl

@[simp] private theorem sequenceExecutionEdge_environment
    (edge : PendingAutomatonEdge) :
    (sequenceExecutionEdge edge).environment = edge.environment := rfl

@[simp] private theorem sequenceExecutionEdge_label
    (edge : PendingAutomatonEdge) :
    (sequenceExecutionEdge edge).label = edge.label := rfl

@[simp] private theorem sequenceExecutionEdge_current
    (edge : PendingAutomatonEdge) :
    (sequenceExecutionEdge edge).current = edge.current := rfl

@[simp] private theorem sequenceExecutionEdge_target
    (edge : PendingAutomatonEdge) :
    (sequenceExecutionEdge edge).target = edge.target := rfl

@[simp] private theorem sequenceExecutionEdge_future
    (edge : PendingAutomatonEdge) :
    (sequenceExecutionEdge edge).future =
      match edge.label with
      | .future => edge.future
      | _ => .at edge.target edge.current := rfl

/-- The child graph followed by a sequence left component.  Ordinary
constructor edges are re-decorated by their transition target, exactly as in
`buildSequenceAutomaton`; construction-only `.future` edges retain their
original symbolic decoration. -/
private def sequenceExecutionAutomaton
    (child : AutomatonFragment) : PendingAutomaton :=
  { states := child.states ∪ child.edges.image PendingAutomatonEdge.target
    edges := child.edges.image sequenceExecutionEdge }

/-- Repackage the execution view as a constructor fragment while retaining
the syntax metadata of the represented child.  This is used only to compose
an outer sequence closure; it does not alter the public compiler. -/
private def sequenceExecutionFragment
    (child : AutomatonFragment) : AutomatonFragment :=
  { states := (sequenceExecutionAutomaton child).states
    initial := child.initial
    accepting := child.accepting
    skipping := child.skipping
    completing := child.completing
    edges := (sequenceExecutionAutomaton child).edges }

@[simp] private theorem sequenceExecutionEdge_idempotent
    (edge : PendingAutomatonEdge) :
    sequenceExecutionEdge (sequenceExecutionEdge edge) =
      sequenceExecutionEdge edge := by
  cases hLabel : edge.label <;> cases hFuture : edge.future <;>
    simp [sequenceExecutionEdge, hLabel, hFuture]

private theorem sequenceExecutionEdge_childPendingEdge
    (index : Nat) (edge : PendingAutomatonEdge) :
    sequenceExecutionEdge (childPendingEdge index edge) =
      childPendingEdge index (sequenceExecutionEdge edge) := by
  cases hLabel : edge.label <;> cases hFuture : edge.future <;>
    simp [sequenceExecutionEdge, childPendingEdge, childFutureSpec,
      childState, hLabel, hFuture]

private theorem sequenceExecutionFragment_futureTargetsInStates
    (child : AutomatonFragment)
    (hTargets : child.FutureTargetsInStates) :
    (sequenceExecutionFragment child).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [sequenceExecutionFragment, sequenceExecutionAutomaton,
    Finset.mem_image] at hEdge
  rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
  cases hLabel : childEdge.label with
  | future =>
      cases hSpec : childEdge.future with
      | explicit offers =>
          simp [sequenceExecutionEdge, hLabel, hSpec] at hFuture
      | «at» referenced childRemoved =>
          have hTarget : target = referenced := by
            have hFields : referenced = target ∧ childRemoved = removed := by
              simpa [sequenceExecutionEdge, hLabel, hSpec] using hFuture
            exact hFields.1.symm
          subst target
          have hReferenced := hTargets childEdge hChildEdge referenced
            childRemoved hSpec
          exact Finset.mem_union_left _ hReferenced
  | visible label =>
      have hTarget : target = childEdge.target := by
        have hFields : childEdge.target = target ∧
            childEdge.current = removed := by
          simpa [sequenceExecutionEdge, hLabel] using hFuture
        exact hFields.1.symm
      subst target
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩)
  | «variable» name =>
      have hTarget : target = childEdge.target := by
        have hFields : childEdge.target = target ∧
            childEdge.current = removed := by
          simpa [sequenceExecutionEdge, hLabel] using hFuture
        exact hFields.1.symm
      subst target
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩)

private theorem sequenceExecution_buildSequence_edges
    (signature : TypeAlphabet) (left right : AutomatonFragment) :
    (sequenceExecutionAutomaton
        (buildSequenceAutomaton signature left right)).edges =
      (buildSequenceAutomaton signature left
        (sequenceExecutionFragment right)).edges := by
  classical
  ext edge
  simp [sequenceExecutionAutomaton, sequenceExecutionFragment,
    buildSequenceAutomaton, finishAutomatonFragment, childPendingEdges,
    childPendingEdge, childFutureSpec, childStates, childState,
    sequenceExecutionEdge, Finset.image_union, Function.comp_def]
  grind

private theorem sequenceExecution_buildChoice_outgoing_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton left
    edge ∈ parent.edges ∧ edge.source = .child 0 state ↔
      ∃ childEdge ∈ child.edges,
        childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hEdge
    rcases hEdge with ⟨raw, hRaw, rfl⟩
    have hRawSource : raw.source = .child 0 state := by
      simpa [sequenceExecutionEdge] using hSource
    rcases (buildChoiceAutomaton_outgoing_left signature left right
      selectionLeft selectionRight state raw).mp ⟨hRaw, hRawSource⟩ with
      ⟨childRaw, hChildRaw, hChildSource, rfl⟩
    refine ⟨sequenceExecutionEdge childRaw, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨childRaw, hChildRaw, rfl⟩
    · simpa [sequenceExecutionEdge] using hChildSource
    · exact sequenceExecutionEdge_childPendingEdge 0 childRaw
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hChildEdge
    rcases hChildEdge with ⟨childRaw, hChildRaw, rfl⟩
    rw [← sequenceExecutionEdge_childPendingEdge]
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨childPendingEdge 0 childRaw, ?_, rfl⟩
      exact (buildChoiceAutomaton_outgoing_left signature left right
        selectionLeft selectionRight childRaw.source
          (childPendingEdge 0 childRaw)).mpr
            ⟨childRaw, hChildRaw, rfl, rfl⟩ |>.1
    · simpa [sequenceExecutionEdge, childPendingEdge, childState] using
        hChildSource

private theorem sequenceExecution_buildChoice_outgoing_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton right
    edge ∈ parent.edges ∧ edge.source = .child 1 state ↔
      ∃ childEdge ∈ child.edges,
        childEdge.source = state ∧ edge = childPendingEdge 1 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hEdge
    rcases hEdge with ⟨raw, hRaw, rfl⟩
    have hRawSource : raw.source = .child 1 state := by
      simpa [sequenceExecutionEdge] using hSource
    rcases (buildChoiceAutomaton_outgoing_right signature left right
      selectionLeft selectionRight state raw).mp ⟨hRaw, hRawSource⟩ with
      ⟨childRaw, hChildRaw, hChildSource, rfl⟩
    refine ⟨sequenceExecutionEdge childRaw, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨childRaw, hChildRaw, rfl⟩
    · simpa [sequenceExecutionEdge] using hChildSource
    · exact sequenceExecutionEdge_childPendingEdge 1 childRaw
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hChildEdge
    rcases hChildEdge with ⟨childRaw, hChildRaw, rfl⟩
    rw [← sequenceExecutionEdge_childPendingEdge]
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨childPendingEdge 1 childRaw, ?_, rfl⟩
      exact (buildChoiceAutomaton_outgoing_right signature left right
        selectionLeft selectionRight childRaw.source
          (childPendingEdge 1 childRaw)).mpr
            ⟨childRaw, hChildRaw, rfl, rfl⟩ |>.1
    · simpa [sequenceExecutionEdge, childPendingEdge, childState] using
        hChildSource

private theorem sequenceExecution_buildChoice_referencedStates_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton left
    parent.referencedStates (.child 0 state) =
      (child.referencedStates state).image (.child 0) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [sequenceExecution_buildChoice_outgoing_left signature left right
    selectionLeft selectionRight state]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem sequenceExecution_buildChoice_referencedStates_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton right
    parent.referencedStates (.child 1 state) =
      (child.referencedStates state).image (.child 1) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [sequenceExecution_buildChoice_outgoing_right signature left right
    selectionLeft selectionRight state]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem sequenceExecution_buildChoice_offersAt_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton left
    parent.offersAt (.child 0 state) = child.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [sequenceExecution_buildChoice_outgoing_left signature left right
    selectionLeft selectionRight state]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem sequenceExecution_buildChoice_offersAt_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton right
    parent.offersAt (.child 1 state) = child.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [sequenceExecution_buildChoice_outgoing_right signature left right
    selectionLeft selectionRight state]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem sequenceExecutionAutomaton_referencesClosed
    (child : AutomatonFragment)
    (hTargets : child.FutureTargetsInStates) :
    (sequenceExecutionAutomaton child).ReferencesClosed := by
  classical
  intro source hSource target hTarget
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter] at hTarget
  rcases hTarget with ⟨edge, ⟨hEdge, _⟩, hFuture⟩
  simp only [sequenceExecutionAutomaton, Finset.mem_image] at hEdge
  rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
  cases hLabel : childEdge.label with
  | future =>
      cases hSpec : childEdge.future with
      | explicit offers => simp [hLabel, hSpec,
          AutomatonConstructionLabel.semantic] at hFuture
      | «at» referenced removed =>
          simp [hLabel, hSpec, AutomatonConstructionLabel.semantic,
            TypeLabel.silent] at hFuture
          have hTarget : target = referenced := by
            simpa using hFuture
          subst target
          have hReferenced := hTargets childEdge hChildEdge referenced removed
            hSpec
          simp [sequenceExecutionAutomaton, hReferenced]
  | visible label =>
      by_cases hTock : label = TypeLabel.tock
      · subst label
        simp [hLabel, AutomatonConstructionLabel.semantic] at hFuture
      · have hTarget : target = childEdge.target := by
          simpa [hLabel, AutomatonConstructionLabel.semantic, hTock]
            using hFuture
        subst target
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩)
  | «variable» name =>
      have hTarget : target = childEdge.target := by
        simpa [hLabel, AutomatonConstructionLabel.semantic, TypeLabel.silent]
          using hFuture
      subst target
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩)

/-- At a product state, the execution view already sees the whole optimistic
menu directly through the two construction-only observation edges.  Ordinary
product transitions add only offers that are contained in those observations. -/
private theorem sequenceExecution_buildParallel_offersAt
    (interface : Interface) (left right : AutomatonFragment)
    (leftState rightState : TypeAutomatonState)
    (hLeftState : leftState ∈ left.states)
    (hRightState : rightState ∈ right.states)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates) :
    (sequenceExecutionAutomaton
        (buildParallelAutomaton interface left right)).offersAt
        (.pair leftState rightState) =
      hideOffers interface
        (computeFuture { states := left.states, edges := left.edges } leftState ∪
          computeFuture { states := right.states, edges := right.edges }
            rightState) := by
  classical
  let leftPending : PendingAutomaton :=
    { states := left.states, edges := left.edges }
  let rightPending : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  have hLeftClosed : leftPending.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates left hLeftTargets
  have hRightClosed : rightPending.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates right
      hRightTargets
  apply Finset.Subset.antisymm
  · intro action hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hAction
    rcases hAction with ⟨executionEdge, ⟨hExecutionEdge, hSource⟩, hOffer⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hExecutionEdge
    rcases hExecutionEdge with ⟨edge, hEdge, rfl⟩
    simp only [buildParallelAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter] at hEdge
    rcases hEdge with hTransition | hObservation
    · rcases hTransition with
        ⟨leftEdge, ⟨hLeftEdge, _⟩, rightEdge,
          ⟨⟨hRightEdge, _⟩, hSync⟩, rfl⟩
      injection hSource with hLeftSource hRightSource
      subst leftState
      subst rightState
      by_cases hClock :
          (AutomatonConstructionLabel.combine interface leftEdge.label
            rightEdge.label).semantic = TypeLabel.tock
      · simp [sequenceExecutionEdge, hClock] at hOffer
      · have hCombinedNotFuture :
            AutomatonConstructionLabel.combine interface leftEdge.label
                rightEdge.label ≠ .future := by
          cases hLeftLabel : leftEdge.label <;>
            cases hRightLabel : rightEdge.label <;>
              simp_all [AutomatonConstructionLabel.combine]
        have hOfferCurrent : action ∈
            hideOffers interface (leftEdge.current ∪ rightEdge.current) := by
          simpa [sequenceExecutionEdge, hClock, hCombinedNotFuture] using hOffer
        rcases hSync with
          ⟨leftWitness, _, rightWitness, _, hWitnesses⟩
        have hLabelSync : TypeLabel.Sync interface leftEdge.label.semantic
            rightEdge.label.semantic := hWitnesses.2.2.2
        have hNonClock :=
          AutomatonConstructionLabel.component_nonclock_of_sync interface
            leftEdge.label rightEdge.label hLabelSync hClock
        have hLeftSubset :=
          resolvedAutomatonEdge_offers_subset_computeFuture left leftEdge
            hLeftEdge hLeftClosed hLeftState hNonClock.1
        have hRightSubset :=
          resolvedAutomatonEdge_offers_subset_computeFuture right rightEdge
            hRightEdge hRightClosed hRightState hNonClock.2
        simp only [hideOffers, Finset.mem_filter, Finset.mem_union]
          at hOfferCurrent ⊢
        rcases hOfferCurrent with ⟨hCurrent, hOutside⟩
        rcases hCurrent with hLeft | hRight
        · exact ⟨Or.inl (hLeftSubset (Finset.mem_union_left _ hLeft)),
            hOutside⟩
        · exact ⟨Or.inr (hRightSubset (Finset.mem_union_left _ hRight)),
            hOutside⟩
    · rcases hObservation with hLeft | hRight
      · rcases hLeft with ⟨leftSource, hLeftSource, rightSource,
          hRightSource, rfl⟩
        injection hSource with hLeftEq hRightEq
        subst leftSource
        subst rightSource
        simp [sequenceExecutionEdge, AutomatonConstructionLabel.semantic,
          TypeLabel.silent, hideOffers] at hOffer
        simpa [hideOffers, leftPending, rightPending] using
          (show (action ∈ computeFuture leftPending leftState ∨
              action ∈ computeFuture rightPending rightState) ∧
                action.1 ∉ interface from ⟨Or.inl hOffer.1, hOffer.2⟩)
      · rcases hRight with ⟨leftSource, hLeftSource, rightSource,
          hRightSource, rfl⟩
        injection hSource with hLeftEq hRightEq
        subst leftSource
        subst rightSource
        simp [sequenceExecutionEdge, AutomatonConstructionLabel.semantic,
          TypeLabel.silent, hideOffers] at hOffer
        simpa [hideOffers, leftPending, rightPending] using
          (show (action ∈ computeFuture leftPending leftState ∨
              action ∈ computeFuture rightPending rightState) ∧
                action.1 ∉ interface from ⟨Or.inr hOffer.1, hOffer.2⟩)
  · intro action hAction
    simp only [hideOffers, Finset.mem_filter, Finset.mem_union] at hAction
    rcases hAction with ⟨hLeft | hRight, hOutside⟩
    · simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
        Finset.mem_filter]
      let observation : PendingAutomatonEdge :=
        { source := .pair leftState rightState
          environment := .empty
          label := .future
          current := hideOffers interface
            (computeFuture leftPending leftState)
          future := .explicit ∅
          target := .pair leftState rightState }
      refine ⟨sequenceExecutionEdge observation, ⟨?_, rfl⟩, ?_⟩
      · simp only [sequenceExecutionAutomaton, Finset.mem_image]
        refine ⟨observation, ?_, rfl⟩
        simp only [buildParallelAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
          Finset.mem_filter]
        exact Or.inr (Or.inl
          ⟨leftState, hLeftState, rightState, hRightState, by
            simp [observation, leftPending]⟩)
      · simp [sequenceExecutionEdge, observation,
          AutomatonConstructionLabel.semantic, TypeLabel.silent, hideOffers,
          leftPending, hLeft, hOutside]
    · simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
        Finset.mem_filter]
      let observation : PendingAutomatonEdge :=
        { source := .pair leftState rightState
          environment := .empty
          label := .future
          current := hideOffers interface
            (computeFuture rightPending rightState)
          future := .explicit ∅
          target := .pair leftState rightState }
      refine ⟨sequenceExecutionEdge observation, ⟨?_, rfl⟩, ?_⟩
      · simp only [sequenceExecutionAutomaton, Finset.mem_image]
        refine ⟨observation, ?_, rfl⟩
        simp only [buildParallelAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
          Finset.mem_filter]
        exact Or.inr (Or.inr
          ⟨leftState, hLeftState, rightState, hRightState, by
            simp [observation, rightPending]⟩)
      · simp [sequenceExecutionEdge, observation,
          AutomatonConstructionLabel.semantic, TypeLabel.silent, hideOffers,
          rightPending, hRight, hOutside]

/-- Every symbolic reference introduced by the execution view of a product is
the pair of targets of two non-clock resolved component edges.  The optimistic
`.future` observations remain explicit and therefore introduce no reference. -/
private theorem sequenceExecution_buildParallel_reference_cases
    (interface : Interface) (left right : AutomatonFragment)
    (leftSource rightSource target : TypeAutomatonState)
    (hReference : target ∈
      (sequenceExecutionAutomaton
        (buildParallelAutomaton interface left right)).referencedStates
          (.pair leftSource rightSource)) :
    ∃ leftEdge ∈ resolvedAutomatonEdges left,
      ∃ rightEdge ∈ resolvedAutomatonEdges right,
        leftEdge.source = leftSource ∧
        rightEdge.source = rightSource ∧
        target = .pair leftEdge.target rightEdge.target ∧
        leftEdge.label ≠ .future ∧
        rightEdge.label ≠ .future ∧
        leftEdge.label.semantic ≠ TypeLabel.tock ∧
        rightEdge.label.semantic ≠ TypeLabel.tock := by
  classical
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter] at hReference
  rcases hReference with
    ⟨executionEdge, ⟨hExecutionEdge, hSource⟩, hFuture⟩
  simp only [sequenceExecutionAutomaton, Finset.mem_image] at hExecutionEdge
  rcases hExecutionEdge with ⟨edge, hEdge, rfl⟩
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter] at hEdge
  rcases hEdge with hTransition | hObservation
  · rcases hTransition with
      ⟨leftEdge, ⟨hLeftEdge, hLeftSemantic⟩, rightEdge,
        ⟨⟨hRightEdge, hRightSemantic⟩, hSync⟩, rfl⟩
    injection hSource with hLeftSource hRightSource
    have hCombinedNotFuture :
        AutomatonConstructionLabel.combine interface leftEdge.label
            rightEdge.label ≠ .future := by
      cases hLeftLabel : leftEdge.label <;>
        cases hRightLabel : rightEdge.label <;>
          simp_all [AutomatonConstructionLabel.combine]
    have hCombinedNonClock :
        (AutomatonConstructionLabel.combine interface leftEdge.label
          rightEdge.label).semantic ≠ TypeLabel.tock := by
      intro hClock
      simp [sequenceExecutionEdge, hCombinedNotFuture, hClock] at hFuture
    have hTarget : target = .pair leftEdge.target rightEdge.target := by
      simpa [sequenceExecutionEdge, hCombinedNotFuture, hCombinedNonClock]
        using hFuture
    rcases hSync with
      ⟨leftWitness, _, rightWitness, _, hWitnesses⟩
    have hLabelSync : TypeLabel.Sync interface leftEdge.label.semantic
        rightEdge.label.semantic := hWitnesses.2.2.2
    have hNonClock :=
      AutomatonConstructionLabel.component_nonclock_of_sync interface
        leftEdge.label rightEdge.label hLabelSync hCombinedNonClock
    exact ⟨leftEdge, hLeftEdge, rightEdge, hRightEdge, hLeftSource,
      hRightSource, hTarget, hLeftSemantic, hRightSemantic, hNonClock⟩
  · rcases hObservation with hLeft | hRight
    · rcases hLeft with ⟨leftState, _, rightState, _, rfl⟩
      simp [sequenceExecutionEdge, AutomatonConstructionLabel.semantic,
        TypeLabel.silent] at hFuture
    · rcases hRight with ⟨leftState, _, rightState, _, rfl⟩
      simp [sequenceExecutionEdge, AutomatonConstructionLabel.semantic,
        TypeLabel.silent] at hFuture

/-- A non-clock resolved edge is followed by the execution view, independently
of how its original symbolic future was resolved. -/
private theorem sequenceExecution_resolvedEdge_target_referenced
    (fragment : AutomatonFragment) (edge : AutomatonFragmentEdge)
    (hEdge : edge ∈ resolvedAutomatonEdges fragment)
    (hVisible : edge.label ≠ .future)
    (hNonClock : edge.label.semantic ≠ TypeLabel.tock) :
    edge.target ∈ (sequenceExecutionAutomaton fragment).referencedStates
      edge.source := by
  classical
  simp only [resolvedAutomatonEdges, Finset.mem_image] at hEdge
  rcases hEdge with ⟨raw, hRaw, rfl⟩
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter]
  refine ⟨sequenceExecutionEdge raw, ⟨?_, rfl⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨raw, hRaw, rfl⟩
  · cases hLabel : raw.label <;>
      simp_all [sequenceExecutionEdge, AutomatonConstructionLabel.semantic]

private theorem resolvedAutomatonEdge_visible_of_pending_visible
    (fragment : AutomatonFragment)
    (hVisible : ∀ raw ∈ fragment.edges, raw.label ≠ .future →
      ∃ label, raw.label = .visible label)
    (edge : AutomatonFragmentEdge)
    (hEdge : edge ∈ resolvedAutomatonEdges fragment)
    (hSemantic : edge.label ≠ .future) :
    ∃ label, edge.label = .visible label := by
  simp only [resolvedAutomatonEdges, Finset.mem_image] at hEdge
  rcases hEdge with ⟨raw, hRaw, rfl⟩
  exact hVisible raw hRaw hSemantic

private theorem hasResolvedEdge_of_mem_visible_resolved
    (fragment : AutomatonFragment) (edge : AutomatonFragmentEdge)
    (hEdge : edge ∈ resolvedAutomatonEdges fragment)
    (label : TypeLabel) (hLabel : edge.label = .visible label) :
    fragment.HasResolvedEdge edge.source edge.environment label
      { current := edge.current, future := edge.future } edge.target := by
  classical
  simp only [resolvedAutomatonEdges, Finset.mem_image] at hEdge
  rcases hEdge with ⟨raw, hRaw, hResolved⟩
  subst edge
  refine ⟨raw, hRaw, rfl, rfl, ?_, rfl, ?_, rfl⟩
  · simpa using hLabel
  · cases hFuture : raw.future <;> simp [hFuture]

/- A constructor-independent execution-view embedding for a tagged child.
Offer constructors have an unbounded number of children, so keeping this
lemma generic avoids reproducing the binary-choice closure proof for every
indexed branch. -/
private theorem sequenceExecution_taggedChild_outgoing
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let parentExecution := sequenceExecutionAutomaton parent
    let childExecution := sequenceExecutionAutomaton child
    edge ∈ parentExecution.edges ∧
        edge.source = childState index state ↔
      ∃ childEdge ∈ childExecution.edges,
        childEdge.source = state ∧
          edge = childPendingEdge index childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hEdge
    rcases hEdge with ⟨raw, hRaw, rfl⟩
    have hRawSource : raw.source = childState index state := by
      simpa [sequenceExecutionEdge] using hSource
    rcases (hOutgoing state raw).mp ⟨hRaw, hRawSource⟩ with
      ⟨childRaw, hChildRaw, hChildSource, rfl⟩
    refine ⟨sequenceExecutionEdge childRaw, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨childRaw, hChildRaw, rfl⟩
    · simpa [sequenceExecutionEdge] using hChildSource
    · exact sequenceExecutionEdge_childPendingEdge index childRaw
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hChildEdge
    rcases hChildEdge with ⟨childRaw, hChildRaw, rfl⟩
    rw [← sequenceExecutionEdge_childPendingEdge]
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨childPendingEdge index childRaw, ?_, rfl⟩
      exact (hOutgoing childRaw.source (childPendingEdge index childRaw)).mpr
        ⟨childRaw, hChildRaw, rfl, rfl⟩ |>.1
    · simpa [sequenceExecutionEdge, childPendingEdge, childState] using
        hChildSource

private theorem sequenceExecution_taggedChild_referencedStates
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (state : TypeAutomatonState) :
    let parentExecution := sequenceExecutionAutomaton parent
    let childExecution := sequenceExecutionAutomaton child
    parentExecution.referencedStates (childState index state) =
      (childExecution.referencedStates state).image (childState index) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [sequenceExecution_taggedChild_outgoing parent child index
    hOutgoing state]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem sequenceExecution_taggedChild_offersAt
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (state : TypeAutomatonState) :
    let parentExecution := sequenceExecutionAutomaton parent
    let childExecution := sequenceExecutionAutomaton child
    parentExecution.offersAt (childState index state) =
      childExecution.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [sequenceExecution_taggedChild_outgoing parent child index
    hOutgoing state]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem sequenceExecution_taggedChild_states_subset
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (hStates : child.states.image (childState index) ⊆ parent.states) :
    let parentExecution := sequenceExecutionAutomaton parent
    let childExecution := sequenceExecutionAutomaton child
    childExecution.states.image (childState index) ⊆
      parentExecution.states := by
  classical
  dsimp only
  intro tagged hTagged
  rcases Finset.mem_image.mp hTagged with ⟨state, hState, rfl⟩
  simp only [sequenceExecutionAutomaton, Finset.mem_union,
    Finset.mem_image] at hState ⊢
  rcases hState with hState | ⟨edge, hEdge, rfl⟩
  · exact Or.inl (hStates (Finset.mem_image.mpr ⟨_, hState, rfl⟩))
  · right
    refine ⟨childPendingEdge index edge, ?_, ?_⟩
    · exact (hOutgoing edge.source (childPendingEdge index edge)).mpr
        ⟨edge, hEdge, rfl, rfl⟩ |>.1
    · simp [childPendingEdge, childState]

private theorem sequenceExecution_taggedChild_futureReachable
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (hStates : child.states.image (childState index) ⊆ parent.states)
    (hTargets : child.FutureTargetsInStates)
    (state : TypeAutomatonState) (hState : state ∈ child.states) :
    let parentExecution := sequenceExecutionAutomaton parent
    let childExecution := sequenceExecutionAutomaton child
    parentExecution.futureReachable (childState index state) =
      (childExecution.futureReachable state).image (childState index) := by
  let parentExecution := sequenceExecutionAutomaton parent
  let childExecution := sequenceExecutionAutomaton child
  have hClosed : childExecution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed child hTargets
  have hChildState : state ∈ childExecution.states :=
    Finset.mem_union_left _ hState
  have hSubset := sequenceExecution_taggedChild_states_subset parent child
    index hOutgoing hStates
  have hCard : childExecution.states.card ≤ parentExecution.states.card := by
    calc
      childExecution.states.card =
          (childExecution.states.image (childState index)).card := by
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ parentExecution.states.card := Finset.card_le_card hSubset
  exact PendingAutomaton.futureReachable_eq_of_embedding childExecution
    parentExecution (childState index)
      (sequenceExecution_taggedChild_referencedStates parent child index
        hOutgoing) hClosed state hChildState hCard

private theorem sequenceExecution_taggedChild_computeFuture
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (hStates : child.states.image (childState index) ⊆ parent.states)
    (hTargets : child.FutureTargetsInStates)
    (state : TypeAutomatonState) (hState : state ∈ child.states) :
    let parentExecution := sequenceExecutionAutomaton parent
    let childExecution := sequenceExecutionAutomaton child
    computeFuture parentExecution (childState index state) =
      computeFuture childExecution state := by
  let parentExecution := sequenceExecutionAutomaton parent
  let childExecution := sequenceExecutionAutomaton child
  have hClosed : childExecution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed child hTargets
  have hChildState : state ∈ childExecution.states :=
    Finset.mem_union_left _ hState
  have hSubset := sequenceExecution_taggedChild_states_subset parent child
    index hOutgoing hStates
  have hCard : childExecution.states.card ≤ parentExecution.states.card := by
    calc
      childExecution.states.card =
          (childExecution.states.image (childState index)).card := by
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ parentExecution.states.card := Finset.card_le_card hSubset
  exact computeFuture_eq_of_embedding childExecution parentExecution
    (childState index)
      (sequenceExecution_taggedChild_referencedStates parent child index
        hOutgoing)
      (sequenceExecution_taggedChild_offersAt parent child index hOutgoing)
      hClosed state hChildState hCard

private theorem taggedCompletionWitness_iff
    (parent child : AutomatonFragment) (index : Nat)
    (reached : Finset TypeAutomatonState)
    (hSkipping : ∀ state,
      childState index state ∈ parent.skipping ↔ state ∈ child.skipping)
    (hCompleting : ∀ state,
      childState index state ∈ parent.completing ↔
        state ∈ child.completing) :
    (∃ completed ∈ reached.image (childState index),
        completed ∈ parent.skipping ∨ completed ∈ parent.completing) ↔
      ∃ completed ∈ reached,
        completed ∈ child.skipping ∨ completed ∈ child.completing := by
  constructor
  · rintro ⟨tagged, hTagged, hCompleted⟩
    rcases Finset.mem_image.mp hTagged with ⟨completed, hReached, rfl⟩
    exact ⟨completed, hReached,
      hCompleted.imp (hSkipping completed).mp (hCompleting completed).mp⟩
  · rintro ⟨completed, hReached, hCompleted⟩
    exact ⟨childState index completed,
      Finset.mem_image.mpr ⟨completed, hReached, rfl⟩,
      hCompleted.imp (hSkipping completed).mpr (hCompleting completed).mpr⟩

private theorem sequenceExecution_root_offersAt_eq
    (fragment : AutomatonFragment)
    (hShape : ∀ edge ∈ fragment.edges, edge.source = .root →
      edge.label ≠ .future ∧
        ∃ removed, edge.future = .at edge.target removed) :
    (sequenceExecutionAutomaton fragment).offersAt .root =
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).offersAt .root := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hEdge
    rcases hEdge with ⟨raw, hRaw, rfl⟩
    have hRawSource : raw.source = .root := by
      simpa using hSource
    rcases hShape raw hRaw hRawSource with ⟨hNotFuture, removed, hFuture⟩
    refine ⟨raw, ⟨hRaw, hRawSource⟩, ?_⟩
    cases hLabel : raw.label with
    | future => exact (hNotFuture hLabel).elim
    | visible label => simpa [sequenceExecutionEdge, hLabel, hFuture] using hOffer
    | «variable» name =>
        simpa [sequenceExecutionEdge, hLabel, hFuture] using hOffer
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
    rcases hShape edge hEdge hSource with ⟨hNotFuture, removed, hFuture⟩
    refine ⟨sequenceExecutionEdge edge, ⟨?_, by simpa⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩
    · cases hLabel : edge.label with
      | future => exact (hNotFuture hLabel).elim
      | visible label =>
          simpa [sequenceExecutionEdge, hLabel, hFuture] using hOffer
      | «variable» name =>
          simpa [sequenceExecutionEdge, hLabel, hFuture] using hOffer

private theorem sequenceExecution_root_referencedStates_eq
    (fragment : AutomatonFragment)
    (hShape : ∀ edge ∈ fragment.edges, edge.source = .root →
      edge.label ≠ .future ∧
        ∃ removed, edge.future = .at edge.target removed) :
    (sequenceExecutionAutomaton fragment).referencedStates .root =
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).referencedStates .root := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hReference⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hEdge
    rcases hEdge with ⟨raw, hRaw, rfl⟩
    have hRawSource : raw.source = .root := by
      simpa using hSource
    rcases hShape raw hRaw hRawSource with ⟨hNotFuture, removed, hFuture⟩
    refine ⟨raw, ⟨hRaw, hRawSource⟩, ?_⟩
    cases hLabel : raw.label with
    | future => exact (hNotFuture hLabel).elim
    | visible label =>
        simpa [sequenceExecutionEdge, hLabel, hFuture] using hReference
    | «variable» name =>
        simpa [sequenceExecutionEdge, hLabel, hFuture] using hReference
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hReference⟩
    rcases hShape edge hEdge hSource with ⟨hNotFuture, removed, hFuture⟩
    refine ⟨sequenceExecutionEdge edge, ⟨?_, by simpa⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩
    · cases hLabel : edge.label with
      | future => exact (hNotFuture hLabel).elim
      | visible label =>
          simpa [sequenceExecutionEdge, hLabel, hFuture] using hReference
      | «variable» name =>
          simpa [sequenceExecutionEdge, hLabel, hFuture] using hReference

private theorem sequenceExecution_computeFuture_root_eq
    (fragment : AutomatonFragment)
    (entries : Finset TypeAutomatonState)
    (hTargets : fragment.FutureTargetsInStates)
    (hRoot : (.root : TypeAutomatonState) ∈ fragment.states)
    (hShape : ∀ edge ∈ fragment.edges, edge.source = .root →
      edge.label ≠ .future ∧
        ∃ removed, edge.future = .at edge.target removed)
    (hUpper :
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).referencedStates .root ⊆ insert .root entries)
    (hEntries : entries ⊆
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).referencedStates .root)
    (hEntryFuture : ∀ entry ∈ entries,
      computeFuture (sequenceExecutionAutomaton fragment) entry =
        computeFuture
          ({ states := fragment.states, edges := fragment.edges } :
            PendingAutomaton) entry) :
    computeFuture (sequenceExecutionAutomaton fragment) .root =
      computeFuture
        ({ states := fragment.states, edges := fragment.edges } :
          PendingAutomaton) .root := by
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  let execution := sequenceExecutionAutomaton fragment
  have hPendingClosed : pending.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates fragment
      hTargets
  have hExecutionClosed : execution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed fragment hTargets
  have hExecutionRoot : (.root : TypeAutomatonState) ∈ execution.states :=
    Finset.mem_union_left _ hRoot
  have hOffers : execution.offersAt .root = pending.offersAt .root := by
    simpa [execution, pending] using
      sequenceExecution_root_offersAt_eq fragment hShape
  have hReferences : execution.referencedStates .root =
      pending.referencedStates .root := by
    simpa [execution, pending] using
      sequenceExecution_root_referencedStates_eq fragment hShape
  have hExecutionUpper : execution.referencedStates .root ⊆
      insert .root entries := by simpa [hReferences] using hUpper
  have hExecutionEntries : entries ⊆ execution.referencedStates .root := by
    simpa [hReferences] using hEntries
  rw [computeFuture_eq_offersAt_union_biUnion execution .root entries
      hExecutionClosed hExecutionRoot hExecutionUpper hExecutionEntries,
    computeFuture_eq_offersAt_union_biUnion pending .root entries
      hPendingClosed hRoot hUpper hEntries,
    hOffers]
  congr 1
  ext action
  simp only [Finset.mem_biUnion]
  constructor <;> rintro ⟨entry, hEntry, hAction⟩ <;>
    refine ⟨entry, hEntry, ?_⟩
  · rw [← hEntryFuture entry hEntry]
    exact hAction
  · rw [hEntryFuture entry hEntry]
    exact hAction

private theorem sequenceExecution_futureReachable_root
    (fragment : AutomatonFragment)
    (entries : Finset TypeAutomatonState)
    (hTargets : fragment.FutureTargetsInStates)
    (hRoot : (.root : TypeAutomatonState) ∈ fragment.states)
    (hShape : ∀ edge ∈ fragment.edges, edge.source = .root →
      edge.label ≠ .future ∧
        ∃ removed, edge.future = .at edge.target removed)
    (hUpper :
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).referencedStates .root ⊆ insert .root entries)
    (hEntries : entries ⊆
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).referencedStates .root) :
    (sequenceExecutionAutomaton fragment).futureReachable .root =
      {.root} ∪ entries.biUnion
        (sequenceExecutionAutomaton fragment).futureReachable := by
  let execution := sequenceExecutionAutomaton fragment
  have hClosed : execution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed fragment hTargets
  have hExecutionRoot : (.root : TypeAutomatonState) ∈ execution.states :=
    Finset.mem_union_left _ hRoot
  have hReferences : execution.referencedStates .root =
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).referencedStates .root := by
    simpa [execution] using
      sequenceExecution_root_referencedStates_eq fragment hShape
  apply execution.futureReachable_eq_self_union_biUnion .root entries
    hClosed hExecutionRoot
  · simpa [hReferences] using hUpper
  · simpa [hReferences] using hEntries

private theorem sequenceExecution_buildExclusiveOffer_root_shape
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata).edges)
    (hSource : edge.source = .root) :
    edge.label ≠ .future ∧
      ∃ removed, edge.future = .at edge.target removed := by
  classical
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
  · simp only [childPendingEdges, Finset.mem_image] at hElse
    rcases hElse with ⟨childEdge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
    rcases hIndexed with hEmpty | ⟨indexed, _, hChild⟩
    · simp at hEmpty
    · simp only [childPendingEdges, Finset.mem_image] at hChild
      rcases hChild with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
  · rw [mem_foldl_union_iff] at hBranch
    rcases hBranch with hEmpty | ⟨indexed, _, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      rcases hNewEdge with ⟨environment, _, rfl⟩
      exact ⟨by simp, ∅, rfl⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    exact ⟨by simp, _, rfl⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    exact ⟨by simp, ∅, rfl⟩

private theorem sequenceExecution_buildConjunctiveOffer_root_shape
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction).edges)
    (hSource : edge.source = .root) :
    edge.label ≠ .future ∧
      ∃ removed, edge.future = .at edge.target removed := by
  classical
  simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hConjunction | hElseChild) | hEnabled) | hWait) |
    hElse)
  · simp only [childPendingEdges, Finset.mem_image] at hConjunction
    rcases hConjunction with ⟨childEdge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · simp only [childPendingEdges, Finset.mem_image] at hElseChild
    rcases hElseChild with ⟨childEdge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · simp only [Finset.mem_image, Finset.mem_filter] at hEnabled
    rcases hEnabled with ⟨environment, _, rfl⟩
    exact ⟨by simp, ∅, rfl⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    exact ⟨by simp, _, rfl⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hElse
    rcases hElse with ⟨environment, _, rfl⟩
    exact ⟨by simp, ∅, rfl⟩

private theorem buildExclusiveOffer_child0_skipping_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildExclusiveOfferAutomaton signature branches elseAutomaton
          branchAutomata).skipping ↔
      state ∈ elseAutomaton.skipping := by
  have hNotIndexed := child_zero_not_mem_indexedFragmentSkipping
    branchAutomata state
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  have hChild : childState 0 state ∈ childSkipping 0 elseAutomaton ↔
      state ∈ elseAutomaton.skipping := by
    simp [childSkipping, childState]
  rw [hChild]
  simp [hNotIndexed]

private theorem buildExclusiveOffer_child0_completing_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildExclusiveOfferAutomaton signature branches elseAutomaton
          branchAutomata).completing ↔
      state ∈ elseAutomaton.completing := by
  have hNotIndexed := child_zero_not_mem_indexedFragmentCompleting
    branchAutomata state
  have hNotHeader : childState 0 state ∉
      (if elseAutomaton.initial ∈ elseAutomaton.completing ∨
          branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
        {TypeAutomatonState.root} else
          (∅ : Finset TypeAutomatonState)) := by
    split <;> simp [childState]
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  have hChild : childState 0 state ∈ childCompleting 0 elseAutomaton ↔
      state ∈ elseAutomaton.completing := by
    simp [childCompleting, childState]
  rw [hChild]
  simp [hNotHeader, hNotIndexed]

private theorem buildExclusiveOffer_root_not_skipping
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) :
    (.root : TypeAutomatonState) ∉
      (buildExclusiveOfferAutomaton signature branches elseAutomaton
        branchAutomata).skipping := by
  have hNotIndexed := root_not_mem_indexedFragmentSkipping branchAutomata
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, not_or]
  exact ⟨by simp [childSkipping, childState], hNotIndexed⟩

private theorem buildExclusiveOffer_branch_skipping_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : branchAutomata[index]? = some entry)
    (state : TypeAutomatonState) :
    childState (index + 1) state ∈
        (buildExclusiveOfferAutomaton signature branches elseAutomaton
          branchAutomata).skipping ↔
      state ∈ entry.2.skipping := by
  have hNotElse : childState (index + 1) state ∉
      childSkipping 0 elseAutomaton := by
    simp [childSkipping, childState]
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, hNotElse, false_or]
  exact childState_mem_indexedFragmentSkipping_iff branchAutomata index
    entry hEntry state

private theorem buildExclusiveOffer_branch_completing_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : branchAutomata[index]? = some entry)
    (state : TypeAutomatonState) :
    childState (index + 1) state ∈
        (buildExclusiveOfferAutomaton signature branches elseAutomaton
          branchAutomata).completing ↔
      state ∈ entry.2.completing := by
  have hNotHeader : childState (index + 1) state ∉
      (if elseAutomaton.initial ∈ elseAutomaton.completing ∨
          branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
        {TypeAutomatonState.root} else
          (∅ : Finset TypeAutomatonState)) := by
    split <;> simp [childState]
  have hNotElse : childState (index + 1) state ∉
      childCompleting 0 elseAutomaton := by
    simp [childCompleting, childState]
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, hNotHeader, hNotElse, false_or]
  exact childState_mem_indexedFragmentCompleting_iff branchAutomata index
    entry hEntry state

private theorem buildConjunctiveOffer_child0_skipping_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildConjunctiveOfferAutomaton signature branches elseAutomaton
          conjunction).skipping ↔
      state ∈ conjunction.skipping := by
  simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    childSkipping, childState]

private theorem buildConjunctiveOffer_child1_skipping_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (state : TypeAutomatonState) :
    childState 1 state ∈
        (buildConjunctiveOfferAutomaton signature branches elseAutomaton
          conjunction).skipping ↔
      state ∈ elseAutomaton.skipping := by
  simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    childSkipping, childState]

private theorem buildConjunctiveOffer_child0_completing_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildConjunctiveOfferAutomaton signature branches elseAutomaton
          conjunction).completing ↔
      state ∈ conjunction.completing := by
  have hNotHeader : childState 0 state ∉
      (if elseAutomaton.initial ∈ elseAutomaton.completing ∨
          branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
        {TypeAutomatonState.root} else (∅ : Finset TypeAutomatonState)) := by
    split <;> simp [childState]
  have hNotElse : childState 0 state ∉ childCompleting 1 elseAutomaton := by
    simp [childCompleting, childState]
  simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, hNotHeader, hNotElse, false_or, or_false]
  simp [childCompleting, childState]

private theorem buildConjunctiveOffer_child1_completing_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (state : TypeAutomatonState) :
    childState 1 state ∈
        (buildConjunctiveOfferAutomaton signature branches elseAutomaton
          conjunction).completing ↔
      state ∈ elseAutomaton.completing := by
  have hNotHeader : childState 1 state ∉
      (if elseAutomaton.initial ∈ elseAutomaton.completing ∨
          branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
        {TypeAutomatonState.root} else (∅ : Finset TypeAutomatonState)) := by
    split <;> simp [childState]
  have hNotConjunction : childState 1 state ∉
      childCompleting 0 conjunction := by
    simp [childCompleting, childState]
  simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, hNotHeader, hNotConjunction, false_or]
  simp [childCompleting, childState]

private theorem buildConjunctiveOffer_root_not_skipping
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment) :
    (.root : TypeAutomatonState) ∉
      (buildConjunctiveOfferAutomaton signature branches elseAutomaton
        conjunction).skipping := by
  simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    childSkipping, childState]

private theorem sequenceExecution_buildChoice_states_left_subset
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton left
    child.states.image (.child 0) ⊆ parent.states := by
  classical
  dsimp only
  intro target hTarget
  rcases Finset.mem_image.mp hTarget with ⟨state, hState, rfl⟩
  simp only [sequenceExecutionAutomaton, Finset.mem_union,
    Finset.mem_image] at hState ⊢
  rcases hState with hState | ⟨edge, hEdge, rfl⟩
  · left
    simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
      childState, hState]
  · right
    refine ⟨childPendingEdge 0 edge, ?_, ?_⟩
    · simp only [buildChoiceAutomaton, finishAutomatonFragment,
        Finset.mem_union, childPendingEdges, Finset.mem_image,
        Finset.mem_biUnion]
      exact Or.inl (Or.inl ⟨edge, hEdge, rfl⟩)
    · simp [childPendingEdge, childState]

private theorem sequenceExecution_buildChoice_states_right_subset
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton right
    child.states.image (.child 1) ⊆ parent.states := by
  classical
  dsimp only
  intro target hTarget
  rcases Finset.mem_image.mp hTarget with ⟨state, hState, rfl⟩
  simp only [sequenceExecutionAutomaton, Finset.mem_union,
    Finset.mem_image] at hState ⊢
  rcases hState with hState | ⟨edge, hEdge, rfl⟩
  · left
    simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
      childState, hState]
  · right
    refine ⟨childPendingEdge 1 edge, ?_, ?_⟩
    · simp only [buildChoiceAutomaton, finishAutomatonFragment,
        Finset.mem_union, childPendingEdges, Finset.mem_image,
        Finset.mem_biUnion]
      exact Or.inl (Or.inr ⟨edge, hEdge, rfl⟩)
    · simp [childPendingEdge, childState]

private theorem sequenceExecution_buildChoice_futureReachable_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hTargets : left.FutureTargetsInStates)
    (state : TypeAutomatonState) (hState : state ∈ left.states) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton left
    parent.futureReachable (.child 0 state) =
      (child.futureReachable state).image (.child 0) := by
  let parent := sequenceExecutionAutomaton
    (buildChoiceAutomaton signature left right selectionLeft selectionRight)
  let child := sequenceExecutionAutomaton left
  have hClosed : child.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed left hTargets
  have hChildState : state ∈ child.states := by
    exact Finset.mem_union_left _ hState
  have hCard : child.states.card ≤ parent.states.card := by
    have hSubset := sequenceExecution_buildChoice_states_left_subset signature
      left right selectionLeft selectionRight
    calc
      child.states.card = (child.states.image (.child 0)).card := by
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ parent.states.card := Finset.card_le_card hSubset
  exact PendingAutomaton.futureReachable_eq_of_embedding child parent
    (.child 0)
    (sequenceExecution_buildChoice_referencedStates_left signature left right
      selectionLeft selectionRight) hClosed state hChildState hCard

private theorem sequenceExecution_buildChoice_futureReachable_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hTargets : right.FutureTargetsInStates)
    (state : TypeAutomatonState) (hState : state ∈ right.states) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton right
    parent.futureReachable (.child 1 state) =
      (child.futureReachable state).image (.child 1) := by
  let parent := sequenceExecutionAutomaton
    (buildChoiceAutomaton signature left right selectionLeft selectionRight)
  let child := sequenceExecutionAutomaton right
  have hClosed : child.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed right hTargets
  have hChildState : state ∈ child.states := by
    exact Finset.mem_union_left _ hState
  have hCard : child.states.card ≤ parent.states.card := by
    have hSubset := sequenceExecution_buildChoice_states_right_subset signature
      left right selectionLeft selectionRight
    calc
      child.states.card = (child.states.image (.child 1)).card := by
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ parent.states.card := Finset.card_le_card hSubset
  exact PendingAutomaton.futureReachable_eq_of_embedding child parent
    (.child 1)
    (sequenceExecution_buildChoice_referencedStates_right signature left right
      selectionLeft selectionRight) hClosed state hChildState hCard

private theorem sequenceExecution_buildChoice_computeFuture_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hTargets : left.FutureTargetsInStates)
    (state : TypeAutomatonState) (hState : state ∈ left.states) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton left
    computeFuture parent (.child 0 state) = computeFuture child state := by
  let parent := sequenceExecutionAutomaton
    (buildChoiceAutomaton signature left right selectionLeft selectionRight)
  let child := sequenceExecutionAutomaton left
  have hClosed : child.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed left hTargets
  have hChildState : state ∈ child.states := by
    exact Finset.mem_union_left _ hState
  have hCard : child.states.card ≤ parent.states.card := by
    have hSubset := sequenceExecution_buildChoice_states_left_subset signature
      left right selectionLeft selectionRight
    calc
      child.states.card = (child.states.image (.child 0)).card := by
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ parent.states.card := Finset.card_le_card hSubset
  exact computeFuture_eq_of_embedding child parent (.child 0)
    (sequenceExecution_buildChoice_referencedStates_left signature left right
      selectionLeft selectionRight)
    (sequenceExecution_buildChoice_offersAt_left signature left right
      selectionLeft selectionRight) hClosed state hChildState hCard

private theorem sequenceExecution_buildChoice_computeFuture_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hTargets : right.FutureTargetsInStates)
    (state : TypeAutomatonState) (hState : state ∈ right.states) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton right
    computeFuture parent (.child 1 state) = computeFuture child state := by
  let parent := sequenceExecutionAutomaton
    (buildChoiceAutomaton signature left right selectionLeft selectionRight)
  let child := sequenceExecutionAutomaton right
  have hClosed : child.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed right hTargets
  have hChildState : state ∈ child.states := by
    exact Finset.mem_union_left _ hState
  have hCard : child.states.card ≤ parent.states.card := by
    have hSubset := sequenceExecution_buildChoice_states_right_subset signature
      left right selectionLeft selectionRight
    calc
      child.states.card = (child.states.image (.child 1)).card := by
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ parent.states.card := Finset.card_le_card hSubset
  exact computeFuture_eq_of_embedding child parent (.child 1)
    (sequenceExecution_buildChoice_referencedStates_right signature left right
      selectionLeft selectionRight)
    (sequenceExecution_buildChoice_offersAt_right signature left right
      selectionLeft selectionRight) hClosed state hChildState hCard

private theorem sequenceExecution_buildChoice_referencedStates_root
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    parent.referencedStates .root =
      {.child 0 left.initial, .child 1 right.initial} := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, sequenceExecutionAutomaton, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hTarget
    rcases hTarget with
      ⟨executionEdge, ⟨hExecutionEdge, hSource⟩, hFuture⟩
    rcases hExecutionEdge with ⟨raw, hRaw, hEdge⟩
    rw [← hEdge] at hSource hFuture
    simp only [buildChoiceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at hRaw
    rcases hRaw with (hLeft | hRight) | hSelection
    · rcases hLeft with ⟨edge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · rcases hRight with ⟨edge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · rcases hSelection with ⟨environment, _, hEdge⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
      rcases hEdge with hEdge | hEdge
      · left
        rw [hEdge] at hFuture
        simpa [sequenceExecutionEdge, AutomatonConstructionLabel.semantic,
          hSelectionLeft, childState] using hFuture
      · right
        rw [hEdge] at hFuture
        simpa [sequenceExecutionEdge, AutomatonConstructionLabel.semantic,
          hSelectionRight, childState] using hFuture
  · intro hTarget
    rcases hTarget with rfl | rfl
    · let raw : PendingAutomatonEdge :=
        { source := .root
          environment := TypeEnvironment.tock
          label := .visible selectionLeft
          current := ∅
          future := .at (.child 0 left.initial) ∅
          target := .child 0 left.initial }
      have hRaw : raw ∈ (buildChoiceAutomaton signature left right
          selectionLeft selectionRight).edges := by
        simp only [buildChoiceAutomaton, finishAutomatonFragment,
          childPendingEdges, Finset.mem_union, Finset.mem_image,
          Finset.mem_biUnion]
        right
        refine ⟨TypeEnvironment.tock, ?_, ?_⟩
        · simp [TypeAlphabet.localEnvironments]
        · simp [raw, childState]
      refine ⟨sequenceExecutionEdge raw, ⟨?_, rfl⟩, ?_⟩
      · exact ⟨raw, hRaw, rfl⟩
      · simp [raw, sequenceExecutionEdge,
          AutomatonConstructionLabel.semantic, hSelectionLeft]
    · let raw : PendingAutomatonEdge :=
        { source := .root
          environment := TypeEnvironment.tock
          label := .visible selectionRight
          current := ∅
          future := .at (.child 1 right.initial) ∅
          target := .child 1 right.initial }
      have hRaw : raw ∈ (buildChoiceAutomaton signature left right
          selectionLeft selectionRight).edges := by
        simp only [buildChoiceAutomaton, finishAutomatonFragment,
          childPendingEdges, Finset.mem_union, Finset.mem_image,
          Finset.mem_biUnion]
        right
        refine ⟨TypeEnvironment.tock, ?_, ?_⟩
        · simp [TypeAlphabet.localEnvironments]
        · simp [raw, childState]
      refine ⟨sequenceExecutionEdge raw, ⟨?_, rfl⟩, ?_⟩
      · exact ⟨raw, hRaw, rfl⟩
      · simp [raw, sequenceExecutionEdge,
          AutomatonConstructionLabel.semantic, hSelectionRight]

private theorem sequenceExecution_buildChoice_offersAt_root
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    parent.offersAt .root = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro action hAction
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter, sequenceExecutionAutomaton, Finset.mem_image]
    at hAction
  rcases hAction with
    ⟨executionEdge, ⟨hExecutionEdge, hSource⟩, hOffer⟩
  rcases hExecutionEdge with ⟨raw, hRaw, hEdge⟩
  rw [← hEdge] at hSource hOffer
  simp only [buildChoiceAutomaton, finishAutomatonFragment,
    childPendingEdges, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion] at hRaw
  rcases hRaw with (hLeft | hRight) | hSelection
  · rcases hLeft with ⟨edge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · rcases hRight with ⟨edge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · rcases hSelection with ⟨environment, _, hEdge⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with hEdge | hEdge <;> rw [hEdge] at hOffer <;>
      simp [sequenceExecutionEdge, AutomatonConstructionLabel.semantic]
        at hOffer

private theorem sequenceExecution_buildChoice_computeFuture_root
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    let parentFragment := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent := sequenceExecutionAutomaton parentFragment
    computeFuture parent .root =
      computeFuture (sequenceExecutionAutomaton left) left.initial ∪
        computeFuture (sequenceExecutionAutomaton right) right.initial := by
  let parentFragment := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  let parent := sequenceExecutionAutomaton parentFragment
  have hParentTargets : parentFragment.FutureTargetsInStates :=
    buildChoiceAutomaton_futureTargetsInStates signature left right
      selectionLeft selectionRight hLeftTargets hRightTargets hLeftInitial
      hRightInitial
  have hClosed : parent.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed parentFragment hParentTargets
  have hRoot : (.root : TypeAutomatonState) ∈ parent.states := by
    simp [parent, parentFragment, sequenceExecutionAutomaton,
      buildChoiceAutomaton, finishAutomatonFragment]
  change computeFuture parent .root = _
  rw [computeFuture_unfold parent .root hClosed hRoot,
    sequenceExecution_buildChoice_offersAt_root signature left right
      selectionLeft selectionRight,
    sequenceExecution_buildChoice_referencedStates_root signature left right
      selectionLeft selectionRight hSelectionLeft hSelectionRight]
  simp only [Finset.empty_union, Finset.biUnion_insert,
    Finset.biUnion_singleton]
  have hLeftEmbedding :=
    sequenceExecution_buildChoice_computeFuture_left signature left right
      selectionLeft selectionRight hLeftTargets left.initial hLeftInitial
  have hRightEmbedding :=
    sequenceExecution_buildChoice_computeFuture_right signature left right
      selectionLeft selectionRight hRightTargets right.initial hRightInitial
  refine congrArg₂ (fun first second => first ∪ second)
    hLeftEmbedding ?_
  simpa using hRightEmbedding

private theorem sequenceExecution_buildChoice_futureReachable_root
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    let parentFragment := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent := sequenceExecutionAutomaton parentFragment
    parent.futureReachable .root =
      {.root} ∪
        ((sequenceExecutionAutomaton left).futureReachable
          left.initial).image (.child 0) ∪
        ((sequenceExecutionAutomaton right).futureReachable
          right.initial).image (.child 1) := by
  let parentFragment := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  let parent := sequenceExecutionAutomaton parentFragment
  have hParentTargets : parentFragment.FutureTargetsInStates :=
    buildChoiceAutomaton_futureTargetsInStates signature left right
      selectionLeft selectionRight hLeftTargets hRightTargets hLeftInitial
      hRightInitial
  have hClosed : parent.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed parentFragment hParentTargets
  have hRoot : (.root : TypeAutomatonState) ∈ parent.states := by
    simp [parent, parentFragment, sequenceExecutionAutomaton,
      buildChoiceAutomaton, finishAutomatonFragment]
  change parent.futureReachable .root = _
  rw [parent.futureReachable_unfold .root hClosed hRoot,
    sequenceExecution_buildChoice_referencedStates_root signature left right
      selectionLeft selectionRight hSelectionLeft hSelectionRight]
  simp only [Finset.biUnion_insert, Finset.biUnion_singleton]
  have hLeftEmbedding :=
    sequenceExecution_buildChoice_futureReachable_left signature left right
      selectionLeft selectionRight hLeftTargets left.initial hLeftInitial
  have hRightEmbedding :=
    sequenceExecution_buildChoice_futureReachable_right signature left right
      selectionLeft selectionRight hRightTargets right.initial hRightInitial
  rw [hLeftEmbedding]
  have hRightSingleton :
      ({.child 1 right.initial} : Finset TypeAutomatonState).biUnion
          parent.futureReachable =
        ((sequenceExecutionAutomaton right).futureReachable
          right.initial).image (.child 1) := by
    simpa using hRightEmbedding
  rw [hRightSingleton]
  simp [Finset.union_assoc]

private theorem buildChoiceAutomaton_completionWitness_left_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (reachable : Finset TypeAutomatonState) :
    let parent := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    (∃ completed ∈ reachable.image (.child 0),
        completed ∈ parent.skipping ∨ completed ∈ parent.completing) ↔
      ∃ completed ∈ reachable,
        completed ∈ left.skipping ∨ completed ∈ left.completing := by
  classical
  constructor
  · rintro ⟨tagged, hTagged, hCompleted⟩
    rcases Finset.mem_image.mp hTagged with
      ⟨completed, hReachable, hTagged⟩
    rw [← hTagged] at hCompleted
    refine ⟨completed, hReachable, ?_⟩
    by_cases hInitial : left.initial ∈ left.completing ∨
        right.initial ∈ right.completing <;>
      simpa [buildChoiceAutomaton, finishAutomatonFragment, childSkipping,
        childCompleting, childState, hInitial] using hCompleted
  · rintro ⟨completed, hReachable, hCompleted⟩
    refine ⟨.child 0 completed, Finset.mem_image.mpr
      ⟨completed, hReachable, rfl⟩, ?_⟩
    by_cases hInitial : left.initial ∈ left.completing ∨
        right.initial ∈ right.completing <;>
      simpa [buildChoiceAutomaton, finishAutomatonFragment, childSkipping,
        childCompleting, childState, hInitial] using hCompleted

private theorem buildChoiceAutomaton_completionWitness_right_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (reachable : Finset TypeAutomatonState) :
    let parent := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    (∃ completed ∈ reachable.image (.child 1),
        completed ∈ parent.skipping ∨ completed ∈ parent.completing) ↔
      ∃ completed ∈ reachable,
        completed ∈ right.skipping ∨ completed ∈ right.completing := by
  classical
  constructor
  · rintro ⟨tagged, hTagged, hCompleted⟩
    rcases Finset.mem_image.mp hTagged with
      ⟨completed, hReachable, hTagged⟩
    rw [← hTagged] at hCompleted
    refine ⟨completed, hReachable, ?_⟩
    by_cases hInitial : left.initial ∈ left.completing ∨
        right.initial ∈ right.completing <;>
      simpa [buildChoiceAutomaton, finishAutomatonFragment, childSkipping,
        childCompleting, childState, hInitial] using hCompleted
  · rintro ⟨completed, hReachable, hCompleted⟩
    refine ⟨.child 1 completed, Finset.mem_image.mpr
      ⟨completed, hReachable, rfl⟩, ?_⟩
    by_cases hInitial : left.initial ∈ left.completing ∨
        right.initial ∈ right.completing <;>
      simpa [buildChoiceAutomaton, finishAutomatonFragment, childSkipping,
        childCompleting, childState, hInitial] using hCompleted

private theorem sequenceExecution_buildChoice_completionWitness_root_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    let parentFragment := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent := sequenceExecutionAutomaton parentFragment
    let leftExecution := sequenceExecutionAutomaton left
    let rightExecution := sequenceExecutionAutomaton right
    ((∃ completed ∈ parent.futureReachable .root,
        completed ∈ parentFragment.skipping ∨
          completed ∈ parentFragment.completing) ↔
      (∃ completed ∈ leftExecution.futureReachable left.initial,
        completed ∈ left.skipping ∨ completed ∈ left.completing) ∨
      (∃ completed ∈ rightExecution.futureReachable right.initial,
        completed ∈ right.skipping ∨ completed ∈ right.completing)) := by
  classical
  let parentFragment := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  let parent := sequenceExecutionAutomaton parentFragment
  let leftExecution := sequenceExecutionAutomaton left
  let rightExecution := sequenceExecutionAutomaton right
  change ((∃ completed ∈ parent.futureReachable .root,
      completed ∈ parentFragment.skipping ∨
        completed ∈ parentFragment.completing) ↔ _)
  rw [sequenceExecution_buildChoice_futureReachable_root signature left right
    selectionLeft selectionRight hSelectionLeft hSelectionRight hLeftTargets
    hRightTargets hLeftInitial hRightInitial]
  have hLeftSelf : left.initial ∈ leftExecution.futureReachable left.initial :=
    leftExecution.mem_futureReachable_self left.initial
  have hRightSelf : right.initial ∈
      rightExecution.futureReachable right.initial :=
    rightExecution.mem_futureReachable_self right.initial
  constructor
  · rintro ⟨completed, hReachable, hCompleted⟩
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
      at hReachable
    rcases hReachable with (rfl | ⟨child, hChild, rfl⟩) |
        ⟨child, hChild, rfl⟩
    · have hInitial : left.initial ∈ left.completing ∨
          right.initial ∈ right.completing := by
        by_cases hInitial : left.initial ∈ left.completing ∨
            right.initial ∈ right.completing
        · exact hInitial
        · simp [parentFragment, buildChoiceAutomaton,
            finishAutomatonFragment, childCompleting, childSkipping,
            childState, hInitial] at hCompleted
      rcases hInitial with hLeft | hRight
      · left
        exact ⟨left.initial, hLeftSelf, Or.inr hLeft⟩
      · right
        exact ⟨right.initial, hRightSelf, Or.inr hRight⟩
    · left
      refine ⟨child, hChild, ?_⟩
      by_cases hInitial : left.initial ∈ left.completing ∨
          right.initial ∈ right.completing <;>
        simpa [parentFragment, buildChoiceAutomaton,
          finishAutomatonFragment, childCompleting, childSkipping,
          childState, hInitial] using hCompleted
    · right
      refine ⟨child, hChild, ?_⟩
      by_cases hInitial : left.initial ∈ left.completing ∨
          right.initial ∈ right.completing <;>
        simpa [parentFragment, buildChoiceAutomaton,
          finishAutomatonFragment, childCompleting, childSkipping,
          childState, hInitial] using hCompleted
  · rintro (hLeft | hRight)
    · rcases hLeft with ⟨child, hChild, hCompleted⟩
      refine ⟨.child 0 child, ?_, ?_⟩
      · simp only [Finset.mem_union, Finset.mem_singleton,
          Finset.mem_image]
        exact Or.inl (Or.inr ⟨child, hChild, rfl⟩)
      · by_cases hInitial : left.initial ∈ left.completing ∨
            right.initial ∈ right.completing <;>
          simpa [parentFragment, buildChoiceAutomaton,
            finishAutomatonFragment, childCompleting, childSkipping,
            childState, hInitial] using hCompleted
    · rcases hRight with ⟨child, hChild, hCompleted⟩
      refine ⟨.child 1 child, ?_, ?_⟩
      · simp only [Finset.mem_union, Finset.mem_singleton,
          Finset.mem_image]
        exact Or.inr ⟨child, hChild, rfl⟩
      · by_cases hInitial : left.initial ∈ left.completing ∨
            right.initial ∈ right.completing <;>
          simpa [parentFragment, buildChoiceAutomaton,
            finishAutomatonFragment, childCompleting, childSkipping,
            childState, hInitial] using hCompleted

/-- Immediate same-cycle references from a tagged sequence-left state are the
tagged execution-child references, plus the right entry exactly when the
state is skipping or optimistically completing. -/
private theorem buildSequenceAutomaton_referencedStates_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    parent.referencedStates (.child 0 state) =
      ((sequenceExecutionAutomaton left).referencedStates state).image
          (.child 0) ∪
        if state ∈ left.skipping ∨ state ∈ left.completing then
          {.child 1 right.initial}
        else ∅ := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_union, Finset.mem_image]
  simp_rw [buildSequenceAutomaton_outgoing_left signature left right]
  simp only [sequenceExecutionAutomaton, Finset.mem_image]
  constructor
  · rintro ⟨edge, hEdge, hFuture⟩
    rcases hEdge with hLeft | hBridge | hFutureBridge
    · rcases hLeft with
        ⟨childEdge, hChildEdge, hChildSource, rfl⟩
      cases hLabel : childEdge.label with
      | future =>
          cases hSpec : childEdge.future with
          | explicit offers =>
              simp [hLabel, hSpec, childFutureSpec,
                AutomatonConstructionLabel.semantic, TypeLabel.silent]
                at hFuture
          | «at» referenced removed =>
              have hTarget : target = childState 0 referenced := by
                simpa [hLabel, hSpec, childFutureSpec,
                  AutomatonConstructionLabel.semantic, TypeLabel.silent]
                  using hFuture
              subst target
              left
              refine ⟨referenced, ?_, rfl⟩
              refine ⟨
                { source := childEdge.source
                  environment := childEdge.environment
                  label := childEdge.label
                  current := childEdge.current
                  future := match childEdge.label with
                    | .future => childEdge.future
                    | _ => .at childEdge.target childEdge.current
                  target := childEdge.target }, ⟨?_, ?_⟩, ?_⟩
              · exact ⟨childEdge, hChildEdge, rfl⟩
              · simpa using hChildSource
              · simp [hLabel, hSpec, AutomatonConstructionLabel.semantic,
                  TypeLabel.silent]
      | visible label =>
          by_cases hTock : label = TypeLabel.tock
          · subst label
            simp [hLabel, childFutureSpec,
              AutomatonConstructionLabel.semantic] at hFuture
          · have hTarget : target = childState 0 childEdge.target := by
              simpa [hLabel, childFutureSpec,
                AutomatonConstructionLabel.semantic, hTock]
                using hFuture
            subst target
            left
            refine ⟨childEdge.target, ?_, rfl⟩
            refine ⟨
              { source := childEdge.source
                environment := childEdge.environment
                label := childEdge.label
                current := childEdge.current
                future := match childEdge.label with
                  | .future => childEdge.future
                  | _ => .at childEdge.target childEdge.current
                target := childEdge.target }, ⟨?_, ?_⟩, ?_⟩
            · exact ⟨childEdge, hChildEdge, rfl⟩
            · simpa using hChildSource
            · simp [hLabel, AutomatonConstructionLabel.semantic, hTock]
      | «variable» name =>
          have hTarget : target = childState 0 childEdge.target := by
            simpa [hLabel, childFutureSpec,
              AutomatonConstructionLabel.semantic, TypeLabel.silent]
              using hFuture
          subst target
          left
          refine ⟨childEdge.target, ?_, rfl⟩
          refine ⟨
            { source := childEdge.source
              environment := childEdge.environment
              label := childEdge.label
              current := childEdge.current
              future := match childEdge.label with
                | .future => childEdge.future
                | _ => .at childEdge.target childEdge.current
              target := childEdge.target }, ⟨?_, ?_⟩, ?_⟩
          · exact ⟨childEdge, hChildEdge, rfl⟩
          · simpa using hChildSource
          · simp [hLabel, AutomatonConstructionLabel.semantic,
              TypeLabel.silent]
    · rcases hBridge with ⟨hSkipping, environment, hEnvironment, rfl⟩
      have hTarget : target = childState 1 right.initial := by
        simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
          using hFuture
      subst target
      right
      simp [childState, hSkipping]
    · rcases hFutureBridge with ⟨hCompleting, rfl⟩
      have hTarget : target = childState 1 right.initial := by
        simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
          using hFuture
      subst target
      right
      simp [childState, hCompleting]
  · intro hTarget
    rcases hTarget with hLeft | hBridge
    · rcases hLeft with ⟨childTarget, hChildTarget, rfl⟩
      rcases hChildTarget with ⟨edge, ⟨hEdge, hSource⟩, hFuture⟩
      rcases hEdge with ⟨childEdge, hChildEdge, hEdge⟩
      rw [← hEdge] at hSource hFuture
      have hChildSource : childEdge.source = state := by simpa using hSource
      cases hLabel : childEdge.label with
      | future =>
          cases hSpec : childEdge.future with
          | explicit offers =>
              simp [hLabel, hSpec, AutomatonConstructionLabel.semantic,
                TypeLabel.silent] at hFuture
          | «at» referenced removed =>
              have hChildTarget : childTarget = referenced := by
                simpa [hLabel, hSpec, AutomatonConstructionLabel.semantic,
                  TypeLabel.silent] using hFuture
              subst childTarget
              refine ⟨_, Or.inl
                ⟨childEdge, hChildEdge, hChildSource, rfl⟩, ?_⟩
              simp [hLabel, hSpec, childFutureSpec,
                AutomatonConstructionLabel.semantic, TypeLabel.silent,
                childState]
      | visible label =>
          by_cases hTock : label = TypeLabel.tock
          · subst label
            simp [hLabel, AutomatonConstructionLabel.semantic] at hFuture
          · have hChildTarget : childTarget = childEdge.target := by
              simpa [hLabel, AutomatonConstructionLabel.semantic, hTock]
                using hFuture
            subst childTarget
            refine ⟨_, Or.inl
              ⟨childEdge, hChildEdge, hChildSource, rfl⟩, ?_⟩
            simp [hLabel, childFutureSpec,
              AutomatonConstructionLabel.semantic, hTock, childState]
      | «variable» name =>
          have hChildTarget : childTarget = childEdge.target := by
            simpa [hLabel, AutomatonConstructionLabel.semantic,
              TypeLabel.silent] using hFuture
          subst childTarget
          refine ⟨_, Or.inl
            ⟨childEdge, hChildEdge, hChildSource, rfl⟩, ?_⟩
          simp [hLabel, childFutureSpec,
            AutomatonConstructionLabel.semantic, TypeLabel.silent,
            childState]
    · by_cases hSkipping : state ∈ left.skipping
      · simp only [hSkipping, true_or, if_true, Finset.mem_singleton]
          at hBridge
        subst target
        let environment := TypeEnvironment.tock
        refine ⟨_, Or.inr (Or.inl
          ⟨hSkipping, environment, ?_, rfl⟩), ?_⟩
        · simp [environment, TypeAlphabet.localEnvironments]
        · simp [childState, AutomatonConstructionLabel.semantic,
            TypeLabel.silent]
      · by_cases hCompleting : state ∈ left.completing
        · simp only [hSkipping, false_or, hCompleting, if_true,
            Finset.mem_singleton] at hBridge
          subst target
          refine ⟨_, Or.inr (Or.inr ⟨hCompleting, rfl⟩), ?_⟩
          simp [childState, AutomatonConstructionLabel.semantic,
            TypeLabel.silent]
        · simp [hSkipping, hCompleting] at hBridge

/-- Sequence-left tagging preserves direct offers; the two bridge families
carry empty current offers. -/
private theorem buildSequenceAutomaton_offersAt_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    parent.offersAt (.child 0 state) =
      (sequenceExecutionAutomaton left).offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [buildSequenceAutomaton_outgoing_left signature left right]
  simp only [sequenceExecutionAutomaton, Finset.mem_image]
  simp [childFutureSpec, childState]
  grind

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

/-- Exact same-cycle reachability from a tagged sequence-left state.  The
left execution closure is always present.  The right closure is present
exactly when that closure reaches either a literal-skip state or a state marked
as optimistically completing by the child compiler. -/
private theorem buildSequenceAutomaton_futureReachable_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hLeftState : state ∈ left.states)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let execution := sequenceExecutionAutomaton left
    let rightPending : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    let leftReach := execution.futureReachable state
    let canBridge := ∃ completed ∈ leftReach,
      completed ∈ left.skipping ∨ completed ∈ left.completing
    parent.futureReachable (.child 0 state) =
      leftReach.image (.child 0) ∪
        if canBridge then
          (rightPending.futureReachable right.initial).image (.child 1)
        else ∅ := by
  classical
  let sequence := buildSequenceAutomaton signature left right
  let parent : PendingAutomaton :=
    { states := sequence.states, edges := sequence.edges }
  let execution := sequenceExecutionAutomaton left
  let rightPending : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  let leftReach := execution.futureReachable state
  let rightReach := rightPending.futureReachable right.initial
  let canBridge := ∃ completed ∈ leftReach,
    completed ∈ left.skipping ∨ completed ∈ left.completing
  change parent.futureReachable (childState 0 state) =
    leftReach.image (childState 0) ∪
      if canBridge then rightReach.image (childState 1) else ∅
  have hExecutionClosed : execution.ReferencesClosed := by
    exact sequenceExecutionAutomaton_referencesClosed left hLeftTargets
  have hRightClosed : rightPending.ReferencesClosed := by
    exact PendingAutomaton.referencesClosed_of_futureTargetsInStates right
      hRightTargets
  have hParentClosed : parent.ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_of_futureTargetsInStates sequence
    exact buildSequenceAutomaton_futureTargetsInStates signature left right
      hLeftTargets hRightTargets hRightInitial
  have hExecutionState : state ∈ execution.states := by
    simp [execution, sequenceExecutionAutomaton, hLeftState]
  have hParentLeftState : childState 0 state ∈ parent.states := by
    simp [parent, sequence, buildSequenceAutomaton, finishAutomatonFragment,
      childStates, childState, hLeftState]
  have hParentRightState : childState 1 right.initial ∈ parent.states := by
    simp [parent, sequence, buildSequenceAutomaton, finishAutomatonFragment,
      childStates, childState, hRightInitial]
  have hLeftReferences : ∀ child,
      parent.referencedStates (childState 0 child) =
        (execution.referencedStates child).image (childState 0) ∪
          if child ∈ left.skipping ∨ child ∈ left.completing then
            {childState 1 right.initial}
          else ∅ := by
    intro child
    exact buildSequenceAutomaton_referencedStates_left signature left right
      child
  have hRightReferences : ∀ child,
      parent.referencedStates (childState 1 child) =
        (rightPending.referencedStates child).image (childState 1) := by
    intro child
    exact buildSequenceAutomaton_referencedStates_right signature left right
      child
  have hExecutionReachClosed : ∀ {source target},
      source ∈ leftReach → target ∈ execution.referencedStates source →
        target ∈ leftReach := by
    intro source target hSourceReach hReference
    have hSourceState : source ∈ execution.states :=
      (execution.futureReachable_subset_of_reference_closed state
        execution.states hExecutionState
        (fun current hCurrent => hExecutionClosed current hCurrent))
        hSourceReach
    have hTargetFromSource :=
      execution.referencedStates_subset_futureReachable source
        hExecutionClosed hSourceState hReference
    exact (execution.futureReachable_subset_of_mem hExecutionClosed
      hExecutionState hSourceReach) hTargetFromSource
  have hRightReachClosed : ∀ {source target},
      source ∈ rightReach → target ∈ rightPending.referencedStates source →
        target ∈ rightReach := by
    intro source target hSourceReach hReference
    have hSourceState : source ∈ rightPending.states :=
      (rightPending.futureReachable_subset_of_reference_closed right.initial
        rightPending.states hRightInitial
        (fun current hCurrent => hRightClosed current hCurrent))
        hSourceReach
    have hTargetFromSource :=
      rightPending.referencedStates_subset_futureReachable source
        hRightClosed hSourceState hReference
    exact (rightPending.futureReachable_subset_of_mem hRightClosed
      hRightInitial hSourceReach) hTargetFromSource
  have hStateReach : state ∈ leftReach := by
    change state ∈ execution.futureReachable state
    rw [execution.futureReachable_unfold state hExecutionClosed
      hExecutionState]
    simp
  have hLeftReachSubset : leftReach.image (childState 0) ⊆
      parent.futureReachable (childState 0 state) := by
    apply PendingAutomaton.futureReachable_image_subset_of_embedding
      execution parent (childState 0)
    · intro child
      rw [hLeftReferences child]
      exact Finset.subset_union_left
    · exact hParentClosed
    · exact hParentLeftState
  by_cases hCanBridge : canBridge
  · have hBridgeStart : childState 1 right.initial ∈
        parent.futureReachable (childState 0 state) := by
      rcases hCanBridge with
        ⟨completed, hCompletedReach, hBridgeable⟩
      have hTaggedCompleted : childState 0 completed ∈
          parent.futureReachable (childState 0 state) :=
        hLeftReachSubset (Finset.mem_image.mpr
          ⟨completed, hCompletedReach, rfl⟩)
      have hBridgeReference : childState 1 right.initial ∈
          parent.referencedStates (childState 0 completed) := by
        rw [hLeftReferences completed]
        simp [hBridgeable]
      have hCompletedState : childState 0 completed ∈ parent.states :=
        (parent.futureReachable_subset_of_reference_closed
          (childState 0 state) parent.states hParentLeftState
          (fun current hCurrent => hParentClosed current hCurrent))
          hTaggedCompleted
      have hReferenceFromCompleted :=
        parent.referencedStates_subset_futureReachable
          (childState 0 completed) hParentClosed hCompletedState
          hBridgeReference
      exact (parent.futureReachable_subset_of_mem hParentClosed
        hParentLeftState hTaggedCompleted) hReferenceFromCompleted
    have hRightFromEntry : rightReach.image (childState 1) ⊆
        parent.futureReachable (childState 1 right.initial) := by
      apply PendingAutomaton.futureReachable_image_subset_of_embedding
        rightPending parent (childState 1)
      · intro child
        rw [hRightReferences child]
      · exact hParentClosed
      · exact hParentRightState
    have hRightEntryToRoot :
        parent.futureReachable (childState 1 right.initial) ⊆
          parent.futureReachable (childState 0 state) :=
      parent.futureReachable_subset_of_mem hParentClosed hParentLeftState
        hBridgeStart
    have hRightReachSubset : rightReach.image (childState 1) ⊆
        parent.futureReachable (childState 0 state) :=
      hRightFromEntry.trans hRightEntryToRoot
    simp only [hCanBridge, if_true]
    apply Finset.Subset.antisymm
    · apply PendingAutomaton.futureReachable_subset_of_reference_closed
        parent (childState 0 state)
        (leftReach.image (childState 0) ∪
          rightReach.image (childState 1))
      · exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨state, hStateReach, rfl⟩)
      · intro source hSource target hReference
        simp only [Finset.mem_union, Finset.mem_image] at hSource ⊢
        rcases hSource with ⟨child, hChildReach, rfl⟩ |
            ⟨child, hChildReach, rfl⟩
        · rw [hLeftReferences child] at hReference
          rcases Finset.mem_union.mp hReference with hChildReference |
            hBridgeReference
          · rcases Finset.mem_image.mp hChildReference with
              ⟨childTarget, hChildTarget, rfl⟩
            left
            refine ⟨childTarget, ?_, rfl⟩
            exact hExecutionReachClosed hChildReach hChildTarget
          · by_cases hBridgeable :
                child ∈ left.skipping ∨ child ∈ left.completing
            · simp [hBridgeable] at hBridgeReference
              subst target
              right
              refine ⟨right.initial, ?_, rfl⟩
              exact rightPending.mem_futureReachable_self right.initial
            · simp [hBridgeable] at hBridgeReference
        · rw [hRightReferences child] at hReference
          rcases Finset.mem_image.mp hReference with
            ⟨childTarget, hChildTarget, rfl⟩
          right
          refine ⟨childTarget, ?_, rfl⟩
          exact hRightReachClosed hChildReach hChildTarget
    · intro target hTarget
      simp only [Finset.mem_union] at hTarget
      rcases hTarget with hLeftTarget | hRightTarget
      · exact hLeftReachSubset hLeftTarget
      · exact hRightReachSubset hRightTarget
  · simp only [hCanBridge, if_false, Finset.union_empty]
    apply Finset.Subset.antisymm
    · apply PendingAutomaton.futureReachable_subset_of_reference_closed
        parent (childState 0 state) (leftReach.image (childState 0))
      · exact Finset.mem_image.mpr ⟨state, hStateReach, rfl⟩
      · intro source hSource target hReference
        rcases Finset.mem_image.mp hSource with ⟨child, hChildReach, rfl⟩
        rw [hLeftReferences child] at hReference
        rcases Finset.mem_union.mp hReference with hChildReference |
          hBridgeReference
        · rcases Finset.mem_image.mp hChildReference with
            ⟨childTarget, hChildTarget, rfl⟩
          apply Finset.mem_image.mpr
          refine ⟨childTarget, ?_, rfl⟩
          exact hExecutionReachClosed hChildReach hChildTarget
        · by_cases hBridgeable :
              child ∈ left.skipping ∨ child ∈ left.completing
          · exact (hCanBridge
              ⟨child, hChildReach, hBridgeable⟩).elim
          · simp [hBridgeable] at hBridgeReference
    · exact hLeftReachSubset

private theorem buildSequenceAutomaton_completionWitness_right_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (reachable : Finset TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    (∃ completed ∈ reachable.image (.child 1),
        completed ∈ sequence.skipping ∨ completed ∈ sequence.completing) ↔
      ∃ completed ∈ reachable,
        completed ∈ right.skipping ∨ completed ∈ right.completing := by
  classical
  constructor
  · rintro ⟨tagged, hTagged, hCompleted⟩
    rcases Finset.mem_image.mp hTagged with
      ⟨completed, hReachable, hTagged⟩
    rw [← hTagged] at hCompleted
    refine ⟨completed, hReachable, ?_⟩
    by_cases hRight : right.initial ∈ right.completing <;>
      simpa [buildSequenceAutomaton, finishAutomatonFragment, childSkipping,
        childCompleting, childState, hRight] using hCompleted
  · rintro ⟨completed, hReachable, hCompleted⟩
    refine ⟨.child 1 completed, Finset.mem_image.mpr
      ⟨completed, hReachable, rfl⟩, ?_⟩
    by_cases hRight : right.initial ∈ right.completing <;>
      simpa [buildSequenceAutomaton, finishAutomatonFragment, childSkipping,
        childCompleting, childState, hRight] using hCompleted

private theorem buildSequenceAutomaton_completionWitness_left_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hLeftState : state ∈ left.states)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let leftExecution := sequenceExecutionAutomaton left
    let rightPending : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    let leftReach := leftExecution.futureReachable state
    let rightReach := rightPending.futureReachable right.initial
    let canBridge := ∃ completed ∈ leftReach,
      completed ∈ left.skipping ∨ completed ∈ left.completing
    let rightCanComplete := ∃ completed ∈ rightReach,
      completed ∈ right.skipping ∨ completed ∈ right.completing
    ((∃ completed ∈ parent.futureReachable (.child 0 state),
        completed ∈ sequence.skipping ∨ completed ∈ sequence.completing) ↔
      canBridge ∧ rightCanComplete) := by
  classical
  let sequence := buildSequenceAutomaton signature left right
  let parent : PendingAutomaton :=
    { states := sequence.states, edges := sequence.edges }
  let leftExecution := sequenceExecutionAutomaton left
  let rightPending : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  let leftReach := leftExecution.futureReachable state
  let rightReach := rightPending.futureReachable right.initial
  let canBridge := ∃ completed ∈ leftReach,
    completed ∈ left.skipping ∨ completed ∈ left.completing
  let rightCanComplete := ∃ completed ∈ rightReach,
    completed ∈ right.skipping ∨ completed ∈ right.completing
  change ((∃ completed ∈ parent.futureReachable (.child 0 state),
      completed ∈ sequence.skipping ∨ completed ∈ sequence.completing) ↔
    canBridge ∧ rightCanComplete)
  rw [buildSequenceAutomaton_futureReachable_left signature left right state
    hLeftState hLeftTargets hRightTargets hRightInitial]
  have hRightSelf : right.initial ∈ rightReach := by
    exact rightPending.mem_futureReachable_self right.initial
  constructor
  · rintro ⟨completed, hReachable, hCompleted⟩
    by_cases hBridge : canBridge
    · have hBridgeExpanded : ∃ completed ∈
          (sequenceExecutionAutomaton left).futureReachable state,
          completed ∈ left.skipping ∨ completed ∈ left.completing := by
        simpa [canBridge, leftReach, leftExecution] using hBridge
      simp only [hBridgeExpanded, if_true, Finset.mem_union,
        Finset.mem_image]
        at hReachable
      constructor
      · exact hBridge
      · rcases hReachable with ⟨child, hChild, hTagged⟩ |
            ⟨child, hChild, hTagged⟩
        · rw [← hTagged] at hCompleted
          have hFields : child ∈ left.completing ∧
              right.initial ∈ right.completing := by
            by_cases hRight : right.initial ∈ right.completing
            · simpa [sequence, buildSequenceAutomaton,
                finishAutomatonFragment, childSkipping, childCompleting,
                childState, hRight] using hCompleted
            · simp [sequence, buildSequenceAutomaton,
                finishAutomatonFragment, childSkipping, childCompleting,
                childState, hRight] at hCompleted
          exact ⟨right.initial, hRightSelf, Or.inr hFields.2⟩
        · rw [← hTagged] at hCompleted
          refine ⟨child, hChild, ?_⟩
          by_cases hRight : right.initial ∈ right.completing <;>
            simpa [sequence, buildSequenceAutomaton,
              finishAutomatonFragment, childSkipping, childCompleting,
              childState, hRight] using hCompleted
    · have hBridgeExpanded : ¬ ∃ completed ∈
          (sequenceExecutionAutomaton left).futureReachable state,
          completed ∈ left.skipping ∨ completed ∈ left.completing := by
        simpa [canBridge, leftReach, leftExecution] using hBridge
      simp only [hBridgeExpanded, if_false, Finset.union_empty,
        Finset.mem_image]
        at hReachable
      rcases hReachable with ⟨child, hChild, hTagged⟩
      rw [← hTagged] at hCompleted
      have hLeftComplete : child ∈ left.completing := by
        by_cases hRight : right.initial ∈ right.completing
        · simpa [sequence, buildSequenceAutomaton,
            finishAutomatonFragment, childSkipping, childCompleting,
            childState, hRight] using hCompleted
        · simp [sequence, buildSequenceAutomaton,
            finishAutomatonFragment, childSkipping, childCompleting,
            childState, hRight] at hCompleted
      exact (hBridge ⟨child, hChild, Or.inr hLeftComplete⟩).elim
  · rintro ⟨hBridge, child, hChild, hCompleted⟩
    refine ⟨.child 1 child, ?_, ?_⟩
    · have hBridgeExpanded : ∃ completed ∈
          (sequenceExecutionAutomaton left).futureReachable state,
          completed ∈ left.skipping ∨ completed ∈ left.completing := by
        simpa [canBridge, leftReach, leftExecution] using hBridge
      simp only [hBridgeExpanded, if_true, Finset.mem_union,
        Finset.mem_image]
      exact Or.inr ⟨child, hChild, rfl⟩
    · by_cases hRight : right.initial ∈ right.completing <;>
        simpa [sequence, buildSequenceAutomaton,
          finishAutomatonFragment, childSkipping, childCompleting,
          childState, hRight] using hCompleted

/-- Future offers at a tagged sequence-left state are the offers of the
child's non-clock execution closure, together with the right-entry menu
exactly when that closure can cross either sequence bridge. -/
private theorem buildSequenceAutomaton_computeFuture_left_formula
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hLeftState : state ∈ left.states)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let execution := sequenceExecutionAutomaton left
    let rightPending : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    let leftReach := execution.futureReachable state
    let canBridge := ∃ completed ∈ leftReach,
      completed ∈ left.skipping ∨ completed ∈ left.completing
    computeFuture parent (.child 0 state) =
      computeFuture execution state ∪
        if canBridge then computeFuture rightPending right.initial else ∅ := by
  classical
  let sequence := buildSequenceAutomaton signature left right
  let parent : PendingAutomaton :=
    { states := sequence.states, edges := sequence.edges }
  let execution := sequenceExecutionAutomaton left
  let rightPending : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  let leftReach := execution.futureReachable state
  let rightReach := rightPending.futureReachable right.initial
  let canBridge := ∃ completed ∈ leftReach,
    completed ∈ left.skipping ∨ completed ∈ left.completing
  change computeFuture parent (childState 0 state) =
    computeFuture execution state ∪
      if canBridge then computeFuture rightPending right.initial else ∅
  have hReach := buildSequenceAutomaton_futureReachable_left signature left
    right state hLeftState hLeftTargets hRightTargets hRightInitial
  have hReach' : parent.futureReachable (childState 0 state) =
      leftReach.image (childState 0) ∪
        if canBridge then rightReach.image (childState 1) else ∅ := by
    simpa [sequence, parent, execution, rightPending, leftReach, rightReach,
      canBridge] using hReach
  have hLeftOffers : ∀ child,
      parent.offersAt (childState 0 child) = execution.offersAt child := by
    intro child
    exact buildSequenceAutomaton_offersAt_left signature left right child
  have hRightOffers : ∀ child,
      parent.offersAt (childState 1 child) = rightPending.offersAt child := by
    intro child
    exact buildSequenceAutomaton_offersAt_right signature left right child
  unfold computeFuture
  change (parent.futureReachable (childState 0 state)).biUnion
      parent.offersAt =
        leftReach.biUnion execution.offersAt ∪
          if canBridge then rightReach.biUnion rightPending.offersAt else ∅
  rw [hReach']
  by_cases hCanBridge : canBridge
  · simp only [hCanBridge, if_true]
    have hBiUnion :
        (leftReach.image (childState 0) ∪
            rightReach.image (childState 1)).biUnion parent.offersAt =
          (leftReach.image (childState 0)).biUnion parent.offersAt ∪
            (rightReach.image (childState 1)).biUnion parent.offersAt := by
      ext action
      simp only [Finset.mem_biUnion, Finset.mem_union]
      constructor
      · rintro ⟨source, hSource, hOffer⟩
        rcases hSource with hLeftSource | hRightSource
        · exact Or.inl ⟨source, hLeftSource, hOffer⟩
        · exact Or.inr ⟨source, hRightSource, hOffer⟩
      · rintro (⟨source, hSource, hOffer⟩ |
          ⟨source, hSource, hOffer⟩)
        · exact ⟨source, Or.inl hSource, hOffer⟩
        · exact ⟨source, Or.inr hSource, hOffer⟩
    rw [hBiUnion]
    rw [PendingAutomaton.biUnion_offersAt_image_of_embedding execution parent
        (childState 0) hLeftOffers leftReach,
      PendingAutomaton.biUnion_offersAt_image_of_embedding rightPending parent
        (childState 1) hRightOffers rightReach]
  · simp only [hCanBridge, if_false, Finset.union_empty,
      Finset.biUnion_empty]
    exact PendingAutomaton.biUnion_offersAt_image_of_embedding execution
      parent (childState 0) hLeftOffers leftReach

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
  sorry
/-
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
-/

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

private theorem allVariablesBound_parallelTypeBranches
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

private theorem computeFuture_eq_empty_of_offersAt_eq_empty
    (automaton : PendingAutomaton)
    (hOffers : ∀ state, automaton.offersAt state = ∅)
    (state : TypeAutomatonState) :
    computeFuture automaton state = ∅ := by
  unfold computeFuture
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro action hAction
  rcases Finset.mem_biUnion.mp hAction with ⟨reached, _, hOffer⟩
  rw [hOffers reached] at hOffer
  simp at hOffer

private theorem sequenceExecutionAutomaton_offersAt_eq_empty
    (fragment : AutomatonFragment) (state : TypeAutomatonState)
    (hEdges : ∀ edge ∈ fragment.edges, edge.source = state →
      edge.current = ∅ ∧ edge.label ≠ .future) :
    (sequenceExecutionAutomaton fragment).offersAt state = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro action hAction
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter] at hAction
  rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
  simp only [sequenceExecutionAutomaton, Finset.mem_image] at hEdge
  rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
  have hFields := hEdges childEdge hChildEdge hSource
  rcases hFields with ⟨hCurrent, hNotFuture⟩
  cases hLabel : childEdge.label with
  | future => exact (hNotFuture hLabel).elim
  | visible label =>
      simp [hLabel, hCurrent, AutomatonConstructionLabel.semantic] at hOffer
  | «variable» name =>
      simp [hLabel, hCurrent, AutomatonConstructionLabel.semantic,
        TypeLabel.silent] at hOffer

private theorem compilationSequenceExecutionCorrect_skip
    (signature : TypeAlphabet) :
    CompilationSequenceExecutionCorrect signature .skip := by
  intro state residual hRelated
  cases hRelated
  constructor
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro action hAction
    unfold computeFuture at hAction
    simp only [Finset.mem_biUnion] at hAction
    rcases hAction with ⟨reached, _, hOffer⟩
    simp [sequenceExecutionAutomaton, PendingAutomaton.offersAt,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
      at hOffer
  · constructor
    · intro _
      simp [PactType.CanCompleteBeforeTock]
    · intro _
      refine ⟨.root,
        PendingAutomaton.mem_futureReachable_self _ .root, ?_⟩
      simp [typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment]

private theorem compilationSequenceExecutionCorrect_progress
    (signature : TypeAlphabet) (pid : ProcId) :
    CompilationSequenceExecutionCorrect signature (.progress pid) := by
  intro state residual hRelated
  cases hRelated with
  | progress_source | progress_final =>
      constructor
      · apply computeFuture_eq_empty_of_offersAt_eq_empty
        intro reached
        apply sequenceExecutionAutomaton_offersAt_eq_empty
        intro edge hEdge hSource
        simp only [typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
          at hEdge
        rcases hEdge with ⟨environment, _, rfl⟩ |
          ⟨environment, _, rfl⟩ <;> simp
      · constructor
        · intro _
          simp [PactType.CanCompleteBeforeTock]
        · intro _
          refine ⟨_, PendingAutomaton.mem_futureReachable_self _ _, ?_⟩
          simp [typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]

private theorem compilationSequenceExecutionCorrect_tock
    (signature : TypeAlphabet) :
    CompilationSequenceExecutionCorrect signature .tock := by
  intro state residual hRelated
  cases hRelated with
  | cycle_source =>
      constructor
      · apply computeFuture_eq_empty_of_offersAt_eq_empty
        intro reached
        apply sequenceExecutionAutomaton_offersAt_eq_empty
        intro edge hEdge hSource
        simp only [typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
          at hEdge
        rcases hEdge with hAction | hFinal
        · rcases hAction with ⟨environment, _, rfl⟩
          split <;> simp
        · rcases hFinal with ⟨environment, _, rfl⟩
          simp
      · constructor
        · rintro ⟨completed, hReachable, hCompleted⟩
          let fragment := compileTypeFuel signature
            (typeCompilationFuel PactType.tock) PactType.tock
          let execution := sequenceExecutionAutomaton fragment
          have hTargets : fragment.FutureTargetsInStates := by
            exact compileTypeFuel_futureTargetsInStates signature
              (typeCompilationFuel PactType.tock) PactType.tock
                (typeCompilationFuel_sufficient PactType.tock)
          have hClosed : execution.ReferencesClosed :=
            sequenceExecutionAutomaton_referencesClosed fragment hTargets
          have hRoot : TypeAutomatonState.root ∈ execution.states := by
            simp [execution, fragment, sequenceExecutionAutomaton,
              typeCompilationFuel, compileTypeFuel,
              finishAutomatonFragment]
          have hReachSubset : execution.futureReachable .root ⊆
              {.root} := by
            apply execution.futureReachable_subset_of_reference_closed
            · simp
            · intro source hSource target hReference
              simp only [Finset.mem_singleton] at hSource ⊢
              subst source
              simp only [PendingAutomaton.referencedStates,
                Finset.mem_biUnion, Finset.mem_filter] at hReference
              rcases hReference with
                ⟨edge, ⟨hEdge, hEdgeSource⟩, hFuture⟩
              simp only [execution, fragment, sequenceExecutionAutomaton,
                Finset.mem_image] at hEdge
              rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
              simp only [typeCompilationFuel, compileTypeFuel,
                finishAutomatonFragment, Finset.mem_union,
                Finset.mem_image] at hChildEdge
              rcases hChildEdge with hAction | hFinalEdge
              · rcases hAction with ⟨environment, _, rfl⟩
                by_cases hClock : environment.clock = true
                · simp [hClock, AutomatonConstructionLabel.semantic]
                    at hFuture
                · simpa [hClock, AutomatonConstructionLabel.semantic,
                    TypeLabel.silent] using hFuture
              · rcases hFinalEdge with ⟨environment, _, rfl⟩
                simp at hEdgeSource
          have hCompletedRoot : completed = .root := by
            simpa [execution, fragment] using hReachSubset hReachable
          subst completed
          simp [fragment, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment] at hCompleted
        · intro hComplete
          simp [PactType.CanCompleteBeforeTock] at hComplete
  | cycle_final =>
      constructor
      · apply computeFuture_eq_empty_of_offersAt_eq_empty
        intro reached
        apply sequenceExecutionAutomaton_offersAt_eq_empty
        intro edge hEdge hSource
        simp only [typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
          at hEdge
        rcases hEdge with hAction | hFinal
        · rcases hAction with ⟨environment, _, rfl⟩
          split <;> simp
        · rcases hFinal with ⟨environment, _, rfl⟩
          simp
      · constructor
        · intro _
          simp [PactType.CanCompleteBeforeTock]
        · intro _
          refine ⟨.final,
            PendingAutomaton.mem_futureReachable_self _ .final, ?_⟩
          simp [typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]

private theorem compilationSequenceExecutionCorrect_message
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CompilationSequenceExecutionCorrect signature (.message msg dir) := by
  let processType := PactType.message msg dir
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  let execution := sequenceExecutionAutomaton fragment
  have hTargets : fragment.FutureTargetsInStates := by
    exact compileTypeFuel_futureTargetsInStates signature
      (typeCompilationFuel processType) processType
        (typeCompilationFuel_sufficient processType)
  have hClosed : execution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed fragment hTargets
  have hRoot : TypeAutomatonState.root ∈ execution.states := by
    simp [execution, fragment, processType, sequenceExecutionAutomaton,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
  have hFinal : TypeAutomatonState.final ∈ execution.states := by
    simp [execution, fragment, processType, sequenceExecutionAutomaton,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
  have hExecutionStates : execution.states = {.root, .final} := by
    ext candidate
    simp only [execution, fragment, processType, sequenceExecutionAutomaton,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image]
    constructor
    · intro hCandidate
      rcases hCandidate with (rfl | rfl) | ⟨edge, hEdge, rfl⟩
      · simp
      · simp
      · rcases hEdge with (hFiring | hWaiting) | hFinalEdge
        · rcases hFiring with ⟨environment, _, rfl⟩
          simp
        · rcases hWaiting with ⟨environment, _, rfl⟩
          simp
        · rcases hFinalEdge with ⟨environment, _, rfl⟩
          simp
    · intro hCandidate
      exact Or.inl hCandidate
  have hOffersRoot : execution.offersAt .root = {(msg, dir)} := by
    ext action
    constructor
    · intro hAction
      simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
        Finset.mem_filter] at hAction
      rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
      simp only [execution, fragment, processType,
        sequenceExecutionAutomaton, Finset.mem_image] at hEdge
      rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
      simp only [typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
        at hChildEdge
      rcases hChildEdge with (hFiring | hWaiting) | hFinalEdge
      · rcases hFiring with ⟨environment, _, rfl⟩
        have hNotTock : TypeLabel.message msg dir ≠ TypeLabel.tock := by
          simp [TypeLabel.message]
        simp [AutomatonConstructionLabel.semantic, hNotTock] at hOffer
        simpa [typeFutureOffers, typeFutureOffersFuel] using hOffer
      · rcases hWaiting with ⟨environment, _, rfl⟩
        have hNotTock : TypeLabel.silent ≠ TypeLabel.tock := by
          simp [TypeLabel.silent]
        simp [AutomatonConstructionLabel.semantic, hNotTock] at hOffer
        simpa [typeFutureOffers, typeFutureOffersFuel] using hOffer
      · rcases hFinalEdge with ⟨environment, _, rfl⟩
        simp at hSource
    · intro hAction
      simp only [Finset.mem_singleton] at hAction
      subst action
      simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
        Finset.mem_filter]
      let environment := TypeEnvironment.empty
      let childEdge : PendingAutomatonEdge :=
        { source := .root
          environment := environment
          label := .visible TypeLabel.silent
          current := {(msg, dir)}
          future := .explicit ∅
          target := .root }
      let edge : PendingAutomatonEdge :=
        { source := childEdge.source
          environment := childEdge.environment
          label := childEdge.label
          current := childEdge.current
          future := .at childEdge.target childEdge.current
          target := childEdge.target }
      refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
      · simp only [edge, execution, sequenceExecutionAutomaton,
          Finset.mem_image]
        refine ⟨childEdge, ?_, rfl⟩
        simp [childEdge, fragment, processType, typeCompilationFuel,
          compileTypeFuel, finishAutomatonFragment, environment,
          TypeAlphabet.localEnvironments, TypeEnvironment.empty,
          TypeEnvironment.hasNeed]
      · simp [edge, childEdge, AutomatonConstructionLabel.semantic,
          TypeLabel.silent]
  have hOffersFinal : execution.offersAt .final = ∅ := by
    apply sequenceExecutionAutomaton_offersAt_eq_empty
    intro edge hEdge hSource
    simp only [fragment, processType, typeCompilationFuel,
      compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
      Finset.mem_image] at hEdge
    rcases hEdge with (hFiring | hWaiting) | hFinalEdge
    · rcases hFiring with ⟨environment, _, rfl⟩
      simp at hSource
    · rcases hWaiting with ⟨environment, _, rfl⟩
      simp at hSource
    · rcases hFinalEdge with ⟨environment, _, rfl⟩
      simp
  intro state residual hRelated
  cases hRelated with
  | message_source =>
      constructor
      · ext action
        constructor
        · intro hAction
          unfold computeFuture at hAction
          rcases Finset.mem_biUnion.mp hAction with
            ⟨reached, hReachable, hOffer⟩
          have hReachState : reached ∈ execution.states :=
            (execution.futureReachable_subset_of_reference_closed .root
              execution.states hRoot
                (fun source hSource => hClosed source hSource)) hReachable
          have hCases : reached = .root ∨ reached = .final := by
            rw [hExecutionStates] at hReachState
            simpa using hReachState
          rcases hCases with rfl | rfl
          · rw [hOffersRoot] at hOffer
            simpa [typeFutureOffers, typeFutureOffersFuel] using hOffer
          · rw [hOffersFinal] at hOffer
            simp at hOffer
        · intro hAction
          simp only [typeFutureOffers, typeFutureOffersFuel,
            Finset.mem_singleton] at hAction
          subst action
          unfold computeFuture
          apply Finset.mem_biUnion.mpr
          refine ⟨.root, execution.mem_futureReachable_self .root, ?_⟩
          rw [hOffersRoot]
          simp
      · constructor
        · intro _
          simp [PactType.CanCompleteBeforeTock]
        · intro _
          refine ⟨.root, execution.mem_futureReachable_self .root, ?_⟩
          simp [fragment, processType, typeCompilationFuel,
            compileTypeFuel, finishAutomatonFragment]
  | message_final =>
      constructor
      · have hReachSubset : execution.futureReachable .final ⊆
            {.final} := by
          apply execution.futureReachable_subset_of_reference_closed
          · simp
          · intro source hSource target hReference
            simp only [Finset.mem_singleton] at hSource ⊢
            subst source
            simp only [PendingAutomaton.referencedStates,
              Finset.mem_biUnion, Finset.mem_filter] at hReference
            rcases hReference with ⟨edge, ⟨hEdge, hSource⟩, hFuture⟩
            simp only [execution, sequenceExecutionAutomaton,
              Finset.mem_image] at hEdge
            rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
            simp only [fragment, processType, typeCompilationFuel,
              compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
              Finset.mem_image] at hChildEdge
            rcases hChildEdge with (hFiring | hWaiting) | hFinalEdge
            · rcases hFiring with ⟨environment, _, rfl⟩
              simp at hSource
            · rcases hWaiting with ⟨environment, _, rfl⟩
              simp at hSource
            · rcases hFinalEdge with ⟨environment, _, rfl⟩
              simpa [AutomatonConstructionLabel.semantic,
                TypeLabel.silent] using hFuture
        unfold computeFuture
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro action hAction
        rcases Finset.mem_biUnion.mp hAction with
          ⟨reached, hReachable, hOffer⟩
        have hReachedFinal : reached = .final := by
          simpa using hReachSubset hReachable
        subst reached
        rw [hOffersFinal] at hOffer
        simp at hOffer
      · constructor
        · intro _
          simp [PactType.CanCompleteBeforeTock]
        · intro _
          refine ⟨.final, execution.mem_futureReachable_self .final, ?_⟩
          simp [fragment, processType, typeCompilationFuel,
            compileTypeFuel, finishAutomatonFragment]

private theorem compilationSequenceExecutionCorrect_choice
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationSequenceExecutionCorrect signature left)
    (hRight : CompilationSequenceExecutionCorrect signature right) :
    CompilationSequenceExecutionCorrect signature (.choice left right) := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let parentFragment := buildChoiceAutomaton signature leftFragment
    rightFragment TypeLabel.silent TypeLabel.silent
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
  have hLeftTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hLeftInitial : leftFragment.initial ∈ leftFragment.states :=
    compileTypeFuel_initial_mem signature fuel left hLeftFuel
  have hRightInitial : rightFragment.initial ∈ rightFragment.states :=
    compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hParent : compileTypeFuel signature
      (typeCompilationFuel (.choice left right)) (.choice left right) =
      parentFragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hLeftRootCanonical := hLeft _ left
    (compileType_initial_relation signature left)
  have hRightRootCanonical := hRight _ right
    (compileType_initial_relation signature right)
  have hLeftRoot :
      computeFuture (sequenceExecutionAutomaton leftFragment)
          leftFragment.initial = typeFutureOffers left ∧
        ((∃ completed ∈
              (sequenceExecutionAutomaton leftFragment).futureReachable
                leftFragment.initial,
              completed ∈ leftFragment.skipping ∨
                completed ∈ leftFragment.completing) ↔
          left.CanCompleteBeforeTock = true) := by
    simpa [CompilationSequenceExecutionCorrect, leftFragment, hLeftStable,
      compileType] using hLeftRootCanonical
  have hRightRoot :
      computeFuture (sequenceExecutionAutomaton rightFragment)
          rightFragment.initial = typeFutureOffers right ∧
        ((∃ completed ∈
              (sequenceExecutionAutomaton rightFragment).futureReachable
                rightFragment.initial,
              completed ∈ rightFragment.skipping ∨
                completed ∈ rightFragment.completing) ↔
          right.CanCompleteBeforeTock = true) := by
    simpa [CompilationSequenceExecutionCorrect, rightFragment, hRightStable,
      compileType] using hRightRootCanonical
  intro state residual hRelated
  rw [hParent]
  cases hRelated with
  | choice_source =>
      constructor
      · rw [sequenceExecution_buildChoice_computeFuture_root signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent
          (by simp [TypeLabel.silent]) (by simp [TypeLabel.silent])
          hLeftTargets hRightTargets hLeftInitial hRightInitial,
        typeFutureOffers_choice]
        exact congrArg₂ (fun first second => first ∪ second)
          hLeftRoot.1 hRightRoot.1
      · have hRootWitness :=
          sequenceExecution_buildChoice_completionWitness_root_iff
            signature leftFragment rightFragment TypeLabel.silent
            TypeLabel.silent (by simp [TypeLabel.silent])
            (by simp [TypeLabel.silent]) hLeftTargets hRightTargets
            hLeftInitial hRightInitial
        refine hRootWitness.trans ((or_congr hLeftRoot.2
          hRightRoot.2).trans ?_)
        simp [PactType.CanCompleteBeforeTock]
  | choice_left _ _ _ childState hChildRelated =>
      have hStateCanonical := compilationStateCorrect_of_compilation
        signature left childState residual hChildRelated
      have hState : childState ∈ leftFragment.states := by
        simpa [leftFragment, hLeftStable] using hStateCanonical
      have hChildCanonical := hLeft childState residual hChildRelated
      have hChild :
          computeFuture (sequenceExecutionAutomaton leftFragment) childState =
              typeFutureOffers residual ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton leftFragment).futureReachable
                    childState,
                  completed ∈ leftFragment.skipping ∨
                    completed ∈ leftFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, leftFragment,
          hLeftStable] using hChildCanonical
      constructor
      · exact (sequenceExecution_buildChoice_computeFuture_left signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent
          hLeftTargets childState hState).trans hChild.1
      · rw [sequenceExecution_buildChoice_futureReachable_left signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent
          hLeftTargets childState hState]
        exact (buildChoiceAutomaton_completionWitness_left_iff signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent
          ((sequenceExecutionAutomaton leftFragment).futureReachable
            childState)).trans hChild.2
  | choice_right _ _ _ childState hChildRelated =>
      have hStateCanonical := compilationStateCorrect_of_compilation
        signature right childState residual hChildRelated
      have hState : childState ∈ rightFragment.states := by
        simpa [rightFragment, hRightStable] using hStateCanonical
      have hChildCanonical := hRight childState residual hChildRelated
      have hChild :
          computeFuture (sequenceExecutionAutomaton rightFragment) childState =
              typeFutureOffers residual ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton rightFragment).futureReachable
                    childState,
                  completed ∈ rightFragment.skipping ∨
                    completed ∈ rightFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, rightFragment,
          hRightStable] using hChildCanonical
      constructor
      · exact (sequenceExecution_buildChoice_computeFuture_right signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent
          hRightTargets childState hState).trans hChild.1
      · rw [sequenceExecution_buildChoice_futureReachable_right signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent
          hRightTargets childState hState]
        exact (buildChoiceAutomaton_completionWitness_right_iff signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent
          ((sequenceExecutionAutomaton rightFragment).futureReachable
            childState)).trans hChild.2
private theorem compilationSequenceExecutionCorrect_fairChoice
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeft : CompilationSequenceExecutionCorrect signature left)
    (hRight : CompilationSequenceExecutionCorrect signature right) :
    CompilationSequenceExecutionCorrect signature
      (.fairChoice bid left right) := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let parentFragment := buildChoiceAutomaton signature leftFragment
    rightFragment (TypeLabel.fair bid true) (TypeLabel.fair bid false)
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
  have hLeftTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hLeftInitial : leftFragment.initial ∈ leftFragment.states :=
    compileTypeFuel_initial_mem signature fuel left hLeftFuel
  have hRightInitial : rightFragment.initial ∈ rightFragment.states :=
    compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hParent : compileTypeFuel signature
      (typeCompilationFuel (.fairChoice bid left right))
        (.fairChoice bid left right) = parentFragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hLeftRootCanonical := hLeft _ left
    (compileType_initial_relation signature left)
  have hRightRootCanonical := hRight _ right
    (compileType_initial_relation signature right)
  have hLeftRoot :
      computeFuture (sequenceExecutionAutomaton leftFragment)
          leftFragment.initial = typeFutureOffers left ∧
        ((∃ completed ∈
              (sequenceExecutionAutomaton leftFragment).futureReachable
                leftFragment.initial,
              completed ∈ leftFragment.skipping ∨
                completed ∈ leftFragment.completing) ↔
          left.CanCompleteBeforeTock = true) := by
    simpa [CompilationSequenceExecutionCorrect, leftFragment, hLeftStable,
      compileType] using hLeftRootCanonical
  have hRightRoot :
      computeFuture (sequenceExecutionAutomaton rightFragment)
          rightFragment.initial = typeFutureOffers right ∧
        ((∃ completed ∈
              (sequenceExecutionAutomaton rightFragment).futureReachable
                rightFragment.initial,
              completed ∈ rightFragment.skipping ∨
                completed ∈ rightFragment.completing) ↔
          right.CanCompleteBeforeTock = true) := by
    simpa [CompilationSequenceExecutionCorrect, rightFragment, hRightStable,
      compileType] using hRightRootCanonical
  intro state residual hRelated
  rw [hParent]
  cases hRelated with
  | fair_source =>
      constructor
      · rw [sequenceExecution_buildChoice_computeFuture_root signature
          leftFragment rightFragment (TypeLabel.fair bid true)
          (TypeLabel.fair bid false) (by simp [TypeLabel.fair])
          (by simp [TypeLabel.fair]) hLeftTargets hRightTargets
          hLeftInitial hRightInitial,
        typeFutureOffers_fairChoice]
        exact congrArg₂ (fun first second => first ∪ second)
          hLeftRoot.1 hRightRoot.1
      · have hRootWitness :=
          sequenceExecution_buildChoice_completionWitness_root_iff
            signature leftFragment rightFragment (TypeLabel.fair bid true)
            (TypeLabel.fair bid false) (by simp [TypeLabel.fair])
            (by simp [TypeLabel.fair]) hLeftTargets hRightTargets
            hLeftInitial hRightInitial
        refine hRootWitness.trans ((or_congr hLeftRoot.2
          hRightRoot.2).trans ?_)
        simp [PactType.CanCompleteBeforeTock]
  | fair_left _ _ _ _ childState hChildRelated =>
      have hStateCanonical := compilationStateCorrect_of_compilation
        signature left childState residual hChildRelated
      have hState : childState ∈ leftFragment.states := by
        simpa [leftFragment, hLeftStable] using hStateCanonical
      have hChildCanonical := hLeft childState residual hChildRelated
      have hChild :
          computeFuture (sequenceExecutionAutomaton leftFragment) childState =
              typeFutureOffers residual ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton leftFragment).futureReachable
                    childState,
                  completed ∈ leftFragment.skipping ∨
                    completed ∈ leftFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, leftFragment,
          hLeftStable] using hChildCanonical
      constructor
      · exact (sequenceExecution_buildChoice_computeFuture_left signature
          leftFragment rightFragment (TypeLabel.fair bid true)
          (TypeLabel.fair bid false) hLeftTargets childState hState).trans
            hChild.1
      · rw [sequenceExecution_buildChoice_futureReachable_left signature
          leftFragment rightFragment (TypeLabel.fair bid true)
          (TypeLabel.fair bid false) hLeftTargets childState hState]
        exact (buildChoiceAutomaton_completionWitness_left_iff signature
          leftFragment rightFragment (TypeLabel.fair bid true)
          (TypeLabel.fair bid false)
          ((sequenceExecutionAutomaton leftFragment).futureReachable
            childState)).trans hChild.2
  | fair_right _ _ _ _ childState hChildRelated =>
      have hStateCanonical := compilationStateCorrect_of_compilation
        signature right childState residual hChildRelated
      have hState : childState ∈ rightFragment.states := by
        simpa [rightFragment, hRightStable] using hStateCanonical
      have hChildCanonical := hRight childState residual hChildRelated
      have hChild :
          computeFuture (sequenceExecutionAutomaton rightFragment) childState =
              typeFutureOffers residual ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton rightFragment).futureReachable
                    childState,
                  completed ∈ rightFragment.skipping ∨
                    completed ∈ rightFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, rightFragment,
          hRightStable] using hChildCanonical
      constructor
      · exact (sequenceExecution_buildChoice_computeFuture_right signature
          leftFragment rightFragment (TypeLabel.fair bid true)
          (TypeLabel.fair bid false) hRightTargets childState hState).trans
            hChild.1
      · rw [sequenceExecution_buildChoice_futureReachable_right signature
          leftFragment rightFragment (TypeLabel.fair bid true)
          (TypeLabel.fair bid false) hRightTargets childState hState]
        exact (buildChoiceAutomaton_completionWitness_right_iff signature
          leftFragment rightFragment (TypeLabel.fair bid true)
          (TypeLabel.fair bid false)
          ((sequenceExecutionAutomaton rightFragment).futureReachable
            childState)).trans hChild.2

private theorem compilationSequenceExecutionCorrect_sequence
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationSequenceExecutionCorrect signature left)
    (hRight : CompilationSequenceExecutionCorrect signature right) :
    CompilationSequenceExecutionCorrect signature (.seq left right) := by
  classical
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let rightExecutionFragment := sequenceExecutionFragment rightFragment
  let parentFragment := buildSequenceAutomaton signature leftFragment
    rightFragment
  let shadowFragment := buildSequenceAutomaton signature leftFragment
    rightExecutionFragment
  let parentExecution := sequenceExecutionAutomaton parentFragment
  let shadow : PendingAutomaton :=
    { states := shadowFragment.states, edges := shadowFragment.edges }
  let leftExecution := sequenceExecutionAutomaton leftFragment
  let rightExecution := sequenceExecutionAutomaton rightFragment
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
  have hLeftTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hRightExecutionTargets :
      rightExecutionFragment.FutureTargetsInStates :=
    sequenceExecutionFragment_futureTargetsInStates rightFragment
      hRightTargets
  have hLeftInitial : leftFragment.initial ∈ leftFragment.states :=
    compileTypeFuel_initial_mem signature fuel left hLeftFuel
  have hRightInitial : rightFragment.initial ∈ rightFragment.states :=
    compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hRightExecutionInitial : rightExecutionFragment.initial ∈
      rightExecutionFragment.states := by
    exact Finset.mem_union_left _ hRightInitial
  have hParentTargets : parentFragment.FutureTargetsInStates :=
    buildSequenceAutomaton_futureTargetsInStates signature leftFragment
      rightFragment hLeftTargets hRightTargets hRightInitial
  have hShadowTargets : shadowFragment.FutureTargetsInStates :=
    buildSequenceAutomaton_futureTargetsInStates signature leftFragment
      rightExecutionFragment hLeftTargets hRightExecutionTargets
      hRightExecutionInitial
  have hParentClosed : parentExecution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed parentFragment hParentTargets
  have hShadowClosed : shadow.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates shadowFragment
      hShadowTargets
  have hEdges : parentExecution.edges = shadow.edges := by
    exact sequenceExecution_buildSequence_edges signature leftFragment
      rightFragment
  have hSkipping : parentFragment.skipping = shadowFragment.skipping := by
    rfl
  have hCompleting : parentFragment.completing = shadowFragment.completing := by
    rfl
  have hParent : compileTypeFuel signature
      (typeCompilationFuel (.seq left right)) (.seq left right) =
      parentFragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hRightRootCanonical := hRight _ right
    (compileType_initial_relation signature right)
  have hRightRoot :
      computeFuture rightExecution rightFragment.initial =
          typeFutureOffers right ∧
        ((∃ completed ∈ rightExecution.futureReachable
              rightFragment.initial,
              completed ∈ rightFragment.skipping ∨
                completed ∈ rightFragment.completing) ↔
          right.CanCompleteBeforeTock = true) := by
    simpa [CompilationSequenceExecutionCorrect, rightExecution,
      rightFragment, hRightStable, compileType] using hRightRootCanonical
  intro state residual hRelated
  rw [hParent]
  cases hRelated with
  | sequence_left _ _ childResidual childQ hChildRelated =>
      have hLeftStateCanonical := compilationStateCorrect_of_compilation
        signature left childQ childResidual hChildRelated
      have hLeftState : childQ ∈ leftFragment.states := by
        simpa [leftFragment, hLeftStable] using hLeftStateCanonical
      have hChildCanonical := hLeft childQ childResidual hChildRelated
      have hChild :
          computeFuture leftExecution childQ =
              typeFutureOffers childResidual ∧
            ((∃ completed ∈ leftExecution.futureReachable childQ,
                  completed ∈ leftFragment.skipping ∨
                    completed ∈ leftFragment.completing) ↔
              childResidual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, leftExecution,
          leftFragment, hLeftStable] using hChildCanonical
      have hParentState : (.child 0 childQ : TypeAutomatonState) ∈
          parentExecution.states := by
        exact Finset.mem_union_left _ (by
          simp [parentFragment, buildSequenceAutomaton,
            finishAutomatonFragment, childStates, childState, hLeftState])
      have hShadowState : (.child 0 childQ : TypeAutomatonState) ∈
          shadow.states := by
        simp [shadow, shadowFragment, buildSequenceAutomaton,
          finishAutomatonFragment, childStates, childState, hLeftState]
      have hSameFuture := computeFuture_eq_of_same_edges parentExecution
        shadow hEdges hParentClosed hShadowClosed (.child 0 childQ)
          hParentState hShadowState
      have hSameReach := PendingAutomaton.futureReachable_eq_of_same_edges
        parentExecution shadow hEdges hParentClosed hShadowClosed
          (.child 0 childQ) hParentState hShadowState
      let canBridge := ∃ completed ∈ leftExecution.futureReachable childQ,
        completed ∈ leftFragment.skipping ∨
          completed ∈ leftFragment.completing
      have hBridgeIff : canBridge ↔
          childResidual.CanCompleteBeforeTock = true := by
        simpa [canBridge] using hChild.2
      have hFormula := buildSequenceAutomaton_computeFuture_left_formula
        signature leftFragment rightExecutionFragment childQ hLeftState
          hLeftTargets hRightExecutionTargets hRightExecutionInitial
      have hShadowFuture : computeFuture shadow (.child 0 childQ) =
          typeFutureOffers (.seq childResidual right) := by
        have hFormula' : computeFuture shadow (.child 0 childQ) =
            computeFuture leftExecution childQ ∪
              if canBridge then
                computeFuture rightExecution rightFragment.initial else ∅ := by
          simpa [shadow, shadowFragment, rightExecutionFragment,
            leftExecution, rightExecution, canBridge,
            sequenceExecutionFragment] using hFormula
        rw [hFormula', hChild.1, hRightRoot.1,
          typeFutureOffers_sequence]
        by_cases hComplete : childResidual.CanCompleteBeforeTock = true
        · have hCanBridge := hBridgeIff.mpr hComplete
          simp [hComplete, hCanBridge]
        · have hCannotBridge : ¬ canBridge := fun h =>
            hComplete (hBridgeIff.mp h)
          simp [hComplete, hCannotBridge]
      constructor
      · exact hSameFuture.trans hShadowFuture
      · rw [hSameReach, hSkipping, hCompleting]
        have hWitness := buildSequenceAutomaton_completionWitness_left_iff
          signature leftFragment rightExecutionFragment childQ
            hLeftState hLeftTargets hRightExecutionTargets
            hRightExecutionInitial
        refine hWitness.trans ((and_congr hChild.2 hRightRoot.2).trans ?_)
        simp [PactType.CanCompleteBeforeTock]
  | sequence_right _ _ _ childQ hChildRelated =>
      have hRightStateCanonical := compilationStateCorrect_of_compilation
        signature right childQ residual hChildRelated
      have hRightState : childQ ∈ rightFragment.states := by
        simpa [rightFragment, hRightStable] using hRightStateCanonical
      have hRightExecutionState : childQ ∈ rightExecution.states := by
        exact Finset.mem_union_left _ hRightState
      have hChildCanonical := hRight childQ residual hChildRelated
      have hChild :
          computeFuture rightExecution childQ =
              typeFutureOffers residual ∧
            ((∃ completed ∈ rightExecution.futureReachable childQ,
                  completed ∈ rightFragment.skipping ∨
                    completed ∈ rightFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, rightExecution,
          rightFragment, hRightStable] using hChildCanonical
      have hParentState : (.child 1 childQ : TypeAutomatonState) ∈
          parentExecution.states := by
        exact Finset.mem_union_left _ (by
          simp [parentFragment, buildSequenceAutomaton,
            finishAutomatonFragment, childStates, childState, hRightState])
      have hShadowState : (.child 1 childQ : TypeAutomatonState) ∈
          shadow.states := by
        simp [shadow, shadowFragment, rightExecutionFragment,
          sequenceExecutionFragment, buildSequenceAutomaton,
          finishAutomatonFragment, childStates, childState,
          rightExecution, hRightExecutionState]
      have hSameFuture := computeFuture_eq_of_same_edges parentExecution
        shadow hEdges hParentClosed hShadowClosed (.child 1 childQ)
          hParentState hShadowState
      have hSameReach := PendingAutomaton.futureReachable_eq_of_same_edges
        parentExecution shadow hEdges hParentClosed hShadowClosed
          (.child 1 childQ) hParentState hShadowState
      have hRightCard : rightExecution.states.card ≤ shadow.states.card := by
        have hSubset : rightExecution.states.image (.child 1) ⊆
            shadow.states := by
          intro tagged hTagged
          rcases Finset.mem_image.mp hTagged with ⟨child, hState, rfl⟩
          simp [shadow, shadowFragment, rightExecutionFragment,
            sequenceExecutionFragment, buildSequenceAutomaton,
            finishAutomatonFragment, childStates, childState,
            rightExecution, hState]
        calc
          rightExecution.states.card =
              (rightExecution.states.image (.child 1)).card := by
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ shadow.states.card := Finset.card_le_card hSubset
      have hShadowFuture : computeFuture shadow (.child 1 childQ) =
          computeFuture rightExecution childQ := by
        exact buildSequenceAutomaton_computeFuture_right signature
          leftFragment rightExecutionFragment childQ
            (sequenceExecutionAutomaton_referencesClosed rightFragment
              hRightTargets) hRightExecutionState hRightCard
      have hShadowReach : shadow.futureReachable (.child 1 childQ) =
          (rightExecution.futureReachable childQ).image (.child 1) := by
        exact PendingAutomaton.futureReachable_eq_of_embedding rightExecution
          shadow (.child 1)
            (buildSequenceAutomaton_referencedStates_right signature
              leftFragment rightExecutionFragment)
            (sequenceExecutionAutomaton_referencesClosed rightFragment
              hRightTargets) childQ hRightExecutionState hRightCard
      constructor
      · exact hSameFuture.trans (hShadowFuture.trans hChild.1)
      · rw [hSameReach, hShadowReach, hSkipping, hCompleting]
        exact (buildSequenceAutomaton_completionWitness_right_iff signature
          leftFragment rightExecutionFragment
            (rightExecution.futureReachable childQ)).trans hChild.2

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
    (hLeftExecution : CompilationSequenceExecutionCorrect signature left)
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
    completed ∈ leftFragment.skipping ∨
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
  have hRightInitial : rightFragment.initial ∈ rightFragment.states :=
    compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hLeftTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hFormula := buildSequenceAutomaton_computeFuture_left_formula signature
    leftFragment rightFragment state hLeftState hLeftTargets hRightTargets
      hRightInitial
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
    have hInitialRelation := compileTypeFuel_initial_relation signature fuel
      right hRightFuel
    have hCanonical := hRight.future rightFragment.initial right
      hInitialRelation
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
          right hLeft hRight hLeftExecution childState childResidual
            hChildRelated
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

theorem compilationResolvedEdgeTargetsRelated_sequence
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftTargets : CompilationResolvedEdgeTargetsRelated signature left)
    (hRightTargets : CompilationResolvedEdgeTargetsRelated signature right) :
    CompilationResolvedEdgeTargetsRelated signature (.seq left right) := by
  intro source residual environment label offers target hRelated hEdge
  cases hRelated with
  | sequence_left _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_sequence_left_edge_cases signature left right
          hEdge with hChild | hBridge
      · rcases hChild with
          ⟨childTarget, childFuture, rfl, hChildEdge, _⟩
        obtain ⟨targetResidual, hTargetRelated⟩ :=
          hLeftTargets hChildRelated hChildEdge
        exact ⟨.seq targetResidual right,
          TypeCompilationRelation.sequence_left left right targetResidual
            childTarget hTargetRelated⟩
      · rcases hBridge with ⟨_, _, _, _, _, rfl⟩
        have hInitial : TypeCompilationRelation right
            (compileTypeFuel signature (typeCompilationFuel right) right).initial
            right :=
          compileTypeFuel_initial_relation signature
            (typeCompilationFuel right) right
            (typeCompilationFuel_sufficient right)
        exact ⟨right, TypeCompilationRelation.sequence_right left right
          right _ hInitial⟩
  | sequence_right _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_sequence_right_edge_cases signature left right
          hEdge with ⟨childTarget, rfl, hChildEdge⟩
      obtain ⟨targetResidual, hTargetRelated⟩ :=
        hRightTargets hChildRelated hChildEdge
      exact ⟨targetResidual,
        TypeCompilationRelation.sequence_right left right targetResidual
          childTarget hTargetRelated⟩

private theorem compileTypeFuel_choiceLike_root_target_cases
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary} {target : TypeAutomatonState}
    (hEdge : AutomatonFragment.HasResolvedEdge
      (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        selectionLeft selectionRight)
      .root environment label offers target) :
    target = .child 0 (compileTypeFuel signature
        (typeCompilationFuel left) left).initial ∨
      target = .child 1 (compileTypeFuel signature
        (typeCompilationFuel right) right).initial := by
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
  have hFields :=
    (buildChoiceAutomaton_root_hasResolvedEdge_iff signature leftFragment
      rightFragment selectionLeft selectionRight environment label offers
      target).mp (by simpa [fuel, leftFragment, rightFragment] using hEdge)
  rcases hFields with hSelected | hSelected
  · left
    simpa [hLeftStable] using hSelected.2.2.2.2
  · right
    simpa [hRightStable] using hSelected.2.2.2.2

private theorem compileTypeFuel_choiceLike_left_target_cases
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    {source target : TypeAutomatonState} {environment : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : AutomatonFragment.HasResolvedEdge
      (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        selectionLeft selectionRight)
      (.child 0 source) environment label offers target) :
    ∃ childTarget,
      target = .child 0 childTarget ∧
        AutomatonFragment.HasResolvedEdge
          (compileTypeFuel signature (typeCompilationFuel left) left)
          source environment label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    selectionLeft selectionRight
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment = compileTypeFuel signature
      (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hParent : fragment.HasResolvedEdge (.child 0 source) environment label
      offers target := by
    simpa [fragment, fuel, leftFragment, rightFragment] using hEdge
  rcases hParent with ⟨pending, hPending, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  rcases (buildChoiceAutomaton_outgoing_left signature leftFragment
      rightFragment selectionLeft selectionRight source pending).mp
      ⟨hPending, hSource⟩ with
    ⟨childEdge, hChildEdge, hChildSource, hPendingEq⟩
  have hTargetEq : target = .child 0 childEdge.target := by
    rw [hPendingEq] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  have hFixed : fragment.HasResolvedEdge (.child 0 source) environment label
      offers (.child 0 childEdge.target) := by
    simpa [hTargetEq] using (show fragment.HasResolvedEdge
      (.child 0 source) environment label offers target from
        ⟨pending, hPending, hSource, hEnvironment, hLabel, hCurrent,
          hFuture, hTarget⟩)
  have hChild :=
    (buildChoiceAutomaton_hasResolvedEdge_left_iff signature leftFragment
      rightFragment selectionLeft selectionRight source childEdge.target
      environment label offers hTargets).mp hFixed
  exact ⟨childEdge.target, hTargetEq, by simpa [hLeftStable] using hChild⟩

private theorem compileTypeFuel_choiceLike_right_target_cases
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    {source target : TypeAutomatonState} {environment : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : AutomatonFragment.HasResolvedEdge
      (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        selectionLeft selectionRight)
      (.child 1 source) environment label offers target) :
    ∃ childTarget,
      target = .child 1 childTarget ∧
        AutomatonFragment.HasResolvedEdge
          (compileTypeFuel signature (typeCompilationFuel right) right)
          source environment label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    selectionLeft selectionRight
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightStable : rightFragment = compileTypeFuel signature
      (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hParent : fragment.HasResolvedEdge (.child 1 source) environment label
      offers target := by
    simpa [fragment, fuel, leftFragment, rightFragment] using hEdge
  rcases hParent with ⟨pending, hPending, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  rcases (buildChoiceAutomaton_outgoing_right signature leftFragment
      rightFragment selectionLeft selectionRight source pending).mp
      ⟨hPending, hSource⟩ with
    ⟨childEdge, hChildEdge, hChildSource, hPendingEq⟩
  have hTargetEq : target = .child 1 childEdge.target := by
    rw [hPendingEq] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  have hFixed : fragment.HasResolvedEdge (.child 1 source) environment label
      offers (.child 1 childEdge.target) := by
    simpa [hTargetEq] using (show fragment.HasResolvedEdge
      (.child 1 source) environment label offers target from
        ⟨pending, hPending, hSource, hEnvironment, hLabel, hCurrent,
          hFuture, hTarget⟩)
  have hChild :=
    (buildChoiceAutomaton_hasResolvedEdge_right_iff signature leftFragment
      rightFragment selectionLeft selectionRight source childEdge.target
      environment label offers hTargets).mp hFixed
  exact ⟨childEdge.target, hTargetEq, by simpa [hRightStable] using hChild⟩

theorem compilationResolvedEdgeTargetsRelated_choice
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftTargets : CompilationResolvedEdgeTargetsRelated signature left)
    (hRightTargets : CompilationResolvedEdgeTargetsRelated signature right) :
    CompilationResolvedEdgeTargetsRelated signature (.choice left right) := by
  intro source residual environment label offers target hRelated hEdge
  have hParent : AutomatonFragment.HasResolvedEdge
      (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        TypeLabel.silent TypeLabel.silent)
      source environment label offers target := by
    simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using hEdge
  cases hRelated with
  | choice_source =>
      rcases compileTypeFuel_choiceLike_root_target_cases signature left right
          TypeLabel.silent TypeLabel.silent hParent with hSelected | hSelected
      · rw [hSelected]
        have hInitial := compileTypeFuel_initial_relation signature
          (typeCompilationFuel left) left (typeCompilationFuel_sufficient left)
        exact ⟨left, TypeCompilationRelation.choice_left left right left _
          hInitial⟩
      · rw [hSelected]
        have hInitial := compileTypeFuel_initial_relation signature
          (typeCompilationFuel right) right (typeCompilationFuel_sufficient right)
        exact ⟨right, TypeCompilationRelation.choice_right left right right _
          hInitial⟩
  | choice_left _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_choiceLike_left_target_cases signature left right
          TypeLabel.silent TypeLabel.silent hParent with
        ⟨childTarget, rfl, hChildEdge⟩
      obtain ⟨targetResidual, hTargetRelated⟩ :=
        hLeftTargets hChildRelated hChildEdge
      exact ⟨targetResidual, TypeCompilationRelation.choice_left left right
        targetResidual childTarget hTargetRelated⟩
  | choice_right _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_choiceLike_right_target_cases signature left right
          TypeLabel.silent TypeLabel.silent hParent with
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
  have hParent : AutomatonFragment.HasResolvedEdge
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
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) hParent with
        hSelected | hSelected
      · rw [hSelected]
        have hInitial := compileTypeFuel_initial_relation signature
          (typeCompilationFuel left) left (typeCompilationFuel_sufficient left)
        exact ⟨left, TypeCompilationRelation.fair_left bid left right left _
          hInitial⟩
      · rw [hSelected]
        have hInitial := compileTypeFuel_initial_relation signature
          (typeCompilationFuel right) right (typeCompilationFuel_sufficient right)
        exact ⟨right, TypeCompilationRelation.fair_right bid left right right _
          hInitial⟩
  | fair_left _ _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_choiceLike_left_target_cases signature left right
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) hParent with
        ⟨childTarget, rfl, hChildEdge⟩
      obtain ⟨targetResidual, hTargetRelated⟩ :=
        hLeftTargets hChildRelated hChildEdge
      exact ⟨targetResidual, TypeCompilationRelation.fair_left bid left right
        targetResidual childTarget hTargetRelated⟩
  | fair_right _ _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_choiceLike_right_target_cases signature left right
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
  intro source residual environment label offers target hRelated hEdge
  let bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
  let recursion := buildRecursionAutomaton signature name bodyFragment
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.recur name body)) (.recur name body) =
        recursion := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment] at hEdge
  cases hRelated with
  | recur_source =>
      rcases (buildRecursionAutomaton_root_hasResolvedEdge_iff signature name
          bodyFragment environment label offers target).mp hEdge with
        ⟨_, _, _, _, rfl⟩
      have hInitial : TypeCompilationRelation body bodyFragment.initial body :=
        compileTypeFuel_initial_relation signature (typeCompilationFuel body)
          body (typeCompilationFuel_sufficient body)
      exact ⟨body.replaceVar name (.recur name body),
        TypeCompilationRelation.recur_body name body body _ hInitial⟩
  | recur_body _ _ childResidual childState hChildRelated =>
      rcases (buildRecursionAutomaton_body_hasResolvedEdge_iff signature name
          bodyFragment childState environment label offers target).mp hEdge with
        hMarker | hBody
      · rcases hMarker with
          ⟨edge, _, _, _, _, _, _, _, rfl⟩
        have hInitial : TypeCompilationRelation body bodyFragment.initial body :=
          compileTypeFuel_initial_relation signature
            (typeCompilationFuel body) body
            (typeCompilationFuel_sufficient body)
        exact ⟨body.replaceVar name (.recur name body),
          TypeCompilationRelation.recur_body name body body _ hInitial⟩
      · rcases hBody with
          ⟨edge, hPending, hSource, _, hEnvironment, hLabel, _, _, rfl⟩
        let childOffers : TypeOfferSummary :=
          { current := edge.current
            future := match edge.future with
              | .explicit future => future
              | .at state removed =>
                  computeFuture
                    { states := bodyFragment.states,
                      edges := bodyFragment.edges } state \ removed }
        have hChildEdge : bodyFragment.HasResolvedEdge childState environment
            label childOffers edge.target := by
          refine ⟨edge, hPending, hSource, hEnvironment, hLabel, rfl, ?_, rfl⟩
          cases hSpec : edge.future <;> simp [childOffers, hSpec]
        obtain ⟨targetResidual, hTargetRelated⟩ :=
          hBodyTargets hChildRelated (by
            simpa [bodyFragment] using hChildEdge)
        exact ⟨targetResidual.replaceVar name (.recur name body),
          TypeCompilationRelation.recur_body name body targetResidual
            edge.target hTargetRelated⟩

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
      · apply compilationResolvedEdgeTargetsRelated_parallelTypeBranches
        intro entry hEntry
        have hEntrySize : sizeOf entry.2 <
            sizeOf (PactType.offer elseType branches) := by
          have hPair := List.sizeOf_lt_of_mem hEntry
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
      (.par left right interface)).HasResolvedEdge state env label offers target)
    (hTarget : TypeCompilationRelation (.par left right interface)
      target residual') :
    DecoratedTypeTransition env residual label offers residual' := by
  have hLeftTargets : CompilationResolvedEdgeTargetsRelated signature left := by
    intro source residual environment label offers target hRelated hEdge
    exact compilationResolvedEdgeTargetsRelated_all signature left hRelated
      hEdge
  have hRightTargets : CompilationResolvedEdgeTargetsRelated signature right := by
    intro source residual environment label offers target hRelated hEdge
    exact compilationResolvedEdgeTargetsRelated_all signature right hRelated
      hEdge
  have hLeftWitness : CompilationScopedResolvedOfferWitnessCorrect signature
      left := by
    intro residual state environment label actualOffers actualTarget hRelated
      hLocal hAvoids hActual witness hWitness hSemantic hSource hEnvironment
      hLabel
    exact (compilationScopedResolvedOfferWitnessCorrect_of_step_targets_visible
      signature left hLeft.scopedStep hLeftTargets
        (compilationPendingEdgesVisible_of_allVariablesBound signature left
          hLeftClosed)) hRelated hLocal hAvoids hActual witness hWitness
            hSemantic hSource hEnvironment hLabel
  have hRightWitness : CompilationScopedResolvedOfferWitnessCorrect signature
      right := by
    intro residual state environment label actualOffers actualTarget hRelated
      hLocal hAvoids hActual witness hWitness hSemantic hSource hEnvironment
      hLabel
    exact (compilationScopedResolvedOfferWitnessCorrect_of_step_targets_visible
      signature right hRight.scopedStep hRightTargets
        (compilationPendingEdgesVisible_of_allVariablesBound signature right
          hRightClosed)) hRelated hLocal hAvoids hActual witness hWitness
            hSemantic hSource hEnvironment hLabel
  exact parallel_resolved_edge_to_semantic_step signature left right interface
    hInterface hScoped hLeft.scopedStep hRight.scopedStep hLeftWitness
      hRightWitness hRelated hLocal hAvoids hEdge hTarget

private theorem compilationFragmentStepCorrect_parallel_leaf
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface) (hSignature : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hScoped : PactType.InterfaceScoped (.par left right interface))
    (hClosed : PactType.AllVariablesBound [] (.par left right interface))
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
    have hClosedFields := hClosed
    simp only [PactType.AllVariablesBound] at hClosedFields
    exact parallel_resolved_edge_to_semantic_step_leaf signature left right
      interface hSignature hInterface hScoped hClosedFields.1 hClosedFields.2
      hLeft hRight hRelated hLocal hAvoids hEdge hTarget

/-- Same-cycle execution correctness composes through a synchronized product.
The product's explicit observation edges expose both syntax menus immediately;
following an ordinary product transition can only decrease those menus, and a
completion reached after such transitions is transported back through the two
child execution invariants. -/
private theorem compilationSequenceExecutionCorrect_parallel_regular_leaf
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hLeftClosed : PactType.AllVariablesBound [] left)
    (hRightClosed : PactType.AllVariablesBound [] right)
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right) :
    CompilationSequenceExecutionCorrect signature
      (.par left right interface) := by
  classical
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildParallelAutomaton interface leftFragment rightFragment
  let execution := sequenceExecutionAutomaton fragment
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
  have hLeftTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hFragmentTargets : fragment.FutureTargetsInStates := by
    exact buildParallelAutomaton_futureTargetsInStates interface leftFragment
      rightFragment
  have hExecutionClosed : execution.ReferencesClosed := by
    exact sequenceExecutionAutomaton_referencesClosed fragment hFragmentTargets
  have hParent : compileTypeFuel signature
      (typeCompilationFuel (.par left right interface))
        (.par left right interface) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  intro state residual hRelated
  rw [hParent]
  cases hRelated with
  | parallel _ _ leftResidual rightResidual _ leftState rightState
      hLeftRelated hRightRelated =>
      have hLeftState : leftState ∈ leftFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          left leftState leftResidual hLeftRelated
        simpa [leftFragment, hLeftStable] using hCanonical
      have hRightState : rightState ∈ rightFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          right rightState rightResidual hRightRelated
        simpa [rightFragment, hRightStable] using hCanonical
      have hSourceState : (.pair leftState rightState : TypeAutomatonState) ∈
          execution.states := by
        apply Finset.mem_union_left
        simp [execution, fragment, buildParallelAutomaton,
          finishAutomatonFragment, hLeftState, hRightState]
      have hLeftAtSource := hLeft.execution leftState leftResidual hLeftRelated
      have hRightAtSource := hRight.execution rightState rightResidual
        hRightRelated
      have hLeftSourceExecution :
          computeFuture (sequenceExecutionAutomaton leftFragment) leftState =
              typeFutureOffers leftResidual ∧
            ((∃ completed ∈
                (sequenceExecutionAutomaton leftFragment).futureReachable
                  leftState,
                completed ∈ leftFragment.skipping ∨
                  completed ∈ leftFragment.completing) ↔
              leftResidual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, leftFragment, hLeftStable]
          using hLeftAtSource
      have hRightSourceExecution :
          computeFuture (sequenceExecutionAutomaton rightFragment) rightState =
              typeFutureOffers rightResidual ∧
            ((∃ completed ∈
                (sequenceExecutionAutomaton rightFragment).futureReachable
                  rightState,
                completed ∈ rightFragment.skipping ∨
                  completed ∈ rightFragment.completing) ↔
              rightResidual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, rightFragment,
          hRightStable] using hRightAtSource
      have hLeftSourceFuture : computeFuture
          { states := leftFragment.states, edges := leftFragment.edges }
          leftState = typeFutureOffers leftResidual := by
        have hCanonical := hLeft.future leftState leftResidual hLeftRelated
        simpa [leftFragment, hLeftStable] using hCanonical
      have hRightSourceFuture : computeFuture
          { states := rightFragment.states, edges := rightFragment.edges }
          rightState = typeFutureOffers rightResidual := by
        have hCanonical := hRight.future rightState rightResidual hRightRelated
        simpa [rightFragment, hRightStable] using hCanonical
      have hSourceOffers : execution.offersAt (.pair leftState rightState) =
          typeFutureOffers (.par leftResidual rightResidual interface) := by
        rw [show execution.offersAt (.pair leftState rightState) =
            hideOffers interface
              (computeFuture
                  { states := leftFragment.states, edges := leftFragment.edges }
                  leftState ∪
                computeFuture
                  { states := rightFragment.states,
                    edges := rightFragment.edges } rightState) by
          exact sequenceExecution_buildParallel_offersAt interface leftFragment
            rightFragment leftState rightState hLeftState hRightState
              hLeftTargets hRightTargets]
        rw [hLeftSourceFuture, hRightSourceFuture,
          typeFutureOffers_parallel]
        rfl
      have hLeftVisible : ∀ edge ∈ leftFragment.edges,
          edge.label ≠ .future → ∃ label, edge.label = .visible label := by
        have hCanonical := compilationPendingEdgesVisible_of_allVariablesBound
          signature left hLeftClosed
        simpa [leftFragment, hLeftStable] using hCanonical
      have hRightVisible : ∀ edge ∈ rightFragment.edges,
          edge.label ≠ .future → ∃ label, edge.label = .visible label := by
        have hCanonical := compilationPendingEdgesVisible_of_allVariablesBound
          signature right hRightClosed
        simpa [rightFragment, hRightStable] using hCanonical
      let represented := fun productState =>
        ∃ childLeft childRight childLeftResidual childRightResidual,
          productState = .pair childLeft childRight ∧
          TypeCompilationRelation left childLeft childLeftResidual ∧
          TypeCompilationRelation right childRight childRightResidual ∧
          (productState ∈ fragment.completing →
            (PactType.par leftResidual rightResidual
              interface).CanCompleteBeforeTock =
              true)
      have hParentCompleting := compilationCompletingCorrect_parallel signature
        left right interface hLeft.completing hRight.completing
      have hSourceRepresented : represented (.pair leftState rightState) := by
        refine ⟨leftState, rightState, leftResidual, rightResidual, rfl,
          hLeftRelated, hRightRelated, ?_⟩
        simpa only [hParent] using
          (hParentCompleting (.pair leftState rightState)
            (.par leftResidual rightResidual interface)
              (TypeCompilationRelation.parallel left right leftResidual
                rightResidual interface leftState rightState hLeftRelated
                  hRightRelated)).mp
      have hReferenceStep : ∀ productState ∈ execution.states,
          represented productState → ∀ target ∈
            execution.referencedStates productState,
            represented target ∧
              execution.offersAt target ⊆
                execution.offersAt productState := by
        intro productState hProductState hRepresented target hReference
        rcases hRepresented with
          ⟨childLeft, childRight, childLeftResidual, childRightResidual,
            rfl, hChildLeftRelated, hChildRightRelated, hCarriesCompletion⟩
        rcases sequenceExecution_buildParallel_reference_cases interface
            leftFragment rightFragment childLeft childRight target hReference
          with ⟨leftEdge, hLeftEdge, rightEdge, hRightEdge, hLeftSource,
            hRightSource, rfl, hLeftSemantic, hRightSemantic, hLeftNonClock,
              hRightNonClock⟩
        subst childLeft
        subst childRight
        have hCurrentLeftState : leftEdge.source ∈ leftFragment.states := by
          have hCanonical := compilationStateCorrect_of_compilation signature
            left leftEdge.source childLeftResidual hChildLeftRelated
          simpa [leftFragment, hLeftStable] using hCanonical
        have hCurrentRightState : rightEdge.source ∈ rightFragment.states := by
          have hCanonical := compilationStateCorrect_of_compilation signature
            right rightEdge.source childRightResidual hChildRightRelated
          simpa [rightFragment, hRightStable] using hCanonical
        have hCurrentLeftExecution := hLeft.execution leftEdge.source
          childLeftResidual hChildLeftRelated
        have hCurrentRightExecution := hRight.execution rightEdge.source
          childRightResidual hChildRightRelated
        have hCurrentLeftExecution' :
            computeFuture (sequenceExecutionAutomaton leftFragment)
                leftEdge.source = typeFutureOffers childLeftResidual ∧
              ((∃ completed ∈
                  (sequenceExecutionAutomaton leftFragment).futureReachable
                    leftEdge.source,
                  completed ∈ leftFragment.skipping ∨
                    completed ∈ leftFragment.completing) ↔
                childLeftResidual.CanCompleteBeforeTock = true) := by
          simpa [CompilationSequenceExecutionCorrect, leftFragment,
            hLeftStable] using hCurrentLeftExecution
        have hCurrentRightExecution' :
            computeFuture (sequenceExecutionAutomaton rightFragment)
                rightEdge.source = typeFutureOffers childRightResidual ∧
              ((∃ completed ∈
                  (sequenceExecutionAutomaton rightFragment).futureReachable
                    rightEdge.source,
                  completed ∈ rightFragment.skipping ∨
                    completed ∈ rightFragment.completing) ↔
                childRightResidual.CanCompleteBeforeTock = true) := by
          simpa [CompilationSequenceExecutionCorrect, rightFragment,
            hRightStable] using hCurrentRightExecution
        rcases resolvedAutomatonEdge_visible_of_pending_visible leftFragment
            hLeftVisible leftEdge hLeftEdge hLeftSemantic with
          ⟨leftLabel, hLeftLabel⟩
        rcases resolvedAutomatonEdge_visible_of_pending_visible rightFragment
            hRightVisible rightEdge hRightEdge hRightSemantic with
          ⟨rightLabel, hRightLabel⟩
        have hLeftResolved := hasResolvedEdge_of_mem_visible_resolved
          leftFragment leftEdge hLeftEdge leftLabel hLeftLabel
        have hRightResolved := hasResolvedEdge_of_mem_visible_resolved
          rightFragment rightEdge hRightEdge rightLabel hRightLabel
        obtain ⟨leftTargetResidual, hLeftTargetRelated⟩ :=
          compilationResolvedEdgeTargetsRelated_all signature left
            hChildLeftRelated (by
              simpa [leftFragment, hLeftStable] using hLeftResolved)
        obtain ⟨rightTargetResidual, hRightTargetRelated⟩ :=
          compilationResolvedEdgeTargetsRelated_all signature right
            hChildRightRelated (by
              simpa [rightFragment, hRightStable] using hRightResolved)
        have hLeftTargetState : leftEdge.target ∈ leftFragment.states := by
          have hCanonical := compilationStateCorrect_of_compilation signature
            left leftEdge.target leftTargetResidual hLeftTargetRelated
          simpa [leftFragment, hLeftStable] using hCanonical
        have hRightTargetState : rightEdge.target ∈ rightFragment.states := by
          have hCanonical := compilationStateCorrect_of_compilation signature
            right rightEdge.target rightTargetResidual hRightTargetRelated
          simpa [rightFragment, hRightStable] using hCanonical
        have hLeftReference :=
          sequenceExecution_resolvedEdge_target_referenced leftFragment
            leftEdge hLeftEdge hLeftSemantic hLeftNonClock
        have hRightReference :=
          sequenceExecution_resolvedEdge_target_referenced rightFragment
            rightEdge hRightEdge hRightSemantic hRightNonClock
        have hLeftExecutionClosed :=
          sequenceExecutionAutomaton_referencesClosed leftFragment hLeftTargets
        have hRightExecutionClosed :=
          sequenceExecutionAutomaton_referencesClosed rightFragment
            hRightTargets
        have hLeftReachable : leftEdge.target ∈
            (sequenceExecutionAutomaton leftFragment).futureReachable
              leftEdge.source :=
          PendingAutomaton.referencedStates_subset_futureReachable
            (sequenceExecutionAutomaton leftFragment) leftEdge.source
              hLeftExecutionClosed
                (Finset.mem_union_left _ hCurrentLeftState) hLeftReference
        have hRightReachable : rightEdge.target ∈
            (sequenceExecutionAutomaton rightFragment).futureReachable
              rightEdge.source :=
          PendingAutomaton.referencedStates_subset_futureReachable
            (sequenceExecutionAutomaton rightFragment) rightEdge.source
              hRightExecutionClosed
                (Finset.mem_union_left _ hCurrentRightState) hRightReference
        have hLeftAtTarget := hLeft.execution leftEdge.target
          leftTargetResidual hLeftTargetRelated
        have hRightAtTarget := hRight.execution rightEdge.target
          rightTargetResidual hRightTargetRelated
        have hLeftTargetExecution :
            computeFuture (sequenceExecutionAutomaton leftFragment)
                leftEdge.target = typeFutureOffers leftTargetResidual ∧
              ((∃ completed ∈
                  (sequenceExecutionAutomaton leftFragment).futureReachable
                    leftEdge.target,
                  completed ∈ leftFragment.skipping ∨
                    completed ∈ leftFragment.completing) ↔
                leftTargetResidual.CanCompleteBeforeTock = true) := by
          simpa [CompilationSequenceExecutionCorrect, leftFragment,
            hLeftStable] using hLeftAtTarget
        have hRightTargetExecution :
            computeFuture (sequenceExecutionAutomaton rightFragment)
                rightEdge.target = typeFutureOffers rightTargetResidual ∧
              ((∃ completed ∈
                  (sequenceExecutionAutomaton rightFragment).futureReachable
                    rightEdge.target,
                  completed ∈ rightFragment.skipping ∨
                    completed ∈ rightFragment.completing) ↔
                rightTargetResidual.CanCompleteBeforeTock = true) := by
          simpa [CompilationSequenceExecutionCorrect, rightFragment,
            hRightStable] using hRightAtTarget
        have hLeftMenuSubset : typeFutureOffers leftTargetResidual ⊆
            typeFutureOffers childLeftResidual := by
          rw [← hLeftTargetExecution.1, ← hCurrentLeftExecution'.1]
          exact computeFuture_subset_of_mem_futureReachable
            (sequenceExecutionAutomaton leftFragment) hLeftExecutionClosed
              (Finset.mem_union_left _ hCurrentLeftState) hLeftReachable
        have hRightMenuSubset : typeFutureOffers rightTargetResidual ⊆
            typeFutureOffers childRightResidual := by
          rw [← hRightTargetExecution.1, ← hCurrentRightExecution'.1]
          exact computeFuture_subset_of_mem_futureReachable
            (sequenceExecutionAutomaton rightFragment) hRightExecutionClosed
              (Finset.mem_union_left _ hCurrentRightState) hRightReachable
        have hTargetOffers : execution.offersAt
            (.pair leftEdge.target rightEdge.target) =
              typeFutureOffers
                (.par leftTargetResidual rightTargetResidual interface) := by
          rw [show execution.offersAt
              (.pair leftEdge.target rightEdge.target) =
              hideOffers interface
                (computeFuture
                    { states := leftFragment.states,
                      edges := leftFragment.edges } leftEdge.target ∪
                  computeFuture
                    { states := rightFragment.states,
                      edges := rightFragment.edges } rightEdge.target) by
            exact sequenceExecution_buildParallel_offersAt interface
              leftFragment rightFragment leftEdge.target rightEdge.target
                hLeftTargetState hRightTargetState hLeftTargets hRightTargets]
          have hLeftFuture := hLeft.future leftEdge.target leftTargetResidual
            hLeftTargetRelated
          have hRightFuture := hRight.future rightEdge.target
            rightTargetResidual hRightTargetRelated
          have hLeftFuture' : computeFuture
              { states := leftFragment.states, edges := leftFragment.edges }
              leftEdge.target = typeFutureOffers leftTargetResidual := by
            simpa [leftFragment, hLeftStable] using hLeftFuture
          have hRightFuture' : computeFuture
              { states := rightFragment.states, edges := rightFragment.edges }
              rightEdge.target = typeFutureOffers rightTargetResidual := by
            simpa [rightFragment, hRightStable] using hRightFuture
          rw [hLeftFuture', hRightFuture', typeFutureOffers_parallel]
          rfl
        have hCurrentOffers : execution.offersAt
            (.pair leftEdge.source rightEdge.source) =
              typeFutureOffers
                (.par childLeftResidual childRightResidual interface) := by
          rw [show execution.offersAt
              (.pair leftEdge.source rightEdge.source) =
              hideOffers interface
                (computeFuture
                    { states := leftFragment.states,
                      edges := leftFragment.edges } leftEdge.source ∪
                  computeFuture
                    { states := rightFragment.states,
                      edges := rightFragment.edges } rightEdge.source) by
            exact sequenceExecution_buildParallel_offersAt interface
              leftFragment rightFragment leftEdge.source rightEdge.source
                hCurrentLeftState hCurrentRightState hLeftTargets hRightTargets]
          have hLeftFuture := hLeft.future leftEdge.source childLeftResidual
            hChildLeftRelated
          have hRightFuture := hRight.future rightEdge.source
            childRightResidual hChildRightRelated
          have hLeftFuture' : computeFuture
              { states := leftFragment.states, edges := leftFragment.edges }
              leftEdge.source = typeFutureOffers childLeftResidual := by
            simpa [leftFragment, hLeftStable] using hLeftFuture
          have hRightFuture' : computeFuture
              { states := rightFragment.states, edges := rightFragment.edges }
              rightEdge.source = typeFutureOffers childRightResidual := by
            simpa [rightFragment, hRightStable] using hRightFuture
          rw [hLeftFuture', hRightFuture', typeFutureOffers_parallel]
          rfl
        have hOffersSubset : execution.offersAt
            (.pair leftEdge.target rightEdge.target) ⊆
              execution.offersAt (.pair leftEdge.source rightEdge.source) := by
          rw [hTargetOffers, hCurrentOffers, typeFutureOffers_parallel,
            typeFutureOffers_parallel]
          intro action hAction
          simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union]
            at hAction ⊢
          rcases hAction with ⟨hTargetMenu, hOutside⟩
          exact ⟨hTargetMenu.elim (fun h => Or.inl (hLeftMenuSubset h))
            (fun h => Or.inr (hRightMenuSubset h)), hOutside⟩
        refine ⟨?_, hOffersSubset⟩
        refine ⟨leftEdge.target, rightEdge.target, leftTargetResidual,
          rightTargetResidual, rfl, hLeftTargetRelated, hRightTargetRelated, ?_⟩
        intro hTargetCompleting
        have hTargetFields : leftEdge.target ∈ leftFragment.completing ∧
            rightEdge.target ∈ rightFragment.completing := by
          simpa [fragment, buildParallelAutomaton, finishAutomatonFragment]
            using hTargetCompleting
        have hLeftCanComplete :
            childLeftResidual.CanCompleteBeforeTock = true :=
          hCurrentLeftExecution'.2.mp
            ⟨leftEdge.target, hLeftReachable, Or.inr hTargetFields.1⟩
        have hRightCanComplete :
            childRightResidual.CanCompleteBeforeTock = true :=
          hCurrentRightExecution'.2.mp
            ⟨rightEdge.target, hRightReachable, Or.inr hTargetFields.2⟩
        have hCurrentLeftCompleting :
            leftEdge.source ∈ leftFragment.completing := by
          have hCanonical := (hLeft.completing leftEdge.source
            childLeftResidual hChildLeftRelated).mpr hLeftCanComplete
          simpa [leftFragment, hLeftStable] using hCanonical
        have hCurrentRightCompleting :
            rightEdge.source ∈ rightFragment.completing := by
          have hCanonical := (hRight.completing rightEdge.source
            childRightResidual hChildRightRelated).mpr hRightCanComplete
          simpa [rightFragment, hRightStable] using hCanonical
        apply hCarriesCompletion
        simpa [fragment, buildParallelAutomaton, finishAutomatonFragment]
          using And.intro hCurrentLeftCompleting hCurrentRightCompleting
      have hSameFuture : computeFuture execution (.pair leftState rightState) =
          execution.offersAt (.pair leftState rightState) :=
        computeFuture_eq_offersAt_of_references_monotone_on execution
          (.pair leftState rightState) represented hExecutionClosed hSourceState
            hSourceRepresented hReferenceStep
      constructor
      · exact hSameFuture.trans hSourceOffers
      · constructor
        · rintro ⟨completed, hReachable, hSkipping | hCompleting⟩
          · simp [fragment, buildParallelAutomaton,
              finishAutomatonFragment] at hSkipping
          · let allowed := execution.states.filter represented
            have hSourceAllowed :
                (.pair leftState rightState : TypeAutomatonState) ∈ allowed := by
              simp [allowed, hSourceState, hSourceRepresented]
            have hAllowedClosed : ∀ current ∈ allowed,
                execution.referencedStates current ⊆ allowed := by
              intro current hCurrent target hTarget
              have hFields := Finset.mem_filter.mp hCurrent
              have hNext := hReferenceStep current hFields.1 hFields.2 target
                hTarget
              exact Finset.mem_filter.mpr
                ⟨hExecutionClosed current hFields.1 hTarget, hNext.1⟩
            have hCompletedAllowed :=
              execution.futureReachable_subset_of_reference_closed
                (.pair leftState rightState) allowed hSourceAllowed
                  hAllowedClosed hReachable
            rcases (Finset.mem_filter.mp hCompletedAllowed).2 with
              ⟨completedLeft, completedRight, completedLeftResidual,
                completedRightResidual, hCompletedPair, _, _, hCarries⟩
            exact hCarries hCompleting
        · intro hCanComplete
          refine ⟨.pair leftState rightState,
            execution.mem_futureReachable_self _, ?_⟩
          right
          have hCanonical := (hParentCompleting (.pair leftState rightState)
            (.par leftResidual rightResidual interface)
              (TypeCompilationRelation.parallel left right leftResidual
                rightResidual interface leftState rightState hLeftRelated
                  hRightRelated)).mpr hCanComplete
          simpa [fragment, hParent] using hCanonical

/-- The binder-local future fold.  This is the remaining variable-marker
calculation: matching markers are interpreted in the graph after the enclosing
backedge has been installed. -/
private theorem recursionBodyFutureAndExecutionCorrect_regular_leaf
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.recur name body))
    (hClosed : PactType.AllVariablesBound [] (.recur name body))
    (hGuarded : PactType.ClockGuarded (.recur name body))
    (hTail : PactType.TailRecursive (.recur name body))
    (hLinear : PactType.SameCycleMessageLinear (.recur name body)) :
    RecursionBodyFutureCorrect signature name body ∧
      CompilationSequenceExecutionCorrect signature (.recur name body) := by
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
  have hBodyPackage :=
    recursionBodyFutureAndExecutionCorrect_regular_leaf signature name body
      hSignature hSupports hClosed hGuarded hTail hLinear
  have hBodyFuture := hBodyPackage.1
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
          hScoped hBodyFuture
      execution := hBodyPackage.2 }

/-- Exclusive-offer closure packages its indexed branch/else/wait
classifiers.  Completion is supplied by the strong-induction hypotheses for
the else continuation and every indexed branch. -/

private theorem compilationFutureCorrect_xoffer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationFutureCorrect signature (.xoffer elseType branches) := by
  have hSupportFields := hSupports
  simp only [TypeAlphabet.Supports] at hSupportFields
  exact compilationFutureCorrect_xoffer_of_children signature elseType
    branches hSupportFields.2 hElse.future
      (fun action branchType index hEntry =>
        (hBranches action branchType index hEntry).future)

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

private theorem compiledBranch_zipIdx_cases
    (signature : TypeAlphabet) (fuel : Nat)
    (branches : List (BareMessage × PactType))
    (indexed : (BareMessage × AutomatonFragment) × Nat)
    (hIndexed : indexed ∈
      (branches.map fun branch =>
        (branch.1, compileTypeFuel signature fuel branch.2)).zipIdx) :
    ∃ action branchType,
      branches[indexed.2]? = some (action, branchType) ∧
        indexed.1 =
          (action, compileTypeFuel signature fuel branchType) := by
  have hFields := List.mem_zipIdx hIndexed
  simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hFields
  rcases hFields with ⟨hBound, hValue⟩
  have hAt :
      (branches.map fun branch =>
        (branch.1, compileTypeFuel signature fuel branch.2))[indexed.2]? =
          some indexed.1 := by
    rw [List.getElem?_eq_getElem hBound, hValue]
  rw [List.getElem?_map] at hAt
  cases hOriginal : branches[indexed.2]? with
  | none => simp [hOriginal] at hAt
  | some branch =>
      rcases branch with ⟨action, branchType⟩
      simp only [hOriginal, Option.map_some, Option.some.injEq] at hAt
      exact ⟨action, branchType, rfl, hAt.symm⟩

private theorem compilationSequenceExecutionCorrect_xoffer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationSequenceExecutionCorrect signature
      (.xoffer elseType branches) := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  let execution := sequenceExecutionAutomaton fragment
  let entries := exclusiveOfferEntryStates elseFragment branchAutomata
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hElseStable : elseFragment = compileTypeFuel signature
      (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hElseTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hElseInitial : elseFragment.initial ∈ elseFragment.states :=
    compileTypeFuel_initial_mem signature fuel elseType hElseFuel
  have hBranchTargets : ∀ entry ∈ branchAutomata,
      entry.2.FutureTargetsInStates := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    exact compileTypeFuel_futureTargetsInStates signature fuel branch.2
      ((typeCompilationFuel_le_typeBranchCompilationFuel branches branch
        hBranch).trans (by simp [fuel]))
  have hBranchInitial : ∀ entry ∈ branchAutomata,
      entry.2.initial ∈ entry.2.states := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    exact compileTypeFuel_initial_mem signature fuel branch.2
      ((typeCompilationFuel_le_typeBranchCompilationFuel branches branch
        hBranch).trans (by simp [fuel]))
  have hFragmentTargets : fragment.FutureTargetsInStates := by
    exact buildExclusiveOfferAutomaton_futureTargetsInStates signature
      branches elseFragment branchAutomata hElseTargets hBranchTargets
        hElseInitial hBranchInitial
  have hRoot : (.root : TypeAutomatonState) ∈ fragment.states := by
    simp [fragment, buildExclusiveOfferAutomaton, finishAutomatonFragment]
  have hSupportFields := hSupports
  simp only [TypeAlphabet.Supports] at hSupportFields
  have hAvailableOriginal : ∀ branch ∈ branches,
      typeNeed branch.1 ∈ signature.localEnvironmentActions :=
    supportedBranchNeed_mem_localEnvironmentActions signature branches
      hSupportFields.2
  have hAvailable : ∀ entry ∈ branchAutomata,
      typeNeed entry.1 ∈ signature.localEnvironmentActions := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    exact hAvailableOriginal branch hBranch
  have hUpper : pending.referencedStates .root ⊆ insert .root entries := by
    simpa [pending, fragment, entries] using
      buildExclusiveOfferAutomaton_root_references_upper signature branches
        elseFragment branchAutomata
  have hEntries : entries ⊆ pending.referencedStates .root := by
    simpa [pending, fragment, entries] using
      buildExclusiveOfferAutomaton_entries_referenced signature branches
        elseFragment branchAutomata hAvailable
  have hShape : ∀ edge ∈ fragment.edges, edge.source = .root →
      edge.label ≠ .future ∧
        ∃ removed, edge.future = .at edge.target removed := by
    intro edge hEdge hSource
    exact sequenceExecution_buildExclusiveOffer_root_shape signature
      branches elseFragment branchAutomata edge hEdge hSource
  have hParent : compileTypeFuel signature
      (typeCompilationFuel (.xoffer elseType branches))
        (.xoffer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hWholeFuture := compilationFutureCorrect_xoffer_regular_leaf signature
    elseType branches hSupports hElse hBranches
  have hBranchCompleting : ∀ (action : BareMessage)
      (branchType : PactType) (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationCompletingCorrect signature branchType := by
    intro action branchType index hEntry
    exact (hBranches action branchType index hEntry).completing
  have hWholeCompleting := compilationCompletingCorrect_xoffer signature
    elseType branches hElse.completing hBranchCompleting
  have hElseStates : elseFragment.states.image (childState 0) ⊆
      fragment.states := by
    intro tagged hTagged
    rcases Finset.mem_image.mp hTagged with ⟨state, hState, rfl⟩
    simp [fragment, buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hState]
  have hElseOutgoing : ∀ state edge,
      edge ∈ fragment.edges ∧ edge.source = childState 0 state ↔
        ∃ childEdge ∈ elseFragment.edges,
          childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
    intro state edge
    simpa [fragment] using
      (buildExclusiveOfferAutomaton_outgoing_else signature branches
        elseFragment branchAutomata state edge)
  have hElseRootRelation : TypeCompilationRelation elseType
      elseFragment.initial elseType := by
    simpa [elseFragment, hElseStable, compileType] using
      compileType_initial_relation signature elseType
  have hElseRootExecution := hElse.execution elseFragment.initial elseType
    hElseRootRelation
  have hElseRootExecution' :
      computeFuture (sequenceExecutionAutomaton elseFragment)
          elseFragment.initial = typeFutureOffers elseType ∧
        ((∃ completed ∈
              (sequenceExecutionAutomaton elseFragment).futureReachable
                elseFragment.initial,
              completed ∈ elseFragment.skipping ∨
                completed ∈ elseFragment.completing) ↔
          elseType.CanCompleteBeforeTock = true) := by
    simpa [CompilationSequenceExecutionCorrect, elseFragment, hElseStable]
      using hElseRootExecution
  have hEntryFacts : ∀ entry ∈ entries,
      computeFuture execution entry = computeFuture pending entry ∧
        ((∃ completed ∈ execution.futureReachable entry,
            completed ∈ fragment.skipping ∨
              completed ∈ fragment.completing) →
          (PactType.xoffer elseType branches).CanCompleteBeforeTock = true) := by
    intro entry hEntry
    simp only [entries, exclusiveOfferEntryStates, Finset.mem_union,
      Finset.mem_singleton] at hEntry
    rcases hEntry with rfl | hBranchEntry
    · have hExecEmbedding := sequenceExecution_taggedChild_computeFuture
        fragment elseFragment 0 hElseOutgoing hElseStates hElseTargets
          elseFragment.initial hElseInitial
      have hParentRelation : TypeCompilationRelation
          (.xoffer elseType branches) (childState 0 elseFragment.initial)
            elseType := TypeCompilationRelation.xoffer_else elseType elseType
              branches elseFragment.initial hElseRootRelation
      have hPendingMenu := hWholeFuture _ _ hParentRelation
      rw [hParent] at hPendingMenu
      constructor
      · exact hExecEmbedding.trans
          (hElseRootExecution'.1.trans hPendingMenu.symm)
      · rintro ⟨completed, hReach, hCompleted⟩
        have hReachEmbedding := sequenceExecution_taggedChild_futureReachable
          fragment elseFragment 0 hElseOutgoing hElseStates hElseTargets
            elseFragment.initial hElseInitial
        rw [hReachEmbedding] at hReach
        have hSkip : ∀ state,
            childState 0 state ∈ fragment.skipping ↔
              state ∈ elseFragment.skipping := by
          intro state
          exact buildExclusiveOffer_child0_skipping_iff signature branches
            elseFragment branchAutomata state
        have hComplete : ∀ state,
            childState 0 state ∈ fragment.completing ↔
              state ∈ elseFragment.completing := by
          intro state
          exact buildExclusiveOffer_child0_completing_iff signature branches
            elseFragment branchAutomata state
        have hChildWitness : ∃ childCompleted ∈
            (sequenceExecutionAutomaton elseFragment).futureReachable
              elseFragment.initial,
            childCompleted ∈ elseFragment.skipping ∨
              childCompleted ∈ elseFragment.completing :=
          (taggedCompletionWitness_iff fragment elseFragment 0 _ hSkip
            hComplete).mp ⟨completed, hReach, hCompleted⟩
        have hElseCan := hElseRootExecution'.2.mp hChildWitness
        simp [PactType.CanCompleteBeforeTock, hElseCan]
    · rw [mem_foldl_union_iff] at hBranchEntry
      rcases hBranchEntry with hEmpty | ⟨indexed, hIndexed, hEntryState⟩
      · simp at hEmpty
      simp only [Finset.mem_singleton] at hEntryState
      subst entry
      rcases compiledBranch_zipIdx_cases signature fuel branches indexed
          (by simpa [branchAutomata] using hIndexed) with
        ⟨action, branchType, hSyntaxEntry, hCompiledEntry⟩
      rcases indexed with ⟨compiledEntry, index⟩
      simp only at hCompiledEntry
      subst compiledEntry
      let branchFragment := compileTypeFuel signature fuel branchType
      have hBranchMember : (action, branchType) ∈ branches := by
        rcases List.getElem?_eq_some_iff.mp hSyntaxEntry with
          ⟨hBound, hValue⟩
        have hMember := List.getElem_mem hBound
        simpa [hValue] using hMember
      have hBranchFuel : TypeCompilationFuelSufficient branchType fuel :=
        (typeCompilationFuel_le_typeBranchCompilationFuel branches
          (action, branchType) hBranchMember).trans (by simp [fuel])
      have hBranchStable : branchFragment = compileTypeFuel signature
          (typeCompilationFuel branchType) branchType :=
        compileTypeFuel_eq_of_sufficient signature branchType hBranchFuel
          (typeCompilationFuel_sufficient branchType)
      have hBranchInitialState : branchFragment.initial ∈
          branchFragment.states :=
        compileTypeFuel_initial_mem signature fuel branchType hBranchFuel
      have hBranchTargets' : branchFragment.FutureTargetsInStates :=
        compileTypeFuel_futureTargetsInStates signature fuel branchType
          hBranchFuel
      have hAutomatonEntry : branchAutomata[index]? =
          some (action, branchFragment) := by
        simp [branchAutomata, branchFragment, hSyntaxEntry]
      have hZipEntry : ((action, branchFragment), index) ∈
          branchAutomata.zipIdx := by
        simpa [branchAutomata, branchFragment] using hIndexed
      have hBranchStates : branchFragment.states.image
          (childState (index + 1)) ⊆ fragment.states := by
        intro tagged hTagged
        rcases Finset.mem_image.mp hTagged with ⟨state, hState, rfl⟩
        have hIndexedState : childState (index + 1) state ∈
            indexedFragmentStates branchAutomata := by
          rw [indexedFragmentStates, mem_foldl_union_iff]
          right
          exact ⟨((action, branchFragment), index), hZipEntry,
            by simp [childStates, childState, hState]⟩
        simp [fragment, buildExclusiveOfferAutomaton,
          finishAutomatonFragment, hIndexedState]
      have hBranchOutgoing : ∀ state edge,
          edge ∈ fragment.edges ∧
              edge.source = childState (index + 1) state ↔
            ∃ childEdge ∈ branchFragment.edges,
              childEdge.source = state ∧
                edge = childPendingEdge (index + 1) childEdge := by
        intro state edge
        simpa [fragment, branchFragment] using
          (buildExclusiveOfferAutomaton_outgoing_branch signature branches
            elseFragment branchAutomata index (action, branchFragment)
              hAutomatonEntry state edge)
      have hBranchRelation : TypeCompilationRelation branchType
          branchFragment.initial branchType := by
        simpa [branchFragment, hBranchStable, compileType] using
          compileType_initial_relation signature branchType
      have hBranchBundle := hBranches action branchType index hSyntaxEntry
      have hBranchExecution := hBranchBundle.execution
        branchFragment.initial branchType hBranchRelation
      have hBranchExecution' :
          computeFuture (sequenceExecutionAutomaton branchFragment)
              branchFragment.initial = typeFutureOffers branchType ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton branchFragment).futureReachable
                    branchFragment.initial,
                  completed ∈ branchFragment.skipping ∨
                    completed ∈ branchFragment.completing) ↔
              branchType.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, branchFragment,
          hBranchStable] using hBranchExecution
      have hExecEmbedding := sequenceExecution_taggedChild_computeFuture
        fragment branchFragment (index + 1) hBranchOutgoing hBranchStates
          hBranchTargets' branchFragment.initial hBranchInitialState
      have hParentRelation : TypeCompilationRelation
          (.xoffer elseType branches)
            (childState (index + 1) branchFragment.initial) branchType :=
        TypeCompilationRelation.xoffer_branch elseType branchType branchType
          branches action index branchFragment.initial hSyntaxEntry
            hBranchRelation
      have hPendingMenu := hWholeFuture _ _ hParentRelation
      rw [hParent] at hPendingMenu
      constructor
      · exact hExecEmbedding.trans
          (hBranchExecution'.1.trans hPendingMenu.symm)
      · rintro ⟨completed, hReach, hCompleted⟩
        have hReachEmbedding := sequenceExecution_taggedChild_futureReachable
          fragment branchFragment (index + 1) hBranchOutgoing hBranchStates
            hBranchTargets' branchFragment.initial hBranchInitialState
        rw [hReachEmbedding] at hReach
        have hSkip : ∀ state,
            childState (index + 1) state ∈ fragment.skipping ↔
              state ∈ branchFragment.skipping := by
          intro state
          exact buildExclusiveOffer_branch_skipping_iff signature branches
            elseFragment branchAutomata index (action, branchFragment)
              hAutomatonEntry state
        have hComplete : ∀ state,
            childState (index + 1) state ∈ fragment.completing ↔
              state ∈ branchFragment.completing := by
          intro state
          exact buildExclusiveOffer_branch_completing_iff signature branches
            elseFragment branchAutomata index (action, branchFragment)
              hAutomatonEntry state
        have hChildWitness : ∃ childCompleted ∈
            (sequenceExecutionAutomaton branchFragment).futureReachable
              branchFragment.initial,
            childCompleted ∈ branchFragment.skipping ∨
              childCompleted ∈ branchFragment.completing :=
          (taggedCompletionWitness_iff fragment branchFragment (index + 1)
            _ hSkip hComplete).mp ⟨completed, hReach, hCompleted⟩
        have hBranchCan := hBranchExecution'.2.mp hChildWitness
        have hAny : branches.any
            (fun branch => branch.2.CanCompleteBeforeTock) = true := by
          apply List.any_eq_true.mpr
          exact ⟨(action, branchType), hBranchMember, hBranchCan⟩
        simp [PactType.CanCompleteBeforeTock,
          branchCanCompleteBeforeTock_eq_any, hAny]
  have hEntryFuture : ∀ entry ∈ entries,
      computeFuture execution entry = computeFuture pending entry := by
    intro entry hEntry
    exact (hEntryFacts entry hEntry).1
  have hRootFutureEquality : computeFuture execution .root =
      computeFuture pending .root := by
    exact sequenceExecution_computeFuture_root_eq fragment entries
      hFragmentTargets hRoot hShape hUpper hEntries hEntryFuture
  have hRootReach : execution.futureReachable .root =
      {.root} ∪ entries.biUnion execution.futureReachable := by
    exact sequenceExecution_futureReachable_root fragment entries
      hFragmentTargets hRoot hShape hUpper hEntries
  intro state residual hRelated
  rw [hParent]
  cases hRelated with
  | xoffer_source =>
      constructor
      · have hPendingRoot := hWholeFuture .root
          (.xoffer elseType branches)
            (TypeCompilationRelation.xoffer_source elseType branches)
        rw [hParent] at hPendingRoot
        exact hRootFutureEquality.trans hPendingRoot
      · constructor
        · rintro ⟨completed, hReach, hCompleted⟩
          rw [hRootReach] at hReach
          simp only [Finset.mem_union, Finset.mem_singleton,
            Finset.mem_biUnion] at hReach
          rcases hReach with hAtRoot | ⟨entry, hEntry, hAtEntry⟩
          · subst completed
            have hRootNotSkipping :
                (.root : TypeAutomatonState) ∉ fragment.skipping := by
              exact buildExclusiveOffer_root_not_skipping signature branches
                elseFragment branchAutomata
            have hRootCompleting : (.root : TypeAutomatonState) ∈
                fragment.completing := hCompleted.resolve_left
              hRootNotSkipping
            exact (hWholeCompleting .root (.xoffer elseType branches)
              (TypeCompilationRelation.xoffer_source elseType branches)).mp
                (by simpa [hParent] using hRootCompleting)
          · exact (hEntryFacts entry hEntry).2
              ⟨completed, hAtEntry, hCompleted⟩
        · intro hCanComplete
          have hRootCompleting :=
            (hWholeCompleting .root (.xoffer elseType branches)
              (TypeCompilationRelation.xoffer_source elseType branches)).mpr
                hCanComplete
          refine ⟨.root, execution.mem_futureReachable_self .root, ?_⟩
          right
          simpa [hParent] using hRootCompleting
  | xoffer_else _ _ _ childState hChildRelated =>
      have hChildState : childState ∈ elseFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          elseType childState residual hChildRelated
        simpa [elseFragment, hElseStable] using hCanonical
      have hChildCanonical := hElse.execution childState residual hChildRelated
      have hChild :
          computeFuture (sequenceExecutionAutomaton elseFragment) childState =
              typeFutureOffers residual ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton elseFragment).futureReachable
                    childState,
                  completed ∈ elseFragment.skipping ∨
                    completed ∈ elseFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, elseFragment,
          hElseStable] using hChildCanonical
      constructor
      · exact (sequenceExecution_taggedChild_computeFuture fragment
          elseFragment 0 hElseOutgoing hElseStates hElseTargets childState
            hChildState).trans hChild.1
      · have hReachEquality :=
          sequenceExecution_taggedChild_futureReachable fragment
            elseFragment 0 hElseOutgoing hElseStates hElseTargets childState
              hChildState
        change ((∃ completed ∈
              (sequenceExecutionAutomaton fragment).futureReachable
                (Pact.childState 0 childState),
              completed ∈ fragment.skipping ∨
                completed ∈ fragment.completing) ↔
            residual.CanCompleteBeforeTock = true)
        rw [hReachEquality]
        have hSkip : ∀ child,
            Pact.childState 0 child ∈ fragment.skipping ↔
              child ∈ elseFragment.skipping := by
          intro child
          exact buildExclusiveOffer_child0_skipping_iff signature branches
            elseFragment branchAutomata child
        have hComplete : ∀ child,
            Pact.childState 0 child ∈ fragment.completing ↔
              child ∈ elseFragment.completing := by
          intro child
          exact buildExclusiveOffer_child0_completing_iff signature branches
            elseFragment branchAutomata child
        exact (taggedCompletionWitness_iff fragment elseFragment 0 _ hSkip
          hComplete).trans hChild.2
  | xoffer_branch _ branchType _ _ action index childState hSyntaxEntry
      hChildRelated =>
      have hBranchMember : (action, branchType) ∈ branches := by
        rcases List.getElem?_eq_some_iff.mp hSyntaxEntry with
          ⟨hBound, hValue⟩
        have hMember := List.getElem_mem hBound
        simpa [hValue] using hMember
      have hBranchFuel : TypeCompilationFuelSufficient branchType fuel :=
        (typeCompilationFuel_le_typeBranchCompilationFuel branches
          (action, branchType) hBranchMember).trans (by simp [fuel])
      let branchFragment := compileTypeFuel signature fuel branchType
      have hBranchStable : branchFragment = compileTypeFuel signature
          (typeCompilationFuel branchType) branchType :=
        compileTypeFuel_eq_of_sufficient signature branchType hBranchFuel
          (typeCompilationFuel_sufficient branchType)
      have hAutomatonEntry : branchAutomata[index]? =
          some (action, branchFragment) := by
        simp [branchAutomata, branchFragment, hSyntaxEntry]
      have hZipEntry : ((action, branchFragment), index) ∈
          branchAutomata.zipIdx := by
        rcases List.getElem?_eq_some_iff.mp hAutomatonEntry with
          ⟨hBound, hValue⟩
        have hZipBound : index < branchAutomata.zipIdx.length := by
          simpa using hBound
        have hMember := List.getElem_mem hZipBound
        have hAt := List.getElem_zipIdx (l := branchAutomata) (i := index)
          (j := 0) hZipBound
        simp only [zero_add] at hAt
        rw [hAt, hValue] at hMember
        exact hMember
      have hChildState : childState ∈ branchFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          branchType childState residual hChildRelated
        simpa [branchFragment, hBranchStable] using hCanonical
      have hTargets : branchFragment.FutureTargetsInStates :=
        compileTypeFuel_futureTargetsInStates signature fuel branchType
          hBranchFuel
      have hStates : branchFragment.states.image
          (Pact.childState (index + 1)) ⊆ fragment.states := by
        intro tagged hTagged
        rcases Finset.mem_image.mp hTagged with ⟨child, hChild, rfl⟩
        have hIndexedState : Pact.childState (index + 1) child ∈
            indexedFragmentStates branchAutomata := by
          rw [indexedFragmentStates, mem_foldl_union_iff]
          right
          exact ⟨((action, branchFragment), index), hZipEntry,
            by simp [childStates, Pact.childState, hChild]⟩
        simp [fragment, buildExclusiveOfferAutomaton,
          finishAutomatonFragment, hIndexedState]
      have hOutgoing : ∀ source edge,
          edge ∈ fragment.edges ∧
              edge.source = Pact.childState (index + 1) source ↔
            ∃ childEdge ∈ branchFragment.edges,
              childEdge.source = source ∧
                edge = childPendingEdge (index + 1) childEdge := by
        intro source edge
        simpa [fragment, branchFragment] using
          (buildExclusiveOfferAutomaton_outgoing_branch signature branches
            elseFragment branchAutomata index (action, branchFragment)
              hAutomatonEntry source edge)
      have hChildCanonical :=
        (hBranches action branchType index hSyntaxEntry).execution childState
          residual hChildRelated
      have hChild :
          computeFuture (sequenceExecutionAutomaton branchFragment) childState =
              typeFutureOffers residual ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton branchFragment).futureReachable
                    childState,
                  completed ∈ branchFragment.skipping ∨
                    completed ∈ branchFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, branchFragment,
          hBranchStable] using hChildCanonical
      constructor
      · exact (sequenceExecution_taggedChild_computeFuture fragment
          branchFragment (index + 1) hOutgoing hStates hTargets childState
            hChildState).trans hChild.1
      · have hReachEquality :=
          sequenceExecution_taggedChild_futureReachable fragment
            branchFragment (index + 1) hOutgoing hStates hTargets childState
              hChildState
        change ((∃ completed ∈
              (sequenceExecutionAutomaton fragment).futureReachable
                (Pact.childState (index + 1) childState),
              completed ∈ fragment.skipping ∨
                completed ∈ fragment.completing) ↔
            residual.CanCompleteBeforeTock = true)
        rw [hReachEquality]
        have hSkip : ∀ child,
            Pact.childState (index + 1) child ∈ fragment.skipping ↔
              child ∈ branchFragment.skipping := by
          intro child
          exact buildExclusiveOffer_branch_skipping_iff signature branches
            elseFragment branchAutomata index (action, branchFragment)
              hAutomatonEntry child
        have hComplete : ∀ child,
            Pact.childState (index + 1) child ∈ fragment.completing ↔
              child ∈ branchFragment.completing := by
          intro child
          exact buildExclusiveOffer_branch_completing_iff signature branches
            elseFragment branchAutomata index (action, branchFragment)
              hAutomatonEntry child
        exact (taggedCompletionWitness_iff fragment branchFragment
          (index + 1) _ hSkip hComplete).trans hChild.2

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
    elseType branches hSupports hElse hBranches
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
          hLinear hScoped hFuture hElse hBranches
      execution := compilationSequenceExecutionCorrect_xoffer_regular_leaf
        signature elseType branches hSupports hElse hBranches }

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
    (hLinear : PactType.SameCycleMessageLinear (.offer elseType branches))
    (hScoped : PactType.InterfaceScoped (.offer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationFutureCorrect signature (.offer elseType branches) := by
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
  exact compilationFutureCorrect_offer_of_children signature elseType branches
    hSupportFields.2 hElse.future hConjunction.future

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

/-
/-- Regression isolating the remaining conjunctive-offer execution mismatch.
The operational completion analysis of `offer tock [a ↦ tock]` is false, but
the constructor execution graph reaches the generated singleton offer, whose
`skip` else-arm marks its initial state completing. -/
theorem conjunctiveOffer_execution_completion_regression
    (signature : TypeAlphabet) (action : BareMessage)
    (hAvailable : typeNeed action ∈ signature.localEnvironmentActions) :
    let branches : List (BareMessage × PactType) := [(action, .tock)]
    let processType : PactType := .offer .tock branches
    let fragment := compileTypeFuel signature
      (typeCompilationFuel processType) processType
    let execution := sequenceExecutionAutomaton fragment
    processType.CanCompleteBeforeTock = false ∧
      ∃ completed ∈ execution.futureReachable .root,
        completed ∈ fragment.completing := by
  classical
  dsimp only
  let branches : List (BareMessage × PactType) := [(action, .tock)]
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel PactType.tock)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel PactType.tock
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  let execution := sequenceExecutionAutomaton fragment
  have hElseFuel : TypeCompilationFuelSufficient PactType.tock fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hConjunctionFuel : TypeCompilationFuelSufficient conjunctionType fuel := by
    rw [TypeCompilationFuelSufficient,
      typeCompilationFuel_parallelTypeBranches]
    simp [fuel, conjunctionType, branches]
  have hConjunctionStable : conjunction = compileTypeFuel signature
      (typeCompilationFuel conjunctionType) conjunctionType :=
    compileTypeFuel_eq_of_sufficient signature conjunctionType
      hConjunctionFuel (typeCompilationFuel_sufficient conjunctionType)
  have hElseTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel .tock hElseFuel
  have hConjunctionTargets : conjunction.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel conjunctionType
      hConjunctionFuel
  have hElseInitial : elseFragment.initial ∈ elseFragment.states :=
    compileTypeFuel_initial_mem signature fuel .tock hElseFuel
  have hConjunctionInitial : conjunction.initial ∈ conjunction.states :=
    compileTypeFuel_initial_mem signature fuel conjunctionType
      hConjunctionFuel
  have hFragmentTargets : fragment.FutureTargetsInStates :=
    buildConjunctiveOfferAutomaton_futureTargetsInStates signature branches
      elseFragment conjunction hElseTargets hConjunctionTargets hElseInitial
        hConjunctionInitial
  have hExecutionClosed : execution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed fragment hFragmentTargets
  have hRoot : (.root : TypeAutomatonState) ∈ execution.states := by
    apply Finset.mem_union_left
    simp [fragment, buildConjunctiveOfferAutomaton,
      finishAutomatonFragment]
  have hParent : compileTypeFuel signature
      (typeCompilationFuel (.offer .tock branches)) (.offer .tock branches) =
        fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    simp [fragment, elseFragment, conjunction, conjunctionType, fuel,
      typeCompilationFuel]
  have hEntries := buildConjunctiveOfferAutomaton_entries_referenced signature
    branches elseFragment conjunction (by
      intro branch hBranch
      simp only [branches, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq] at hBranch
      rcases hBranch with ⟨rfl, rfl⟩
      exact hAvailable)
  have hPendingReference : childState 0 conjunction.initial ∈
      pending.referencedStates .root := by
    apply hEntries
    simp [conjunctiveOfferEntryStates, branches]
  have hShape := sequenceExecution_buildConjunctiveOffer_root_shape signature
    branches elseFragment conjunction
  have hReferenceEquality := sequenceExecution_root_referencedStates_eq
    fragment hShape
  have hExecutionReference : childState 0 conjunction.initial ∈
      execution.referencedStates .root := by
    rw [hReferenceEquality]
    simpa [pending, execution] using hPendingReference
  have hReachable : childState 0 conjunction.initial ∈
      execution.futureReachable .root :=
    execution.referencedStates_subset_futureReachable .root hExecutionClosed
      hRoot hExecutionReference
  have hConjunctionRelation : TypeCompilationRelation conjunctionType
      conjunction.initial conjunctionType := by
    have hCanonical := compileType_initial_relation signature conjunctionType
    simpa [conjunction, hConjunctionStable, compileType] using hCanonical
  have hConjunctionCompleting : conjunction.initial ∈
      conjunction.completing := by
    have hSkipCompleting := compilationCompletingCorrect_skip signature
    have hTockCompleting := compilationCompletingCorrect_tock signature
    have hWhole := compilationCompletingCorrect_xoffer signature .skip
      [(action, .tock)] hSkipCompleting (by
        intro selected selectedType index hEntry
        have hIndex : index = 0 := by
          simpa using (List.getElem?_eq_some_iff.mp hEntry).1
        subst index
        simp only [List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hEntry
        rcases hEntry with ⟨rfl, rfl⟩
        exact hTockCompleting)
    have hCanonical := (hWhole conjunction.initial conjunctionType
      hConjunctionRelation).mpr (by
        simp [conjunctionType, branches, parallelTypeBranches,
          singletonTypeXOffer, PactType.CanCompleteBeforeTock])
    simpa [conjunction, hConjunctionStable] using hCanonical
  have hParentCompleting : childState 0 conjunction.initial ∈
      fragment.completing :=
    (buildConjunctiveOffer_child0_completing_iff signature branches
      elseFragment conjunction conjunction.initial).mpr hConjunctionCompleting
  constructor
  · simp [PactType.CanCompleteBeforeTock,
      PactType.BranchCanCompleteBeforeTock]
  · rw [hParent]
    exact ⟨childState 0 conjunction.initial, hReachable, hParentCompleting⟩

/-- Consequently the strengthened execution field required by the current
hierarchy is false for this well-supported conjunctive offer. -/
theorem conjunctiveOffer_not_sequenceExecutionCorrect
    (signature : TypeAlphabet) (action : BareMessage)
    (hAvailable : typeNeed action ∈ signature.localEnvironmentActions) :
    ¬ CompilationSequenceExecutionCorrect signature
      (.offer .tock [(action, .tock)]) := by
  intro hCorrect
  have hAtRoot := hCorrect .root (.offer .tock [(action, .tock)])
    (TypeCompilationRelation.offer_source .tock [(action, .tock)])
  rcases conjunctiveOffer_execution_completion_regression signature action
      hAvailable with ⟨hCannotComplete, completed, hReachable, hCompleting⟩
  have hCanComplete := hAtRoot.2.mp
    ⟨completed, hReachable, Or.inr hCompleting⟩
  simp_all
-/

/-- Hierarchy adapter for selected conjunctive-offer products.  Its remaining
proof obligation is to transport execution correctness through the indexed
post-construction products; the obsolete all-else counterexample no longer
applies because that one outcome is absent. -/
private theorem compilationSequenceExecutionCorrect_offer_regular_leaf
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
    CompilationSequenceExecutionCorrect signature
      (.offer elseType branches) := by
  sorry

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
      hScoped hElse hBranches
  exact
    { future := hFuture
      completing := compilationCompletingCorrect_offer_regular_leaf signature
        elseType branches hElse hBranches
      scopedStep := compilationFragmentStepCorrect_offer_regular_leaf
        signature elseType branches hSignature hSupports hClosed hGuarded hTail
          hLinear hScoped hFuture hElse hBranches
      execution := compilationSequenceExecutionCorrect_offer_regular_leaf
        signature elseType branches hSignature hSupports hClosed hGuarded hTail
          hLinear hScoped hElse hBranches }

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
              (compilationFragmentStepCorrect_message_leaf signature msg dir)
          execution := compilationSequenceExecutionCorrect_message signature
            msg dir }
  | progress pid =>
      intro _ _ _ _ _ _ _
      exact
        { future := compilationFutureCorrect_progress signature pid
          completing := compilationCompletingCorrect_progress signature pid
          scopedStep := compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
            signature (.progress pid)
              (compilationFragmentStepCorrect_progress_leaf signature pid)
          execution := compilationSequenceExecutionCorrect_progress signature
            pid }
  | tock =>
      intro _ _ _ _ _ _ _
      exact
        { future := compilationFutureCorrect_tock signature
          completing := compilationCompletingCorrect_tock signature
          scopedStep := compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
            signature .tock
              (compilationFragmentStepCorrect_tock_leaf signature)
          execution := compilationSequenceExecutionCorrect_tock signature }
  | skip =>
      intro _ _ _ _ _ _ _
      exact
        { future := compilationFutureCorrect_skip signature
          completing := compilationCompletingCorrect_skip signature
          scopedStep := compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
            signature .skip
              (compilationFragmentStepCorrect_skip_leaf signature)
          execution := compilationSequenceExecutionCorrect_skip signature }
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
            left right hLeft hRight
          execution := compilationSequenceExecutionCorrect_choice signature
            left right hLeft.execution hRight.execution }
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
            signature bid left right hLeft hRight
          execution := compilationSequenceExecutionCorrect_fairChoice signature
            bid left right hLeft.execution hRight.execution }
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
      intro hSignature hSupports hClosed hGuarded hTail hLinear hScoped
      have hScopedWhole : PactType.InterfaceScoped (.par left right interface) :=
        hScoped
      have hClosedWhole : PactType.AllVariablesBound []
          (.par left right interface) := hClosed
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
              hClosedWhole hLeft hRight
          execution :=
            compilationSequenceExecutionCorrect_parallel_regular_leaf
              signature left right interface hClosed.1 hClosed.2 hLeft hRight }
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
