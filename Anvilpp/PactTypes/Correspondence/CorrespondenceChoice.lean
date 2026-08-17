import Anvilpp.PactTypes.Correspondence.CorrespondenceOffers
import Anvilpp.PactTypes.Correspondence.CorrespondenceParallel

/-!
# Ordinary and fair-choice correspondence
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

private theorem choiceFutureCorrect_core
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (hLeftCorrect : CompilationFutureCorrect signature left)
    (hRightCorrect : CompilationFutureCorrect signature right)
    (hLeftCanonical : left.EntryCanonical)
    (hRightCanonical : right.EntryCanonical)
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
    have hRelation := compileTypeFuel_initial_relation_of_canonical signature
      fuel left hLeftFuel
      (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
        hLeftCanonical)
    have hResult := hLeftCorrect hLeftCanonical leftFragment.initial left
      hRelation
    have hStable := compileTypeFuel_eq_of_sufficient signature left
      hLeftFuel (typeCompilationFuel_sufficient left)
    simpa [leftFragment, hStable] using hResult
  have hRightSemantic : computeFuture
      { states := rightFragment.states, edges := rightFragment.edges }
      rightFragment.initial = typeFutureOffers right := by
    unfold CompilationFutureCorrect at hRightCorrect
    have hRelation := compileTypeFuel_initial_relation_of_canonical signature
      fuel right hRightFuel
      (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
        hRightCanonical)
    have hResult := hRightCorrect hRightCanonical rightFragment.initial right
      hRelation
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
    (hRightCorrect : CompilationFutureCorrect signature right)
    (hLeftCanonical : left.EntryCanonical)
    (hRightCanonical : right.EntryCanonical) :
    ChoiceFutureCorrect signature left right := by
  apply choiceFutureCorrect_core signature left right
    TypeLabel.silent TypeLabel.silent hLeftCorrect hRightCorrect
    hLeftCanonical hRightCanonical
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
    (hRightCorrect : CompilationFutureCorrect signature right)
    (hLeftCanonical : left.EntryCanonical)
    (hRightCanonical : right.EntryCanonical) :
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
    compileTypeFuel_initial_relation_of_canonical signature fuel left hLeftFuel
      (PactType.canonicalEntryResidual_eq_self_of_entryCanonical hLeftCanonical)
  have hRightRelation :
      TypeCompilationRelation right rightFragment.initial right :=
    compileTypeFuel_initial_relation_of_canonical signature fuel right
      hRightFuel
      (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
        hRightCanonical)
  have hLeftSemantic : computeFuture
      { states := leftFragment.states, edges := leftFragment.edges }
      leftFragment.initial = typeFutureOffers left := by
    have hResult := hLeftCorrect hLeftCanonical leftFragment.initial left
      hLeftRelation
    have hStable := compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
    simpa [leftFragment, hStable] using hResult
  have hRightSemantic : computeFuture
      { states := rightFragment.states, edges := rightFragment.edges }
      rightFragment.initial = typeFutureOffers right := by
    have hResult := hRightCorrect hRightCanonical rightFragment.initial right
      hRightRelation
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
    (hStateCorrect : CompilationStateCorrect signature left)
    (hCanonical : left.EntryCanonical) :
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
  have hSemantic := hFuture hCanonical state residual hRelated
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
    (hStateCorrect : CompilationStateCorrect signature right)
    (hCanonical : right.EntryCanonical) :
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
  have hSemantic := hFuture hCanonical state residual hRelated
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
  intro hCanonical state residual hRelated
  have hLeftCanonical : left.EntryCanonical := by
    have h := hCanonical
    simp only [PactType.EntryCanonical] at h
    exact h.1
  have hRightCanonical : right.EntryCanonical := by
    have h := hCanonical
    simp only [PactType.EntryCanonical] at h
    exact h.2
  cases hRelated with
  | choice_source =>
      have hRoot := compiledChoiceRootFuture_eq_union signature left right
        TypeLabel.silent TypeLabel.silent (by simp [TypeLabel.silent])
        (by simp [TypeLabel.silent]) hLeftFuture hRightFuture hLeftCanonical
        hRightCanonical
      have hSyntax := typeFutureOffers_choice left right
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
        hRoot.trans hSyntax.symm
  | choice_left _ _ childResidual childState hChildRelated =>
      have hChild := compiledChoiceLeftFuture_eq signature left right
        residual TypeLabel.silent TypeLabel.silent childState
        hChildRelated hLeftFuture
        (compilationStateCorrect_of_compilation signature left) hLeftCanonical
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
        hChild
  | choice_right _ _ childResidual childState hChildRelated =>
      have hChild := compiledChoiceRightFuture_eq signature left right
        residual TypeLabel.silent TypeLabel.silent childState
        hChildRelated hRightFuture
        (compilationStateCorrect_of_compilation signature right) hRightCanonical
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
        hChild

/-- Whole-fragment future correctness composes through fair choice; its
selection labels do not alter the syntax-derived branch union. -/
theorem compilationFutureCorrect_fairChoice
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeftFuture : CompilationFutureCorrect signature left)
    (hRightFuture : CompilationFutureCorrect signature right) :
    CompilationFutureCorrect signature (.fairChoice bid left right) := by
  intro hCanonical state residual hRelated
  have hLeftCanonical : left.EntryCanonical := by
    have h := hCanonical
    simp only [PactType.EntryCanonical] at h
    exact h.1
  have hRightCanonical : right.EntryCanonical := by
    have h := hCanonical
    simp only [PactType.EntryCanonical] at h
    exact h.2
  cases hRelated with
  | fair_source =>
      have hRoot := compiledChoiceRootFuture_eq_union signature left right
        (TypeLabel.fair bid true) (TypeLabel.fair bid false)
        (by simp [TypeLabel.fair]) (by simp [TypeLabel.fair])
        hLeftFuture hRightFuture hLeftCanonical hRightCanonical
      have hSyntax := typeFutureOffers_fairChoice bid left right
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
        hRoot.trans hSyntax.symm
  | fair_left _ _ _ childResidual childState hChildRelated =>
      have hChild := compiledChoiceLeftFuture_eq signature left right
        residual (TypeLabel.fair bid true) (TypeLabel.fair bid false)
        childState hChildRelated hLeftFuture
        (compilationStateCorrect_of_compilation signature left) hLeftCanonical
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
        hChild
  | fair_right _ _ _ childResidual childState hChildRelated =>
      have hChild := compiledChoiceRightFuture_eq signature left right
        residual (TypeLabel.fair bid true) (TypeLabel.fair bid false)
        childState hChildRelated hRightFuture
        (compilationStateCorrect_of_compilation signature right) hRightCanonical
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
  sorry -- TODO(redevelopment): body relied on old computeFuture-based
  -- HasResolvedEdge classifiers / resolvedAutomatonEdges; .
theorem compileType_choice_right_child_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature (.choice left right)).HasEdge
        (.child 1 source) env label offers (.child 1 target) ↔
      (compileType signature right).HasEdge source env label offers target := by
  sorry -- TODO(redevelopment): body relied on old computeFuture-based
  -- HasResolvedEdge classifiers / resolvedAutomatonEdges; .
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
  sorry -- TODO(redevelopment): body relied on old computeFuture-based
  -- HasResolvedEdge classifiers / resolvedAutomatonEdges; .
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
  sorry -- TODO(redevelopment): body relied on old computeFuture-based
  -- HasResolvedEdge classifiers / resolvedAutomatonEdges; .
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
  sorry -- TODO(redevelopment): body relied on old computeFuture-based
  -- HasResolvedEdge classifiers / resolvedAutomatonEdges; .
theorem TypeOffers.choice_left_fields
    {env : TypeEnvironment} {left right : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.choice left right) TypeLabel.silent left
      current future) :
    current = ∅ ∧ future = typeFutureOffers left := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers <;> simp_all

theorem TypeOffers.choice_right_fields
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
    (hCanonical : left.EntryCanonical)
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
        (compileType_initial_relation_of_canonical signature left
          (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
            hCanonical))
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
    (hCanonical : right.EntryCanonical)
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
        (compileType_initial_relation_of_canonical signature right
          (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
            hCanonical))
  · intro _
    exact ⟨TypeTransition.choice_right env left right hWellFormed,
      TypeOffers.choice_right env left right hWellFormed⟩

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
    (hRightCorrect : CompilationFutureCorrect signature right)
    (hLeftCanonical : left.EntryCanonical)
    (hRightCanonical : right.EntryCanonical) :
    FairChoiceFutureCorrect signature bid left right := by
  apply choiceFutureCorrect_core signature left right
    (TypeLabel.fair bid true) (TypeLabel.fair bid false)
    hLeftCorrect hRightCorrect hLeftCanonical hRightCanonical
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
  sorry -- TODO(redevelopment): body relied on old computeFuture-based
  -- HasResolvedEdge classifiers / resolvedAutomatonEdges; .
theorem compileType_fairChoice_right_child_edge_iff
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature (.fairChoice bid left right)).HasEdge
        (.child 1 source) env label offers (.child 1 target) ↔
      (compileType signature right).HasEdge source env label offers target := by
  sorry -- TODO(redevelopment): body relied on old computeFuture-based
  -- HasResolvedEdge classifiers / resolvedAutomatonEdges; .
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
  sorry -- TODO(redevelopment): body relied on old computeFuture-based
  -- HasResolvedEdge classifiers / resolvedAutomatonEdges; .
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
  sorry -- TODO(redevelopment): body relied on old computeFuture-based
  -- HasResolvedEdge classifiers / resolvedAutomatonEdges; .
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
  sorry -- TODO(redevelopment): body relied on old computeFuture-based
  -- HasResolvedEdge classifiers / resolvedAutomatonEdges; .
theorem TypeOffers.fair_left_fields
    {env : TypeEnvironment} {bid : BranchId} {left right : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.fairChoice bid left right)
      (TypeLabel.fair bid true) left current future) :
    current = ∅ ∧ future = typeFutureOffers left := by
  generalize hLabel : TypeLabel.fair bid true = actualLabel at hOffers
  cases hOffers <;> simp_all

theorem TypeOffers.fair_right_fields
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
    (hCanonical : left.EntryCanonical)
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
        (compileType_initial_relation_of_canonical signature left
          (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
            hCanonical))
  · intro _
    exact ⟨TypeTransition.fair_left env bid left right hWellFormed,
      TypeOffers.fair_left env bid left right hWellFormed⟩

/-- Root-state step correspondence for the taken-right fair branch. -/
theorem compileType_fairChoice_right_selection_step_iff
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : FairChoiceFutureCorrect signature bid left right)
    (hCanonical : right.EntryCanonical)
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
        (compileType_initial_relation_of_canonical signature right
          (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
            hCanonical))
  · intro _
    exact ⟨TypeTransition.fair_right env bid left right hWellFormed,
      TypeOffers.fair_right env bid left right hWellFormed⟩


end

end Pact
