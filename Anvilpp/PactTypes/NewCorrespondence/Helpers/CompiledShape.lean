import Anvilpp.PactTypes.NewCorrespondence.Helpers.EnvironmentAndAlphabet

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-!
### Offer-branch disjointness under reannotation and branch generation
-/

/-- Every branch of a reannotated list comes from a source branch. -/
theorem reannotateBranches_mem
    {alphabet : PactTypeAlphabet} {branches : List (BareMessage × PactType)}
    {item : BareMessage × PactType}
    (hMem : item ∈ PactType.reannotateBranches alphabet branches) :
    ∃ source ∈ branches, item = (source.1, source.2.reannotate alphabet) := by
  induction branches with
  | nil => rw [PactType.reannotateBranches_nil] at hMem; cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      rw [PactType.reannotateBranches_cons, List.mem_cons] at hMem
      rcases hMem with hEq | hTail
      · exact ⟨(action, branchType), by simp, hEq⟩
      · obtain ⟨source, hSource, hEq⟩ := ih hTail
        exact ⟨source, List.mem_cons_of_mem _ hSource, hEq⟩

/-- Reannotation keeps branch heads and structural footprints, so it keeps
declaration-disjointness of a branch list. -/
theorem reannotateBranches_pairwise_branchDeclarationsDisjoint
    (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      List.Pairwise BranchDeclarationsDisjoint branches →
      List.Pairwise BranchDeclarationsDisjoint
        (PactType.reannotateBranches alphabet branches) := by
  intro branches
  induction branches with
  | nil => intro _; rw [PactType.reannotateBranches_nil]; exact List.Pairwise.nil
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      intro hPairwise
      rw [PactType.reannotateBranches_cons, List.pairwise_cons]
      rw [List.pairwise_cons] at hPairwise
      refine ⟨?_, ih hPairwise.2⟩
      intro other hOther
      obtain ⟨source, hSource, hEq⟩ := reannotateBranches_mem hOther
      subst hEq
      have hHead := hPairwise.1 source hSource
      exact ⟨by simpa using hHead.1, by simpa using hHead.2.1,
        by simpa using hHead.2.2⟩

/-- Every branch of a re-signed conjunctive-offer list comes from a source
branch, carrying that branch's own alphabet. -/
theorem reannotateOfferBranches_mem (alphabet : PactTypeAlphabet) :
    ∀ (branches : List (BareMessage × PactType)) (seen : Finset BareMessage)
      (item : BareMessage × PactType),
      item ∈ PactType.reannotateOfferBranches alphabet seen branches →
      ∃ source ∈ branches, ∃ branchAlphabet,
        item = (source.1, source.2.reannotate branchAlphabet) := by
  intro branches
  induction branches with
  | nil =>
      intro seen item hMem
      rw [PactType.reannotateOfferBranches_nil] at hMem
      cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      intro seen item hMem
      rw [PactType.reannotateOfferBranches_cons, List.mem_cons] at hMem
      rcases hMem with hEq | hTail
      · exact ⟨(action, branchType), by simp, alphabet, hEq⟩
      · obtain ⟨source, hSource, branchAlphabet, hEq⟩ := ih _ _ hTail
        exact ⟨source, List.mem_cons_of_mem _ hSource, branchAlphabet, hEq⟩

/-- Re-signing a conjunctive-offer branch list keeps branch heads and
structural footprints, so it keeps declaration-disjointness. -/
theorem reannotateOfferBranches_pairwise_branchDeclarationsDisjoint
    (alphabet : PactTypeAlphabet) :
    ∀ (branches : List (BareMessage × PactType)) (seen : Finset BareMessage),
      List.Pairwise BranchDeclarationsDisjoint branches →
      List.Pairwise BranchDeclarationsDisjoint
        (PactType.reannotateOfferBranches alphabet seen branches) := by
  intro branches
  induction branches with
  | nil =>
      intro seen _
      rw [PactType.reannotateOfferBranches_nil]
      exact List.Pairwise.nil
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      intro seen hPairwise
      rw [PactType.reannotateOfferBranches_cons, List.pairwise_cons]
      rw [List.pairwise_cons] at hPairwise
      refine ⟨?_, ih _ hPairwise.2⟩
      intro other hOther
      obtain ⟨source, hSource, branchAlphabet, hEq⟩ :=
        reannotateOfferBranches_mem alphabet _ _ _ hOther
      subst hEq
      have hHead := hPairwise.1 source hSource
      exact ⟨by simpa using hHead.1, by simpa using hHead.2.1,
        by simpa using hHead.2.2⟩

theorem reannotate_offerBranchesDisjoint :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      processType.OfferBranchesDisjoint →
      (processType.reannotate alphabet).OfferBranchesDisjoint := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ (branches : List (BareMessage × PactType)),
          sizeOf branches < n → ∀ branchAlphabet,
          PactType.OfferBranchesDisjointBranches branches →
          PactType.OfferBranchesDisjointBranches
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches hBranchesSize branchAlphabet hDisjoint
        induction branches with
        | nil =>
            rw [PactType.reannotateBranches_nil]
            simp [PactType.OfferBranchesDisjointBranches]
        | cons head tail restIH =>
            rcases head with ⟨action, branchType⟩
            rw [PactType.reannotateBranches_cons]
            simp only [PactType.OfferBranchesDisjointBranches] at hDisjoint ⊢
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have : sizeOf tail < sizeOf ((action, branchType) :: tail) := by
                simp_wf; omega
              omega
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl branchAlphabet
              hDisjoint.1, restIH hTailSize hDisjoint.2⟩
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType)),
          sizeOf branches < n → ∀ branchAlphabet (seen : Finset BareMessage),
          PactType.OfferBranchesDisjointBranches branches →
          PactType.OfferBranchesDisjointBranches
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches hBranchesSize branchAlphabet
        induction branches with
        | nil =>
            intro seen _
            rw [PactType.reannotateOfferBranches_nil]
            simp [PactType.OfferBranchesDisjointBranches]
        | cons head tail restIH =>
            rcases head with ⟨action, branchType⟩
            intro seen hDisjoint
            rw [PactType.reannotateOfferBranches_cons]
            simp only [PactType.OfferBranchesDisjointBranches] at hDisjoint ⊢
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have : sizeOf tail < sizeOf ((action, branchType) :: tail) := by
                simp_wf; omega
              omega
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl _
              hDisjoint.1, restIH hTailSize _ hDisjoint.2⟩
      intro alphabet hDisjoint
      cases processType with
      | message a m d | progress a p | tock a | skip a | var a _ =>
          simp [PactType.reannotate, PactType.OfferBranchesDisjoint]
      | choice a l r | seq a l r | fairChoice a b l r =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [PactType.reannotate, PactType.OfferBranchesDisjoint]
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf l) hL l rfl alphabet hDisjoint.1,
            ih (sizeOf r) hR r rfl alphabet hDisjoint.2⟩
      | par a l r i =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [PactType.reannotate, PactType.OfferBranchesDisjoint]
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf l) hL l rfl _ hDisjoint.1,
            ih (sizeOf r) hR r rfl _ hDisjoint.2⟩
      | recur a name body =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [PactType.reannotate, PactType.OfferBranchesDisjoint]
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          exact ih (sizeOf body) hB body rfl alphabet hDisjoint
      | xoffer a elseType branches =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [PactType.reannotate, PactType.OfferBranchesDisjoint]
          have hE : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBr : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hE elseType rfl alphabet hDisjoint.1,
            hBranches branches hBr alphabet hDisjoint.2⟩
      | offer a elseType branches =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [PactType.reannotate, PactType.OfferBranchesDisjoint]
          have hE : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBr : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hE elseType rfl alphabet hDisjoint.1,
            reannotateOfferBranches_pairwise_branchDeclarationsDisjoint alphabet
              branches ∅ hDisjoint.2.1,
            hOfferBranches branches hBr alphabet ∅ hDisjoint.2.2⟩

/-- A generated singleton offer has a one-element branch list. -/
theorem singletonTypeXOfferAt_offerBranchesDisjoint
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hBranch : branch.2.OfferBranchesDisjoint) :
    (singletonTypeXOfferAt alphabet branch).OfferBranchesDisjoint := by
  rcases branch with ⟨action, branchType⟩
  simp only [singletonTypeXOfferAt, PactType.OfferBranchesDisjoint,
    PactType.OfferBranchesDisjointBranches]
  exact ⟨trivial,
    reannotate_offerBranchesDisjoint branchType alphabet hBranch, trivial⟩

/-- A committed branch is a mandatory action followed by the continuation. -/
theorem selectedTypeBranchAt_offerBranchesDisjoint
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hBranch : branch.2.OfferBranchesDisjoint) :
    (selectedTypeBranchAt alphabet branch).OfferBranchesDisjoint := by
  rcases branch with ⟨action, branchType⟩
  simp only [selectedTypeBranchAt, PactType.OfferBranchesDisjoint]
  exact ⟨trivial, reannotate_offerBranchesDisjoint branchType alphabet hBranch⟩

/-- The generated branch product only introduces singleton offers. -/
theorem parallelTypeBranchesWithin_offerBranchesDisjoint
    (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      (∀ branch ∈ branches, branch.2.OfferBranchesDisjoint) →
      (parallelTypeBranchesWithin alphabet branches).OfferBranchesDisjoint
  | [], _ => by simp [parallelTypeBranchesWithin, PactType.OfferBranchesDisjoint]
  | [branch], hBranches =>
      singletonTypeXOfferAt_offerBranchesDisjoint alphabet branch
        (hBranches branch (by simp))
  | branch :: next :: rest, hBranches => by
      simp only [parallelTypeBranchesWithin, PactType.OfferBranchesDisjoint]
      exact ⟨singletonTypeXOfferAt_offerBranchesDisjoint _ branch
          (hBranches branch (by simp)),
        parallelTypeBranchesWithin_offerBranchesDisjoint _ (next :: rest)
          (fun item hItem => hBranches item (by simp [hItem]))⟩

/-- Committing one branch of the generated product keeps the property. -/
theorem parallelTypeBranchesSelectingWithin_offerBranchesDisjoint
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType),
      (∀ branch ∈ branches, branch.2.OfferBranchesDisjoint) →
      PactType.OfferBranchesDisjoint
        (parallelTypeBranchesSelectingWithin alphabet selected branches)
  | [], _ => by
      simp [parallelTypeBranchesSelectingWithin, PactType.OfferBranchesDisjoint]
  | [branch], hBranches => by
      by_cases hSelected : branch = selected
      · simp only [parallelTypeBranchesSelectingWithin, if_pos hSelected]
        exact selectedTypeBranchAt_offerBranchesDisjoint alphabet branch
          (hBranches branch (by simp))
      · simp only [parallelTypeBranchesSelectingWithin, if_neg hSelected]
        exact singletonTypeXOfferAt_offerBranchesDisjoint alphabet branch
          (hBranches branch (by simp))
  | branch :: next :: rest, hBranches => by
      by_cases hSelected : branch = selected
      · simp only [parallelTypeBranchesSelectingWithin, if_pos hSelected,
          PactType.OfferBranchesDisjoint]
        exact ⟨selectedTypeBranchAt_offerBranchesDisjoint _ branch
            (hBranches branch (by simp)),
          parallelTypeBranchesWithin_offerBranchesDisjoint _ (next :: rest)
            (fun item hItem => hBranches item (by simp [hItem]))⟩
      · simp only [parallelTypeBranchesSelectingWithin, if_neg hSelected,
          PactType.OfferBranchesDisjoint]
        exact ⟨singletonTypeXOfferAt_offerBranchesDisjoint _ branch
            (hBranches branch (by simp)),
          parallelTypeBranchesSelectingWithin_offerBranchesDisjoint _ selected
            (next :: rest) (fun item hItem => hBranches item (by simp [hItem]))⟩

/-- Committing a conjunctive offer keeps offer-branch disjointness. -/
theorem parallelTypeBranchesSelecting_offerBranchesDisjoint
    (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hBranches : ∀ branch ∈ branches, branch.2.OfferBranchesDisjoint) :
    (parallelTypeBranchesSelecting alphabet selected branches).OfferBranchesDisjoint := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.OfferBranchesDisjoint]
  | cons branch rest =>
      exact parallelTypeBranchesSelectingWithin_offerBranchesDisjoint _ selected
        (branch :: rest) hBranches

/-- Branch bodies of an offer whose branches are disjoint inherit the
property. -/
theorem offerBranchesDisjoint_of_mem
    {branches : List (BareMessage × PactType)}
    (hDisjoint : PactType.OfferBranchesDisjointBranches branches)
    {action : BareMessage} {branchType : PactType}
    (hMem : (action, branchType) ∈ branches) :
    branchType.OfferBranchesDisjoint := by
  induction branches with
  | nil => cases hMem
  | cons head tail ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.OfferBranchesDisjointBranches] at hDisjoint
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hTail
      · cases hEq
        exact hDisjoint.1
      · exact ih hDisjoint.2 hTail

/-- The pair form of `offerBranchesDisjoint_of_mem`. -/
theorem offerBranchesDisjoint_of_mem_branch
    {branches : List (BareMessage × PactType)}
    (hDisjoint : PactType.OfferBranchesDisjointBranches branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    branch.2.OfferBranchesDisjoint := by
  rcases branch with ⟨action, branchType⟩
  exact offerBranchesDisjoint_of_mem hDisjoint hMem

/-!
### The compiled shape

Re-stamping a type changes no state, entry, or accepting state of the compiled
fragment, provided every conjunctive offer below it has pairwise disjoint
branch declarations.  Disjointness is what pins the committed branch down:
the generated product selects it by comparing whole branches, and re-stamping
erases the annotations that would otherwise tell two branches apart.
-/

namespace CompiledShape

/-- Two compiled fragments have the same carrier, entry, and accepting set. -/
def ShapeEq (first second : AutomatonFragment) : Prop :=
  first.states = second.states ∧ first.initial = second.initial ∧
    first.accepting = second.accepting

theorem ShapeEq.symm {first second : AutomatonFragment} (h : ShapeEq first second) :
    ShapeEq second first := ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem ShapeEq.trans {a b c : AutomatonFragment} (h1 : ShapeEq a b)
    (h2 : ShapeEq b c) : ShapeEq a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

/-- Zero fuel compiles every type to the same defensive fragment. -/
theorem shapeEq_zero (first second : PactType) :
    ShapeEq (compileTypeFuel 0 first) (compileTypeFuel 0 second) := by
  simp [compileTypeFuel, ShapeEq]

/-! ### Congruence of the constructor builders in the compiled shape -/

theorem indexedFragmentStates_congr :
    ∀ (first second : List (BareMessage × AutomatonFragment)),
      List.Forall₂ (fun x y => x.2.states = y.2.states) first second →
      indexedFragmentStates first = indexedFragmentStates second := by
  have general : ∀ (first second : List (BareMessage × AutomatonFragment)),
      List.Forall₂ (fun x y => x.2.states = y.2.states) first second →
      ∀ (index : Nat) (acc : Finset TypeAutomatonState),
        (first.zipIdx index).foldl (fun states indexed =>
            states ∪ childStates (indexed.2 + 1) indexed.1.2) acc =
          (second.zipIdx index).foldl (fun states indexed =>
            states ∪ childStates (indexed.2 + 1) indexed.1.2) acc := by
    intro first second hRel
    induction hRel with
    | nil => intro index acc; simp
    | cons hHead hTail ih =>
        intro index acc
        simp only [List.zipIdx_cons, List.foldl_cons]
        rw [ih (index + 1) (acc ∪ childStates (index + 1) _)]
        simp [childStates, hHead]
  intro first second hRel
  exact general first second hRel 0 ∅

theorem indexedFragmentAccepting_congr :
    ∀ (first second : List (BareMessage × AutomatonFragment)),
      List.Forall₂ (fun x y => x.2.accepting = y.2.accepting) first second →
      indexedFragmentAccepting first = indexedFragmentAccepting second := by
  have general : ∀ (first second : List (BareMessage × AutomatonFragment)),
      List.Forall₂ (fun x y => x.2.accepting = y.2.accepting) first second →
      ∀ (index : Nat) (acc : Finset TypeAutomatonState),
        (first.zipIdx index).foldl (fun states indexed =>
            states ∪ childAccepting (indexed.2 + 1) indexed.1.2) acc =
          (second.zipIdx index).foldl (fun states indexed =>
            states ∪ childAccepting (indexed.2 + 1) indexed.1.2) acc := by
    intro first second hRel
    induction hRel with
    | nil => intro index acc; simp
    | cons hHead hTail ih =>
        intro index acc
        simp only [List.zipIdx_cons, List.foldl_cons]
        rw [ih (index + 1) (acc ∪ childAccepting (index + 1) _)]
        simp [childAccepting, hHead]
  intro first second hRel
  exact general first second hRel 0 ∅

theorem buildChoiceAutomaton_shapeEq
    (firstAlphabet secondAlphabet : PactTypeAlphabet)
    (firstLeft firstRight secondLeft secondRight : AutomatonFragment)
    (l1 r1 l2 r2 : TypeLabel)
    (hLeft : ShapeEq firstLeft secondLeft)
    (hRight : ShapeEq firstRight secondRight) :
    ShapeEq (buildChoiceAutomaton firstAlphabet firstLeft firstRight l1 r1)
      (buildChoiceAutomaton secondAlphabet secondLeft secondRight l2 r2) :=
  ⟨by simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
      hLeft.1, hRight.1], rfl,
   by simp [buildChoiceAutomaton, finishAutomatonFragment, childAccepting,
      hLeft.2.2, hRight.2.2]⟩

theorem buildRecursionAutomaton_shapeEq
    (firstAlphabet secondAlphabet : PactTypeAlphabet) (name : String)
    (firstBody secondBody : AutomatonFragment)
    (hBody : ShapeEq firstBody secondBody) :
    ShapeEq (buildRecursionAutomaton firstAlphabet name firstBody)
      (buildRecursionAutomaton secondAlphabet name secondBody) :=
  ⟨by simp [buildRecursionAutomaton, finishAutomatonFragment, childStates,
      hBody.1], rfl,
   by simp [buildRecursionAutomaton, finishAutomatonFragment, childAccepting,
      hBody.2.2]⟩

theorem buildSequenceAutomaton_shapeEq
    (firstLeft firstRight secondLeft secondRight : AutomatonFragment)
    (hLeft : ShapeEq firstLeft secondLeft)
    (hRight : ShapeEq firstRight secondRight) :
    ShapeEq (buildSequenceAutomaton firstLeft firstRight)
      (buildSequenceAutomaton secondLeft secondRight) :=
  ⟨by simp [buildSequenceAutomaton, finishAutomatonFragment, childStates,
      sequenceDeleted, hLeft.1, hLeft.2.1, hLeft.2.2, hRight.1],
   by simp [buildSequenceAutomaton, finishAutomatonFragment, childState,
      hLeft.2.1],
   by simp [buildSequenceAutomaton, finishAutomatonFragment, childAccepting,
      hRight.2.2]⟩

theorem buildParallelAutomaton_shapeEq
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (parentAlphabet' leftAlphabet' rightAlphabet' : PactTypeAlphabet)
    (interface : Interface)
    (firstLeft firstRight firstRestampedLeft firstRestampedRight
      secondLeft secondRight secondRestampedLeft secondRestampedRight :
        AutomatonFragment)
    (f1 f2 f3 f4 g1 g2 g3 g4 : TypeAutomatonState → Finset BareMessage)
    (hLeft : ShapeEq firstLeft secondLeft)
    (hRight : ShapeEq firstRight secondRight) :
    ShapeEq
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface firstLeft firstRight firstRestampedLeft firstRestampedRight
        f1 f2 f3 f4)
      (buildParallelAutomaton parentAlphabet' leftAlphabet' rightAlphabet'
        interface secondLeft secondRight secondRestampedLeft
        secondRestampedRight g1 g2 g3 g4) :=
  ⟨by simp [buildParallelAutomaton, finishAutomatonFragment, hLeft.1, hRight.1],
   by simp [buildParallelAutomaton, finishAutomatonFragment, hLeft.2.1,
      hRight.2.1],
   by simp [buildParallelAutomaton, finishAutomatonFragment]⟩

theorem buildExclusiveOfferAutomaton_shapeEq
    (firstAlphabet secondAlphabet : PactTypeAlphabet)
    (firstBranches secondBranches : List (BareMessage × PactType))
    (firstElse secondElse : AutomatonFragment)
    (firstAutomata secondAutomata : List (BareMessage × AutomatonFragment))
    (hElse : ShapeEq firstElse secondElse)
    (hAutomata : List.Forall₂ (fun x y => ShapeEq x.2 y.2)
      firstAutomata secondAutomata) :
    ShapeEq
      (buildExclusiveOfferAutomaton firstAlphabet firstBranches firstElse
        firstAutomata)
      (buildExclusiveOfferAutomaton secondAlphabet secondBranches secondElse
        secondAutomata) :=
  ⟨by simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        childStates, hElse.1,
        indexedFragmentStates_congr firstAutomata secondAutomata
          (hAutomata.imp fun _ _ h => h.1)], rfl,
   by simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        childAccepting, hElse.2.2,
        indexedFragmentAccepting_congr firstAutomata secondAutomata
          (hAutomata.imp fun _ _ h => h.2.2)]⟩

theorem buildSelectedConjunctiveOfferAutomaton_shapeEq
    (firstAlphabet secondAlphabet : PactTypeAlphabet)
    (firstBranches secondBranches : List (BareMessage × PactType))
    (firstElse secondElse : AutomatonFragment)
    (firstAutomata secondAutomata : List (BareMessage × AutomatonFragment))
    (hElse : ShapeEq firstElse secondElse)
    (hAutomata : List.Forall₂ (fun x y => ShapeEq x.2 y.2)
      firstAutomata secondAutomata) :
    ShapeEq
      (buildSelectedConjunctiveOfferAutomaton firstAlphabet firstBranches
        firstElse firstAutomata)
      (buildSelectedConjunctiveOfferAutomaton secondAlphabet secondBranches
        secondElse secondAutomata) :=
  ⟨by simp only [buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, childStates, hElse.1,
        indexedFragmentStates_congr firstAutomata secondAutomata
          (hAutomata.imp fun _ _ h => h.1)], rfl,
   by simp only [buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, childAccepting, hElse.2.2,
        indexedFragmentAccepting_congr firstAutomata secondAutomata
          (hAutomata.imp fun _ _ h => h.2.2)]⟩

theorem forall₂_map_map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → γ} {g : β → δ} {first : List α} {second : List β}
    (h : ∀ a b, R a b → S (f a) (g b))
    (hRel : List.Forall₂ R first second) :
    List.Forall₂ S (first.map f) (second.map g) := by
  induction hRel with
  | nil => simp
  | cons hHead _ ih => exact List.Forall₂.cons (h _ _ hHead) ih

/-! ### Compiled-shape congruence, one constructor at a time -/

theorem shapeEq_choice (fuel : Nat) (a1 a2 : PactTypeAlphabet)
    (l1 r1 l2 r2 : PactType)
    (hLeft : ShapeEq (compileTypeFuel fuel l1) (compileTypeFuel fuel l2))
    (hRight : ShapeEq (compileTypeFuel fuel r1) (compileTypeFuel fuel r2)) :
    ShapeEq (compileTypeFuel (fuel + 1) (.choice a1 l1 r1))
      (compileTypeFuel (fuel + 1) (.choice a2 l2 r2)) := by
  simp only [compileTypeFuel]
  exact buildChoiceAutomaton_shapeEq _ _ _ _ _ _ _ _ _ _ hLeft hRight

theorem shapeEq_fairChoice (fuel : Nat) (a1 a2 : PactTypeAlphabet) (bid : BranchId)
    (l1 r1 l2 r2 : PactType)
    (hLeft : ShapeEq (compileTypeFuel fuel l1) (compileTypeFuel fuel l2))
    (hRight : ShapeEq (compileTypeFuel fuel r1) (compileTypeFuel fuel r2)) :
    ShapeEq (compileTypeFuel (fuel + 1) (.fairChoice a1 bid l1 r1))
      (compileTypeFuel (fuel + 1) (.fairChoice a2 bid l2 r2)) := by
  simp only [compileTypeFuel]
  exact buildChoiceAutomaton_shapeEq _ _ _ _ _ _ _ _ _ _ hLeft hRight

theorem shapeEq_recur (fuel : Nat) (a1 a2 : PactTypeAlphabet) (name : String)
    (b1 b2 : PactType)
    (hBody : ShapeEq (compileTypeFuel fuel b1) (compileTypeFuel fuel b2)) :
    ShapeEq (compileTypeFuel (fuel + 1) (.recur a1 name b1))
      (compileTypeFuel (fuel + 1) (.recur a2 name b2)) := by
  simp only [compileTypeFuel]
  exact buildRecursionAutomaton_shapeEq _ _ _ _ _ hBody

theorem shapeEq_seq (fuel : Nat) (a1 a2 : PactTypeAlphabet)
    (l1 r1 l2 r2 : PactType)
    (hLeft : ShapeEq (compileTypeFuel fuel l1) (compileTypeFuel fuel l2))
    (hRight : ShapeEq (compileTypeFuel fuel r1) (compileTypeFuel fuel r2)) :
    ShapeEq (compileTypeFuel (fuel + 1) (.seq a1 l1 r1))
      (compileTypeFuel (fuel + 1) (.seq a2 l2 r2)) := by
  simp only [compileTypeFuel]
  exact buildSequenceAutomaton_shapeEq _ _ _ _ hLeft hRight

theorem shapeEq_par (fuel : Nat) (a1 a2 : PactTypeAlphabet)
    (l1 r1 l2 r2 : PactType) (interface : Interface)
    (hLeft : ShapeEq (compileTypeFuel fuel l1) (compileTypeFuel fuel l2))
    (hRight : ShapeEq (compileTypeFuel fuel r1) (compileTypeFuel fuel r2)) :
    ShapeEq (compileTypeFuel (fuel + 1) (.par a1 l1 r1 interface))
      (compileTypeFuel (fuel + 1) (.par a2 l2 r2 interface)) := by
  simp only [compileTypeFuel]
  exact buildParallelAutomaton_shapeEq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ hLeft hRight

theorem shapeEq_xoffer (fuel : Nat) (a1 a2 : PactTypeAlphabet)
    (e1 e2 : PactType) (bs1 bs2 : List (BareMessage × PactType))
    (hElse : ShapeEq (compileTypeFuel fuel e1) (compileTypeFuel fuel e2))
    (hBranches : List.Forall₂ (fun b1 b2 =>
      ShapeEq (compileTypeFuel fuel b1.2) (compileTypeFuel fuel b2.2)) bs1 bs2) :
    ShapeEq (compileTypeFuel (fuel + 1) (.xoffer a1 e1 bs1))
      (compileTypeFuel (fuel + 1) (.xoffer a2 e2 bs2)) := by
  simp only [compileTypeFuel]
  exact buildExclusiveOfferAutomaton_shapeEq _ _ _ _ _ _ _ _ hElse
    (forall₂_map_map (fun _ _ h => h) hBranches)

theorem shapeEq_offer (fuel : Nat) (a1 a2 : PactTypeAlphabet)
    (e1 e2 : PactType) (bs1 bs2 : List (BareMessage × PactType))
    (hElse : ShapeEq (compileTypeFuel fuel e1) (compileTypeFuel fuel e2))
    (hBranches : List.Forall₂ (fun s1 s2 =>
      ShapeEq (compileTypeFuel fuel (parallelTypeBranchesSelecting a1 s1 bs1))
        (compileTypeFuel fuel (parallelTypeBranchesSelecting a2 s2 bs2)))
      bs1 bs2) :
    ShapeEq (compileTypeFuel (fuel + 1) (.offer a1 e1 bs1))
      (compileTypeFuel (fuel + 1) (.offer a2 e2 bs2)) := by
  simp only [compileTypeFuel]
  exact buildSelectedConjunctiveOfferAutomaton_shapeEq _ _ _ _ _ _ _ _ hElse
    (forall₂_map_map (fun _ _ h => h) hBranches)

/-! ### Atoms ignore their alphabet in the compiled shape -/

theorem shapeEq_skip (fuel : Nat) (a1 a2 : PactTypeAlphabet) :
    ShapeEq (compileTypeFuel fuel (.skip a1)) (compileTypeFuel fuel (.skip a2)) := by
  cases fuel with
  | zero => exact shapeEq_zero _ _
  | succ f => simp [compileTypeFuel, finishAutomatonFragment, ShapeEq]

theorem shapeEq_message (fuel : Nat) (a1 a2 : PactTypeAlphabet) (msg : MessageId)
    (dir : MessageDir) :
    ShapeEq (compileTypeFuel fuel (.message a1 msg dir))
      (compileTypeFuel fuel (.message a2 msg dir)) := by
  cases fuel with
  | zero => exact shapeEq_zero _ _
  | succ f => simp [compileTypeFuel, finishAutomatonFragment, ShapeEq]

theorem shapeEq_tock (fuel : Nat) (a1 a2 : PactTypeAlphabet) :
    ShapeEq (compileTypeFuel fuel (.tock a1)) (compileTypeFuel fuel (.tock a2)) := by
  cases fuel with
  | zero => exact shapeEq_zero _ _
  | succ f => simp [compileTypeFuel, finishAutomatonFragment, ShapeEq]

theorem shapeEq_progress (fuel : Nat) (a1 a2 : PactTypeAlphabet) (pid : ProcId) :
    ShapeEq (compileTypeFuel fuel (.progress a1 pid))
      (compileTypeFuel fuel (.progress a2 pid)) := by
  cases fuel with
  | zero => exact shapeEq_zero _ _
  | succ f => simp [compileTypeFuel, finishAutomatonFragment, ShapeEq]

theorem shapeEq_var (fuel : Nat) (a1 a2 : PactTypeAlphabet) (name : String) :
    ShapeEq (compileTypeFuel fuel (.var a1 name))
      (compileTypeFuel fuel (.var a2 name)) := by
  cases fuel with
  | zero => exact shapeEq_zero _ _
  | succ f => simp [compileTypeFuel, finishAutomatonFragment, ShapeEq]

/-! ### The generated branch product -/

theorem reannotateBranches_eq_map (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      PactType.reannotateBranches alphabet branches =
        branches.map fun branch => (branch.1, branch.2.reannotate alphabet)
  | [] => by simp
  | (action, branchType) :: rest => by
      simp [PactType.reannotateBranches_cons, reannotateBranches_eq_map alphabet rest]

/-- The alphabet `reannotateOfferBranches` hands to the branch whose head
action is `target`: every branch carries the whole enclosing alphabet. -/
def offerBranchAlphabet (alphabet : PactTypeAlphabet) :
    Finset BareMessage → List (BareMessage × PactType) → BareMessage →
      PactTypeAlphabet
  | _, _, _ => alphabet

/-- Every branch carries the enclosing alphabet, so re-signing a conjunctive
offer is a map. -/
theorem reannotateOfferBranches_eq_map (alphabet : PactTypeAlphabet) :
    ∀ (branches : List (BareMessage × PactType)) (seen : Finset BareMessage),
      List.Pairwise (fun first second => first.1 ≠ second.1) branches →
      PactType.reannotateOfferBranches alphabet seen branches =
        branches.map fun branch =>
          (branch.1, branch.2.reannotate
            (offerBranchAlphabet alphabet seen branches branch.1))
  | [], seen, _ => by
      simp [PactType.reannotateOfferBranches_nil]
  | (action, branchType) :: tail, seen, hPairwise => by
      rw [PactType.reannotateOfferBranches_cons, List.map_cons,
        reannotateOfferBranches_eq_map alphabet tail seen
          (List.pairwise_cons.mp hPairwise).2]
      simp [offerBranchAlphabet]

theorem shapeEq_singletonTypeXOfferAt (fuel : Nat) (a1 a2 : PactTypeAlphabet)
    (action : BareMessage) (t1 t2 : PactType)
    (hBody : ShapeEq (compileTypeFuel fuel (t1.reannotate a1))
      (compileTypeFuel fuel (t2.reannotate a2))) :
    ShapeEq (compileTypeFuel (fuel + 1) (singletonTypeXOfferAt a1 (action, t1)))
      (compileTypeFuel (fuel + 1) (singletonTypeXOfferAt a2 (action, t2))) := by
  simp only [singletonTypeXOfferAt]
  exact shapeEq_xoffer fuel a1 a2 _ _ _ _ (shapeEq_skip fuel a1 a2)
    (List.Forall₂.cons hBody List.Forall₂.nil)

theorem shapeEq_selectedTypeBranchAt (fuel : Nat) (a1 a2 : PactTypeAlphabet)
    (action : BareMessage) (t1 t2 : PactType)
    (hBody : ShapeEq (compileTypeFuel fuel (t1.reannotate a1))
      (compileTypeFuel fuel (t2.reannotate a2))) :
    ShapeEq (compileTypeFuel (fuel + 1) (selectedTypeBranchAt a1 (action, t1)))
      (compileTypeFuel (fuel + 1) (selectedTypeBranchAt a2 (action, t2))) := by
  simp only [selectedTypeBranchAt]
  exact shapeEq_seq fuel a1 a2 _ _ _ _ (shapeEq_message fuel a1 a2 _ _) hBody

theorem shapeEq_double_reannotate (fuel : Nat)
    (hStable : ∀ m, m ≤ fuel → ∀ t : PactType, t.OfferBranchesDisjoint →
      ∀ alpha, ShapeEq (compileTypeFuel m (t.reannotate alpha))
        (compileTypeFuel m t))
    (m : Nat) (hm : m ≤ fuel) (processType : PactType)
    (hDisjoint : processType.OfferBranchesDisjoint)
    (source a1 a2 : PactTypeAlphabet) :
    ShapeEq (compileTypeFuel m ((processType.reannotate source).reannotate a1))
      (compileTypeFuel m (processType.reannotate a2)) :=
  ((hStable m hm _ (reannotate_offerBranchesDisjoint processType source hDisjoint)
      a1).trans (hStable m hm processType hDisjoint source)).trans
    (hStable m hm processType hDisjoint a2).symm

theorem shapeEq_singletonTypeXOfferAt_stable (fuel : Nat)
    (hStable : ∀ m, m ≤ fuel → ∀ t : PactType, t.OfferBranchesDisjoint →
      ∀ alpha, ShapeEq (compileTypeFuel m (t.reannotate alpha))
        (compileTypeFuel m t))
    (action : BareMessage) (branchType : PactType)
    (hDisjoint : branchType.OfferBranchesDisjoint)
    (source a1 a2 : PactTypeAlphabet) :
    ShapeEq
      (compileTypeFuel fuel
        (singletonTypeXOfferAt a1 (action, branchType.reannotate source)))
      (compileTypeFuel fuel (singletonTypeXOfferAt a2 (action, branchType))) := by
  cases fuel with
  | zero => exact shapeEq_zero _ _
  | succ f =>
      exact shapeEq_singletonTypeXOfferAt f a1 a2 action _ _
        (shapeEq_double_reannotate (f + 1) hStable f (Nat.le_succ f) branchType
          hDisjoint source a1 a2)

theorem shapeEq_selectedTypeBranchAt_stable (fuel : Nat)
    (hStable : ∀ m, m ≤ fuel → ∀ t : PactType, t.OfferBranchesDisjoint →
      ∀ alpha, ShapeEq (compileTypeFuel m (t.reannotate alpha))
        (compileTypeFuel m t))
    (action : BareMessage) (branchType : PactType)
    (hDisjoint : branchType.OfferBranchesDisjoint)
    (source a1 a2 : PactTypeAlphabet) :
    ShapeEq
      (compileTypeFuel fuel
        (selectedTypeBranchAt a1 (action, branchType.reannotate source)))
      (compileTypeFuel fuel (selectedTypeBranchAt a2 (action, branchType))) := by
  cases fuel with
  | zero => exact shapeEq_zero _ _
  | succ f =>
      exact shapeEq_selectedTypeBranchAt f a1 a2 action _ _
        (shapeEq_double_reannotate (f + 1) hStable f (Nat.le_succ f) branchType
          hDisjoint source a1 a2)

theorem shapeEq_parallelTypeBranchesWithin :
    ∀ (branches : List (BareMessage × PactType)) (fuel : Nat),
      (∀ m, m ≤ fuel → ∀ t : PactType, t.OfferBranchesDisjoint →
        ∀ alpha, ShapeEq (compileTypeFuel m (t.reannotate alpha))
          (compileTypeFuel m t)) →
      (∀ branch ∈ branches, branch.2.OfferBranchesDisjoint) →
      ∀ (source : BareMessage × PactType → PactTypeAlphabet)
        (a1 a2 : PactTypeAlphabet),
        ShapeEq
          (compileTypeFuel fuel (parallelTypeBranchesWithin a1
            (branches.map fun branch =>
              (branch.1, branch.2.reannotate (source branch)))))
          (compileTypeFuel fuel (parallelTypeBranchesWithin a2 branches)) := by
  intro branches
  induction branches with
  | nil =>
      intro fuel _ _ source a1 a2
      simp only [List.map_nil, parallelTypeBranchesWithin]
      exact shapeEq_skip fuel a1 a2
  | cons head tail ih =>
      intro fuel hStable hDisjoint source a1 a2
      cases fuel with
      | zero => exact shapeEq_zero _ _
      | succ f =>
          rcases head with ⟨action, headType⟩
          have hHead : headType.OfferBranchesDisjoint :=
            hDisjoint (action, headType) (by simp)
          have hSmaller : ∀ m, m ≤ f → ∀ t : PactType, t.OfferBranchesDisjoint →
              ∀ alpha, ShapeEq (compileTypeFuel m (t.reannotate alpha))
                (compileTypeFuel m t) :=
            fun m hm => hStable m (Nat.le_succ_of_le hm)
          cases tail with
          | nil =>
              simp only [List.map_cons, List.map_nil,
                parallelTypeBranchesWithin]
              exact shapeEq_singletonTypeXOfferAt_stable (f + 1) hStable action
                headType hHead (source (action, headType)) _ _
          | cons next rest =>
              simp only [List.map_cons, parallelTypeBranchesWithin]
              exact shapeEq_par f _ _ _ _ _ _ ∅
                (shapeEq_singletonTypeXOfferAt_stable f hSmaller action headType
                  hHead (source (action, headType)) _ _)
                (ih f hSmaller
                  (fun branch hBranch =>
                    hDisjoint branch (List.mem_cons_of_mem _ hBranch))
                  source _ _)

theorem shapeEq_parallelTypeBranchesSelectingWithin :
    ∀ (branches : List (BareMessage × PactType)) (fuel : Nat),
      (∀ m, m ≤ fuel → ∀ t : PactType, t.OfferBranchesDisjoint →
        ∀ alpha, ShapeEq (compileTypeFuel m (t.reannotate alpha))
          (compileTypeFuel m t)) →
      List.Pairwise (fun first second => first.1 ≠ second.1) branches →
      (∀ branch ∈ branches, branch.2.OfferBranchesDisjoint) →
      ∀ (source : BareMessage × PactType → PactTypeAlphabet)
        (a1 a2 : PactTypeAlphabet) (selected : BareMessage × PactType),
        selected ∈ branches →
        ShapeEq
          (compileTypeFuel fuel (parallelTypeBranchesSelectingWithin a1
            (selected.1, selected.2.reannotate (source selected))
            (branches.map fun branch =>
              (branch.1, branch.2.reannotate (source branch)))))
          (compileTypeFuel fuel
            (parallelTypeBranchesSelectingWithin a2 selected branches)) := by
  intro branches
  induction branches with
  | nil => intro _ _ _ _ _ _ _ selected hSelected; simp at hSelected
  | cons head tail ih =>
      intro fuel hStable hPairwise hDisjoint source a1 a2 selected hSelected
      cases fuel with
      | zero => exact shapeEq_zero _ _
      | succ f =>
          have hSmaller : ∀ m, m ≤ f → ∀ t : PactType, t.OfferBranchesDisjoint →
              ∀ alpha, ShapeEq (compileTypeFuel m (t.reannotate alpha))
                (compileTypeFuel m t) :=
            fun m hm => hStable m (Nat.le_succ_of_le hm)
          obtain ⟨hHeadDistinct, hTailPairwise⟩ := List.pairwise_cons.mp hPairwise
          have hHead : head.2.OfferBranchesDisjoint := hDisjoint head (by simp)
          have hTailDisjoint : ∀ branch ∈ tail, branch.2.OfferBranchesDisjoint :=
            fun branch hBranch => hDisjoint branch (List.mem_cons_of_mem _ hBranch)
          cases tail with
          | nil =>
              have hEq : selected = head := by simpa using hSelected
              subst hEq
              simp only [List.map_cons, List.map_nil,
                parallelTypeBranchesSelectingWithin]
              exact shapeEq_selectedTypeBranchAt_stable (f + 1) hStable
                selected.1 selected.2 hHead (source selected) _ _
          | cons next rest =>
              by_cases hIsHead : head = selected
              · subst hIsHead
                simp only [List.map_cons, parallelTypeBranchesSelectingWithin]
                exact shapeEq_par f _ _ _ _ _ _ ∅
                  (shapeEq_selectedTypeBranchAt_stable f hSmaller head.1 head.2
                    hHead (source head) _ _)
                  (shapeEq_parallelTypeBranchesWithin (next :: rest) f hSmaller
                    hTailDisjoint source _ _)
              · have hInTail : selected ∈ next :: rest := by
                  rcases List.mem_cons.mp hSelected with hEq | hTail
                  · exact absurd hEq.symm hIsHead
                  · exact hTail
                have hHeadNe : head.1 ≠ selected.1 := hHeadDistinct selected hInTail
                have hMappedNe :
                    ((head.1, head.2.reannotate (source head)) :
                      BareMessage × PactType) ≠
                      (selected.1, selected.2.reannotate (source selected)) := by
                  intro hEq
                  rw [Prod.mk.injEq] at hEq
                  exact hHeadNe hEq.1
                simp only [List.map_cons, parallelTypeBranchesSelectingWithin,
                  if_neg hMappedNe, if_neg hIsHead]
                exact shapeEq_par f _ _ _ _ _ _ ∅
                  (shapeEq_singletonTypeXOfferAt_stable f hSmaller head.1 head.2
                    hHead (source head) _ _)
                  (ih f hSmaller hTailPairwise hTailDisjoint source _ _ selected
                    hInTail)

theorem forall₂_map_left_of_mem {α β : Type} {R : β → α → Prop} {l : List α}
    {f : α → β} (h : ∀ x ∈ l, R (f x) x) : List.Forall₂ R (l.map f) l := by
  induction l with
  | nil => simp
  | cons head tail ih =>
      exact List.Forall₂.cons (h head (by simp))
        (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem heads_ne_of_branchDeclarationsDisjoint
    {first second : BareMessage × PactType}
    (hBranch : BranchDeclarationsDisjoint first second) : first.1 ≠ second.1 := by
  intro hEq
  have hFirst : first.1 ∈ ({first.1} ∪ PactType.MessageActions first.2) := by simp
  have hSecond : first.1 ∈ ({second.1} ∪ PactType.MessageActions second.2) := by
    simp [hEq]
  exact Finset.disjoint_left.mp hBranch.1 hFirst hSecond

theorem compileTypeFuel_shapeEq_reannotate (fuel : Nat) :
    ∀ processType : PactType, processType.OfferBranchesDisjoint →
      ∀ alphabet : PactTypeAlphabet,
        ShapeEq (compileTypeFuel fuel (processType.reannotate alphabet))
          (compileTypeFuel fuel processType) := by
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
      intro processType hDisjoint alphabet
      cases fuel with
      | zero => exact shapeEq_zero _ _
      | succ f =>
          have hStable : ∀ m, m ≤ f → ∀ t : PactType, t.OfferBranchesDisjoint →
              ∀ alpha, ShapeEq (compileTypeFuel m (t.reannotate alpha))
                (compileTypeFuel m t) :=
            fun m hm => ih m (Nat.lt_succ_of_le hm)
          cases processType with
          | message a msg dir =>
              simp only [PactType.reannotate]
              exact shapeEq_message _ _ _ _ _
          | progress a pid =>
              simp only [PactType.reannotate]
              exact shapeEq_progress _ _ _ _
          | tock a =>
              simp only [PactType.reannotate]
              exact shapeEq_tock _ _ _
          | skip a =>
              simp only [PactType.reannotate]
              exact shapeEq_skip _ _ _
          | var a name =>
              simp only [PactType.reannotate]
              exact shapeEq_var _ _ _ _
          | recur a name body =>
              simp only [PactType.OfferBranchesDisjoint] at hDisjoint
              simp only [PactType.reannotate]
              exact shapeEq_recur f _ _ name _ _
                (hStable f le_rfl body hDisjoint alphabet)
          | choice a left right =>
              simp only [PactType.OfferBranchesDisjoint] at hDisjoint
              simp only [PactType.reannotate]
              exact shapeEq_choice f _ _ _ _ _ _
                (hStable f le_rfl left hDisjoint.1 alphabet)
                (hStable f le_rfl right hDisjoint.2 alphabet)
          | fairChoice a bid left right =>
              simp only [PactType.OfferBranchesDisjoint] at hDisjoint
              simp only [PactType.reannotate]
              exact shapeEq_fairChoice f _ _ bid _ _ _ _
                (hStable f le_rfl left hDisjoint.1 alphabet)
                (hStable f le_rfl right hDisjoint.2 alphabet)
          | seq a left right =>
              simp only [PactType.OfferBranchesDisjoint] at hDisjoint
              simp only [PactType.reannotate]
              exact shapeEq_seq f _ _ _ _ _ _
                (hStable f le_rfl left hDisjoint.1 alphabet)
                (hStable f le_rfl right hDisjoint.2 alphabet)
          | par a left right interface =>
              simp only [PactType.OfferBranchesDisjoint] at hDisjoint
              simp only [PactType.reannotate]
              exact shapeEq_par f _ _ _ _ _ _ interface
                (hStable f le_rfl left hDisjoint.1 _)
                (hStable f le_rfl right hDisjoint.2 _)
          | xoffer a elseType branches =>
              simp only [PactType.OfferBranchesDisjoint] at hDisjoint
              simp only [PactType.reannotate,
                reannotateBranches_eq_map alphabet branches]
              exact shapeEq_xoffer f _ _ _ _ _ _
                (hStable f le_rfl elseType hDisjoint.1 alphabet)
                (forall₂_map_left_of_mem fun branch hBranch =>
                  hStable f le_rfl branch.2
                    (offerBranchesDisjoint_of_mem_branch hDisjoint.2 hBranch)
                    alphabet)
          | offer a elseType branches =>
              simp only [PactType.OfferBranchesDisjoint] at hDisjoint
              obtain ⟨hElse, hPairwise, hBranches⟩ := hDisjoint
              simp only [PactType.reannotate,
                reannotateOfferBranches_eq_map alphabet branches ∅
                  (hPairwise.imp heads_ne_of_branchDeclarationsDisjoint)]
              refine shapeEq_offer f _ _ _ _ _ _
                (hStable f le_rfl elseType hElse alphabet) ?_
              cases branches with
              | nil => simp
              | cons head tail =>
                  refine forall₂_map_left_of_mem fun branch hBranch => ?_
                  simp only [List.map_cons, parallelTypeBranchesSelecting]
                  exact shapeEq_parallelTypeBranchesSelectingWithin
                    (head :: tail) f hStable
                    (hPairwise.imp heads_ne_of_branchDeclarationsDisjoint)
                    (fun item hItem =>
                      offerBranchesDisjoint_of_mem_branch hBranches hItem)
                    (fun item => offerBranchAlphabet alphabet ∅ (head :: tail)
                      item.1)
                    alphabet a branch hBranch

end CompiledShape

end

end Pact
