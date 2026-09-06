import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.FutureClosure

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

theorem buildExclusiveOfferAutomaton_outgoing_else
     (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildExclusiveOfferAutomaton alphabet branches
      elseAutomaton branchAutomata
    edge ∈ offer.edges ∧ edge.source = .child 0 state ↔
      ∃ childEdge ∈ elseAutomaton.edges,
        childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, hChildEdge, hEdgeEq⟩
      have hChildSource := hSource
      rw [← hEdgeEq] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEdgeEq.symm⟩
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, _hIndexed, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, _hChildEdge, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp [childPendingEdge, childState] at hSource
    · rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, _hIndexed, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, _hEnvironment, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp at hSource
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl (Or.inl
        ⟨childEdge, hChildEdge, rfl⟩)))
    · simp [childPendingEdge, childState, hChildSource]

/-- Characterizes a public exclusive-offer edge leaving a tagged branch-`i`-child state as a copy of that branch's own outgoing edge. -/
theorem buildExclusiveOfferAutomaton_outgoing_branch
     (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment)
    (hBranch : branchAutomata[i]? = some (action, automaton))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildExclusiveOfferAutomaton alphabet branches
      elseAutomaton branchAutomata
    edge ∈ offer.edges ∧ edge.source = .child (i + 1) state ↔
      ∃ childEdge ∈ automaton.edges,
        childEdge.source = state ∧ edge = childPendingEdge (i + 1) childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hBranchEdges) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, _hChildEdge, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childPendingEdge, childState] at hSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, hChildEdge, hEdgeEq⟩
        have hChildSource := hSource
        rw [← hEdgeEq] at hChildSource
        simp [childPendingEdge, childState] at hChildSource
        rcases hChildSource with ⟨hIndexEq, hSourceEq⟩
        have hIndexedGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
        have hEntryEq : indexed.1 = (action, automaton) := by
          have hGet :
              branchAutomata[i]? = some indexed.1 := by
            simpa [hIndexEq] using hIndexedGet
          rw [hBranch] at hGet
          exact (Option.some.inj hGet).symm
        have hAutomatonEq : indexed.1.2 = automaton :=
          congrArg Prod.snd hEntryEq
        have hEdgeEq' : edge = childPendingEdge (i + 1) childEdge := by
          simpa [hIndexEq] using hEdgeEq.symm
        exact ⟨childEdge, by simpa [hAutomatonEq] using hChildEdge,
          hSourceEq, hEdgeEq'⟩
    · rw [mem_foldl_union_iff] at hBranchEdges
      rcases hBranchEdges with hEmpty | ⟨indexed, _hIndexed, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, _hEnvironment, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp at hSource
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
      rw [indexedFragmentEdges, mem_foldl_union_iff]
      exact Or.inr ⟨((action, automaton), i),
        List.mk_mem_zipIdx_iff_getElem?.mpr hBranch,
        Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩⟩
    · simp [childPendingEdge, childState, hChildSource]

/-- Relates a branch found by index after mapping compiled fragments in to the same branch found by index in the original list. -/
theorem branches_map_getElem?_eq_some_iff
     (branches : List (BareMessage × PactType))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment) :
    (branches.map fun branch =>
        (branch.1, compileTypeFuel (typeCompilationFuel branch.2)
          branch.2))[i]? = some (action, automaton) ↔
      ∃ branchType, branches[i]? = some (action, branchType) ∧
        compileTypeFuel (typeCompilationFuel branchType) branchType =
          automaton := by
  rw [List.getElem?_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨branchAction, branchType⟩, hGet, hEq⟩
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨hAction, hAut⟩ := hEq
    subst hAction
    exact ⟨branchType, hGet, hAut⟩
  · rintro ⟨branchType, hGet, hAut⟩
    exact ⟨(action, branchType), hGet, by simp [hAut]⟩

end

end Pact
