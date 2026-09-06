import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.ChoiceAndSequence

/-!
Exclusive and conjunctive offers: edge locality, the lift/restrict families,
the current-offer correspondence, the menu equations, and the conjunctive
automaton helpers.
-/

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-- Compiling an exclusive offer at its own budget builds the offer automaton
over the default and branch fragments compiled at theirs. -/
theorem compileTypeFuel_xoffer_eq (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType)) :
    compileTypeFuel (typeCompilationFuel (.xoffer alphabet elseType branches))
        (.xoffer alphabet elseType branches) =
      buildExclusiveOfferAutomaton alphabet branches
        (compileTypeFuel (typeCompilationFuel elseType) elseType)
        (branches.map fun branch =>
          (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2)) := by
  have hFuelEq : typeCompilationFuel (.xoffer alphabet elseType branches) =
      max (typeCompilationFuel elseType)
        (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  simp only [compileTypeFuel]
  congr 1
  · exact compileTypeFuel_eq_of_sufficient elseType (Nat.le_max_left _ _)
      (Nat.le_refl _)
  · refine List.map_congr_left ?_
    intro branch hBranch
    have hFuel : typeCompilationFuel branch.2 ≤
        max (typeCompilationFuel elseType)
          (typeBranchCompilationFuel branches) := by
      have hLe := typeCompilationFuel_le_typeBranchCompilationFuel branches
        branch hBranch
      omega
    rw [compileTypeFuel_eq_of_sufficient branch.2 hFuel (Nat.le_refl _)]

/-- Environments and offers stay local across the indexed branch copies. -/
private lemma indexedFragment_edgeLocal
    (alphabet : PactTypeAlphabet)
    (automata : List (BareMessage × AutomatonFragment))
    (hFamilies : ∀ entry ∈ automata, ∀ edge ∈ entry.2.edges,
      edge.environment ∈ alphabet.localEnvironments)
    (hOffers : ∀ entry ∈ automata, ∀ edge ∈ entry.2.edges,
      edge.current ⊆ alphabet.actions ∧
        ∀ offers, edge.future = .explicit offers → offers ⊆ alphabet.actions) :
    ∀ edge ∈ indexedFragmentEdges automata,
      edge.environment ∈ alphabet.localEnvironments ∧
        edge.current ⊆ alphabet.actions ∧
        ∀ offers, edge.future = .explicit offers →
          offers ⊆ alphabet.actions := by
  classical
  intro edge hEdge
  rw [indexedFragmentEdges, mem_foldl_union_iff] at hEdge
  rcases hEdge with hEmpty | ⟨indexed, hIndexed, hChildEdge⟩
  · simp at hEmpty
  · have hEntry : indexed.1 ∈ automata := by
      have hMapped : indexed.1 ∈ automata.zipIdx.map Prod.fst :=
        List.mem_map_of_mem (f := Prod.fst) hIndexed
      simpa using hMapped
    simp only [childPendingEdges, Finset.mem_image] at hChildEdge
    obtain ⟨childEdge, hChildMem, rfl⟩ := hChildEdge
    obtain ⟨hCur, hFut⟩ := hOffers indexed.1 hEntry childEdge hChildMem
    refine ⟨hFamilies indexed.1 hEntry childEdge hChildMem, hCur, ?_⟩
    intro offers hSpecEq
    simp only [childPendingEdge, childFutureSpec] at hSpecEq
    cases hSpec : childEdge.future with
    | explicit childOffers =>
        rw [hSpec] at hSpecEq
        simp only [FutureSpec.explicit.injEq] at hSpecEq
        subst hSpecEq
        exact hFut childOffers hSpec
    | «at» t r => rw [hSpec] at hSpecEq; simp at hSpecEq

private lemma edgeLocal_xoffer (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseAlphabet : elseType.alphabet = alphabet)
    (hBranchAlphabet : ∀ branch ∈ branches, branch.2.alphabet = alphabet)
    (hElse : EdgeEnvironmentsLocal elseType ∧ EdgeOffersLocal elseType)
    (hBranch : ∀ branch ∈ branches,
      EdgeEnvironmentsLocal branch.2 ∧ EdgeOffersLocal branch.2) :
    EdgeEnvironmentsLocal (.xoffer alphabet elseType branches) ∧
      EdgeOffersLocal (.xoffer alphabet elseType branches) := by
  classical
  have hIndexedFamilies : ∀ entry ∈ (branches.map fun branch =>
      (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2)),
      ∀ edge ∈ entry.2.edges,
        edge.environment ∈ alphabet.localEnvironments := by
    intro entry hEntry edge hEdgeMem
    obtain ⟨branch, hBranchMem, rfl⟩ := List.mem_map.mp hEntry
    have := (hBranch branch hBranchMem).1 edge hEdgeMem
    rwa [hBranchAlphabet branch hBranchMem] at this
  have hIndexedOffers : ∀ entry ∈ (branches.map fun branch =>
      (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2)),
      ∀ edge ∈ entry.2.edges,
        edge.current ⊆ alphabet.actions ∧
          ∀ offers, edge.future = .explicit offers →
            offers ⊆ alphabet.actions := by
    intro entry hEntry edge hEdgeMem
    obtain ⟨branch, hBranchMem, rfl⟩ := List.mem_map.mp hEntry
    have := (hBranch branch hBranchMem).2 edge hEdgeMem
    rwa [hBranchAlphabet branch hBranchMem] at this
  constructor <;> intro edge hEdge <;>
    rw [compileTypeFuel_xoffer_eq alphabet elseType branches] at hEdge <;>
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge <;>
    rcases hEdge with ((((hElseEdge | hIndexed) | hBranchEdge) | hWait) |
      hResolved)
  · simp only [childPendingEdges, Finset.mem_image] at hElseEdge
    obtain ⟨childEdge, hChildMem, rfl⟩ := hElseEdge
    have := hElse.1 childEdge hChildMem
    rw [hElseAlphabet] at this
    simpa [childPendingEdge] using this
  · exact (indexedFragment_edgeLocal alphabet _ hIndexedFamilies
      hIndexedOffers edge hIndexed).1
  · rw [mem_foldl_union_iff] at hBranchEdge
    rcases hBranchEdge with hEmpty | ⟨indexed, -, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hNewEdge
      exact hLocal
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hWait
    exact hLocal
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hResolved
    exact hLocal
  · simp only [childPendingEdges, Finset.mem_image] at hElseEdge
    obtain ⟨childEdge, hChildMem, rfl⟩ := hElseEdge
    obtain ⟨hCur, hFut⟩ := hElse.2 childEdge hChildMem
    rw [hElseAlphabet] at hCur hFut
    refine ⟨by simpa [childPendingEdge] using hCur, ?_⟩
    intro offers hOffers
    simp only [childPendingEdge, childFutureSpec] at hOffers
    cases hSpec : childEdge.future with
    | explicit childOffers =>
        rw [hSpec] at hOffers
        simp only [FutureSpec.explicit.injEq] at hOffers
        subst hOffers
        exact hFut childOffers hSpec
    | «at» t r => rw [hSpec] at hOffers; simp at hOffers
  · exact (indexedFragment_edgeLocal alphabet _ hIndexedFamilies
      hIndexedOffers edge hIndexed).2
  · rw [mem_foldl_union_iff] at hBranchEdge
    rcases hBranchEdge with hEmpty | ⟨indexed, hIndexedMem, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      obtain ⟨environment, ⟨-, -, -, hGate⟩, rfl⟩ := hNewEdge
      have hEntry : indexed.1 ∈ (branches.map fun branch =>
          (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2)) := by
        have hMapped : indexed.1 ∈ (branches.map fun branch =>
            (branch.1, compileTypeFuel (typeCompilationFuel branch.2)
              branch.2)).zipIdx.map Prod.fst :=
          List.mem_map_of_mem (f := Prod.fst) hIndexedMem
        simpa using hMapped
      obtain ⟨branch, hBranchMem, hEq⟩ := List.mem_map.mp hEntry
      refine ⟨?_, by intro _ h; simp at h⟩
      have hActionEq : indexed.1.1 = branch.1 := by rw [← hEq]
      simp only [Finset.singleton_subset_iff, hActionEq]
      exact hGate branch hBranchMem
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, ⟨-, -, -, hGate⟩, rfl⟩ := hWait
    refine ⟨?_, by intro _ h; simp at h⟩
    intro action hAction
    have hIn : action ∈ typeBranchActions branches :=
      (Finset.mem_inter.mp hAction).2
    simp only [typeBranchActions, List.mem_toFinset, List.mem_map] at hIn
    obtain ⟨branch, hBranchMem, rfl⟩ := hIn
    exact hGate branch hBranchMem
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    obtain ⟨environment, -, rfl⟩ := hResolved
    exact ⟨by simp, by intro _ h; simp at h⟩

private lemma edgeLocal_offer (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseAlphabet : elseType.alphabet = alphabet)
    (hSelectedAlphabet : ∀ selected ∈ branches,
      (parallelTypeBranchesSelecting alphabet selected branches).alphabet =
        alphabet)
    (hElse : EdgeEnvironmentsLocal elseType ∧ EdgeOffersLocal elseType)
    (hSelected : ∀ selected ∈ branches,
      EdgeEnvironmentsLocal (parallelTypeBranchesSelecting alphabet selected
          branches) ∧
        EdgeOffersLocal (parallelTypeBranchesSelecting alphabet selected
          branches)) :
    EdgeEnvironmentsLocal (.offer alphabet elseType branches) ∧
      EdgeOffersLocal (.offer alphabet elseType branches) := by
  classical
  have hIndexedFamilies : ∀ entry ∈ (branches.map fun selected =>
      (selected.1, compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet selected branches))
        (parallelTypeBranchesSelecting alphabet selected branches))),
      ∀ edge ∈ entry.2.edges,
        edge.environment ∈ alphabet.localEnvironments := by
    intro entry hEntry edge hEdgeMem
    obtain ⟨selected, hSelectedMem, rfl⟩ := List.mem_map.mp hEntry
    have := (hSelected selected hSelectedMem).1 edge hEdgeMem
    rwa [hSelectedAlphabet selected hSelectedMem] at this
  have hIndexedOffers : ∀ entry ∈ (branches.map fun selected =>
      (selected.1, compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet selected branches))
        (parallelTypeBranchesSelecting alphabet selected branches))),
      ∀ edge ∈ entry.2.edges,
        edge.current ⊆ alphabet.actions ∧
          ∀ offers, edge.future = .explicit offers →
            offers ⊆ alphabet.actions := by
    intro entry hEntry edge hEdgeMem
    obtain ⟨selected, hSelectedMem, rfl⟩ := List.mem_map.mp hEntry
    have := (hSelected selected hSelectedMem).2 edge hEdgeMem
    rwa [hSelectedAlphabet selected hSelectedMem] at this
  constructor <;> intro edge hEdge <;>
    rw [compileTypeFuel_offer_eq alphabet elseType branches] at hEdge <;>
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge <;>
    rcases hEdge with ((((hElseEdge | hIndexed) | hEnabled) | hWait) | hResolved)
  · simp only [childPendingEdges, Finset.mem_image] at hElseEdge
    obtain ⟨childEdge, hChildMem, rfl⟩ := hElseEdge
    have := hElse.1 childEdge hChildMem
    rw [hElseAlphabet] at this
    simpa [childPendingEdge] using this
  · exact (indexedFragment_edgeLocal alphabet _ hIndexedFamilies
      hIndexedOffers edge hIndexed).1
  · rw [mem_foldl_union_iff] at hEnabled
    rcases hEnabled with hEmpty | ⟨indexed, -, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hNewEdge
      exact hLocal
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hWait
    exact hLocal
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hResolved
    exact hLocal
  · simp only [childPendingEdges, Finset.mem_image] at hElseEdge
    obtain ⟨childEdge, hChildMem, rfl⟩ := hElseEdge
    obtain ⟨hCur, hFut⟩ := hElse.2 childEdge hChildMem
    rw [hElseAlphabet] at hCur hFut
    refine ⟨by simpa [childPendingEdge] using hCur, ?_⟩
    intro offers hOffers
    simp only [childPendingEdge, childFutureSpec] at hOffers
    cases hSpec : childEdge.future with
    | explicit childOffers =>
        rw [hSpec] at hOffers
        simp only [FutureSpec.explicit.injEq] at hOffers
        subst hOffers
        exact hFut childOffers hSpec
    | «at» t r => rw [hSpec] at hOffers; simp at hOffers
  · exact (indexedFragment_edgeLocal alphabet _ hIndexedFamilies
      hIndexedOffers edge hIndexed).2
  · rw [mem_foldl_union_iff] at hEnabled
    rcases hEnabled with hEmpty | ⟨indexed, -, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      obtain ⟨environment, -, rfl⟩ := hNewEdge
      exact ⟨by simp, by intro _ h; simp at h⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, ⟨-, -, -, -, hGate⟩, rfl⟩ := hWait
    refine ⟨?_, by intro _ h; simp at h⟩
    intro action hAction
    simp only [typeBranchActions, List.mem_toFinset, List.mem_map] at hAction
    obtain ⟨branch, hBranchMem, rfl⟩ := hAction
    exact hGate branch hBranchMem
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    obtain ⟨environment, ⟨-, -, -, -, hGate⟩, rfl⟩ := hResolved
    refine ⟨?_, by intro _ h; simp at h⟩
    intro action hAction
    simp only [typeBranchActions, List.mem_toFinset, List.mem_map] at hAction
    obtain ⟨branch, hBranchMem, rfl⟩ := hAction
    exact hGate branch hBranchMem

/-- Each branch of a conjunctive offer carries the node alphabet and is itself
alphabet-well-formed. -/
theorem offerBranchesWellFormed_of_mem :
    ∀ {alphabet : PactTypeAlphabet} {seen : Finset BareMessage}
      {branches : List (BareMessage × PactType)}
      {branch : BareMessage × PactType},
      PactType.OfferBranchesWellFormed alphabet seen branches →
      branch ∈ branches →
      branch.2.alphabet = alphabet ∧ branch.2.AlphabetWellFormed
  | _, _, (_, _) :: rest, branch, hWF, hMem => by
      rw [PactType.OfferBranchesWellFormed] at hWF
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact ⟨hWF.1, hWF.2.1⟩
      · exact offerBranchesWellFormed_of_mem hWF.2.2 hRest
  | _, _, [], _, _, hMem => by simp at hMem
  termination_by _ _ branches => sizeOf branches

/-- Alphabet well-formedness descends to each branch body. -/
theorem branchAlphabetWellFormed_of_mem :
    ∀ {alphabet : PactTypeAlphabet} {branches : List (BareMessage × PactType)}
      {branch : BareMessage × PactType},
      PactType.BranchesAlphabetWellFormed alphabet branches →
      branch ∈ branches → branch.2.AlphabetWellFormed
  | _, (_, _) :: rest, branch, hWF, hMem => by
      rw [PactType.BranchesAlphabetWellFormed] at hWF
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact hWF.2.1
      · exact branchAlphabetWellFormed_of_mem hWF.2.2 hRest
  | _, [], _, _, hMem => by simp at hMem
  termination_by _ branches => sizeOf branches

/-- Interface scoping descends to each branch body. -/
theorem interfaceScopedBranches_mem :
    ∀ {branches : List (BareMessage × PactType)}
      {branch : BareMessage × PactType},
      PactType.InterfaceScopedBranches branches → branch ∈ branches →
      branch.2.InterfaceScoped
  | (_, _) :: rest, branch, hScoped, hMem => by
      rw [PactType.InterfaceScopedBranches] at hScoped
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact hScoped.1
      · exact interfaceScopedBranches_mem hScoped.2 hRest
  | [], _, _, hMem => by simp at hMem
  termination_by branches => sizeOf branches

/-- Interface-alphabet scoping descends to each branch body. -/
theorem interfaceAlphabetScopedBranches_mem :
    ∀ {branches : List (BareMessage × PactType)}
      {branch : BareMessage × PactType},
      PactType.InterfaceAlphabetScopedBranches branches → branch ∈ branches →
      branch.2.InterfaceAlphabetScoped
  | (_, _) :: rest, branch, hScoped, hMem => by
      rw [PactType.InterfaceAlphabetScopedBranches] at hScoped
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact hScoped.1
      · exact interfaceAlphabetScopedBranches_mem hScoped.2 hRest
  | [], _, _, hMem => by simp at hMem
  termination_by branches => sizeOf branches

/-- Edge locality holds at every constructor.  Each builder draws environments
from the node's own `localEnvironments` and its currents from `∅`, a gated
singleton, or a gated branch-action set, and copies child edges unchanged. -/
theorem edgeLocalAt_holds :
    ∀ fuel processType, TypeCompilationFuelSufficient processType fuel →
      processType.AlphabetWellFormed →
      processType.InterfaceScoped →
      processType.InterfaceAlphabetScoped →
      EdgeLocalAt fuel processType := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel _ _ _
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel hWF hScoped hAlphaScoped
      cases processType with
      | skip alphabet =>
          exact edgeLocalAt_of_edgeLocal hFuel (edgeLocal_skip alphabet)
      | var alphabet name =>
          exact edgeLocalAt_of_edgeLocal hFuel (edgeLocal_var alphabet name)
      | message alphabet msg dir =>
          exact edgeLocalAt_of_edgeLocal hFuel (edgeLocal_message alphabet msg dir)
      | tock alphabet =>
          exact edgeLocalAt_of_edgeLocal hFuel (edgeLocal_tock alphabet)
      | progress alphabet pid =>
          exact edgeLocalAt_of_edgeLocal hFuel (edgeLocal_progress alphabet pid)
      | choice alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.InterfaceAlphabetScoped] at hAlphaScoped
          simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          refine edgeLocalAt_of_edgeLocal (by
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel]; omega)
            (edgeLocal_choice alphabet left right hWF.2.1 hWF.2.2.1 ?_ ?_)
          · exact edgeLocal_of_edgeLocalAt hLeftFuel
              (ih left hLeftFuel hWF.2.2.2.1 hScoped.1 hAlphaScoped.2.1)
          · exact edgeLocal_of_edgeLocalAt hRightFuel
              (ih right hRightFuel hWF.2.2.2.2 hScoped.2 hAlphaScoped.2.2)
      | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.InterfaceAlphabetScoped] at hAlphaScoped
          simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          refine edgeLocalAt_of_edgeLocal (by
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel]; omega)
            (edgeLocal_fairChoice alphabet bid left right hWF.2.1 hWF.2.2.1 ?_ ?_)
          · exact edgeLocal_of_edgeLocalAt hLeftFuel
              (ih left hLeftFuel hWF.2.2.2.1 hScoped.1 hAlphaScoped.2.1)
          · exact edgeLocal_of_edgeLocalAt hRightFuel
              (ih right hRightFuel hWF.2.2.2.2 hScoped.2 hAlphaScoped.2.2)
      | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.InterfaceAlphabetScoped] at hAlphaScoped
          simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          refine edgeLocalAt_of_edgeLocal (by
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel]; omega)
            (edgeLocal_seq alphabet left right hWF.2.1 hWF.2.2.1 ?_ ?_)
          · exact edgeLocal_of_edgeLocalAt hLeftFuel
              (ih left hLeftFuel hWF.2.2.2.1 hScoped.1 hAlphaScoped.2.1)
          · exact edgeLocal_of_edgeLocalAt hRightFuel
              (ih right hRightFuel hWF.2.2.2.2 hScoped.2 hAlphaScoped.2.2)
      | recur alphabet name body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.InterfaceAlphabetScoped] at hAlphaScoped
          simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
          have hBodyFuel : TypeCompilationFuelSufficient body fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          refine edgeLocalAt_of_edgeLocal (by
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel]; omega)
            (edgeLocal_recur alphabet name body hWF.2.1 ?_)
          exact edgeLocal_of_edgeLocalAt hBodyFuel
            (ih body hBodyFuel hWF.2.2 hScoped hAlphaScoped.2)
      | xoffer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.InterfaceAlphabetScoped] at hAlphaScoped
          simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          have hBranchFuel : ∀ branch ∈ branches,
              TypeCompilationFuelSufficient branch.2 fuel := by
            intro branch hBranch
            have hBound := typeCompilationFuel_le_typeBranchCompilationFuel
              branches branch hBranch
            simp only [TypeCompilationFuelSufficient]; omega
          refine edgeLocalAt_of_edgeLocal (by
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel]; omega)
            (edgeLocal_xoffer alphabet elseType branches hWF.2.1 ?_ ?_ ?_)
          · intro branch hBranch
            exact PactType.branch_alphabet_eq_of_mem hWF.2.2.2 hBranch
          · exact edgeLocal_of_edgeLocalAt hElseFuel
              (ih elseType hElseFuel hWF.2.2.1 hScoped.1 hAlphaScoped.2.1)
          · intro branch hBranch
            exact edgeLocal_of_edgeLocalAt (hBranchFuel branch hBranch)
              (ih branch.2 (hBranchFuel branch hBranch)
                (branchAlphabetWellFormed_of_mem hWF.2.2.2 hBranch)
                (interfaceScopedBranches_mem hScoped.2 hBranch)
                (interfaceAlphabetScopedBranches_mem hAlphaScoped.2.2 hBranch))
      | offer alphabet elseType branches =>
          have hWFOffer := hWF
          have hScopedOffer := hScoped
          have hAlphaScopedOffer := hAlphaScoped
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.InterfaceAlphabetScoped] at hAlphaScoped
          simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          have hSelectedFuel : ∀ selected ∈ branches,
              TypeCompilationFuelSufficient
                (parallelTypeBranchesSelecting alphabet selected branches) fuel := by
            intro selected hSelected
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting]
            omega
          refine edgeLocalAt_of_edgeLocal (by
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel]; omega)
            (edgeLocal_offer alphabet elseType branches hWF.2.1 ?_ ?_ ?_)
          · intro selected hSelected
            exact parallelTypeBranchesSelecting_alphabet_eq_of_mem hSelected
          · exact edgeLocal_of_edgeLocalAt hElseFuel
              (ih elseType hElseFuel hWF.2.2.1 hScoped.1 hAlphaScoped.2.1)
          · intro selected hSelected
            exact edgeLocal_of_edgeLocalAt (hSelectedFuel selected hSelected)
              (ih _ (hSelectedFuel selected hSelected)
                (committedOfferAlphabetWellFormed_holds alphabet elseType branches
                  selected hWFOffer hScopedOffer hAlphaScopedOffer hSelected)
                (committedOfferScoping_holds alphabet elseType branches selected
                  hScopedOffer hAlphaScopedOffer hSelected).1
                (committedOfferScoping_holds alphabet elseType branches selected
                  hScopedOffer hAlphaScopedOffer hSelected).2)
      | par alphabet left right interface =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.InterfaceAlphabetScoped] at hAlphaScoped
          simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          -- The re-stamped children avoid the parent's own interfaces, so the
          -- three regularity predicates transport across `reannotate`.
          have hAvoidLeft : ∀ action ∈ alphabet.actions,
              action.1 ∉ PactType.ParallelInterfaces left := by
            intro action hAction hInterface
            refine absurd hAlphaScoped.1 (Finset.not_disjoint_iff.mpr
              ⟨action.1, Finset.mem_image.mpr ⟨action, hAction, rfl⟩, ?_⟩)
            exact Finset.mem_union_left _ (Finset.mem_union_right _ hInterface)
          have hAvoidRight : ∀ action ∈ alphabet.actions,
              action.1 ∉ PactType.ParallelInterfaces right := by
            intro action hAction hInterface
            refine absurd hAlphaScoped.1 (Finset.not_disjoint_iff.mpr
              ⟨action.1, Finset.mem_image.mpr ⟨action, hAction, rfl⟩, ?_⟩)
            exact Finset.mem_union_right _ hInterface
          have hLeftRestampFuel : TypeCompilationFuelSufficient
              (left.reannotate alphabet) fuel := by
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_reannotate]
            exact hLeftFuel
          have hRightRestampFuel : TypeCompilationFuelSufficient
              (right.reannotate alphabet) fuel := by
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_reannotate]
            exact hRightFuel
          have hLeftLocal := ih left hLeftFuel hWF.2.2.1 hScoped.2.1
            hAlphaScoped.2.1
          have hRightLocal := ih right hRightFuel hWF.2.2.2 hScoped.2.2
            hAlphaScoped.2.2
          have hLeftRestamp := ih (left.reannotate alphabet) hLeftRestampFuel
            (PactType.reannotate_alphabetWellFormed_avoiding left alphabet
              hWF.2.2.1 hWF.1 hScoped.2.1 hAvoidLeft)
            (PactType.reannotate_interfaceScoped left alphabet hScoped.2.1)
            (PactType.reannotate_interfaceAlphabetScoped left alphabet
              hAlphaScoped.2.1 hAvoidLeft)
          have hRightRestamp := ih (right.reannotate alphabet) hRightRestampFuel
            (PactType.reannotate_alphabetWellFormed_avoiding right alphabet
              hWF.2.2.2 hWF.1 hScoped.2.2 hAvoidRight)
            (PactType.reannotate_interfaceScoped right alphabet hScoped.2.2)
            (PactType.reannotate_interfaceAlphabetScoped right alphabet
              hAlphaScoped.2.2 hAvoidRight)
          intro edge hEdge
          rw [compileTypeFuel] at hEdge
          refine ⟨?_, ?_⟩
          · exact buildParallelAutomaton_edge_families alphabet left.alphabet
              right.alphabet interface _ _ _ _ _ _ _ _
              hWF.2.1.parent_eq_left
              (fun e he => (hLeftLocal e he).1) (fun e he => (hRightLocal e he).1)
              (fun e he => by
                have := (hLeftRestamp e he).1
                rwa [PactType.reannotate_alphabet] at this)
              (fun e he => by
                have := (hRightRestamp e he).1
                rwa [PactType.reannotate_alphabet] at this)
              edge hEdge
          · exact buildParallelAutomaton_edge_offers alphabet left.alphabet
              right.alphabet interface _ _ _ _ _ _ _ _
              hWF.2.1.parent_eq_left hWF.2.1.parent_eq_right
              (fun e he => (hLeftLocal e he).2.1)
              (fun e he => (hRightLocal e he).2.1)
              (fun e he => by
                have := (hLeftRestamp e he).2.1
                rwa [PactType.reannotate_alphabet] at this)
              (fun e he => by
                have := (hRightRestamp e he).2.1
                rwa [PactType.reannotate_alphabet] at this)
              edge hEdge

/-- A copied default-arm edge of an exclusive offer restricts to an edge of
the default arm. -/
theorem xoffer_else_edge_restrict (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseDisjoint : elseType.OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet =
      (PactType.xoffer alphabet elseType branches).alphabet)
    {q : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage} {state' : TypeAutomatonState}
    (hEdge : (compileType (.xoffer alphabet elseType branches)).HasEdge
      (.child 0 q) env label ⟨current, future⟩ state') :
    ∃ q', state' = .child 0 q' ∧
      (compileType elseType).HasEdge q env label ⟨current, future⟩ q' := by
  classical
  have hWhole := compileTypeFuel_xoffer_eq alphabet elseType branches
  have hFuelElse : typeCompilationFuel elseType + 1 ≤
      typeCompilationFuel (.xoffer alphabet elseType branches) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.xoffer alphabet elseType branches) (.child 0 visited) =
        stateProductInfo elseType visited :=
    stateProductInfo_xoffer_child_else alphabet elseType branches
  obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
    hPFuture, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge (.xoffer alphabet elseType branches)
      (.child 0 q) state' env label ⟨current, future⟩).mp hEdge
  rw [hWhole] at hPendingMem
  -- Invert directly: only the copied default family is sourced at `child 0`.
  obtain ⟨childEdge, hChildEdgeMem, hChildEq⟩ : ∃ childEdge ∈
      (compileTypeFuel (typeCompilationFuel elseType) elseType).edges,
      pendingEdge = childPendingEdge 0 childEdge := by
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hPendingMem
    rcases hPendingMem with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · obtain ⟨childEdge, hMem, hEq⟩ := hElse
      exact ⟨childEdge, hMem, hEq.symm⟩
    · exfalso
      rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, -, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [childPendingEdges, Finset.mem_image] at hIn
        obtain ⟨childEdge, -, hEq⟩ := hIn
        rw [← hEq] at hPSource
        simp [childPendingEdge, childState] at hPSource
    · exfalso
      rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, -, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [Finset.mem_image] at hIn
        obtain ⟨environment, -, hEq⟩ := hIn
        rw [← hEq] at hPSource
        simp [childState] at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hWait
      rw [← hEq] at hPSource
      simp at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hResolved
      rw [← hEq] at hPSource
      simp at hPSource
  have hChildSource : childEdge.source = q := by
    rw [hChildEq] at hPSource
    simpa [childPendingEdge, childState] using hPSource
  refine ⟨childEdge.target, by rw [← hPTarget, hChildEq]; rfl, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge elseType q childEdge.target env
    label ⟨current, future⟩]
  refine ⟨childEdge, hChildEdgeMem, hChildSource, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hPEnv, hChildEq]; rfl
  · rw [← hPLabel, hChildEq]; rfl
  · rw [← hPCurrent, hChildEq]; rfl
  · rw [← hPFuture, hChildEq]
    cases hSpec : childEdge.future with
    | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel elseType) elseType le_rfl hElseDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_exclusiveOffer_else elseType branches
          (.xoffer alphabet elseType branches) hWhole hFuelElse hElseDisjoint
          hElseAlphabet hProductInfo t hStateMem]

/-- A default-arm edge lifts to the copied edge of an exclusive offer. -/
theorem xoffer_else_edge_lift (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseDisjoint : elseType.OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet =
      (PactType.xoffer alphabet elseType branches).alphabet)
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType elseType).HasEdge q env label ⟨current, future⟩ q') :
    (compileType (.xoffer alphabet elseType branches)).HasEdge
      (.child 0 q) env label ⟨current, future⟩ (.child 0 q') := by
  classical
  have hWhole := compileTypeFuel_xoffer_eq alphabet elseType branches
  have hFuelElse : typeCompilationFuel elseType + 1 ≤
      typeCompilationFuel (.xoffer alphabet elseType branches) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.xoffer alphabet elseType branches) (.child 0 visited) =
        stateProductInfo elseType visited :=
    stateProductInfo_xoffer_child_else alphabet elseType branches
  obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent,
    hCFuture, hCTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge elseType q q' env label
      ⟨current, future⟩).mp hEdge
  rw [compileType_hasEdge_iff_hasResolvedEdge (.xoffer alphabet elseType branches)
    (.child 0 q) (.child 0 q') env label ⟨current, future⟩, hWhole]
  refine ⟨childPendingEdge 0 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨childEdge, hChildEdgeMem, rfl⟩)))
  · simp [childPendingEdge, childState, hCSource]
  · simp [childPendingEdge, hCEnv]
  · simp [childPendingEdge, hCLabel]
  · simp [childPendingEdge, hCCurrent]
  · cases hSpec : childEdge.future with
    | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel elseType) elseType le_rfl hElseDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_exclusiveOffer_else elseType branches
          (.xoffer alphabet elseType branches) hWhole hFuelElse hElseDisjoint
          hElseAlphabet hProductInfo t hStateMem]
        simpa [childFutureSpec, hSpec] using hCFuture
  · simp [childPendingEdge, childState, hCTarget]

theorem xoffer_branch_edge_restrict (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (i : Nat) (action : BareMessage) (branchType : PactType)
    (hGet : branches[i]? = some (action, branchType))
    (hBranchDisjoint : branchType.OfferBranchesDisjoint)
    (hBranchAlphabet : branchType.alphabet =
      (PactType.xoffer alphabet elseType branches).alphabet)
    {q : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage} {state' : TypeAutomatonState}
    (hEdge : (compileType (.xoffer alphabet elseType branches)).HasEdge
      (.child (i + 1) q) env label ⟨current, future⟩ state') :
    ∃ q', state' = .child (i + 1) q' ∧
      (compileType branchType).HasEdge q env label ⟨current, future⟩ q' := by
  classical
  have hWhole := compileTypeFuel_xoffer_eq alphabet elseType branches
  have hFuelBranch : typeCompilationFuel branchType + 1 ≤
      typeCompilationFuel (.xoffer alphabet elseType branches) := by
    have hBound := typeCompilationFuel_le_typeBranchCompilationFuel branches
      (action, branchType) (List.mem_of_getElem? hGet)
    simp only [typeCompilationFuel] at *
    omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.xoffer alphabet elseType branches) (.child (i + 1) visited) =
        stateProductInfo branchType visited :=
    stateProductInfo_xoffer_child_branch alphabet elseType branches i action branchType hGet
  obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
    hPFuture, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge (.xoffer alphabet elseType branches)
      (.child (i + 1) q) state' env label ⟨current, future⟩).mp hEdge
  rw [hWhole] at hPendingMem
  -- Invert directly: only the copied default family is sourced at `child 0`.
  obtain ⟨childEdge, hChildEdgeMem, hChildEq⟩ : ∃ childEdge ∈
      (compileTypeFuel (typeCompilationFuel branchType) branchType).edges,
      pendingEdge = childPendingEdge (i + 1) childEdge := by
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hPendingMem
    rcases hPendingMem with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · exfalso
      obtain ⟨childEdge, -, hEq⟩ := hElse
      rw [← hEq] at hPSource
      simp [childPendingEdge, childState] at hPSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [childPendingEdges, Finset.mem_image] at hIn
        obtain ⟨childEdge, hMem, hEq⟩ := hIn
        -- The tag pins the index, and the index pins the branch automaton.
        have hIdx : indexed.2 = i := by
          rw [← hEq] at hPSource
          have h := hPSource
          simp only [childPendingEdge, childState,
            TypeAutomatonState.child.injEq] at h
          omega
        subst hIdx
        have hMapGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
        rw [List.getElem?_map, hGet] at hMapGet
        have hFragEq : indexed.1.2 =
            compileTypeFuel (typeCompilationFuel branchType) branchType := by
          simpa using (congrArg (fun o => (Option.map Prod.snd o)) hMapGet).symm
        rw [hFragEq] at hMem
        exact ⟨childEdge, hMem, hEq.symm⟩
    · exfalso
      rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, -, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [Finset.mem_image] at hIn
        obtain ⟨environment, -, hEq⟩ := hIn
        rw [← hEq] at hPSource
        simp [childState] at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hWait
      rw [← hEq] at hPSource
      simp at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hResolved
      rw [← hEq] at hPSource
      simp at hPSource
  have hChildSource : childEdge.source = q := by
    rw [hChildEq] at hPSource
    simpa [childPendingEdge, childState] using hPSource
  refine ⟨childEdge.target, by rw [← hPTarget, hChildEq]; rfl, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge branchType q childEdge.target env
    label ⟨current, future⟩]
  refine ⟨childEdge, hChildEdgeMem, hChildSource, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hPEnv, hChildEq]; rfl
  · rw [← hPLabel, hChildEq]; rfl
  · rw [← hPCurrent, hChildEq]; rfl
  · rw [← hPFuture, hChildEq]
    cases hSpec : childEdge.future with
    | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel branchType) branchType le_rfl hBranchDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_exclusiveOffer_branch elseType branches
          (.xoffer alphabet elseType branches) hWhole i action branchType hGet
          hFuelBranch hBranchDisjoint hBranchAlphabet hProductInfo t hStateMem]

/-- A branch-body edge lifts to the copied edge of an exclusive offer. -/
theorem xoffer_branch_edge_lift (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (i : Nat) (action : BareMessage) (branchType : PactType)
    (hGet : branches[i]? = some (action, branchType))
    (hBranchDisjoint : branchType.OfferBranchesDisjoint)
    (hBranchAlphabet : branchType.alphabet =
      (PactType.xoffer alphabet elseType branches).alphabet)
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType branchType).HasEdge q env label ⟨current, future⟩ q') :
    (compileType (.xoffer alphabet elseType branches)).HasEdge
      (.child (i + 1) q) env label ⟨current, future⟩ (.child (i + 1) q') := by
  classical
  have hWhole := compileTypeFuel_xoffer_eq alphabet elseType branches
  have hFuelBranch : typeCompilationFuel branchType + 1 ≤
      typeCompilationFuel (.xoffer alphabet elseType branches) := by
    have hBound := typeCompilationFuel_le_typeBranchCompilationFuel branches
      (action, branchType) (List.mem_of_getElem? hGet)
    simp only [typeCompilationFuel] at *
    omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.xoffer alphabet elseType branches) (.child (i + 1) visited) =
        stateProductInfo branchType visited :=
    stateProductInfo_xoffer_child_branch alphabet elseType branches i action branchType hGet
  obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent,
    hCFuture, hCTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge branchType q q' env label
      ⟨current, future⟩).mp hEdge
  rw [compileType_hasEdge_iff_hasResolvedEdge (.xoffer alphabet elseType branches)
    (.child (i + 1) q) (.child (i + 1) q') env label ⟨current, future⟩, hWhole]
  refine ⟨childPendingEdge (i + 1) childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hMapGet : (branches.map fun branch => (branch.1, compileTypeFuel
        (typeCompilationFuel branch.2) branch.2))[i]? =
        some (action, compileTypeFuel (typeCompilationFuel branchType)
          branchType) := by
      simpa using congrArg (Option.map fun b => ((b.1 : BareMessage),
        compileTypeFuel (typeCompilationFuel b.2) b.2)) hGet
    exact ((buildExclusiveOfferAutomaton_outgoing_branch alphabet branches
      (compileTypeFuel (typeCompilationFuel elseType) elseType)
      (branches.map fun branch => (branch.1, compileTypeFuel
        (typeCompilationFuel branch.2) branch.2)) i action
      (compileTypeFuel (typeCompilationFuel branchType) branchType) hMapGet q
      (childPendingEdge (i + 1) childEdge)).mpr
      ⟨childEdge, hChildEdgeMem, hCSource, rfl⟩).1
  · simp [childPendingEdge, childState, hCSource]
  · simp [childPendingEdge, hCEnv]
  · simp [childPendingEdge, hCLabel]
  · simp [childPendingEdge, hCCurrent]
  · cases hSpec : childEdge.future with
    | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel branchType) branchType le_rfl hBranchDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_exclusiveOffer_branch elseType branches
          (.xoffer alphabet elseType branches) hWhole i action branchType hGet
          hFuelBranch hBranchDisjoint hBranchAlphabet hProductInfo t hStateMem]
        simpa [childFutureSpec, hSpec] using hCFuture
  · simp [childPendingEdge, childState, hCTarget]

/-- Current-offer correspondence at an exclusive offer.  Following the paper:
the root's guards, labels, current offers and targets are identical in the
semantic rule and the edge family, and the copied default and branch entries use
the lower-rank hypothesis. -/
theorem currentOfferCorrespondence_xoffer (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseDisjoint : elseType.OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet =
      (PactType.xoffer alphabet elseType branches).alphabet)
    (hBranchDisjoint : ∀ action branchType, (action, branchType) ∈ branches →
      branchType.OfferBranchesDisjoint)
    (hBranchAlphabet : ∀ action branchType, (action, branchType) ∈ branches →
      branchType.alphabet = (PactType.xoffer alphabet elseType branches).alphabet)
    (hElse : CurrentOfferCorrespondence elseType)
    (hBranches : ∀ action branchType, (action, branchType) ∈ branches →
      CurrentOfferCorrespondence branchType) :
    CurrentOfferCorrespondence (.xoffer alphabet elseType branches) := by
  classical
  constructor
  · intro residual residual' state env label current future hRelated hTransition
    rcases relationMembership_xoffer_cases alphabet elseType branches hRelated
      with hRoot | ⟨q, hStateEq, hChildRelated⟩ |
        ⟨i, action, branchType, q, hGet, hStateEq, hChildRelated⟩
    · -- Root: each offer rule names its own root edge family.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, hStateEq'⟩ := hRoot
      simp only at hResEq hStateEq'
      subst hResEq; subst hStateEq'
      have hWhole := compileTypeFuel_xoffer_eq alphabet elseType branches
      obtain ⟨-, hOffers⟩ := hTransition
      cases hOffers with
      | xoffer_branch cEnv cAlpha cElse cBranches cAction residual' hCond hGate =>
          obtain ⟨index, hBranchGet⟩ := List.mem_iff_getElem?.mp hCond.2.1
          refine Exists.intro
            (.child (index + 1) (compileTypeFuel
              (typeCompilationFuel residual') residual').initial)
            (Exists.intro
              (computeFutureOf (.xoffer alphabet elseType branches)
                (.child (index + 1) (compileTypeFuel
                  (typeCompilationFuel residual') residual').initial) \
                {cAction}) ⟨?_, ?_⟩)
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.xoffer alphabet elseType branches) TypeAutomatonState.root
              (.child (index + 1) (compileTypeFuel
                (typeCompilationFuel residual') residual').initial) env
              (TypeLabel.message cAction.1 cAction.2) _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible
                  (TypeLabel.message cAction.1 cAction.2),
                current := {cAction},
                future := FutureSpec.at (childState (index + 1)
                  (compileTypeFuel (typeCompilationFuel residual') residual').initial)
                  {cAction},
                target := childState (index + 1) (compileTypeFuel
                  (typeCompilationFuel residual') residual').initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
                Finset.mem_union]
              refine Or.inl (Or.inl (Or.inr ?_))
              rw [mem_foldl_union_iff]
              refine Or.inr ⟨(⟨cAction, compileTypeFuel
                (typeCompilationFuel residual') residual'⟩, index), ?_, ?_⟩
              · exact List.mk_mem_zipIdx_iff_getElem?.mpr
                  ((branches_map_getElem?_eq_some_iff branches index cAction
                    (compileTypeFuel (typeCompilationFuel residual') residual')).mpr
                    ⟨residual', hBranchGet, rfl⟩)
              · simp only [Finset.mem_image, Finset.mem_filter]
                exact ⟨env,
                  ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hCond.1,
                    hCond.2.2.1, hCond.2.2.2, hGate⟩, rfl⟩
            · simp [childState]
          · exact relationMembership_xoffer_branch alphabet elseType branches
              hBranchGet
              (buildRelationSet_initial residual' (compileType residual'))
      | xoffer_else cEnv cAlpha cElse cBranches hCond hGate =>
          refine Exists.intro
            (.child 0 (compileTypeFuel (typeCompilationFuel elseType)
              elseType).initial)
            (Exists.intro
              (computeFutureOf (.xoffer alphabet elseType branches)
                (.child 0 (compileTypeFuel (typeCompilationFuel elseType)
                  elseType).initial)) ⟨?_, ?_⟩)
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.xoffer alphabet elseType branches) TypeAutomatonState.root
              (.child 0 (compileTypeFuel (typeCompilationFuel elseType)
                elseType).initial) env TypeLabel.silent _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := (∅ : Finset BareMessage),
                future := FutureSpec.at (childState 0 (compileTypeFuel
                  (typeCompilationFuel elseType) elseType).initial) ∅,
                target := childState 0 (compileTypeFuel
                  (typeCompilationFuel elseType) elseType).initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_image, Finset.mem_filter]
              exact Or.inr ⟨env,
                ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hCond.1,
                  hCond.2.1, hCond.2.2.1, hCond.2.2.2, hGate⟩, rfl⟩
            · simp [childState]
          · exact relationMembership_xoffer_else alphabet elseType branches
              (buildRelationSet_initial elseType (compileType elseType))
      | xoffer_wait cEnv cAlpha cElse cBranches hCond hGate =>
          refine Exists.intro TypeAutomatonState.root
            (Exists.intro
              (computeFutureOf (.xoffer alphabet elseType branches)
                TypeAutomatonState.root \
                  typeWaitingOffers env branches) ⟨?_, ?_⟩)
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.xoffer alphabet elseType branches) TypeAutomatonState.root
              TypeAutomatonState.root env TypeLabel.silent _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := typeWaitingOffers env branches,
                future := FutureSpec.at TypeAutomatonState.root
                  (typeWaitingOffers env branches),
                target := TypeAutomatonState.root }
              ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
              Finset.mem_union, Finset.mem_image, Finset.mem_filter]
            refine Or.inl (Or.inr ⟨env, ⟨
              PactTypeAlphabet.mem_localEnvironments_of_wellFormed hCond.1,
              hCond.2.2, ?_, hGate⟩, ?_⟩)
            · exact hCond.2.1
            · simp [typeWaitingOffers, typeBranchActions]
          · exact relationMembership_xoffer_root alphabet elseType branches
    · -- Copied default entry.
      subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        hElse.1 hChildRelated hTransition
      exact ⟨.child 0 q', future',
        xoffer_else_edge_lift alphabet elseType branches hElseDisjoint
          hElseAlphabet hChildEdge,
        relationMembership_xoffer_else alphabet elseType branches hChildTarget⟩
    · -- Copied branch entry.
      subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        (hBranches action branchType
          (List.mem_of_getElem? hGet)).1 hChildRelated hTransition
      exact ⟨.child (i + 1) q', future',
        xoffer_branch_edge_lift alphabet elseType branches i action branchType
          hGet (hBranchDisjoint action branchType (List.mem_of_getElem? hGet))
          (hBranchAlphabet action branchType (List.mem_of_getElem? hGet))
          hChildEdge,
        relationMembership_xoffer_branch alphabet elseType branches
          hGet hChildTarget⟩
  · intro residual state state' env label current future hRelated hEdge
    rcases relationMembership_xoffer_cases alphabet elseType branches hRelated
      with hRoot | ⟨q, hStateEq, hChildRelated⟩ |
        ⟨i, action, branchType, q, hGet, hStateEq, hChildRelated⟩
    · -- Root: the three root families are exactly the three offer rules.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, hStateEq'⟩ := hRoot
      simp only at hResEq hStateEq'
      subst hResEq; subst hStateEq'
      have hWhole := compileTypeFuel_xoffer_eq alphabet elseType branches
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
        hPFuture, hPTarget⟩ :=
        (compileType_hasEdge_iff_hasResolvedEdge
          (.xoffer alphabet elseType branches) TypeAutomatonState.root state'
          env label ⟨current, future⟩).mp hEdge
      rw [hWhole] at hPendingMem
      simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image] at hPendingMem
      rcases hPendingMem with ((((hElseCopy | hIndexed) | hBranch) | hWait)
        | hResolved)
      · exfalso
        obtain ⟨childEdge, -, hEq⟩ := hElseCopy
        rw [← hEq] at hPSource
        simp [childPendingEdge, childState] at hPSource
      · exfalso
        rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
        rcases hIndexed with hEmpty | ⟨indexed, -, hIn⟩
        · exact absurd hEmpty (Finset.notMem_empty _)
        · rw [childPendingEdges, Finset.mem_image] at hIn
          obtain ⟨childEdge, -, hEq⟩ := hIn
          rw [← hEq] at hPSource
          simp [childPendingEdge, childState] at hPSource
      · -- Fire family: one root edge per enabled branch.
        rw [mem_foldl_union_iff] at hBranch
        rcases hBranch with hEmpty | ⟨indexed, hIndexedMem, hIn⟩
        · exact absurd hEmpty (Finset.notMem_empty _)
        · rw [Finset.mem_image, ] at hIn
          obtain ⟨environment, hFilter, hEq⟩ := hIn
          rw [Finset.mem_filter] at hFilter
          obtain ⟨hEnvMem, hEnabled, hResolvedNeeds, hGate⟩ := hFilter
          -- Recover the branch this index names.
          have hMapGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
          rw [List.getElem?_map] at hMapGet
          obtain ⟨entry, hEntryGet, hEntryEq⟩ :=
            Option.map_eq_some_iff.mp hMapGet
          rw [← hEq] at hPEnv hPLabel hPCurrent hPTarget
          simp only at hPEnv hPLabel hPCurrent hPTarget
          subst hPEnv
          have hActionEq : indexed.1.1 = entry.1 := by rw [← hEntryEq]
          have hLabelEq : label =
              TypeLabel.message indexed.1.1.1 indexed.1.1.2 := by
            have h := hPLabel; simp at h; exact h.symm
          subst hLabelEq
          have hCurrentEq : current = {indexed.1.1} := hPCurrent.symm
          subst hCurrentEq
          refine ⟨entry.2, typeFutureOffers entry.2 \ {entry.1}, ?_, ?_⟩
          · rw [hActionEq]
            exact ⟨TypeTransition.xoffer_branch environment alphabet elseType
                branches entry.1 entry.2
                ⟨PactTypeAlphabet.environment_wellFormed hEnvMem,
                  List.mem_of_getElem? hEntryGet, hActionEq ▸ hEnabled,
                  hResolvedNeeds⟩ hGate,
              TypeOffers.xoffer_branch environment alphabet elseType branches
                entry.1 entry.2
                ⟨PactTypeAlphabet.environment_wellFormed hEnvMem,
                  List.mem_of_getElem? hEntryGet, hActionEq ▸ hEnabled,
                  hResolvedNeeds⟩ hGate⟩
          · rw [← hPTarget]
            have hFragEq : indexed.1.2 =
                compileTypeFuel (typeCompilationFuel entry.2) entry.2 := by
              rw [← hEntryEq]
            rw [hFragEq]
            exact relationMembership_xoffer_branch alphabet elseType branches
              hEntryGet
              (buildRelationSet_initial entry.2 (compileType entry.2))
      · -- Wait family: the root's silent self-loop.
        obtain ⟨environment, hFilter, hEq⟩ := hWait
        rw [Finset.mem_filter] at hFilter
        obtain ⟨hEnvMem, hClock, hUnresolved, hGate⟩ := hFilter
        rw [← hEq] at hPEnv hPLabel hPCurrent hPTarget
        simp only at hPEnv hPLabel hPCurrent hPTarget
        subst hPEnv
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        subst hLabelEq
        refine ⟨.xoffer alphabet elseType branches,
          typeFutureOffers (.xoffer alphabet elseType branches) \
            typeWaitingOffers environment branches, ?_, ?_⟩
        · have hCurrentEq : current = typeWaitingOffers environment branches :=
            hPCurrent.symm
          subst hCurrentEq
          exact ⟨TypeTransition.xoffer_wait environment alphabet elseType
              branches ⟨PactTypeAlphabet.environment_wellFormed hEnvMem,
                hUnresolved, hClock⟩ hGate,
            TypeOffers.xoffer_wait environment alphabet elseType branches
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hUnresolved,
                hClock⟩ hGate⟩
        · rw [← hPTarget]
          exact relationMembership_xoffer_root alphabet elseType branches
      · -- Default family: the root's silent edge into the copied else entry.
        obtain ⟨environment, hFilter, hEq⟩ := hResolved
        rw [Finset.mem_filter] at hFilter
        obtain ⟨hEnvMem, hClock, hNoImmediate, hResolvedNeeds, hGate⟩ := hFilter
        rw [← hEq] at hPEnv hPLabel hPCurrent hPTarget
        simp only at hPEnv hPLabel hPCurrent hPTarget
        subst hPEnv
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        subst hLabelEq
        have hCurrentEq : current = ∅ := hPCurrent.symm
        subst hCurrentEq
        refine ⟨elseType, typeFutureOffers elseType, ?_, ?_⟩
        · exact ⟨TypeTransition.xoffer_else environment alphabet elseType
              branches ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hClock,
                hNoImmediate, hResolvedNeeds⟩ hGate,
            TypeOffers.xoffer_else environment alphabet elseType branches
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hClock,
                hNoImmediate, hResolvedNeeds⟩ hGate⟩
        · rw [← hPTarget]
          exact relationMembership_xoffer_else alphabet elseType branches
            (buildRelationSet_initial elseType (compileType elseType))
    · -- Copied default entry: restrict, apply the child, and lift back.
      subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        xoffer_else_edge_restrict alphabet elseType branches hElseDisjoint
          hElseAlphabet hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        hElse.2 hChildRelated hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_xoffer_else alphabet elseType branches hChildTarget⟩
    · -- Copied branch entry.
      subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        xoffer_branch_edge_restrict alphabet elseType branches i action
          branchType hGet
          (hBranchDisjoint action branchType (List.mem_of_getElem? hGet))
          (hBranchAlphabet action branchType (List.mem_of_getElem? hGet))
          hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        (hBranches action branchType
          (List.mem_of_getElem? hGet)).2 hChildRelated hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_xoffer_branch alphabet elseType branches hGet
          hChildTarget⟩

/-- A default tag on a conjunctive offer peels to the default arm. -/
theorem stateProductInfo_offer_child_else (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (q : TypeAutomatonState) :
    stateProductInfo (.offer alphabet elseType branches) (.child 0 q) =
      stateProductInfo elseType q := by
  have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
      max (typeCompilationFuel elseType)
        (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  simp only [stateProductInfo, hFuelEq, stateProductInfoFuel]
  exact stateProductInfoFuel_eq_of_sufficient elseType q
    (Nat.le_max_left _ _) (Nat.le_refl _)

/-- So does a selected-conjunction tag. -/
theorem stateProductInfo_offer_child_branch (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (i : Nat) (selected : BareMessage × PactType)
    (hBranch : branches[i]? = some selected)
    (q : TypeAutomatonState) :
    stateProductInfo (.offer alphabet elseType branches) (.child (i + 1) q) =
      stateProductInfo
        (parallelTypeBranchesSelecting alphabet selected branches) q := by
  have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
      max (typeCompilationFuel elseType)
        (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hFuel : typeCompilationFuel
      (parallelTypeBranchesSelecting alphabet selected branches) ≤
      max (typeCompilationFuel elseType)
        (conjunctiveCompilationFuel branches) := by
    rw [typeCompilationFuel_parallelTypeBranchesSelecting]
    exact Nat.le_max_right _ _
  simp only [stateProductInfo, hFuelEq, stateProductInfoFuel, hBranch]
  exact stateProductInfoFuel_eq_of_sufficient _ q hFuel (Nat.le_refl _)

/-- A copied default-arm edge of a conjunctive offer restricts to an edge of
the default arm. -/
theorem offer_else_edge_restrict (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseDisjoint : elseType.OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet =
      (PactType.offer alphabet elseType branches).alphabet)
    {q : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage} {state' : TypeAutomatonState}
    (hEdge : (compileType (.offer alphabet elseType branches)).HasEdge
      (.child 0 q) env label ⟨current, future⟩ state') :
    ∃ q', state' = .child 0 q' ∧
      (compileType elseType).HasEdge q env label ⟨current, future⟩ q' := by
  classical
  have hWhole := compileTypeFuel_offer_eq alphabet elseType branches
  have hFuelElse : typeCompilationFuel elseType + 1 ≤
      typeCompilationFuel (.offer alphabet elseType branches) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.offer alphabet elseType branches) (.child 0 visited) =
        stateProductInfo elseType visited :=
    stateProductInfo_offer_child_else alphabet elseType branches
  obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
    hPFuture, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge (.offer alphabet elseType branches)
      (.child 0 q) state' env label ⟨current, future⟩).mp hEdge
  rw [hWhole] at hPendingMem
  -- Invert directly: only the copied default family is sourced at `child 0`.
  obtain ⟨childEdge, hChildEdgeMem, hChildEq⟩ : ∃ childEdge ∈
      (compileTypeFuel (typeCompilationFuel elseType) elseType).edges,
      pendingEdge = childPendingEdge 0 childEdge := by
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hPendingMem
    rcases hPendingMem with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · obtain ⟨childEdge, hMem, hEq⟩ := hElse
      exact ⟨childEdge, hMem, hEq.symm⟩
    · exfalso
      rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, -, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [childPendingEdges, Finset.mem_image] at hIn
        obtain ⟨childEdge, -, hEq⟩ := hIn
        rw [← hEq] at hPSource
        simp [childPendingEdge, childState] at hPSource
    · exfalso
      rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, -, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [Finset.mem_image] at hIn
        obtain ⟨environment, -, hEq⟩ := hIn
        rw [← hEq] at hPSource
        simp [childState] at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hWait
      rw [← hEq] at hPSource
      simp at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hResolved
      rw [← hEq] at hPSource
      simp at hPSource
  have hChildSource : childEdge.source = q := by
    rw [hChildEq] at hPSource
    simpa [childPendingEdge, childState] using hPSource
  refine ⟨childEdge.target, by rw [← hPTarget, hChildEq]; rfl, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge elseType q childEdge.target env
    label ⟨current, future⟩]
  refine ⟨childEdge, hChildEdgeMem, hChildSource, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hPEnv, hChildEq]; rfl
  · rw [← hPLabel, hChildEq]; rfl
  · rw [← hPCurrent, hChildEq]; rfl
  · rw [← hPFuture, hChildEq]
    cases hSpec : childEdge.future with
    | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel elseType) elseType le_rfl hElseDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_selectedConjunctiveOffer_else elseType branches
          (.offer alphabet elseType branches) hWhole hElseAlphabet hFuelElse
          hElseDisjoint hProductInfo t hStateMem]

/-- A default-arm edge lifts to the copied edge of a conjunctive offer. -/
theorem offer_else_edge_lift (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseDisjoint : elseType.OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet =
      (PactType.offer alphabet elseType branches).alphabet)
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType elseType).HasEdge q env label ⟨current, future⟩ q') :
    (compileType (.offer alphabet elseType branches)).HasEdge
      (.child 0 q) env label ⟨current, future⟩ (.child 0 q') := by
  classical
  have hWhole := compileTypeFuel_offer_eq alphabet elseType branches
  have hFuelElse : typeCompilationFuel elseType + 1 ≤
      typeCompilationFuel (.offer alphabet elseType branches) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.offer alphabet elseType branches) (.child 0 visited) =
        stateProductInfo elseType visited :=
    stateProductInfo_offer_child_else alphabet elseType branches
  obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent,
    hCFuture, hCTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge elseType q q' env label
      ⟨current, future⟩).mp hEdge
  rw [compileType_hasEdge_iff_hasResolvedEdge (.offer alphabet elseType branches)
    (.child 0 q) (.child 0 q') env label ⟨current, future⟩, hWhole]
  refine ⟨childPendingEdge 0 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨childEdge, hChildEdgeMem, rfl⟩)))
  · simp [childPendingEdge, childState, hCSource]
  · simp [childPendingEdge, hCEnv]
  · simp [childPendingEdge, hCLabel]
  · simp [childPendingEdge, hCCurrent]
  · cases hSpec : childEdge.future with
    | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel elseType) elseType le_rfl hElseDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_selectedConjunctiveOffer_else elseType branches
          (.offer alphabet elseType branches) hWhole hElseAlphabet hFuelElse
          hElseDisjoint hProductInfo t hStateMem]
        simpa [childFutureSpec, hSpec] using hCFuture
  · simp [childPendingEdge, childState, hCTarget]

/-- A copied selected-conjunction edge of a conjunctive offer restricts to an
edge of that generated product. -/
theorem offer_selected_edge_restrict (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (i : Nat) (selected : BareMessage × PactType)
    (hGet : branches[i]? = some selected)
    (hDisjoint : ∀ branch ∈ branches, branch.2.OfferBranchesDisjoint)
    (hSelDisjoint :
      (parallelTypeBranchesSelecting alphabet selected branches).OfferBranchesDisjoint)
    (hSelAlphabet :
      (parallelTypeBranchesSelecting alphabet selected branches).alphabet =
        (PactType.offer alphabet elseType branches).alphabet)
    {q : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage} {state' : TypeAutomatonState}
    (hEdge : (compileType (.offer alphabet elseType branches)).HasEdge
      (.child (i + 1) q) env label ⟨current, future⟩ state') :
    ∃ q', state' = .child (i + 1) q' ∧
      (compileType (parallelTypeBranchesSelecting alphabet selected branches)).HasEdge
        q env label ⟨current, future⟩ q' := by
  classical
  have hWhole := compileTypeFuel_offer_eq alphabet elseType branches
  have hFuelSel :
      typeCompilationFuel
        (parallelTypeBranchesSelecting alphabet selected branches) + 1 ≤
      typeCompilationFuel (.offer alphabet elseType branches) := by
    rw [typeCompilationFuel_parallelTypeBranchesSelecting]
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.offer alphabet elseType branches)
          (.child (i + 1) visited) =
        stateProductInfo
          (parallelTypeBranchesSelecting alphabet selected branches) visited :=
    stateProductInfo_offer_child_branch alphabet elseType branches i selected
      hGet
  obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
    hPFuture, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge (.offer alphabet elseType branches)
      (.child (i + 1) q) state' env label ⟨current, future⟩).mp hEdge
  rw [hWhole] at hPendingMem
  -- Only the copied selected-conjunction family is sourced at `child (i+1)`.
  obtain ⟨childEdge, hChildEdgeMem, hChildEq⟩ : ∃ childEdge ∈
      (compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet selected branches))
        (parallelTypeBranchesSelecting alphabet selected branches)).edges,
      pendingEdge = childPendingEdge (i + 1) childEdge := by
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hPendingMem
    rcases hPendingMem with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · exfalso
      obtain ⟨childEdge, -, hEq⟩ := hElse
      rw [← hEq] at hPSource
      simp [childPendingEdge, childState] at hPSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [childPendingEdges, Finset.mem_image] at hIn
        obtain ⟨childEdge, hMem, hEq⟩ := hIn
        have hIdx : indexed.2 = i := by
          have h := hPSource
          rw [← hEq] at h
          simp only [childPendingEdge, childState,
            TypeAutomatonState.child.injEq] at h
          omega
        subst hIdx
        have hMapGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
        rw [List.getElem?_map, hGet] at hMapGet
        have hFragEq : indexed.1.2 =
            compileTypeFuel
              (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches))
              (parallelTypeBranchesSelecting alphabet selected branches) := by
          simpa using (congrArg (fun o => (Option.map Prod.snd o)) hMapGet).symm
        rw [hFragEq] at hMem
        exact ⟨childEdge, hMem, hEq.symm⟩
    · exfalso
      rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, -, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [Finset.mem_image] at hIn
        obtain ⟨environment, -, hEq⟩ := hIn
        rw [← hEq] at hPSource
        simp [childState] at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hWait
      rw [← hEq] at hPSource
      simp at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hResolved
      rw [← hEq] at hPSource
      simp at hPSource
  have hChildSource : childEdge.source = q := by
    rw [hChildEq] at hPSource
    simpa [childPendingEdge, childState] using hPSource
  refine ⟨childEdge.target, by rw [← hPTarget, hChildEq]; rfl, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge
    (parallelTypeBranchesSelecting alphabet selected branches) q
    childEdge.target env label ⟨current, future⟩]
  refine ⟨childEdge, hChildEdgeMem, hChildSource, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hPEnv, hChildEq]; rfl
  · rw [← hPLabel, hChildEq]; rfl
  · rw [← hPCurrent, hChildEq]; rfl
  · rw [← hPFuture, hChildEq]
    cases hSpec : childEdge.future with
    | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel
            (parallelTypeBranchesSelecting alphabet selected branches))
          (parallelTypeBranchesSelecting alphabet selected branches) le_rfl
          hSelDisjoint childEdge hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_selectedConjunctiveOffer_branch elseType branches
          (.offer alphabet elseType branches) hWhole i selected hGet hFuelSel
          hSelAlphabet hDisjoint hProductInfo t hStateMem]

/-- A selected-conjunction edge lifts to the copied edge of a conjunctive
offer. -/
theorem offer_selected_edge_lift (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (i : Nat) (selected : BareMessage × PactType)
    (hGet : branches[i]? = some selected)
    (hDisjoint : ∀ branch ∈ branches, branch.2.OfferBranchesDisjoint)
    (hSelDisjoint :
      (parallelTypeBranchesSelecting alphabet selected branches).OfferBranchesDisjoint)
    (hSelAlphabet :
      (parallelTypeBranchesSelecting alphabet selected branches).alphabet =
        (PactType.offer alphabet elseType branches).alphabet)
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge :
      (compileType (parallelTypeBranchesSelecting alphabet selected branches)).HasEdge
        q env label ⟨current, future⟩ q') :
    (compileType (.offer alphabet elseType branches)).HasEdge
      (.child (i + 1) q) env label ⟨current, future⟩ (.child (i + 1) q') := by
  classical
  have hWhole := compileTypeFuel_offer_eq alphabet elseType branches
  have hFuelSel :
      typeCompilationFuel
        (parallelTypeBranchesSelecting alphabet selected branches) + 1 ≤
      typeCompilationFuel (.offer alphabet elseType branches) := by
    rw [typeCompilationFuel_parallelTypeBranchesSelecting]
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.offer alphabet elseType branches)
          (.child (i + 1) visited) =
        stateProductInfo
          (parallelTypeBranchesSelecting alphabet selected branches) visited :=
    stateProductInfo_offer_child_branch alphabet elseType branches i selected
      hGet
  obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent,
    hCFuture, hCTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge
      (parallelTypeBranchesSelecting alphabet selected branches) q q' env label
      ⟨current, future⟩).mp hEdge
  rw [compileType_hasEdge_iff_hasResolvedEdge (.offer alphabet elseType branches)
    (.child (i + 1) q) (.child (i + 1) q') env label ⟨current, future⟩, hWhole]
  refine ⟨childPendingEdge (i + 1) childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hMapGet : (branches.map fun branch => (branch.1, compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet branch branches))
        (parallelTypeBranchesSelecting alphabet branch branches)))[i]? =
        some (selected.1, compileTypeFuel
          (typeCompilationFuel
            (parallelTypeBranchesSelecting alphabet selected branches))
          (parallelTypeBranchesSelecting alphabet selected branches)) := by
      rw [List.getElem?_map, hGet]; rfl
    exact ((buildSelectedConjunctiveOfferAutomaton_outgoing_branch alphabet
      branches (compileTypeFuel (typeCompilationFuel elseType) elseType)
      (branches.map fun branch => (branch.1, compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet branch branches))
        (parallelTypeBranchesSelecting alphabet branch branches))) i selected.1
      (compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet selected branches))
        (parallelTypeBranchesSelecting alphabet selected branches)) hMapGet q
      (childPendingEdge (i + 1) childEdge)).mpr
      ⟨childEdge, hChildEdgeMem, hCSource, rfl⟩).1
  · simp [childPendingEdge, childState, hCSource]
  · simp [childPendingEdge, hCEnv]
  · simp [childPendingEdge, hCLabel]
  · simp [childPendingEdge, hCCurrent]
  · cases hSpec : childEdge.future with
    | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel
            (parallelTypeBranchesSelecting alphabet selected branches))
          (parallelTypeBranchesSelecting alphabet selected branches) le_rfl
          hSelDisjoint childEdge hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_selectedConjunctiveOffer_branch elseType branches
          (.offer alphabet elseType branches) hWhole i selected hGet hFuelSel
          hSelAlphabet hDisjoint hProductInfo t hStateMem]
        simpa [childFutureSpec, hSpec] using hCFuture
  · simp [childPendingEdge, childState, hCTarget]

/-- Current-offer correspondence at a conjunctive offer.  The construction has
the same form as the exclusive offer, except that the `i`-th child is the
compiled residual obtained by selecting branch `i`; the root's three rules name
the builder's three root families, and the copied entries use the lower-rank
hypothesis. -/
theorem currentOfferCorrespondence_offer (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseDisjoint : elseType.OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet =
      (PactType.offer alphabet elseType branches).alphabet)
    (hDisjoint : ∀ branch ∈ branches, branch.2.OfferBranchesDisjoint)
    (hSelDisjoint : ∀ selected ∈ branches,
      (parallelTypeBranchesSelecting alphabet selected branches).OfferBranchesDisjoint)
    (hSelAlphabet : ∀ selected ∈ branches,
      (parallelTypeBranchesSelecting alphabet selected branches).alphabet =
        (PactType.offer alphabet elseType branches).alphabet)
    (hElse : CurrentOfferCorrespondence elseType)
    (hSelected : ∀ selected ∈ branches,
      CurrentOfferCorrespondence
        (parallelTypeBranchesSelecting alphabet selected branches)) :
    CurrentOfferCorrespondence (.offer alphabet elseType branches) := by
  classical
  constructor
  · intro residual residual' state env label current future hRelated hTransition
    rcases relationMembership_offer_cases alphabet elseType branches hRelated
      with hRoot | ⟨q, hStateEq, hChildRelated⟩ |
        ⟨i, selected, q, hGet, hStateEq, hChildRelated⟩
    · -- Root: each offer rule names its own root edge family.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, hStateEq'⟩ := hRoot
      simp only at hResEq hStateEq'
      subst hResEq; subst hStateEq'
      have hWhole := compileTypeFuel_offer_eq alphabet elseType branches
      obtain ⟨-, hOffers⟩ := hTransition
      cases hOffers with
      | offer_some cEnv cAlpha cElse cBranches cEnabled hCond hGate =>
          obtain ⟨index, hBranchGet⟩ := List.mem_iff_getElem?.mp hCond.2.1
          refine Exists.intro
            (.child (index + 1) (compileTypeFuel
              (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet cEnabled branches))
              (parallelTypeBranchesSelecting alphabet cEnabled
                branches)).initial)
            (Exists.intro
              (computeFutureOf (.offer alphabet elseType branches)
                (.child (index + 1) (compileTypeFuel
                  (typeCompilationFuel
                    (parallelTypeBranchesSelecting alphabet cEnabled branches))
                  (parallelTypeBranchesSelecting alphabet cEnabled
                    branches)).initial)) ⟨?_, ?_⟩)
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.offer alphabet elseType branches) TypeAutomatonState.root
              (.child (index + 1) (compileTypeFuel
                (typeCompilationFuel
                  (parallelTypeBranchesSelecting alphabet cEnabled branches))
                (parallelTypeBranchesSelecting alphabet cEnabled
                  branches)).initial) env TypeLabel.silent _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := (∅ : Finset BareMessage),
                future := FutureSpec.at (childState (index + 1)
                  (compileTypeFuel
                    (typeCompilationFuel
                      (parallelTypeBranchesSelecting alphabet cEnabled branches))
                    (parallelTypeBranchesSelecting alphabet cEnabled
                      branches)).initial) ∅,
                target := childState (index + 1) (compileTypeFuel
                  (typeCompilationFuel
                    (parallelTypeBranchesSelecting alphabet cEnabled branches))
                  (parallelTypeBranchesSelecting alphabet cEnabled
                    branches)).initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildSelectedConjunctiveOfferAutomaton,
                finishAutomatonFragment, Finset.mem_union]
              refine Or.inl (Or.inl (Or.inr ?_))
              rw [mem_foldl_union_iff]
              refine Or.inr ⟨(⟨cEnabled.1, compileTypeFuel
                (typeCompilationFuel
                  (parallelTypeBranchesSelecting alphabet cEnabled branches))
                (parallelTypeBranchesSelecting alphabet cEnabled branches)⟩,
                index), ?_, ?_⟩
              · refine List.mk_mem_zipIdx_iff_getElem?.mpr ?_
                rw [List.getElem?_map, hBranchGet]; rfl
              · simp only [Finset.mem_image, Finset.mem_filter]
                exact ⟨env,
                  ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hCond.1,
                    hCond.2.2, hGate⟩, rfl⟩
            · simp [childState]
          · exact relationMembership_offer_selected alphabet elseType branches
              hBranchGet
              (buildRelationSet_initial _ (compileType _))
      | offer_else cEnv cAlpha cElse cBranches hCond hGate =>
          refine Exists.intro
            (.child 0 (compileTypeFuel (typeCompilationFuel elseType)
              elseType).initial)
            (Exists.intro
              (computeFutureOf (.offer alphabet elseType branches)
                (.child 0 (compileTypeFuel (typeCompilationFuel elseType)
                  elseType).initial) \ typeBranchActions branches) ⟨?_, ?_⟩)
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.offer alphabet elseType branches) TypeAutomatonState.root
              (.child 0 (compileTypeFuel (typeCompilationFuel elseType)
                elseType).initial) env TypeLabel.silent _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := typeBranchActions branches,
                future := FutureSpec.at (childState 0 (compileTypeFuel
                  (typeCompilationFuel elseType) elseType).initial)
                  (typeBranchActions branches),
                target := childState 0 (compileTypeFuel
                  (typeCompilationFuel elseType) elseType).initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildSelectedConjunctiveOfferAutomaton,
                finishAutomatonFragment, Finset.mem_union, Finset.mem_image,
                Finset.mem_filter]
              exact Or.inr ⟨env,
                ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hCond.1,
                  hCond.2.1, hCond.2.2.1, hCond.2.2.2, hGate⟩, rfl⟩
            · simp [childState]
          · exact relationMembership_offer_else alphabet elseType branches
              (buildRelationSet_initial elseType (compileType elseType))
      | offer_wait cEnv cAlpha cElse cBranches hCond hGate =>
          refine Exists.intro TypeAutomatonState.root
            (Exists.intro
              (computeFutureOf (.offer alphabet elseType branches)
                TypeAutomatonState.root \ typeBranchActions branches) ⟨?_, ?_⟩)
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.offer alphabet elseType branches) TypeAutomatonState.root
              TypeAutomatonState.root env TypeLabel.silent _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := typeBranchActions branches,
                future := FutureSpec.at TypeAutomatonState.root
                  (typeBranchActions branches),
                target := TypeAutomatonState.root }
              ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp only [buildSelectedConjunctiveOfferAutomaton,
              finishAutomatonFragment, Finset.mem_union, Finset.mem_image,
              Finset.mem_filter]
            exact Or.inl (Or.inr ⟨env,
              ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hCond.1,
                hCond.2.1, hCond.2.2.1, hCond.2.2.2, hGate⟩, rfl⟩)
          · exact relationMembership_offer_root alphabet elseType branches
    · -- Copied default entry.
      subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        hElse.1 hChildRelated hTransition
      exact ⟨.child 0 q', future',
        offer_else_edge_lift alphabet elseType branches hElseDisjoint
          hElseAlphabet hChildEdge,
        relationMembership_offer_else alphabet elseType branches hChildTarget⟩
    · -- Copied selected-conjunction entry.
      subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        (hSelected selected (List.mem_of_getElem? hGet)).1 hChildRelated
          hTransition
      exact ⟨.child (i + 1) q', future',
        offer_selected_edge_lift alphabet elseType branches i selected hGet
          hDisjoint (hSelDisjoint selected (List.mem_of_getElem? hGet))
          (hSelAlphabet selected (List.mem_of_getElem? hGet)) hChildEdge,
        relationMembership_offer_selected alphabet elseType branches hGet
          hChildTarget⟩
  · intro residual state state' env label current future hRelated hEdge
    rcases relationMembership_offer_cases alphabet elseType branches hRelated
      with hRoot | ⟨q, hStateEq, hChildRelated⟩ |
        ⟨i, selected, q, hGet, hStateEq, hChildRelated⟩
    · -- Root: the three root families are exactly the three offer rules.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, hStateEq'⟩ := hRoot
      simp only at hResEq hStateEq'
      subst hResEq; subst hStateEq'
      have hWhole := compileTypeFuel_offer_eq alphabet elseType branches
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
        hPFuture, hPTarget⟩ :=
        (compileType_hasEdge_iff_hasResolvedEdge
          (.offer alphabet elseType branches) TypeAutomatonState.root state'
          env label ⟨current, future⟩).mp hEdge
      rw [hWhole] at hPendingMem
      simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image] at hPendingMem
      rcases hPendingMem with ((((hElseCopy | hIndexed) | hEnabled) | hWait)
        | hResolved)
      · exfalso
        obtain ⟨childEdge, -, hEq⟩ := hElseCopy
        rw [← hEq] at hPSource
        simp [childPendingEdge, childState] at hPSource
      · exfalso
        rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
        rcases hIndexed with hEmpty | ⟨indexed, -, hIn⟩
        · exact absurd hEmpty (Finset.notMem_empty _)
        · rw [childPendingEdges, Finset.mem_image] at hIn
          obtain ⟨childEdge, -, hEq⟩ := hIn
          rw [← hEq] at hPSource
          simp [childPendingEdge, childState] at hPSource
      · -- Enabled family: one root edge per enabled branch.
        rw [mem_foldl_union_iff] at hEnabled
        rcases hEnabled with hEmpty | ⟨indexed, hIndexedMem, hIn⟩
        · exact absurd hEmpty (Finset.notMem_empty _)
        · rw [Finset.mem_image] at hIn
          obtain ⟨environment, hFilter, hEq⟩ := hIn
          rw [Finset.mem_filter] at hFilter
          obtain ⟨hEnvMem, hEnabledNeed, hGate⟩ := hFilter
          have hMapGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
          rw [List.getElem?_map] at hMapGet
          obtain ⟨entry, hEntryGet, hEntryEq⟩ :=
            Option.map_eq_some_iff.mp hMapGet
          rw [← hEq] at hPEnv hPLabel hPCurrent hPTarget
          simp only at hPEnv hPLabel hPCurrent hPTarget
          subst hPEnv
          have hActionEq : indexed.1.1 = entry.1 := by rw [← hEntryEq]
          have hEnabledEntry : TypeBranchEnabled environment entry := by
            simp only [TypeBranchEnabled]
            rw [← hActionEq]
            exact hEnabledNeed
          have hLabelEq : label = TypeLabel.silent := by
            have h := hPLabel; simp at h; exact h.symm
          subst hLabelEq
          have hCurrentEq : current = ∅ := hPCurrent.symm
          subst hCurrentEq
          refine ⟨parallelTypeBranchesSelecting alphabet entry branches,
            typeFutureOffers
              (parallelTypeBranchesSelecting alphabet entry branches), ?_, ?_⟩
          · exact ⟨TypeTransition.offer_some environment alphabet elseType
                branches entry
                ⟨PactTypeAlphabet.environment_wellFormed hEnvMem,
                  List.mem_of_getElem? hEntryGet, hEnabledEntry⟩
                hGate,
              TypeOffers.offer_some environment alphabet elseType branches entry
                ⟨PactTypeAlphabet.environment_wellFormed hEnvMem,
                  List.mem_of_getElem? hEntryGet, hEnabledEntry⟩
                hGate⟩
          · rw [← hPTarget]
            have hFragEq : indexed.1.2 =
                compileTypeFuel
                  (typeCompilationFuel
                    (parallelTypeBranchesSelecting alphabet entry branches))
                  (parallelTypeBranchesSelecting alphabet entry branches) := by
              rw [← hEntryEq]
            rw [hFragEq]
            exact relationMembership_offer_selected alphabet elseType branches
              hEntryGet (buildRelationSet_initial _ (compileType _))
      · -- Wait family: the root's silent self-loop.
        obtain ⟨environment, hFilter, hEq⟩ := hWait
        rw [Finset.mem_filter] at hFilter
        obtain ⟨hEnvMem, hClock, hNoImmediate, hUnresolved, hGate⟩ := hFilter
        rw [← hEq] at hPEnv hPLabel hPCurrent hPTarget
        simp only at hPEnv hPLabel hPCurrent hPTarget
        subst hPEnv
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        subst hLabelEq
        have hCurrentEq : current = typeBranchActions branches := hPCurrent.symm
        subst hCurrentEq
        refine ⟨.offer alphabet elseType branches,
          typeFutureOffers (.offer alphabet elseType branches) \
            typeBranchActions branches, ?_, ?_⟩
        · exact ⟨TypeTransition.offer_wait environment alphabet elseType branches
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hClock,
                hNoImmediate, hUnresolved⟩ hGate,
            TypeOffers.offer_wait environment alphabet elseType branches
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hClock,
                hNoImmediate, hUnresolved⟩ hGate⟩
        · rw [← hPTarget]
          exact relationMembership_offer_root alphabet elseType branches
      · -- Default family: the root's silent edge into the copied else entry.
        obtain ⟨environment, hFilter, hEq⟩ := hResolved
        rw [Finset.mem_filter] at hFilter
        obtain ⟨hEnvMem, hClock, hNoImmediate, hResolvedNeeds, hGate⟩ := hFilter
        rw [← hEq] at hPEnv hPLabel hPCurrent hPTarget
        simp only at hPEnv hPLabel hPCurrent hPTarget
        subst hPEnv
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        subst hLabelEq
        have hCurrentEq : current = typeBranchActions branches := hPCurrent.symm
        subst hCurrentEq
        refine ⟨elseType,
          typeFutureOffers elseType \ typeBranchActions branches, ?_, ?_⟩
        · exact ⟨TypeTransition.offer_else environment alphabet elseType branches
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hClock,
                hNoImmediate, hResolvedNeeds⟩ hGate,
            TypeOffers.offer_else environment alphabet elseType branches
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hClock,
                hNoImmediate, hResolvedNeeds⟩ hGate⟩
        · rw [← hPTarget]
          exact relationMembership_offer_else alphabet elseType branches
            (buildRelationSet_initial elseType (compileType elseType))
    · -- Copied default entry.
      subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        offer_else_edge_restrict alphabet elseType branches hElseDisjoint
          hElseAlphabet hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        hElse.2 hChildRelated hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_offer_else alphabet elseType branches hChildTarget⟩
    · -- Copied selected-conjunction entry.
      subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        offer_selected_edge_restrict alphabet elseType branches i selected hGet
          hDisjoint (hSelDisjoint selected (List.mem_of_getElem? hGet))
          (hSelAlphabet selected (List.mem_of_getElem? hGet)) hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        (hSelected selected (List.mem_of_getElem? hGet)).2 hChildRelated
          hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_offer_selected alphabet elseType branches hGet
          hChildTarget⟩

/-- A conjunctive-offer root carries no product information. -/
theorem stateProductInfo_offer_root (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType)) :
    stateProductInfo (.offer alphabet elseType branches)
        TypeAutomatonState.root = none := by
  obtain ⟨k, hk⟩ : ∃ k,
      typeCompilationFuel (.offer alphabet elseType branches) = k + 1 :=
    ⟨typeCompilationFuel (.offer alphabet elseType branches) - 1, by
      have := typeCompilationFuel_positive (.offer alphabet elseType branches)
      omega⟩
  simp only [stateProductInfo, hk, stateProductInfoFuel]

/-- A conjunctive-offer root offers exactly the branch head actions.  Unlike the
exclusive root, its enabling edges publish nothing (their current offer is `∅`);
the branch actions come from the wait and default families, whose filters the
empty environment always satisfies. -/
theorem buildSelectedConjunctiveOfferAutomaton_offersAt_root
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (hGuard : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions) :
    ({ states := (buildSelectedConjunctiveOfferAutomaton alphabet branches
         elseAutomaton selectedConjunctions).states
       edges := (buildSelectedConjunctiveOfferAutomaton alphabet branches
         elseAutomaton selectedConjunctions).edges } : PendingAutomaton).offersAt
        TypeAutomatonState.root =
      typeBranchActions branches := by
  classical
  apply Finset.Subset.antisymm
  · -- Every root edge publishes either `∅` or exactly the branch actions.
    intro action hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hAction
    obtain ⟨edge, ⟨hEdge, hSource⟩, hIn⟩ := hAction
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter] at hEdge
    rcases hEdge with ((((hElseCopy | hIndexed) | hEnabled) | hWait) | hResolved)
    · exfalso
      obtain ⟨childEdge, -, hEq⟩ := hElseCopy
      rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
    · exfalso
      rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, -, hIn'⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [childPendingEdges, Finset.mem_image] at hIn'
        obtain ⟨childEdge, -, hEq⟩ := hIn'
        rw [← hEq] at hSource
        simp [childPendingEdge, childState] at hSource
    · -- An enabling edge publishes nothing.
      exfalso
      rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, -, hIn'⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [Finset.mem_image] at hIn'
        obtain ⟨environment, -, hEq⟩ := hIn'
        rw [← hEq] at hIn
        simp at hIn
    · obtain ⟨environment, -, hEq⟩ := hWait
      rw [← hEq] at hIn
      simpa using hIn
    · obtain ⟨environment, -, hEq⟩ := hResolved
      rw [← hEq] at hIn
      simpa using hIn
  · -- The empty environment satisfies the default family's filter, and that
    -- edge publishes exactly the branch actions.
    intro action hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion, Finset.mem_filter]
    refine Exists.intro
      { source := TypeAutomatonState.root,
        environment := TypeEnvironment.empty,
        label := AutomatonConstructionLabel.visible TypeLabel.silent,
        current := typeBranchActions branches,
        future := FutureSpec.at (childState 0 elseAutomaton.initial)
          (typeBranchActions branches),
        target := childState 0 elseAutomaton.initial }
      ⟨⟨?_, rfl⟩, ?_⟩
    · simp only [buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_image,
        Finset.mem_filter]
      refine Or.inr ⟨TypeEnvironment.empty,
        ⟨empty_mem_localEnvironments alphabet, rfl, ?_, ?_, hGuard⟩, rfl⟩
      · simp [TypeEnvironment.empty]
      · simp [TypeEnvironment.empty]
    · simpa using hAction

/-- Menus agree at an exclusive offer.  The root exposes the branch heads on its
own edges and reaches exactly the default and branch entries. -/
theorem futureOffersAgree_xoffer (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hWholeDisjoint :
      (PactType.xoffer alphabet elseType branches).OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet = alphabet)
    (hBranchAlphabet : ∀ branch ∈ branches, branch.2.alphabet = alphabet)
    (hElse : FutureOffersAgree elseType)
    (hBranches : ∀ branch ∈ branches, FutureOffersAgree branch.2) :
    FutureOffersAgree (.xoffer alphabet elseType branches) := by
  classical
  set whole : PactType := .xoffer alphabet elseType branches with hWholeDef
  have hWhole := compileTypeFuel_xoffer_eq alphabet elseType branches
  have hDisjointParts :
      elseType.OfferBranchesDisjoint ∧
        PactType.OfferBranchesDisjointBranches branches := by
    simpa only [hWholeDef, PactType.OfferBranchesDisjoint] using hWholeDisjoint
  have hElseDisjoint : elseType.OfferBranchesDisjoint := hDisjointParts.1
  have hBranchDisjoint : ∀ branch ∈ branches,
      branch.2.OfferBranchesDisjoint := by
    intro branch hBranch
    exact offerBranchesDisjoint_of_mem hDisjointParts.2 hBranch
  have hElseFuel :
      typeCompilationFuel elseType + 1 ≤ typeCompilationFuel whole := by
    simp only [hWholeDef, typeCompilationFuel]
    omega
  have hBranchFuel : ∀ branch ∈ branches,
      typeCompilationFuel branch.2 + 1 ≤ typeCompilationFuel whole := by
    intro branch hBranch
    have hLe := typeCompilationFuel_le_typeBranchCompilationFuel branches
      branch hBranch
    simp only [hWholeDef, typeCompilationFuel]
    omega
  intro residual state hRelated
  rcases relationMembership_xoffer_cases alphabet elseType branches
      hRelated with hRoot | ⟨q, hState, hChild⟩ |
      ⟨i, action, branchType, q, hGet, hState, hChild⟩
  · injection hRoot with hResidual hStateEq
    subst hResidual
    subst hStateEq
    set branchAutomata :=
      branches.map fun branch =>
        (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2)
      with hBranchAutomata
    set elseFragment :=
      compileTypeFuel (typeCompilationFuel elseType) elseType with hElseFragment
    set pending : PendingAutomaton :=
      { states := (compileTypeFuel (typeCompilationFuel whole) whole).states
        edges := (compileTypeFuel (typeCompilationFuel whole) whole).edges }
      with hPending
    have hHeads : branchAutomata.map Prod.fst = branches.map Prod.fst := by
      rw [hBranchAutomata, List.map_map]
      rfl
    -- Both menus are gated on the same declaredness condition: if it fails,
    -- `typeFutureOffers` is empty by its own gate and the root has no outgoing
    -- edges, since all three root families carry the gate too.
    by_cases hGuard : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
    case neg =>
      -- The semantic menu is `∅` by its own gate, and the compiled menu is
      -- bounded by the type's alphabet, which the undeclared heads escape.
      have hSemantic : typeFutureOffers whole = ∅ := by
        rw [hWholeDef]
        simp only [typeFutureOffers, typeFutureOffersFuel, if_neg hGuard]
      rw [hSemantic]
      -- Every root family carries the gate, so the root has no outgoing edge;
      -- its same-cycle reach is itself and it publishes nothing.
      have hNoRootEdge : ∀ edge ∈ (compileTypeFuel (typeCompilationFuel whole)
          whole).edges, edge.source ≠ TypeAutomatonState.root := by
        intro edge hEdge hSource
        rw [hWhole] at hEdge
        simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
          childPendingEdges, Finset.mem_union, Finset.mem_image,
          Finset.mem_filter] at hEdge
        rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
        · obtain ⟨childEdge, -, hEq⟩ := hElse
          rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
        · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
          rcases hIndexed with hEmpty | ⟨indexed, -, hIn⟩
          · exact absurd hEmpty (Finset.notMem_empty _)
          · rw [childPendingEdges, Finset.mem_image] at hIn
            obtain ⟨childEdge, -, hEq⟩ := hIn
            rw [← hEq] at hSource
            simp [childPendingEdge, childState] at hSource
        · rw [mem_foldl_union_iff] at hBranch
          rcases hBranch with hEmpty | ⟨indexed, -, hIn⟩
          · exact absurd hEmpty (Finset.notMem_empty _)
          · rw [Finset.mem_image] at hIn
            obtain ⟨environment, hEnv, -⟩ := hIn
            rw [Finset.mem_filter] at hEnv
            exact hGuard hEnv.2.2.2
        · obtain ⟨environment, hEnv, -⟩ := hWait
          exact hGuard hEnv.2.2.2
        · obtain ⟨environment, hEnv, -⟩ := hResolved
          exact hGuard hEnv.2.2.2.2
      -- With no root-sourced edge the root references nothing, so its
      -- same-cycle reach is itself and it publishes no offer.
      have hRefs : pending.referencedStates TypeAutomatonState.root = ∅ := by
        rw [hPending]
        simp only [PendingAutomaton.referencedStates]
        rw [Finset.filter_eq_empty_iff.mpr (fun edge hEdge => hNoRootEdge edge
          hEdge)]
        simp
      have hOffersEmpty : pending.offersAt TypeAutomatonState.root = ∅ := by
        rw [hPending]
        simp only [PendingAutomaton.offersAt]
        rw [Finset.filter_eq_empty_iff.mpr (fun edge hEdge => hNoRootEdge edge
          hEdge)]
        simp
      have hReach : pending.futureReachable TypeAutomatonState.root =
          {TypeAutomatonState.root} := by
        simp only [PendingAutomaton.futureReachable]
        generalize pending.states.card = k
        induction k with
        | zero => rfl
        | succ k ihk =>
            rw [PendingAutomaton.futureReachableAux]
            have hStep : PendingAutomaton.futureStep pending
                {TypeAutomatonState.root} = {TypeAutomatonState.root} := by
              simp only [PendingAutomaton.futureStep]
              rw [show ({TypeAutomatonState.root} : Finset TypeAutomatonState).biUnion
                  pending.referencedStates = ∅ by
                rw [Finset.singleton_biUnion]; exact hRefs]
              simp
            rw [hStep]
            exact ihk
      -- The menu unfolds to a union over `{root}` of `offersAt root`, which is
      -- empty, plus the product term, which is `none` at an offer root.
      obtain ⟨k, hk⟩ : ∃ k, typeCompilationFuel whole = k + 1 :=
        ⟨typeCompilationFuel whole - 1, by
          have := typeCompilationFuel_positive whole; omega⟩
      show computeFutureOf whole TypeAutomatonState.root = ∅
      unfold computeFutureOf
      rw [hk, computeFutureOfFuel]
      simp only [← hk, ← hPending]
      rw [FiniteMenuGraph.futureReachable_eq_singleton_of_referencedStates_eq_empty
        _ .root (by simp only [PendingAutomaton.withMenuDependencies, hRefs,
          compileTypeMenuLinksFuel_root, Finset.union_empty])]
      simp only [Finset.singleton_biUnion, hOffersEmpty]
      rw [show stateProductInfo whole TypeAutomatonState.root = none by
        simp only [hWholeDef]
        exact stateProductInfo_xoffer_root alphabet elseType branches]
      simp
    have hOffers : pending.offersAt TypeAutomatonState.root =
        typeBranchActions branches := by
      rw [hPending, hWhole]
      exact buildExclusiveOfferAutomaton_offersAt_root alphabet branches
        elseFragment branchAutomata hHeads hGuard
    have hDecomp := computeFutureOf_root_decomposition whole
      TypeAutomatonState.root
      (exclusiveOfferEntries elseFragment branchAutomata) pending hPending
      (referencesClosed_compileTypeFuel whole (typeCompilationFuel whole)
        (Nat.le_refl _) hWholeDisjoint)
      (by
        rw [hPending]
        show TypeAutomatonState.root ∈
          (compileTypeFuel (typeCompilationFuel whole) whole).states
        rw [hWhole]
        simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment]
        exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_singleton_self _)))
      (by
        rw [hPending, hWhole]
        exact buildExclusiveOfferAutomaton_referencedStates_root_subset
          alphabet branches elseFragment branchAutomata)
      (by
        rw [hPending, hWhole]
        exact buildExclusiveOfferAutomaton_entries_subset_referencedStates_root
          alphabet branches elseFragment branchAutomata hHeads hGuard)
      (by
        simp only [hWholeDef]
        exact stateProductInfo_xoffer_root alphabet elseType branches)
      (by
        intro action hIn
        rw [hOffers] at hIn
        simp only [typeBranchActions, List.mem_toFinset, List.mem_map] at hIn
        obtain ⟨branch, hMem, rfl⟩ := hIn
        simpa [hWholeDef, PactType.alphabet] using hGuard branch hMem)
    rw [hDecomp, hOffers, hWholeDef,
      typeFutureOffers_xoffer alphabet elseType branches hGuard]
    -- the default entry carries the default's menu
    have hElseMenu : computeFutureOf whole
        (childState 0 elseFragment.initial) = typeFutureOffers elseType := by
      rw [childState, computeFutureOf_exclusiveOffer_else elseType branches
        whole hWhole hElseFuel hElseDisjoint
        (by rw [hElseAlphabet, hWholeDef]; rfl)
        (stateProductInfo_xoffer_child_else alphabet elseType branches)
        elseFragment.initial
        (compileTypeFuel_initial_mem _ elseType (Nat.le_refl _))]
      exact hElse (buildRelationSet_initial elseType _ rfl)
    -- and each branch entry its branch's
    have hBranchMenu : ∀ indexed ∈ branchAutomata.zipIdx,
        ∃ branch ∈ branches,
          computeFutureOf whole
            (childState (indexed.2 + 1) indexed.1.2.initial) =
            typeFutureOffers branch.2 := by
      intro indexed hIndexed
      have hGetAuto : branchAutomata[indexed.2]? = some indexed.1 := by
        rw [← List.mk_mem_zipIdx_iff_getElem?]
        simpa using hIndexed
      rw [hBranchAutomata, List.getElem?_map, Option.map_eq_some_iff]
        at hGetAuto
      obtain ⟨branch, hGetBranch, hEq⟩ := hGetAuto
      have hMem : branch ∈ branches := List.mem_of_getElem? hGetBranch
      refine ⟨branch, hMem, ?_⟩
      have hShape : indexed.1.2 =
          compileTypeFuel (typeCompilationFuel branch.2) branch.2 := by
        rw [← hEq]
      rw [hShape, childState, computeFutureOf_exclusiveOffer_branch elseType
        branches whole hWhole indexed.2 branch.1 branch.2 hGetBranch
        (hBranchFuel branch hMem) (hBranchDisjoint branch hMem)
        (by rw [hBranchAlphabet branch hMem, hWholeDef]; rfl)
        (stateProductInfo_xoffer_child_branch alphabet elseType branches
          indexed.2 branch.1 branch.2 hGetBranch) _
        (compileTypeFuel_initial_mem _ branch.2 (Nat.le_refl _))]
      exact hBranches branch hMem (buildRelationSet_initial branch.2 _ rfl)
    have hBranchMenu' : ∀ branch ∈ branches,
        ∃ indexed ∈ branchAutomata.zipIdx,
          computeFutureOf whole
            (childState (indexed.2 + 1) indexed.1.2.initial) =
            typeFutureOffers branch.2 := by
      intro branch hMem
      obtain ⟨index, hGetBranch⟩ := List.getElem?_of_mem hMem
      have hGetAuto : branchAutomata[index]? =
          some (branch.1, compileTypeFuel (typeCompilationFuel branch.2)
            branch.2) := by
        rw [hBranchAutomata, List.getElem?_map, hGetBranch]
        rfl
      refine ⟨((branch.1, compileTypeFuel (typeCompilationFuel branch.2)
        branch.2), index), List.mk_mem_zipIdx_iff_getElem?.mpr hGetAuto, ?_⟩
      rw [childState, computeFutureOf_exclusiveOffer_branch elseType branches
        whole hWhole index branch.1 branch.2 hGetBranch
        (hBranchFuel branch hMem) (hBranchDisjoint branch hMem)
        (by rw [hBranchAlphabet branch hMem, hWholeDef]; rfl)
        (stateProductInfo_xoffer_child_branch alphabet elseType branches index
          branch.1 branch.2 hGetBranch) _
        (compileTypeFuel_initial_mem _ branch.2 (Nat.le_refl _))]
      exact hBranches branch hMem (buildRelationSet_initial branch.2 _ rfl)
    ext offer
    rw [mem_foldl_offer_menu, Finset.mem_union, Finset.mem_biUnion,
      typeBranchActions, List.mem_toFinset, List.mem_map]
    simp only [exclusiveOfferEntries, Finset.mem_insert, List.mem_toFinset,
      List.mem_map]
    constructor
    · rintro (⟨branch, hMem, rfl⟩ | ⟨entry, hEntry, hIn⟩)
      · exact Or.inr ⟨branch, hMem, Or.inl rfl⟩
      · rcases hEntry with rfl | ⟨indexed, hIndexed, rfl⟩
        · rw [hElseMenu] at hIn
          exact Or.inl hIn
        · obtain ⟨branch, hMem, hMenu⟩ := hBranchMenu indexed hIndexed
          rw [hMenu] at hIn
          exact Or.inr ⟨branch, hMem, Or.inr hIn⟩
    · rintro (hElseIn | ⟨branch, hMem, rfl | hMenuIn⟩)
      · exact Or.inr ⟨childState 0 elseFragment.initial, Or.inl rfl,
          by rw [hElseMenu]; exact hElseIn⟩
      · exact Or.inl ⟨branch, hMem, rfl⟩
      · obtain ⟨indexed, hIndexed, hMenu⟩ := hBranchMenu' branch hMem
        exact Or.inr ⟨childState (indexed.2 + 1) indexed.1.2.initial,
          Or.inr ⟨indexed, hIndexed, rfl⟩, by rw [hMenu]; exact hMenuIn⟩
  · subst hState
    rw [computeFutureOf_exclusiveOffer_else elseType branches whole hWhole
      hElseFuel hElseDisjoint (by rw [hElseAlphabet, hWholeDef]; rfl)
      (stateProductInfo_xoffer_child_else alphabet elseType branches) q
      (relationMembership_state_mem elseType _ q hElseDisjoint hChild)]
    exact hElse hChild
  · subst hState
    have hMem : (action, branchType) ∈ branches := List.mem_of_getElem? hGet
    have hDisjoint : branchType.OfferBranchesDisjoint :=
      hBranchDisjoint (action, branchType) hMem
    rw [computeFutureOf_exclusiveOffer_branch elseType branches whole hWhole
      i action branchType hGet (hBranchFuel (action, branchType) hMem)
      hDisjoint (by rw [hBranchAlphabet (action, branchType) hMem, hWholeDef]; rfl)
      (stateProductInfo_xoffer_child_branch alphabet elseType branches i action
        branchType hGet) q
      (relationMembership_state_mem branchType _ q hDisjoint hChild)]
    exact hBranches (action, branchType) hMem hChild

/-- Menus agree at a conjunctive offer.  The root exposes the branch heads on
its own edges and reaches exactly the default entry and the entries of the
generated selected products. -/
theorem futureOffersAgree_offer (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hWholeDisjoint :
      (PactType.offer alphabet elseType branches).OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet = alphabet)
    (hSelAlphabet : ∀ selected ∈ branches,
      (parallelTypeBranchesSelecting alphabet selected branches).alphabet =
        alphabet)
    -- Needed only once the branch heads are declared; both menus are empty
    -- otherwise, by their shared gate.
    (hSelMenu : (∀ b ∈ branches, b.1 ∈ alphabet.actions) →
      ∀ selected ∈ branches,
      typeFutureOffers
          (parallelTypeBranchesSelecting alphabet selected branches) =
        branches.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅)
    (hElse : FutureOffersAgree elseType)
    (hSelected : ∀ selected ∈ branches,
      FutureOffersAgree
        (parallelTypeBranchesSelecting alphabet selected branches)) :
    FutureOffersAgree (.offer alphabet elseType branches) := by
  classical
  set whole : PactType := .offer alphabet elseType branches with hWholeDef
  have hWhole := compileTypeFuel_offer_eq alphabet elseType branches
  have hDisjointParts :
      elseType.OfferBranchesDisjoint ∧
        PactType.OfferBranchesDisjointBranches branches := by
    have hParts := hWholeDisjoint
    simp only [hWholeDef, PactType.OfferBranchesDisjoint] at hParts
    exact ⟨hParts.1, hParts.2.2⟩
  have hElseDisjoint : elseType.OfferBranchesDisjoint := hDisjointParts.1
  have hBranchDisjoint : ∀ branch ∈ branches,
      branch.2.OfferBranchesDisjoint := by
    intro branch hBranch
    exact offerBranchesDisjoint_of_mem_branch hDisjointParts.2 hBranch
  have hElseFuel :
      typeCompilationFuel elseType + 1 ≤ typeCompilationFuel whole := by
    simp only [hWholeDef, typeCompilationFuel]
    omega
  have hSelFuel : ∀ selected ∈ branches,
      typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet selected branches) + 1 ≤
        typeCompilationFuel whole := by
    intro selected _
    rw [typeCompilationFuel_parallelTypeBranchesSelecting]
    simp only [hWholeDef, typeCompilationFuel]
    omega
  intro residual state hRelated
  rcases relationMembership_offer_cases alphabet elseType branches
      hRelated with hRoot | ⟨q, hState, hChild⟩ |
      ⟨i, selected, q, hGet, hState, hChild⟩
  · injection hRoot with hResidual hStateEq
    subst hResidual
    subst hStateEq
    set selectedAutomata :=
      branches.map fun selected =>
        (selected.1,
          compileTypeFuel
            (typeCompilationFuel
              (parallelTypeBranchesSelecting alphabet selected branches))
            (parallelTypeBranchesSelecting alphabet selected branches))
      with hSelectedAutomata
    set elseFragment :=
      compileTypeFuel (typeCompilationFuel elseType) elseType with hElseFragment
    set pending : PendingAutomaton :=
      { states := (compileTypeFuel (typeCompilationFuel whole) whole).states
        edges := (compileTypeFuel (typeCompilationFuel whole) whole).edges }
      with hPending
    have hHeads : selectedAutomata.map Prod.fst = branches.map Prod.fst := by
      rw [hSelectedAutomata, List.map_map]
      rfl
    -- Both menus are gated on the same declaredness condition: if it fails,
    -- `typeFutureOffers` is empty by its own gate and the root has no outgoing
    -- edges, since all three root families carry the gate too.
    by_cases hGuard : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
    case neg =>
      -- The semantic menu is `∅` by its own gate, and the compiled root has no
      -- outgoing edge at all.
      have hSemantic : typeFutureOffers whole = ∅ := by
        rw [hWholeDef]
        simp only [typeFutureOffers, typeFutureOffersFuel, if_neg hGuard]
      rw [hSemantic]
      -- Every root family carries the gate, so the root has no outgoing edge;
      -- its same-cycle reach is itself and it publishes nothing.
      have hNoRootEdge : ∀ edge ∈ (compileTypeFuel (typeCompilationFuel whole)
          whole).edges, edge.source ≠ TypeAutomatonState.root := by
        intro edge hEdge hSource
        rw [hWhole] at hEdge
        simp only [buildSelectedConjunctiveOfferAutomaton,
          finishAutomatonFragment, childPendingEdges, Finset.mem_union,
          Finset.mem_image, Finset.mem_filter] at hEdge
        rcases hEdge with
          ((((hElseCopy | hIndexed) | hEnabled) | hWait) | hResolved)
        · obtain ⟨childEdge, -, hEq⟩ := hElseCopy
          rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
        · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
          rcases hIndexed with hEmpty | ⟨indexed, -, hIn⟩
          · exact absurd hEmpty (Finset.notMem_empty _)
          · rw [childPendingEdges, Finset.mem_image] at hIn
            obtain ⟨childEdge, -, hEq⟩ := hIn
            rw [← hEq] at hSource
            simp [childPendingEdge, childState] at hSource
        · rw [mem_foldl_union_iff] at hEnabled
          rcases hEnabled with hEmpty | ⟨indexed, -, hIn⟩
          · exact absurd hEmpty (Finset.notMem_empty _)
          · rw [Finset.mem_image] at hIn
            obtain ⟨environment, hEnv, -⟩ := hIn
            rw [Finset.mem_filter] at hEnv
            exact hGuard hEnv.2.2
        · obtain ⟨environment, hEnv, -⟩ := hWait
          exact hGuard hEnv.2.2.2.2
        · obtain ⟨environment, hEnv, -⟩ := hResolved
          exact hGuard hEnv.2.2.2.2
      -- With no root-sourced edge the root references nothing, so its
      -- same-cycle reach is itself and it publishes no offer.
      have hRefs : pending.referencedStates TypeAutomatonState.root = ∅ := by
        rw [hPending]
        simp only [PendingAutomaton.referencedStates]
        rw [Finset.filter_eq_empty_iff.mpr (fun edge hEdge => hNoRootEdge edge
          hEdge)]
        simp
      have hOffersEmpty : pending.offersAt TypeAutomatonState.root = ∅ := by
        rw [hPending]
        simp only [PendingAutomaton.offersAt]
        rw [Finset.filter_eq_empty_iff.mpr (fun edge hEdge => hNoRootEdge edge
          hEdge)]
        simp
      have hReach : pending.futureReachable TypeAutomatonState.root =
          {TypeAutomatonState.root} := by
        simp only [PendingAutomaton.futureReachable]
        generalize pending.states.card = k
        induction k with
        | zero => rfl
        | succ k ihk =>
            rw [PendingAutomaton.futureReachableAux]
            have hStep : PendingAutomaton.futureStep pending
                {TypeAutomatonState.root} = {TypeAutomatonState.root} := by
              simp only [PendingAutomaton.futureStep]
              rw [show ({TypeAutomatonState.root} : Finset TypeAutomatonState).biUnion
                  pending.referencedStates = ∅ by
                rw [Finset.singleton_biUnion]; exact hRefs]
              simp
            rw [hStep]
            exact ihk
      -- The menu unfolds to a union over `{root}` of `offersAt root`, which is
      -- empty, plus the product term, which is `none` at an offer root.
      obtain ⟨k, hk⟩ : ∃ k, typeCompilationFuel whole = k + 1 :=
        ⟨typeCompilationFuel whole - 1, by
          have := typeCompilationFuel_positive whole; omega⟩
      show computeFutureOf whole TypeAutomatonState.root = ∅
      unfold computeFutureOf
      rw [hk, computeFutureOfFuel]
      simp only [← hk, ← hPending]
      rw [FiniteMenuGraph.futureReachable_eq_singleton_of_referencedStates_eq_empty
        _ .root (by simp only [PendingAutomaton.withMenuDependencies, hRefs,
          compileTypeMenuLinksFuel_root, Finset.union_empty])]
      simp only [Finset.singleton_biUnion, hOffersEmpty]
      rw [show stateProductInfo whole TypeAutomatonState.root = none by
        simp only [hWholeDef]
        exact stateProductInfo_offer_root alphabet elseType branches]
      simp
    have hOffers : pending.offersAt TypeAutomatonState.root =
        typeBranchActions branches := by
      rw [hPending, hWhole]
      exact buildSelectedConjunctiveOfferAutomaton_offersAt_root alphabet
        branches elseFragment selectedAutomata hGuard
    have hDecomp := computeFutureOf_root_decomposition whole
      TypeAutomatonState.root
      (conjunctiveOfferEntries elseFragment selectedAutomata) pending hPending
      (referencesClosed_compileTypeFuel whole (typeCompilationFuel whole)
        (Nat.le_refl _) hWholeDisjoint)
      (by
        rw [hPending]
        show TypeAutomatonState.root ∈
          (compileTypeFuel (typeCompilationFuel whole) whole).states
        rw [hWhole]
        simp only [buildSelectedConjunctiveOfferAutomaton,
          finishAutomatonFragment]
        exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_singleton_self _)))
      (by
        rw [hPending, hWhole]
        exact buildSelectedConjunctiveOfferAutomaton_referencedStates_root_subset
          alphabet branches elseFragment selectedAutomata)
      (by
        rw [hPending, hWhole]
        exact
          buildSelectedConjunctiveOfferAutomaton_entries_subset_referencedStates_root
            alphabet branches elseFragment selectedAutomata hHeads hGuard)
      (by
        simp only [hWholeDef]
        exact stateProductInfo_offer_root alphabet elseType branches)
      (by
        intro action hIn
        rw [hOffers] at hIn
        simp only [typeBranchActions, List.mem_toFinset, List.mem_map] at hIn
        obtain ⟨branch, hMem, rfl⟩ := hIn
        simpa [hWholeDef, PactType.alphabet] using hGuard branch hMem)
    rw [hDecomp, hOffers, hWholeDef,
      typeFutureOffers_offer alphabet elseType branches hGuard]
    -- the default entry carries the default's menu
    have hElseMenu : computeFutureOf whole
        (childState 0 elseFragment.initial) = typeFutureOffers elseType := by
      rw [childState, computeFutureOf_selectedConjunctiveOffer_else elseType
        branches whole hWhole (by rw [hElseAlphabet, hWholeDef]; rfl)
        hElseFuel hElseDisjoint
        (stateProductInfo_offer_child_else alphabet elseType branches)
        elseFragment.initial
        (compileTypeFuel_initial_mem _ elseType (Nat.le_refl _))]
      exact hElse (buildRelationSet_initial elseType _ rfl)
    -- and each selected-product entry the branch fold's menu
    have hBranchMenu : ∀ indexed ∈ selectedAutomata.zipIdx,
        computeFutureOf whole
            (childState (indexed.2 + 1) indexed.1.2.initial) =
          branches.foldl (fun offers branch =>
            offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅ := by
      intro indexed hIndexed
      have hGetAuto : selectedAutomata[indexed.2]? = some indexed.1 := by
        rw [← List.mk_mem_zipIdx_iff_getElem?]
        simpa using hIndexed
      rw [hSelectedAutomata, List.getElem?_map, Option.map_eq_some_iff]
        at hGetAuto
      obtain ⟨branch, hGetBranch, hEq⟩ := hGetAuto
      have hMem : branch ∈ branches := List.mem_of_getElem? hGetBranch
      have hShape : indexed.1.2 =
          compileTypeFuel
            (typeCompilationFuel
              (parallelTypeBranchesSelecting alphabet branch branches))
            (parallelTypeBranchesSelecting alphabet branch branches) := by
        rw [← hEq]
      rw [hShape, childState, computeFutureOf_selectedConjunctiveOffer_branch
        elseType branches whole hWhole indexed.2 branch hGetBranch
        (hSelFuel branch hMem)
        (by rw [hSelAlphabet branch hMem, hWholeDef]; rfl) hBranchDisjoint
        (stateProductInfo_offer_child_branch alphabet elseType branches
          indexed.2 branch hGetBranch) _
        (compileTypeFuel_initial_mem _ _ (Nat.le_refl _))]
      rw [← hSelMenu hGuard branch hMem]
      exact hSelected branch hMem (buildRelationSet_initial _ _ rfl)
    have hBranchMenu' : ∀ branch ∈ branches,
        ∃ indexed ∈ selectedAutomata.zipIdx,
          computeFutureOf whole
              (childState (indexed.2 + 1) indexed.1.2.initial) =
            branches.foldl (fun offers branch =>
              offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅ := by
      intro branch hMem
      obtain ⟨index, hGetBranch⟩ := List.getElem?_of_mem hMem
      have hGetAuto : selectedAutomata[index]? =
          some (branch.1, compileTypeFuel
            (typeCompilationFuel
              (parallelTypeBranchesSelecting alphabet branch branches))
            (parallelTypeBranchesSelecting alphabet branch branches)) := by
        rw [hSelectedAutomata, List.getElem?_map, hGetBranch]
        rfl
      refine ⟨((branch.1, compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet branch branches))
        (parallelTypeBranchesSelecting alphabet branch branches)), index),
        List.mk_mem_zipIdx_iff_getElem?.mpr hGetAuto, ?_⟩
      rw [childState, computeFutureOf_selectedConjunctiveOffer_branch elseType
        branches whole hWhole index branch hGetBranch (hSelFuel branch hMem)
        (by rw [hSelAlphabet branch hMem, hWholeDef]; rfl) hBranchDisjoint
        (stateProductInfo_offer_child_branch alphabet elseType branches index
          branch hGetBranch) _
        (compileTypeFuel_initial_mem _ _ (Nat.le_refl _))]
      rw [← hSelMenu hGuard branch hMem]
      exact hSelected branch hMem (buildRelationSet_initial _ _ rfl)
    ext offer
    rw [mem_foldl_offer_menu, Finset.mem_union, Finset.mem_biUnion,
      typeBranchActions, List.mem_toFinset, List.mem_map]
    simp only [conjunctiveOfferEntries, Finset.mem_insert, List.mem_toFinset,
      List.mem_map]
    constructor
    · rintro (⟨branch, hMem, rfl⟩ | ⟨entry, hEntry, hIn⟩)
      · exact Or.inr ⟨branch, hMem, Or.inl rfl⟩
      · rcases hEntry with rfl | ⟨indexed, hIndexed, rfl⟩
        · rw [hElseMenu] at hIn
          exact Or.inl hIn
        · rw [hBranchMenu indexed hIndexed, mem_foldl_offer_menu] at hIn
          simp only [Finset.notMem_empty, false_or] at hIn
          exact Or.inr hIn
    · rintro (hElseIn | ⟨branch, hMem, rfl | hMenuIn⟩)
      · exact Or.inr ⟨childState 0 elseFragment.initial, Or.inl rfl,
          by rw [hElseMenu]; exact hElseIn⟩
      · exact Or.inl ⟨branch, hMem, rfl⟩
      · obtain ⟨indexed, hIndexed, hMenu⟩ := hBranchMenu' branch hMem
        refine Or.inr ⟨childState (indexed.2 + 1) indexed.1.2.initial,
          Or.inr ⟨indexed, hIndexed, rfl⟩, ?_⟩
        rw [hMenu, mem_foldl_offer_menu]
        exact Or.inr ⟨branch, hMem, Or.inr hMenuIn⟩
  · subst hState
    rw [computeFutureOf_selectedConjunctiveOffer_else elseType branches whole
      hWhole (by rw [hElseAlphabet, hWholeDef]; rfl) hElseFuel hElseDisjoint
      (stateProductInfo_offer_child_else alphabet elseType branches) q
      (relationMembership_state_mem elseType _ q hElseDisjoint hChild)]
    exact hElse hChild
  · subst hState
    have hMem : selected ∈ branches := List.mem_of_getElem? hGet
    rw [computeFutureOf_selectedConjunctiveOffer_branch elseType branches whole
      hWhole i selected hGet (hSelFuel selected hMem)
      (by rw [hSelAlphabet selected hMem, hWholeDef]; rfl) hBranchDisjoint
      (stateProductInfo_offer_child_branch alphabet elseType branches i
        selected hGet) q
      (relationMembership_state_mem _ _ q
        (parallelTypeBranchesSelecting_offerBranchesDisjoint selected branches
          hBranchDisjoint) hChild)]
    exact hSelected selected hMem hChild

/-! ### Conjunctive-offer automaton helpers

The conjunctive builder has the same five-family edge set and the same
accepting set as the exclusive one, so these mirror the
`buildExclusiveOfferAutomaton` family clause for clause.  The committing
family differs only in its decoration: it is silent with an empty current
offer, and its guard drops the future-resolution condition. -/

/-! ### Same-cycle completion at the compound fragments

`helper_h14_same_cycle_completion`'s proved constructor cases, restated with
the children's completion statements as hypotheses so that the simultaneous
induction supplies them. -/


end

end Pact
