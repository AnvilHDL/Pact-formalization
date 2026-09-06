import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.MarkerMenus
import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.Base
import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.ChoiceAndSequence
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.ExclusiveOffer
import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.Offers

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-- A faithful child copy preserves paths including optimistic menu links. -/
theorem compiledMenuMarkerPath_child (parent child : PactType) (index : Nat)
    (name : String) (hDisjoint : child.OfferBranchesDisjoint)
    (hStates : (compileTypeFuel (typeCompilationFuel child) child).states.image
      (childState index) ⊆ (compileTypeFuel (typeCompilationFuel parent) parent).states)
    (hOutgoing : ∀ q edge,
      (edge ∈ (compileTypeFuel (typeCompilationFuel parent) parent).edges ∧
        edge.source = childState index q) ↔
      ∃ original ∈ (compileTypeFuel (typeCompilationFuel child) child).edges,
        original.source = q ∧ edge = childPendingEdge index original)
    (hLinks : ∀ q,
      menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel parent) parent)
        (childState index q) =
      (menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel child) child)
        q).image (childState index))
    (q : TypeAutomatonState)
    (hq : q ∈ (compileTypeFuel (typeCompilationFuel child) child).states) :
    (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel parent) parent).futureReachable
        (childState index q),
      MarkerSource (compileTypeFuel (typeCompilationFuel parent) parent) name r) ↔
    ∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel child) child).futureReachable q,
      MarkerSource (compileTypeFuel (typeCompilationFuel child) child) name r := by
  have hReach := FiniteMenuGraph.futureReachable_eq_of_embedding
    (compiledMenuGraphFuel (typeCompilationFuel child) child)
    (compiledMenuGraphFuel (typeCompilationFuel parent) parent) (childState index)
    (fun source => by
      simp only [compiledMenuGraphFuel, Nat.min_self,
        PendingAutomaton.withMenuDependencies]
      have hStep := menuStep_of_outgoing_childPendingEdge _ _ index source
        (hOutgoing source)
      dsimp only [AutomatonFragment.toPending] at hStep
      rw [hStep, hLinks, Finset.image_union])
    (compiledMenuGraphFuel_referencesClosed _ child le_rfl hDisjoint) q hq
    (by
      change (compileTypeFuel (typeCompilationFuel child) child).states.card ≤
        (compileTypeFuel (typeCompilationFuel parent) parent).states.card
      calc
        _ = ((compileTypeFuel (typeCompilationFuel child) child).states.image
            (childState index)).card :=
          (Finset.card_image_of_injective _ (by
            intro a b h; simpa [childState] using h)).symm
        _ ≤ _ := Finset.card_le_card hStates)
  have hMarker : ∀ r,
      MarkerSource (compileTypeFuel (typeCompilationFuel parent) parent) name
        (childState index r) ↔
      MarkerSource (compileTypeFuel (typeCompilationFuel child) child) name r := by
    intro r
    constructor
    · rintro ⟨edge, hEdge, hSource, hLabel⟩
      obtain ⟨original, hOriginal, hOriginalSource, rfl⟩ :=
        (hOutgoing r edge).mp ⟨hEdge, hSource⟩
      exact ⟨original, hOriginal, hOriginalSource, hLabel⟩
    · rintro ⟨edge, hEdge, hSource, hLabel⟩
      obtain ⟨hMem, hSource⟩ := (hOutgoing r (childPendingEdge index edge)).mpr
        ⟨edge, hEdge, hSource, rfl⟩
      exact ⟨childPendingEdge index edge, hMem, hSource, hLabel⟩
  rw [hReach]
  simp only [Finset.mem_image, exists_exists_and_eq_and, hMarker]

/-- At a fresh root, every marker path continues from one of its entries. -/
theorem compiledMenuMarkerPath_root (ty : PactType) (name : String)
    (entries : Finset TypeAutomatonState) (hDisjoint : ty.OfferBranchesDisjoint)
    (hRoot : TypeAutomatonState.root ∈
      (compileTypeFuel (typeCompilationFuel ty) ty).states)
    (hNoMarker : ¬ MarkerSource (compileTypeFuel (typeCompilationFuel ty) ty)
      name .root)
    (hUpper : ({ states := (compileTypeFuel (typeCompilationFuel ty) ty).states, edges := (compileTypeFuel (typeCompilationFuel ty) ty).edges } :
        PendingAutomaton).menuStep .root ⊆ insert .root entries)
    (hEntries : entries ⊆
      ({ states := (compileTypeFuel (typeCompilationFuel ty) ty).states, edges := (compileTypeFuel (typeCompilationFuel ty) ty).edges } :
          PendingAutomaton).menuStep .root) :
    (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel ty) ty).futureReachable .root,
      MarkerSource (compileTypeFuel (typeCompilationFuel ty) ty) name r) ↔
    ∃ entry ∈ entries,
      ∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel ty) ty).futureReachable entry,
        MarkerSource (compileTypeFuel (typeCompilationFuel ty) ty) name r := by
  have hRefs : (compiledMenuGraphFuel (typeCompilationFuel ty) ty).referencedStates
      .root = ({ states := (compileTypeFuel (typeCompilationFuel ty) ty).states, edges := (compileTypeFuel (typeCompilationFuel ty) ty).edges } :
          PendingAutomaton).menuStep .root := by
    simp only [compiledMenuGraphFuel, Nat.min_self,
      PendingAutomaton.withMenuDependencies, compileTypeMenuLinksFuel_root,
      Finset.union_empty]
  rw [FiniteMenuGraph.futureReachable_eq_self_union_biUnion _ .root entries
    (compiledMenuGraphFuel_referencesClosed _ ty le_rfl hDisjoint) hRoot
    (by rw [hRefs]; exact hUpper) (by rw [hRefs]; exact hEntries)]
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
  constructor
  · rintro ⟨r, h | ⟨entry, he, hr⟩, hm⟩
    · exact (hNoMarker (h ▸ hm)).elim
    · exact ⟨entry, he, r, hr, hm⟩
  · rintro ⟨entry, he, r, hr, hm⟩
    exact ⟨r, Or.inr ⟨entry, he, hr⟩, hm⟩

/-- A root with no outgoing edge has no marker path. -/
theorem compiledMenuMarkerPath_root_of_no_outgoing (ty : PactType) (name : String)
    (hDisjoint : ty.OfferBranchesDisjoint)
    (hRoot : TypeAutomatonState.root ∈
      (compileTypeFuel (typeCompilationFuel ty) ty).states)
    (hNoMarker : ¬ MarkerSource (compileTypeFuel (typeCompilationFuel ty) ty)
      name .root)
    (hNoOutgoing : ∀ edge ∈
      (compileTypeFuel (typeCompilationFuel ty) ty).edges,
      edge.source ≠ TypeAutomatonState.root) :
    ¬ ∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel ty) ty).futureReachable
        .root,
      MarkerSource (compileTypeFuel (typeCompilationFuel ty) ty) name r := by
  have hReferences :
      ({ states := (compileTypeFuel (typeCompilationFuel ty) ty).states,
          edges := (compileTypeFuel (typeCompilationFuel ty) ty).edges } :
        PendingAutomaton).menuStep .root = ∅ := by
    simp only [PendingAutomaton.menuStep]
    rw [Finset.filter_eq_empty_iff.mpr (fun edge hEdge => hNoOutgoing edge hEdge)]
    simp
  have hPath := compiledMenuMarkerPath_root ty name ∅ hDisjoint hRoot hNoMarker
    (by rw [hReferences]; simp) (by simp)
  simpa using hPath

theorem compiledMenuMarkerPath_of_absent (ty : PactType) (name : String)
    (hTailRec : ty.TailRecursive) (hTail : ty.TailOccurrences name False)
    {rho : PactType} {q : TypeAutomatonState}
    (hRelated : relationMembership (buildRelationSet ty (compileType ty)) rho q) :
    (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel ty) ty).futureReachable q,
      MarkerSource (compileTypeFuel (typeCompilationFuel ty) ty) name r) ↔
    menuReachesVar name rho = true := by
  have hAbsent := compileTypeFuel_noMarkerFor name (typeCompilationFuel ty) ty hTail
  have hRho := relationMembership_tailOccurrences ty rho q name False
    hTailRec hTail hRelated
  rw [menuReachesVar_of_absent name rho hRho]
  constructor
  · rintro ⟨r, -, edge, hEdge, -, hLabel⟩
    exact (hAbsent edge hEdge hLabel).elim
  · intro h; cases h

theorem compiledMenuMarkerPath_skip (a : PactTypeAlphabet) (name : String)
    {rho : PactType} {q : TypeAutomatonState}
    (hRelated : relationMembership (buildRelationSet (.skip a) (compileType (.skip a)))
      rho q) :
    (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel (.skip a)) (.skip a)).futureReachable q,
      MarkerSource (compileTypeFuel (typeCompilationFuel (.skip a)) (.skip a)) name r) ↔
    menuReachesVar name rho = true :=
  compiledMenuMarkerPath_of_absent _ name (by simp [PactType.TailRecursive])
    (by simp [PactType.TailOccurrences]) hRelated

theorem compiledMenuMarkerPath_message (a : PactTypeAlphabet) (msg : MessageId)
    (dir : MessageDir) (name : String) {rho : PactType} {q : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet (.message a msg dir) (compileType (.message a msg dir))) rho q) :
    (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel (.message a msg dir))
        (.message a msg dir)).futureReachable q,
      MarkerSource (compileTypeFuel (typeCompilationFuel (.message a msg dir))
        (.message a msg dir)) name r) ↔ menuReachesVar name rho = true :=
  compiledMenuMarkerPath_of_absent _ name (by simp [PactType.TailRecursive])
    (by simp [PactType.TailOccurrences]) hRelated

theorem compiledMenuMarkerPath_tock (a : PactTypeAlphabet) (name : String)
    {rho : PactType} {q : TypeAutomatonState}
    (hRelated : relationMembership (buildRelationSet (.tock a) (compileType (.tock a)))
      rho q) :
    (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel (.tock a)) (.tock a)).futureReachable q,
      MarkerSource (compileTypeFuel (typeCompilationFuel (.tock a)) (.tock a)) name r) ↔
    menuReachesVar name rho = true :=
  compiledMenuMarkerPath_of_absent _ name (by simp [PactType.TailRecursive])
    (by simp [PactType.TailOccurrences]) hRelated

theorem compiledMenuMarkerPath_progress (a : PactTypeAlphabet) (pid : ProcId)
    (name : String) {rho : PactType} {q : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet (.progress a pid) (compileType (.progress a pid))) rho q) :
    (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel (.progress a pid))
        (.progress a pid)).futureReachable q,
      MarkerSource (compileTypeFuel (typeCompilationFuel (.progress a pid))
        (.progress a pid)) name r) ↔ menuReachesVar name rho = true :=
  compiledMenuMarkerPath_of_absent _ name (by simp [PactType.TailRecursive])
    (by simp [PactType.TailOccurrences]) hRelated

theorem compiledMenuMarkerPath_var (a : PactTypeAlphabet) (other name : String)
    {rho : PactType} {q : TypeAutomatonState}
    (hRelated : relationMembership (buildRelationSet (.var a other)
      (compileType (.var a other))) rho q) :
    (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel (.var a other))
        (.var a other)).futureReachable q,
      MarkerSource (compileTypeFuel (typeCompilationFuel (.var a other))
        (.var a other)) name r) ↔ menuReachesVar name rho = true := by
  by_cases hName : name = other
  · subst other
    have hMarker := (markerSource_iff_var_residual (.var a name) name
      (by simp [PactType.TailOccurrences]) hRelated).mpr
      ⟨a, (relationMembership_var_cases a name hRelated).1⟩
    rw [(relationMembership_var_cases a name hRelated).1, menuReachesVar_var]
    simp only [beq_self_eq_true, iff_true]
    exact ⟨q, FiniteMenuGraph.mem_futureReachable_self _ q, hMarker⟩
  · exact compiledMenuMarkerPath_of_absent _ name (by simp [PactType.TailRecursive])
      (by simp [PactType.TailOccurrences, Ne.symm hName]) hRelated

private theorem compiledMenuMarkerPath_binaryChoice (a : PactTypeAlphabet)
    (left right whole : PactType) (leftLabel rightLabel : TypeLabel) (name : String)
    (hCompile : compileTypeFuel (typeCompilationFuel whole) whole =
      buildChoiceAutomaton a (compileTypeFuel (typeCompilationFuel left) left)
        (compileTypeFuel (typeCompilationFuel right) right) leftLabel rightLabel)
    (hLeftLabel : leftLabel ≠ .tock) (hRightLabel : rightLabel ≠ .tock)
    (hWholeDisjoint : whole.OfferBranchesDisjoint)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hLinksLeft : ∀ q,
      menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel whole) whole)
        (.child 0 q) =
      (menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel left) left)
        q).image (.child 0))
    (hLinksRight : ∀ q,
      menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel whole) whole)
        (.child 1 q) =
      (menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel right) right)
        q).image (.child 1))
    (hSyntax : menuReachesVar name whole =
      (menuReachesVar name left || menuReachesVar name right))
    (hLeft : ∀ {rho q} (_ : relationMembership (buildRelationSet left (compileType left)) rho q),
      (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel left) left).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel left) left) name r) ↔
      menuReachesVar name rho = true)
    (hRight : ∀ {rho q} (_ : relationMembership (buildRelationSet right (compileType right)) rho q),
      (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel right) right).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel right) right) name r) ↔
      menuReachesVar name rho = true)
    {rho : PactType} {q : TypeAutomatonState}
    (hShape : binaryChoiceRelationShape whole left right (rho, q)) :
    (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel whole) whole).futureReachable q,
      MarkerSource (compileTypeFuel (typeCompilationFuel whole) whole) name r) ↔
    menuReachesVar name rho = true := by
  have hCopyLeft : ∀ q (hq : q ∈ (compileTypeFuel (typeCompilationFuel left) left).states),
      (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel whole) whole).futureReachable (.child 0 q),
        MarkerSource (compileTypeFuel (typeCompilationFuel whole) whole) name r) ↔
      ∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel left) left).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel left) left) name r := by
    intro q hq
    apply compiledMenuMarkerPath_child whole left 0 name hLeftDisjoint
    · rw [hCompile]
      intro r hr
      simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union]
      exact Or.inl (Or.inr hr)
    · intro q edge
      rw [hCompile]
      exact buildChoiceAutomaton_outgoing_left a _ _ leftLabel rightLabel q edge
    · exact hLinksLeft
    · exact hq
  have hCopyRight : ∀ q (hq : q ∈ (compileTypeFuel (typeCompilationFuel right) right).states),
      (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel whole) whole).futureReachable (.child 1 q),
        MarkerSource (compileTypeFuel (typeCompilationFuel whole) whole) name r) ↔
      ∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel right) right).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel right) right) name r := by
    intro q hq
    apply compiledMenuMarkerPath_child whole right 1 name hRightDisjoint
    · rw [hCompile]
      intro r hr
      simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union]
      exact Or.inr hr
    · intro q edge
      rw [hCompile]
      exact buildChoiceAutomaton_outgoing_right a _ _ leftLabel rightLabel q edge
    · exact hLinksRight
    · exact hq
  rcases hShape with hRoot | ⟨state, rfl, hRelated⟩ | ⟨state, rfl, hRelated⟩
  · cases hRoot
    have hRefs := buildChoiceAutomaton_menuStep_root a
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right) leftLabel rightLabel
      hLeftLabel hRightLabel
      ⟨TypeEnvironment.empty, empty_mem_localEnvironments a, rfl⟩
    rw [compiledMenuMarkerPath_root whole name
      {childState 0 (compileTypeFuel (typeCompilationFuel left) left).initial,
        childState 1 (compileTypeFuel (typeCompilationFuel right) right).initial}
      hWholeDisjoint
      (by rw [hCompile]; simp [buildChoiceAutomaton, finishAutomatonFragment])
      (by rw [hCompile]; exact buildChoiceAutomaton_markerSource_root a _ _ _ _ name)
      (by rw [hCompile, hRefs]; exact Finset.subset_insert _ _)
      (by rw [hCompile, hRefs])]
    simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left,
      childState]
    have hLeftEntry := hLeft (buildRelationSet_initial left _ rfl)
    have hRightEntry := hRight (buildRelationSet_initial right _ rfl)
    simp only [compileType] at hLeftEntry hRightEntry
    rw [hCopyLeft _ (compileTypeFuel_initial_mem _ left le_rfl),
      hCopyRight _ (compileTypeFuel_initial_mem _ right le_rfl),
      hLeftEntry, hRightEntry, hSyntax, Bool.or_eq_true]
  · exact (hCopyLeft state (relationMembership_state_mem left rho state
      hLeftDisjoint hRelated)).trans (hLeft hRelated)
  · exact (hCopyRight state (relationMembership_state_mem right rho state
      hRightDisjoint hRelated)).trans (hRight hRelated)

theorem compiledMenuMarkerPath_choice (a : PactTypeAlphabet) (left right : PactType)
    (name : String) {bound : List String}
    (hWF : TypeWellFormedIn bound (.choice a left right))
    (hLeft : ∀ {rho q} (_ : relationMembership (buildRelationSet left (compileType left)) rho q),
      (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel left) left).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel left) left) name r) ↔
      menuReachesVar name rho = true)
    (hRight : ∀ {rho q} (_ : relationMembership (buildRelationSet right (compileType right)) rho q),
      (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel right) right).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel right) right) name r) ↔
      menuReachesVar name rho = true)
    {rho : PactType} {q : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet (.choice a left right) (compileType (.choice a left right))) rho q) :
    (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel (.choice a left right))
        (.choice a left right)).futureReachable q,
      MarkerSource (compileTypeFuel (typeCompilationFuel (.choice a left right))
        (.choice a left right)) name r) ↔ menuReachesVar name rho = true := by
  obtain ⟨hL, hR⟩ := typeWellFormedIn_choice hWF
  exact compiledMenuMarkerPath_binaryChoice a left right (.choice a left right)
    .silent .silent name (compileTypeFuel_choice_eq a left right)
    (by simp [TypeLabel.silent]) (by simp [TypeLabel.silent])
    (offerBranchesDisjoint_of_wellFormedIn hWF)
    (offerBranchesDisjoint_of_wellFormedIn hL)
    (offerBranchesDisjoint_of_wellFormedIn hR)
    (menuDependencyTargets_choice_left a left right)
    (menuDependencyTargets_choice_right a left right)
    (menuReachesVar_choice name a left right (hL.2.2.2.1 name) (hR.2.2.2.1 name))
    hLeft hRight (relationMembership_choice_cases a left right hRelated)

theorem compiledMenuMarkerPath_fairChoice (a : PactTypeAlphabet) (bid : BranchId)
    (left right : PactType) (name : String) {bound : List String}
    (hWF : TypeWellFormedIn bound (.fairChoice a bid left right))
    (hLeft : ∀ {rho q} (_ : relationMembership (buildRelationSet left (compileType left)) rho q),
      (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel left) left).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel left) left) name r) ↔
      menuReachesVar name rho = true)
    (hRight : ∀ {rho q} (_ : relationMembership (buildRelationSet right (compileType right)) rho q),
      (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel right) right).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel right) right) name r) ↔
      menuReachesVar name rho = true)
    {rho : PactType} {q : TypeAutomatonState}
    (hRelated : relationMembership (buildRelationSet (.fairChoice a bid left right)
      (compileType (.fairChoice a bid left right))) rho q) :
    (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel (.fairChoice a bid left right))
        (.fairChoice a bid left right)).futureReachable q,
      MarkerSource (compileTypeFuel (typeCompilationFuel (.fairChoice a bid left right))
        (.fairChoice a bid left right)) name r) ↔ menuReachesVar name rho = true := by
  obtain ⟨hL, hR⟩ := typeWellFormedIn_fairChoice hWF
  exact compiledMenuMarkerPath_binaryChoice a left right (.fairChoice a bid left right)
    (.fair bid true) (.fair bid false) name (compileTypeFuel_fairChoice_eq a bid left right)
    (by simp [TypeLabel.fair]) (by simp [TypeLabel.fair])
    (offerBranchesDisjoint_of_wellFormedIn hWF)
    (offerBranchesDisjoint_of_wellFormedIn hL)
    (offerBranchesDisjoint_of_wellFormedIn hR)
    (menuDependencyTargets_fairChoice_left a bid left right)
    (menuDependencyTargets_fairChoice_right a bid left right)
    (menuReachesVar_fairChoice name a bid left right
      (hL.2.2.2.1 name) (hR.2.2.2.1 name))
    hLeft hRight (relationMembership_fairChoice_cases a bid left right hRelated)

theorem compiledMenuMarkerPath_xoffer (a : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (name : String) {bound : List String}
    (hWF : TypeWellFormedIn bound (.xoffer a elseType branches))
    (hElse : ∀ {rho q}
      (_ : relationMembership (buildRelationSet elseType (compileType elseType)) rho q),
      (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel elseType) elseType).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel elseType) elseType) name r) ↔
      menuReachesVar name rho = true)
    (hBranches : ∀ branch ∈ branches, ∀ {rho q}
      (_ : relationMembership (buildRelationSet branch.2 (compileType branch.2)) rho q),
      (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel branch.2)
          branch.2).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel branch.2) branch.2) name r) ↔
      menuReachesVar name rho = true)
    {rho : PactType} {q : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet (.xoffer a elseType branches)
        (compileType (.xoffer a elseType branches))) rho q) :
    (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel (.xoffer a elseType branches))
        (.xoffer a elseType branches)).futureReachable q,
      MarkerSource (compileTypeFuel (typeCompilationFuel (.xoffer a elseType branches))
        (.xoffer a elseType branches)) name r) ↔ menuReachesVar name rho = true := by
  let whole : PactType := .xoffer a elseType branches
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2)
  have hCompile := compileTypeFuel_xoffer_eq a elseType branches
  obtain ⟨hElseWF, hBranchWF⟩ := typeWellFormedIn_xoffer hWF
  have hWholeDisjoint := offerBranchesDisjoint_of_wellFormedIn hWF
  have hElseDisjoint := offerBranchesDisjoint_of_wellFormedIn hElseWF
  have hBranchDisjoint : ∀ branch ∈ branches, branch.2.OfferBranchesDisjoint := by
    intro branch hBranch
    exact offerBranchesDisjoint_of_wellFormedIn (hBranchWF branch hBranch)
  have hCopyElse : ∀ state
      (hState : state ∈ (compileTypeFuel (typeCompilationFuel elseType) elseType).states),
      (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel whole) whole).futureReachable
          (.child 0 state),
        MarkerSource (compileTypeFuel (typeCompilationFuel whole) whole) name r) ↔
      ∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel elseType)
          elseType).futureReachable state,
        MarkerSource (compileTypeFuel (typeCompilationFuel elseType) elseType) name r := by
    intro state hState
    apply compiledMenuMarkerPath_child whole elseType 0 name hElseDisjoint
    · rw [show whole = .xoffer a elseType branches by rfl, hCompile]
      intro tagged hTagged
      simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      exact Or.inl (Or.inr hTagged)
    · intro source edge
      rw [show whole = .xoffer a elseType branches by rfl, hCompile]
      exact buildExclusiveOfferAutomaton_outgoing_else a branches _ _ source edge
    · intro source
      exact menuDependencyTargets_xoffer_else a elseType branches source
    · exact hState
  have hCopyBranch : ∀ index action branchType
      (hGet : branches[index]? = some (action, branchType)) state
      (hState : state ∈
        (compileTypeFuel (typeCompilationFuel branchType) branchType).states),
      (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel whole) whole).futureReachable
          (.child (index + 1) state),
        MarkerSource (compileTypeFuel (typeCompilationFuel whole) whole) name r) ↔
      ∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel branchType)
          branchType).futureReachable state,
        MarkerSource (compileTypeFuel (typeCompilationFuel branchType) branchType) name r := by
    intro index action branchType hGet state hState
    have hAutomatonGet : branchAutomata[index]? = some
        (action, compileTypeFuel (typeCompilationFuel branchType) branchType) := by
      simp [branchAutomata, List.getElem?_map, hGet]
    apply compiledMenuMarkerPath_child whole branchType (index + 1) name
      (hBranchDisjoint (action, branchType) (List.mem_of_getElem? hGet))
    · rw [show whole = .xoffer a elseType branches by rfl, hCompile]
      intro tagged hTagged
      simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      apply Or.inr
      rw [indexedFragmentStates, mem_foldl_union_iff]
      exact Or.inr ⟨((action,
        compileTypeFuel (typeCompilationFuel branchType) branchType), index),
        List.mk_mem_zipIdx_iff_getElem?.mpr hAutomatonGet, hTagged⟩
    · intro source edge
      rw [show whole = .xoffer a elseType branches by rfl, hCompile]
      exact buildExclusiveOfferAutomaton_outgoing_branch a branches _ _ index action _
        hAutomatonGet source edge
    · intro source
      exact menuDependencyTargets_xoffer_branch a elseType branches index action branchType
        hGet source
    · exact hState
  rcases relationMembership_xoffer_cases a elseType branches hRelated with
    hRoot | ⟨state, hState, hChild⟩ |
      ⟨index, action, branchType, state, hGet, hState, hChild⟩
  · injection hRoot with hResidual hStateEq
    subst hResidual
    subst hStateEq
    have hWholeTail := hWF.2.2.2.1 name
    simp only [PactType.TailOccurrences] at hWholeTail
    rw [menuReachesVar_xoffer name a elseType branches
      (hElseWF.2.2.2.1 name) hWholeTail.2]
    by_cases hGuard : ∀ branch ∈ branches, branch.1 ∈ a.actions
    · simp only [if_pos hGuard]
      have hHeads : branchAutomata.map Prod.fst = branches.map Prod.fst := by
        simp [branchAutomata, List.map_map]
      have hRootPath := compiledMenuMarkerPath_root whole name
        (exclusiveOfferEntries
          (compileTypeFuel (typeCompilationFuel elseType) elseType) branchAutomata)
        hWholeDisjoint
        (by rw [show whole = .xoffer a elseType branches by rfl, hCompile]
            simp [buildExclusiveOfferAutomaton, finishAutomatonFragment])
        (by rw [show whole = .xoffer a elseType branches by rfl, hCompile]
            exact buildExclusiveOfferAutomaton_markerSource_root a branches _ _ name)
        (by rw [show whole = .xoffer a elseType branches by rfl, hCompile]
            exact buildExclusiveOfferAutomaton_menuStep_root_subset a branches _ _)
        (by rw [show whole = .xoffer a elseType branches by rfl, hCompile]
            exact buildExclusiveOfferAutomaton_entries_subset_menuStep_root
              a branches _ _ hHeads hGuard)
      rw [hRootPath]
      constructor
      · rintro ⟨entry, hEntry, reached, hReach, hMarker⟩
        simp only [exclusiveOfferEntries, Finset.mem_insert, List.mem_toFinset,
          List.mem_map] at hEntry
        rcases hEntry with rfl | ⟨indexed, hIndexed, rfl⟩
        · rw [Bool.or_eq_true]
          apply Or.inl
          apply (hElse (buildRelationSet_initial elseType _ rfl)).mp
          apply (hCopyElse _ (compileTypeFuel_initial_mem _ elseType le_rfl)).mp
          exact ⟨reached, hReach, hMarker⟩
        · rcases indexed with ⟨entry, index⟩
          have hGetAuto : branchAutomata[index]? = some entry :=
            List.mk_mem_zipIdx_iff_getElem?.mp hIndexed
          simp only [branchAutomata, List.getElem?_map,
            Option.map_eq_some_iff] at hGetAuto
          obtain ⟨branch, hGet, rfl⟩ := hGetAuto
          have hMem : branch ∈ branches := List.mem_of_getElem? hGet
          rw [Bool.or_eq_true]
          apply Or.inr
          rw [List.any_eq_true]
          refine ⟨branch, hMem, ?_⟩
          apply (hBranches branch hMem
            (buildRelationSet_initial branch.2 _ rfl)).mp
          apply (hCopyBranch index branch.1 branch.2 hGet _
            (compileTypeFuel_initial_mem _ branch.2 le_rfl)).mp
          exact ⟨reached, hReach, hMarker⟩
      · intro hSyntax
        rw [Bool.or_eq_true] at hSyntax
        rcases hSyntax with hElseTest | hBranchTest
        · refine ⟨childState 0
              (compileTypeFuel (typeCompilationFuel elseType) elseType).initial,
            Finset.mem_insert_self _ _, ?_⟩
          apply (hCopyElse _ (compileTypeFuel_initial_mem _ elseType le_rfl)).mpr
          apply (hElse (buildRelationSet_initial elseType _ rfl)).mpr
          exact hElseTest
        · rw [List.any_eq_true] at hBranchTest
          obtain ⟨branch, hMem, hBranchTest⟩ := hBranchTest
          obtain ⟨index, hGet⟩ := List.getElem?_of_mem hMem
          have hAutomatonGet : branchAutomata[index]? = some
              (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2) := by
            simp [branchAutomata, List.getElem?_map, hGet]
          refine ⟨.child (index + 1)
                (compileTypeFuel (typeCompilationFuel branch.2) branch.2).initial,
            ?_, ?_⟩
          · simp only [exclusiveOfferEntries, Finset.mem_insert,
              List.mem_toFinset, List.mem_map]
            exact Or.inr ⟨((branch.1,
              compileTypeFuel (typeCompilationFuel branch.2) branch.2), index),
              List.mk_mem_zipIdx_iff_getElem?.mpr hAutomatonGet, rfl⟩
          · apply (hCopyBranch index branch.1 branch.2 hGet _
              (compileTypeFuel_initial_mem _ branch.2 le_rfl)).mpr
            apply (hBranches branch hMem
              (buildRelationSet_initial branch.2 _ rfl)).mpr
            exact hBranchTest
    · simp only [if_neg hGuard, Bool.false_eq_true, iff_false]
      apply compiledMenuMarkerPath_root_of_no_outgoing whole name hWholeDisjoint
      · rw [show whole = .xoffer a elseType branches by rfl, hCompile]
        simp [buildExclusiveOfferAutomaton, finishAutomatonFragment]
      · rw [show whole = .xoffer a elseType branches by rfl, hCompile]
        exact buildExclusiveOfferAutomaton_markerSource_root a branches _ _ name
      · intro edge hEdge hSource
        rw [show whole = .xoffer a elseType branches by rfl, hCompile] at hEdge
        simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
          childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
        rcases hEdge with ((((hElseEdge | hIndexed) | hBranch) | hWait) | hResolved)
        · obtain ⟨childEdge, -, rfl⟩ := hElseEdge
          simp [childPendingEdge, childState] at hSource
        · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
          rcases hIndexed with hEmpty | ⟨indexed, -, hChild⟩
          · simp at hEmpty
          · obtain ⟨childEdge, -, rfl⟩ := Finset.mem_image.mp hChild
            simp [childPendingEdge, childState] at hSource
        · rw [mem_foldl_union_iff] at hBranch
          rcases hBranch with hEmpty | ⟨indexed, -, hEnabled⟩
          · simp at hEmpty
          · simp only [Finset.mem_image, Finset.mem_filter] at hEnabled
            obtain ⟨environment, hEnvironment, rfl⟩ := hEnabled
            exact hGuard hEnvironment.2.2.2
        · obtain ⟨environment, hEnvironment, rfl⟩ := hWait
          rw [Finset.mem_filter] at hEnvironment
          exact hGuard hEnvironment.2.2.2
        · obtain ⟨environment, hEnvironment, rfl⟩ := hResolved
          rw [Finset.mem_filter] at hEnvironment
          exact hGuard hEnvironment.2.2.2.2
  · subst hState
    exact (hCopyElse state (relationMembership_state_mem elseType rho state
      hElseDisjoint hChild)).trans (hElse hChild)
  · subst hState
    have hMem : (action, branchType) ∈ branches := List.mem_of_getElem? hGet
    exact (hCopyBranch index action branchType hGet state
      (relationMembership_state_mem branchType rho state
        (hBranchDisjoint (action, branchType) hMem) hChild)).trans
      (hBranches (action, branchType) hMem hChild)

theorem compiledMenuMarkerPath_offer (a : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (name : String) {bound : List String}
    (hWF : TypeWellFormedIn bound (.offer a elseType branches))
    (hElse : ∀ {rho q}
      (_ : relationMembership (buildRelationSet elseType (compileType elseType)) rho q),
      (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel elseType) elseType).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel elseType) elseType) name r) ↔
      menuReachesVar name rho = true)
    {rho : PactType} {q : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet (.offer a elseType branches)
        (compileType (.offer a elseType branches))) rho q) :
    (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel (.offer a elseType branches))
        (.offer a elseType branches)).futureReachable q,
      MarkerSource (compileTypeFuel (typeCompilationFuel (.offer a elseType branches))
        (.offer a elseType branches)) name r) ↔ menuReachesVar name rho = true := by
  let whole : PactType := .offer a elseType branches
  let selectedAutomata := branches.map fun selected =>
    (selected.1, compileTypeFuel
      (typeCompilationFuel (parallelTypeBranchesSelecting a selected branches))
      (parallelTypeBranchesSelecting a selected branches))
  have hCompile := compileTypeFuel_offer_eq a elseType branches
  obtain ⟨hElseWF, hSelectedWF⟩ := typeWellFormedIn_offer hWF
  have hWholeTail := hWF.2.2.2.1 name
  simp only [PactType.TailOccurrences] at hWholeTail
  have hBranchTail : ∀ branch ∈ branches,
      branch.2.TailOccurrences name False :=
    tailBranchOccurrences_forall name False branches hWholeTail.2
  have hWholeDisjoint := offerBranchesDisjoint_of_wellFormedIn hWF
  have hElseDisjoint := offerBranchesDisjoint_of_wellFormedIn hElseWF
  have hSelectedDisjoint : ∀ selected ∈ branches,
      (parallelTypeBranchesSelecting a selected branches).OfferBranchesDisjoint := by
    intro selected hSelected
    exact offerBranchesDisjoint_of_wellFormedIn (hSelectedWF selected hSelected)
  have hSelectedTail : ∀ selected ∈ branches,
      (parallelTypeBranchesSelecting a selected branches).TailOccurrences name False := by
    intro selected hSelected
    exact parallelTypeBranchesSelecting_tailOccurrences name a selected branches False
      hBranchTail (hBranchTail selected hSelected)
  have hCopyElse : ∀ state
      (hState : state ∈ (compileTypeFuel (typeCompilationFuel elseType) elseType).states),
      (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel whole) whole).futureReachable
          (.child 0 state),
        MarkerSource (compileTypeFuel (typeCompilationFuel whole) whole) name r) ↔
      ∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel elseType)
          elseType).futureReachable state,
        MarkerSource (compileTypeFuel (typeCompilationFuel elseType) elseType) name r := by
    intro state hState
    apply compiledMenuMarkerPath_child whole elseType 0 name hElseDisjoint
    · rw [show whole = .offer a elseType branches by rfl, hCompile]
      intro tagged hTagged
      simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      exact Or.inl (Or.inr hTagged)
    · intro source edge
      rw [show whole = .offer a elseType branches by rfl, hCompile]
      exact buildSelectedConjunctiveOfferAutomaton_outgoing_else
        a branches _ _ source edge
    · intro source
      exact menuDependencyTargets_offer_else a elseType branches source
    · exact hState
  have hCopySelected : ∀ index selected
      (hGet : branches[index]? = some selected) state
      (hState : state ∈ (compileTypeFuel
        (typeCompilationFuel (parallelTypeBranchesSelecting a selected branches))
        (parallelTypeBranchesSelecting a selected branches)).states),
      (∃ r ∈ (compiledMenuGraphFuel (typeCompilationFuel whole) whole).futureReachable
          (.child (index + 1) state),
        MarkerSource (compileTypeFuel (typeCompilationFuel whole) whole) name r) ↔
      ∃ r ∈ (compiledMenuGraphFuel
          (typeCompilationFuel (parallelTypeBranchesSelecting a selected branches))
          (parallelTypeBranchesSelecting a selected branches)).futureReachable state,
        MarkerSource (compileTypeFuel
          (typeCompilationFuel (parallelTypeBranchesSelecting a selected branches))
          (parallelTypeBranchesSelecting a selected branches)) name r := by
    intro index selected hGet state hState
    have hAutomatonGet : selectedAutomata[index]? = some
        (selected.1, compileTypeFuel
          (typeCompilationFuel (parallelTypeBranchesSelecting a selected branches))
          (parallelTypeBranchesSelecting a selected branches)) := by
      simp [selectedAutomata, List.getElem?_map, hGet]
    apply compiledMenuMarkerPath_child whole
      (parallelTypeBranchesSelecting a selected branches) (index + 1) name
      (hSelectedDisjoint selected (List.mem_of_getElem? hGet))
    · rw [show whole = .offer a elseType branches by rfl, hCompile]
      intro tagged hTagged
      simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      apply Or.inr
      rw [indexedFragmentStates, mem_foldl_union_iff]
      exact Or.inr ⟨((selected.1, compileTypeFuel
          (typeCompilationFuel (parallelTypeBranchesSelecting a selected branches))
          (parallelTypeBranchesSelecting a selected branches)), index),
        List.mk_mem_zipIdx_iff_getElem?.mpr hAutomatonGet, hTagged⟩
    · intro source edge
      rw [show whole = .offer a elseType branches by rfl, hCompile]
      exact buildSelectedConjunctiveOfferAutomaton_outgoing_branch a branches _ _
        index selected.1 _ hAutomatonGet source edge
    · intro source
      rcases selected with ⟨action, branchType⟩
      exact menuDependencyTargets_offer_branch a elseType branches index action
        branchType hGet source
    · exact hState
  rcases relationMembership_offer_cases a elseType branches hRelated with
    hRoot | ⟨state, hState, hChild⟩ |
      ⟨index, selected, state, hGet, hState, hChild⟩
  · injection hRoot with hResidual hStateEq
    subst hResidual
    subst hStateEq
    rw [menuReachesVar_offer name a elseType branches
      (hElseWF.2.2.2.1 name) hWholeTail.2]
    by_cases hGuard : ∀ branch ∈ branches, branch.1 ∈ a.actions
    · simp only [if_pos hGuard]
      have hHeads : selectedAutomata.map Prod.fst = branches.map Prod.fst := by
        simp [selectedAutomata, List.map_map]
      have hRootPath := compiledMenuMarkerPath_root whole name
        (conjunctiveOfferEntries
          (compileTypeFuel (typeCompilationFuel elseType) elseType) selectedAutomata)
        hWholeDisjoint
        (by rw [show whole = .offer a elseType branches by rfl, hCompile]
            simp [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment])
        (by rw [show whole = .offer a elseType branches by rfl, hCompile]
            exact buildSelectedConjunctiveOfferAutomaton_markerSource_root
              a branches _ _ name)
        (by rw [show whole = .offer a elseType branches by rfl, hCompile]
            exact buildSelectedConjunctiveOfferAutomaton_menuStep_root_subset
              a branches _ _)
        (by rw [show whole = .offer a elseType branches by rfl, hCompile]
            exact
              buildSelectedConjunctiveOfferAutomaton_entries_subset_menuStep_root
                a branches _ _ hHeads hGuard)
      rw [hRootPath]
      constructor
      · rintro ⟨entry, hEntry, reached, hReach, hMarker⟩
        simp only [conjunctiveOfferEntries, Finset.mem_insert, List.mem_toFinset,
          List.mem_map] at hEntry
        rcases hEntry with rfl | ⟨indexed, hIndexed, rfl⟩
        · apply (hElse (buildRelationSet_initial elseType _ rfl)).mp
          apply (hCopyElse _ (compileTypeFuel_initial_mem _ elseType le_rfl)).mp
          exact ⟨reached, hReach, hMarker⟩
        · rcases indexed with ⟨entry, index⟩
          have hGetAuto : selectedAutomata[index]? = some entry :=
            List.mk_mem_zipIdx_iff_getElem?.mp hIndexed
          simp only [selectedAutomata, List.getElem?_map,
            Option.map_eq_some_iff] at hGetAuto
          obtain ⟨selected, hGet, rfl⟩ := hGetAuto
          have hMem : selected ∈ branches := List.mem_of_getElem? hGet
          have hSelectedPath := (hCopySelected index selected hGet _
            (compileTypeFuel_initial_mem _
              (parallelTypeBranchesSelecting a selected branches) le_rfl)).mp
            ⟨reached, hReach, hMarker⟩
          have hNoPath := compiledMenuMarkerPath_of_absent
            (parallelTypeBranchesSelecting a selected branches) name
            (hSelectedWF selected hMem).2.2.2.2.2.1
            (hSelectedTail selected hMem)
            (buildRelationSet_initial
              (parallelTypeBranchesSelecting a selected branches) _ rfl)
          have hFalse := hNoPath.mp hSelectedPath
          rw [menuReachesVar_of_absent name _ (hSelectedTail selected hMem)] at hFalse
          cases hFalse
      · intro hElseTest
        refine ⟨childState 0
            (compileTypeFuel (typeCompilationFuel elseType) elseType).initial,
          Finset.mem_insert_self _ _, ?_⟩
        apply (hCopyElse _ (compileTypeFuel_initial_mem _ elseType le_rfl)).mpr
        apply (hElse (buildRelationSet_initial elseType _ rfl)).mpr
        exact hElseTest
    · simp only [if_neg hGuard, Bool.false_eq_true, iff_false]
      apply compiledMenuMarkerPath_root_of_no_outgoing whole name hWholeDisjoint
      · rw [show whole = .offer a elseType branches by rfl, hCompile]
        simp [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment]
      · rw [show whole = .offer a elseType branches by rfl, hCompile]
        exact buildSelectedConjunctiveOfferAutomaton_markerSource_root
          a branches _ _ name
      · intro edge hEdge hSource
        rw [show whole = .offer a elseType branches by rfl, hCompile] at hEdge
        simp only [buildSelectedConjunctiveOfferAutomaton,
          finishAutomatonFragment, childPendingEdges, Finset.mem_union,
          Finset.mem_image, Finset.mem_filter] at hEdge
        rcases hEdge with
          ((((hElseEdge | hIndexed) | hEnabled) | hWait) | hResolved)
        · obtain ⟨childEdge, -, rfl⟩ := hElseEdge
          simp [childPendingEdge, childState] at hSource
        · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
          rcases hIndexed with hEmpty | ⟨indexed, -, hChild⟩
          · simp at hEmpty
          · obtain ⟨childEdge, -, rfl⟩ := Finset.mem_image.mp hChild
            simp [childPendingEdge, childState] at hSource
        · rw [mem_foldl_union_iff] at hEnabled
          rcases hEnabled with hEmpty | ⟨indexed, -, hEntry⟩
          · simp at hEmpty
          · rw [Finset.mem_image] at hEntry
            obtain ⟨environment, hEnvironment, rfl⟩ := hEntry
            rw [Finset.mem_filter] at hEnvironment
            exact hGuard hEnvironment.2.2
        · obtain ⟨environment, hEnvironment, rfl⟩ := hWait
          exact hGuard hEnvironment.2.2.2.2
        · obtain ⟨environment, hEnvironment, rfl⟩ := hResolved
          exact hGuard hEnvironment.2.2.2.2
  · subst hState
    exact (hCopyElse state (relationMembership_state_mem elseType rho state
      hElseDisjoint hChild)).trans (hElse hChild)
  · subst hState
    have hMem : selected ∈ branches := List.mem_of_getElem? hGet
    have hSelectedWF' := hSelectedWF selected hMem
    exact (hCopySelected index selected hGet state
      (relationMembership_state_mem
        (parallelTypeBranchesSelecting a selected branches) rho state
        (hSelectedDisjoint selected hMem) hChild)).trans
      (compiledMenuMarkerPath_of_absent
        (parallelTypeBranchesSelecting a selected branches) name
        hSelectedWF'.2.2.2.2.2.1 (hSelectedTail selected hMem) hChild)

end
end Pact
