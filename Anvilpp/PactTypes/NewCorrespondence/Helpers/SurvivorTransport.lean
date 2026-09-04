import Anvilpp.PactTypes.NewCorrespondence.Helpers.TypeWellFormedIn

/-!
Transport of a related residual along re-signing: for every state related to a
residual of a type, the re-signed type relates the same state to a
live-equivalent residual.  `SurvivorTransport` names the obligation and one
lemma per constructor discharges it from the corresponding component
obligations.
-/

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

namespace PactTypeAlphabet

/-- Projecting a child twice keeps only the outer alphabet, provided the
intermediate one declares no interface action. -/
theorem projectParallel_reannotate
    {child source target : PactTypeAlphabet} {interface : Interface}
    (hSourceHidden : ∀ action ∈ source.actions, action.1 ∉ interface) :
    projectParallel target (projectParallel source child interface) interface =
      projectParallel target child interface := by
  refine congrArg PactTypeAlphabet.mk (Finset.ext fun action => ?_)
  simp only [projectParallel, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨(⟨hChild, _⟩ | hSource), hIface⟩ | hOuter)
    · exact Or.inl ⟨hChild, hIface⟩
    · exact absurd hIface (hSourceHidden action hSource)
    · exact Or.inr hOuter
  · rintro (⟨hChild, hIface⟩ | hOuter)
    · exact Or.inl ⟨Or.inl ⟨hChild, hIface⟩, hIface⟩
    · exact Or.inr hOuter

end PactTypeAlphabet

namespace PactType

set_option maxHeartbeats 1000000 in
/-- Re-signing an alphabet-well-formed type twice discards the intermediate
alphabet. -/
theorem reannotate_reannotate :
    ∀ (processType : PactType) (source target : PactTypeAlphabet),
      processType.AlphabetWellFormed →
      (processType.reannotate source).AlphabetWellFormed →
      (processType.reannotate source).reannotate target =
        processType.reannotate target := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hXBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          ∀ origin source target : PactTypeAlphabet,
          BranchesAlphabetWellFormed origin branches →
          BranchesAlphabetWellFormed source
            (reannotateBranches source branches) →
          reannotateBranches target (reannotateBranches source branches) =
            reannotateBranches target branches := by
        intro branches
        induction branches with
        | nil => intro _ _ _ _ _ _; simp
        | cons head tail restIH =>
            intro hSizeCons origin source target hWF hWF'
            rcases head with ⟨action, body⟩
            have hBodySize : sizeOf body < n := by
              have hPair : sizeOf body < sizeOf (action, body) := by
                simp_wf; omega
              have hHead : sizeOf (action, body) <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have hRest : sizeOf tail <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            rw [reannotateBranches_cons] at hWF' ⊢
            rw [reannotateBranches_cons, reannotateBranches_cons]
            simp only [BranchesAlphabetWellFormed] at hWF hWF'
            rw [ih (sizeOf body) hBodySize body rfl source target
              hWF.2.1 hWF'.2.1,
              restIH hTailSize origin source target hWF.2.2 hWF'.2.2]
      have hOBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          ∀ (origin source target : PactTypeAlphabet)
            (seenOrigin seenSource seenTarget : Finset BareMessage),
          OfferBranchesWellFormed origin seenOrigin branches →
          OfferBranchesWellFormed source seenSource
            (reannotateOfferBranches source seenSource branches) →
          reannotateOfferBranches target seenTarget
              (reannotateOfferBranches source seenSource branches) =
            reannotateOfferBranches target seenTarget branches := by
        intro branches
        induction branches with
        | nil =>
            intro _ _ _ _ _ _ _ _ _
            simp [reannotateOfferBranches_nil]
        | cons head tail restIH =>
            intro hSizeCons origin source target seenOrigin seenSource
              seenTarget hWF hWF'
            rcases head with ⟨action, body⟩
            have hBodySize : sizeOf body < n := by
              have hPair : sizeOf body < sizeOf (action, body) := by
                simp_wf; omega
              have hHead : sizeOf (action, body) <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have hRest : sizeOf tail <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            rw [reannotateOfferBranches_cons] at hWF' ⊢
            rw [reannotateOfferBranches_cons, reannotateOfferBranches_cons]
            simp only [OfferBranchesWellFormed] at hWF hWF'
            rw [ih (sizeOf body) hBodySize body rfl _ _ hWF.2.1 hWF'.2.1,
              restIH hTailSize origin source target _ _ _ hWF.2.2 hWF'.2.2]
      intro source target hWF hWF'
      cases processType with
      | message a msg dir | progress a pid | tock a | skip a | var a name =>
          simp only [reannotate]
      | choice a left right | seq a left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [reannotate] at hWF' ⊢
          simp only [AlphabetWellFormed] at hWF hWF'
          rw [ih (sizeOf left) hLeftSize left rfl source target hWF.2.2.2.1
            hWF'.2.2.2.1,
            ih (sizeOf right) hRightSize right rfl source target
              hWF.2.2.2.2 hWF'.2.2.2.2]
      | fairChoice a bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [reannotate] at hWF' ⊢
          simp only [AlphabetWellFormed] at hWF hWF'
          rw [ih (sizeOf left) hLeftSize left rfl source target hWF.2.2.2.1
            hWF'.2.2.2.1,
            ih (sizeOf right) hRightSize right rfl source target
              hWF.2.2.2.2 hWF'.2.2.2.2]
      | recur a name body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [reannotate] at hWF' ⊢
          simp only [AlphabetWellFormed] at hWF hWF'
          rw [ih (sizeOf body) hBodySize body rfl source target hWF.2.2
            hWF'.2.2]
      | xoffer a elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [reannotate] at hWF' ⊢
          simp only [AlphabetWellFormed] at hWF hWF'
          rw [ih (sizeOf elseType) hElseSize elseType rfl source target
            hWF.2.2.1 hWF'.2.2.1,
            hXBranches branches hBranchesSize a source target hWF.2.2.2
              hWF'.2.2.2]
      | offer a elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [reannotate] at hWF' ⊢
          simp only [AlphabetWellFormed] at hWF hWF'
          rw [ih (sizeOf elseType) hElseSize elseType rfl source target
            hWF.2.2.1 hWF'.2.2.1,
            hOBranches branches hBranchesSize a source target ∅ ∅ ∅
              hWF.2.2.2 hWF'.2.2.2]
      | par a left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [reannotate] at hWF' ⊢
          simp only [AlphabetWellFormed] at hWF hWF'
          have hHidden : ∀ action ∈ source.actions, action.1 ∉ interface :=
            hWF'.2.1.parent_hides_interface
          simp only [reannotate_alphabet]
          rw [PactTypeAlphabet.projectParallel_reannotate hHidden,
            PactTypeAlphabet.projectParallel_reannotate hHidden,
            ih (sizeOf left) hLeftSize left rfl _ _ hWF.2.2.1 hWF'.2.2.1,
            ih (sizeOf right) hRightSize right rfl _ _ hWF.2.2.2 hWF'.2.2.2]

end PactType

/-- Target transport for one type: every state related to a residual of
`sigma` is related to a live-equivalent residual of the re-signed `sigma`. -/
def SurvivorTransport (sigma : PactType) : Prop :=
  ∀ bound : List String, TypeWellFormedIn bound sigma →
    ∀ target : PactTypeAlphabet, target.WellFormed →
      (∀ action ∈ target.actions,
        action.1 ∉ PactType.ParallelInterfaces sigma) →
      ∀ (rho : PactType) (q : TypeAutomatonState),
        relationMembership (buildRelationSet sigma (compileType sigma)) rho q →
        ∃ theta,
          relationMembership
            (buildRelationSet (sigma.reannotate target)
              (compileType (sigma.reannotate target))) theta q ∧
          PactType.LiveEq (rho.reannotate target) theta

theorem survivorTransport_skip (a : PactTypeAlphabet) :
    SurvivorTransport (.skip a) := by
  intro _ _ target _ _ rho q hRelated
  obtain ⟨rfl, rfl⟩ := relationMembership_skip_cases a hRelated
  refine ⟨(PactType.skip a).reannotate target, ?_,
    PactType.liveEq_refl _⟩
  simp only [PactType.reannotate]
  show ((PactType.skip target : PactType), TypeAutomatonState.root) ∈
    buildRelationSetCoreFuel (typeCompilationFuel (PactType.skip target))
      (PactType.skip target)
  simp [typeCompilationFuel, buildRelationSetCoreFuel]

theorem survivorTransport_var (a : PactTypeAlphabet) (name : String) :
    SurvivorTransport (.var a name) := by
  intro _ _ target _ _ rho q hRelated
  obtain ⟨rfl, rfl⟩ := relationMembership_var_cases a name hRelated
  refine ⟨(PactType.var a name).reannotate target, ?_,
    PactType.liveEq_refl _⟩
  simp only [PactType.reannotate]
  show ((PactType.var target name : PactType), TypeAutomatonState.root) ∈
    buildRelationSetCoreFuel (typeCompilationFuel (PactType.var target name))
      (PactType.var target name)
  simp [typeCompilationFuel, buildRelationSetCoreFuel]

theorem survivorTransport_message (a : PactTypeAlphabet) (msg : MessageId)
    (dir : MessageDir) : SurvivorTransport (.message a msg dir) := by
  intro _ _ target _ _ rho q hRelated
  rcases relationMembership_message_cases a msg dir hRelated with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨(PactType.message a msg dir).reannotate target, ?_,
      PactType.liveEq_refl _⟩
    simp only [PactType.reannotate]
    show ((PactType.message target msg dir : PactType),
        TypeAutomatonState.root) ∈
      buildRelationSetCoreFuel
        (typeCompilationFuel (PactType.message target msg dir))
        (PactType.message target msg dir)
    simp [typeCompilationFuel, buildRelationSetCoreFuel]
  · refine ⟨(PactType.skip a).reannotate target, ?_, PactType.liveEq_refl _⟩
    simp only [PactType.reannotate]
    show ((PactType.skip target : PactType), TypeAutomatonState.final) ∈
      buildRelationSetCoreFuel (typeCompilationFuel (PactType.message target msg dir)) (PactType.message target msg dir)
    simp [typeCompilationFuel, buildRelationSetCoreFuel]

theorem survivorTransport_tock (a : PactTypeAlphabet) :
    SurvivorTransport (.tock a) := by
  intro _ _ target _ _ rho q hRelated
  rcases relationMembership_tock_cases a hRelated with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨(PactType.tock a).reannotate target, ?_, PactType.liveEq_refl _⟩
    simp only [PactType.reannotate]
    show ((PactType.tock target : PactType), TypeAutomatonState.root) ∈
      buildRelationSetCoreFuel (typeCompilationFuel (PactType.tock target))
        (PactType.tock target)
    simp [typeCompilationFuel, buildRelationSetCoreFuel]
  · refine ⟨(PactType.skip a).reannotate target, ?_, PactType.liveEq_refl _⟩
    simp only [PactType.reannotate]
    show ((PactType.skip target : PactType), TypeAutomatonState.final) ∈
      buildRelationSetCoreFuel (typeCompilationFuel (PactType.tock target)) (PactType.tock target)
    simp [typeCompilationFuel, buildRelationSetCoreFuel]

theorem survivorTransport_progress (a : PactTypeAlphabet) (pid : ProcId) :
    SurvivorTransport (.progress a pid) := by
  intro _ _ target _ _ rho q hRelated
  rcases relationMembership_progress_cases a pid hRelated with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨(PactType.progress a pid).reannotate target, ?_,
      PactType.liveEq_refl _⟩
    simp only [PactType.reannotate]
    show ((PactType.progress target pid : PactType),
        TypeAutomatonState.root) ∈
      buildRelationSetCoreFuel
        (typeCompilationFuel (PactType.progress target pid))
        (PactType.progress target pid)
    simp [typeCompilationFuel, buildRelationSetCoreFuel]
  · refine ⟨(PactType.skip a).reannotate target, ?_, PactType.liveEq_refl _⟩
    simp only [PactType.reannotate]
    show ((PactType.skip target : PactType), TypeAutomatonState.final) ∈
      buildRelationSetCoreFuel (typeCompilationFuel (PactType.progress target pid)) (PactType.progress target pid)
    simp [typeCompilationFuel, buildRelationSetCoreFuel]



/-- A branch body's interfaces are among the list's. -/
theorem parallelInterfaces_subset_branches :
    ∀ (branches : List (BareMessage × PactType))
      (entry : BareMessage × PactType), entry ∈ branches →
      PactType.ParallelInterfaces entry.2 ⊆
        PactType.ParallelBranchInterfaces branches
  | [], _, hMem => absurd hMem (List.not_mem_nil)
  | (action, body) :: rest, entry, hMem => by
      rcases List.mem_cons.mp hMem with rfl | hRest
      · simp only [PactType.ParallelBranchInterfaces]
        exact Finset.subset_union_left
      · simp only [PactType.ParallelBranchInterfaces]
        exact (parallelInterfaces_subset_branches rest entry hRest).trans
          Finset.subset_union_right

/-- The root of a choice represents the whole choice. -/
theorem relationMembership_choice_root (a : PactTypeAlphabet)
    (left right : PactType) :
    relationMembership
      (buildRelationSet (.choice a left right)
        (compileType (.choice a left right)))
      (.choice a left right) .root := by
  show ((PactType.choice a left right : PactType), TypeAutomatonState.root) ∈
    buildRelationSetCoreFuel
      (typeCompilationFuel (PactType.choice a left right))
      (PactType.choice a left right)
  have hFuelEq : typeCompilationFuel (PactType.choice a left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  simp [buildRelationSetCoreFuel]

/-- The root of a fair choice represents the whole fair choice. -/
theorem relationMembership_fairChoice_root (a : PactTypeAlphabet)
    (bid : BranchId) (left right : PactType) :
    relationMembership
      (buildRelationSet (.fairChoice a bid left right)
        (compileType (.fairChoice a bid left right)))
      (.fairChoice a bid left right) .root := by
  show ((PactType.fairChoice a bid left right : PactType),
    TypeAutomatonState.root) ∈
    buildRelationSetCoreFuel
      (typeCompilationFuel (PactType.fairChoice a bid left right))
      (PactType.fairChoice a bid left right)
  have hFuelEq : typeCompilationFuel (PactType.fairChoice a bid left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  simp [buildRelationSetCoreFuel]

/-- The root of a recursion represents the whole recursion. -/
theorem relationMembership_recur_root (a : PactTypeAlphabet) (name : String)
    (body : PactType) :
    relationMembership
      (buildRelationSet (.recur a name body)
        (compileType (.recur a name body)))
      (.recur a name body) .root := by
  show ((PactType.recur a name body : PactType), TypeAutomatonState.root) ∈
    buildRelationSetCoreFuel
      (typeCompilationFuel (PactType.recur a name body))
      (PactType.recur a name body)
  have hFuelEq : typeCompilationFuel (PactType.recur a name body) =
      typeCompilationFuel body + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  simp [buildRelationSetCoreFuel]

theorem survivorTransport_choice (a : PactTypeAlphabet)
    (left right : PactType) (hLeft : SurvivorTransport left)
    (hRight : SurvivorTransport right) :
    SurvivorTransport (.choice a left right) := by
  intro bound hWF target hTargetWF hAvoid rho q hRelated
  obtain ⟨hWFL, hWFR⟩ := typeWellFormedIn_choice hWF
  simp only [PactType.ParallelInterfaces, Finset.mem_union, not_or] at hAvoid
  rcases relationMembership_choice_cases a left right hRelated with
    hRoot | ⟨q', hState, hChild⟩ | ⟨q', hState, hChild⟩
  · rw [Prod.ext_iff] at hRoot
    obtain ⟨rfl, rfl⟩ := hRoot
    exact ⟨(PactType.choice a left right).reannotate target,
      by simpa only [PactType.reannotate] using
        relationMembership_choice_root target (left.reannotate target)
          (right.reannotate target),
      PactType.liveEq_refl _⟩
  · simp only at hState hChild
    subst hState
    obtain ⟨theta, hMem, hLive⟩ := hLeft bound hWFL target hTargetWF
      (fun act hAct => (hAvoid act hAct).1) rho q' hChild
    refine ⟨theta, ?_, hLive⟩
    simpa only [PactType.reannotate] using
      relationMembership_choice_left target (left.reannotate target)
        (right.reannotate target) theta hMem
  · simp only at hState hChild
    subst hState
    obtain ⟨theta, hMem, hLive⟩ := hRight bound hWFR target hTargetWF
      (fun act hAct => (hAvoid act hAct).2) rho q' hChild
    refine ⟨theta, ?_, hLive⟩
    simpa only [PactType.reannotate] using
      relationMembership_choice_right target (left.reannotate target)
        (right.reannotate target) theta hMem

theorem survivorTransport_fairChoice (a : PactTypeAlphabet) (bid : BranchId)
    (left right : PactType) (hLeft : SurvivorTransport left)
    (hRight : SurvivorTransport right) :
    SurvivorTransport (.fairChoice a bid left right) := by
  intro bound hWF target hTargetWF hAvoid rho q hRelated
  obtain ⟨hWFL, hWFR⟩ := typeWellFormedIn_fairChoice hWF
  simp only [PactType.ParallelInterfaces, Finset.mem_union, not_or] at hAvoid
  rcases relationMembership_fairChoice_cases a bid left right hRelated with
    hRoot | ⟨q', hState, hChild⟩ | ⟨q', hState, hChild⟩
  · rw [Prod.ext_iff] at hRoot
    obtain ⟨rfl, rfl⟩ := hRoot
    exact ⟨(PactType.fairChoice a bid left right).reannotate target,
      by simpa only [PactType.reannotate] using
        relationMembership_fairChoice_root target bid
          (left.reannotate target) (right.reannotate target),
      PactType.liveEq_refl _⟩
  · simp only at hState hChild
    subst hState
    obtain ⟨theta, hMem, hLive⟩ := hLeft bound hWFL target hTargetWF
      (fun act hAct => (hAvoid act hAct).1) rho q' hChild
    refine ⟨theta, ?_, hLive⟩
    simpa only [PactType.reannotate] using
      relationMembership_fairChoice_left target bid (left.reannotate target)
        (right.reannotate target) theta hMem
  · simp only at hState hChild
    subst hState
    obtain ⟨theta, hMem, hLive⟩ := hRight bound hWFR target hTargetWF
      (fun act hAct => (hAvoid act hAct).2) rho q' hChild
    refine ⟨theta, ?_, hLive⟩
    simpa only [PactType.reannotate] using
      relationMembership_fairChoice_right target bid (left.reannotate target)
        (right.reannotate target) theta hMem

theorem survivorTransport_xoffer (a : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElse : SurvivorTransport elseType)
    (hBranch : ∀ entry ∈ branches, SurvivorTransport entry.2) :
    SurvivorTransport (.xoffer a elseType branches) := by
  intro bound hWF target hTargetWF hAvoid rho q hRelated
  obtain ⟨hWFE, hWFB⟩ := typeWellFormedIn_xoffer hWF
  simp only [PactType.ParallelInterfaces, Finset.mem_union, not_or] at hAvoid
  rcases relationMembership_xoffer_cases a elseType branches hRelated with
    hRoot | ⟨q', hState, hChild⟩ |
    ⟨i, action, branchType, q', hGet, hState, hChild⟩
  · rw [Prod.ext_iff] at hRoot
    obtain ⟨rfl, rfl⟩ := hRoot
    exact ⟨(PactType.xoffer a elseType branches).reannotate target,
      by simpa only [PactType.reannotate] using
        relationMembership_xoffer_root target (elseType.reannotate target)
          (PactType.reannotateBranches target branches),
      PactType.liveEq_refl _⟩
  · simp only at hState hChild
    subst hState
    obtain ⟨theta, hMem, hLive⟩ := hElse bound hWFE target hTargetWF
      (fun act hAct => (hAvoid act hAct).1) rho q' hChild
    refine ⟨theta, ?_, hLive⟩
    simpa only [PactType.reannotate] using
      relationMembership_xoffer_else target (elseType.reannotate target)
        (PactType.reannotateBranches target branches) hMem
  · simp only at hState hChild
    subst hState
    have hMemBranch : (action, branchType) ∈ branches :=
      List.mem_iff_getElem?.mpr ⟨i, hGet⟩
    have hAvoidBranch : ∀ act ∈ target.actions,
        act.1 ∉ PactType.ParallelInterfaces branchType := by
      intro act hAct hIn
      exact (hAvoid act hAct).2
        (parallelInterfaces_subset_branches branches (action, branchType)
          hMemBranch hIn)
    obtain ⟨theta, hMem, hLive⟩ := hBranch (action, branchType) hMemBranch
      bound (hWFB (action, branchType) hMemBranch) target hTargetWF
      hAvoidBranch rho q' hChild
    refine ⟨theta, ?_, hLive⟩
    have hGet' : (PactType.reannotateBranches target branches)[i]? =
        some (action, branchType.reannotate target) := by
      rw [CompiledShape.reannotateBranches_eq_map, List.getElem?_map, hGet]
      rfl
    simpa only [PactType.reannotate] using
      relationMembership_xoffer_branch target (elseType.reannotate target)
        (PactType.reannotateBranches target branches) hGet' hMem




/-- Synchronising on nothing leaves the parent alphabet unchanged. -/
@[simp] theorem PactTypeAlphabet.projectParallel_empty
    (parent child : PactTypeAlphabet) :
    PactTypeAlphabet.projectParallel parent child ∅ = parent := by
  refine congrArg PactTypeAlphabet.mk (Finset.ext fun action => ?_)
  simp only [PactTypeAlphabet.projectParallel, Finset.mem_union,
    Finset.mem_filter, Finset.notMem_empty, and_false, false_or]

/-- Re-signing a singleton exclusive offer re-signs its head and body. -/
theorem reannotate_singletonTypeXOfferAt
    (source target : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hWF : branch.2.AlphabetWellFormed)
    (hWF' : (branch.2.reannotate source).AlphabetWellFormed) :
    (singletonTypeXOfferAt source branch).reannotate target =
      singletonTypeXOfferAt target branch := by
  rcases branch with ⟨action, body⟩
  simp only [singletonTypeXOfferAt, PactType.reannotate,
    PactType.reannotateBranches_cons, PactType.reannotateBranches_nil]
  rw [PactType.reannotate_reannotate body source target hWF hWF']

/-- Re-signing a committed branch re-signs its head message and continuation. -/
theorem reannotate_selectedTypeBranchAt
    (source target : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hWF : branch.2.AlphabetWellFormed)
    (hWF' : (branch.2.reannotate source).AlphabetWellFormed) :
    (selectedTypeBranchAt source branch).reannotate target =
      selectedTypeBranchAt target branch := by
  rcases branch with ⟨action, body⟩
  simp only [selectedTypeBranchAt, PactType.reannotate]
  rw [PactType.reannotate_reannotate body source target hWF hWF']


/-- Every component of the branch product already carries the enclosing
alphabet, so re-signing the product rebuilds it at the new alphabet. -/
theorem reannotate_parallelTypeBranchesWithin
    (source target : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      (∀ b ∈ branches, b.2.AlphabetWellFormed) →
      (∀ b ∈ branches, (b.2.reannotate source).AlphabetWellFormed) →
      (parallelTypeBranchesWithin source branches).reannotate target =
        parallelTypeBranchesWithin target branches := by
  intro branches
  induction branches with
  | nil =>
      intro _ _
      simp [parallelTypeBranchesWithin, PactType.reannotate]
  | cons head rest ih =>
      intro hWF hWF'
      cases rest with
      | nil =>
          simp only [parallelTypeBranchesWithin]
          exact reannotate_singletonTypeXOfferAt source target head
            (hWF head (by simp)) (hWF' head (by simp))
      | cons next tail =>
          simp only [parallelTypeBranchesWithin, PactType.reannotate,
            PactTypeAlphabet.projectParallel_empty]
          rw [reannotate_singletonTypeXOfferAt source target head
              (hWF head (by simp)) (hWF' head (by simp)),
            ih (fun b hb => hWF b (by simp [hb]))
              (fun b hb => hWF' b (by simp [hb]))]

/-- The committed product re-signs the same way. -/
theorem reannotate_parallelTypeBranchesSelectingWithin
    (source target : PactTypeAlphabet) (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType),
      (∀ b ∈ branches, b.2.AlphabetWellFormed) →
      (∀ b ∈ branches, (b.2.reannotate source).AlphabetWellFormed) →
      (parallelTypeBranchesSelectingWithin source selected branches).reannotate
          target =
        parallelTypeBranchesSelectingWithin target selected branches := by
  intro branches
  induction branches with
  | nil =>
      intro _ _
      simp [parallelTypeBranchesSelectingWithin, PactType.reannotate]
  | cons head rest ih =>
      intro hWF hWF'
      cases rest with
      | nil =>
          by_cases hSel : head = selected
          · simp only [parallelTypeBranchesSelectingWithin, if_pos hSel]
            exact reannotate_selectedTypeBranchAt source target head
              (hWF head (by simp)) (hWF' head (by simp))
          · simp only [parallelTypeBranchesSelectingWithin, if_neg hSel]
            exact reannotate_singletonTypeXOfferAt source target head
              (hWF head (by simp)) (hWF' head (by simp))
      | cons next tail =>
          by_cases hSel : head = selected
          · simp only [parallelTypeBranchesSelectingWithin, if_pos hSel,
              PactType.reannotate, PactTypeAlphabet.projectParallel_empty]
            rw [reannotate_selectedTypeBranchAt source target head
                (hWF head (by simp)) (hWF' head (by simp)),
              reannotate_parallelTypeBranchesWithin source target (next :: tail)
                (fun b hb => hWF b (by simp [hb]))
                (fun b hb => hWF' b (by simp [hb]))]
          · simp only [parallelTypeBranchesSelectingWithin, if_neg hSel,
              PactType.reannotate, PactTypeAlphabet.projectParallel_empty]
            rw [reannotate_singletonTypeXOfferAt source target head
                (hWF head (by simp)) (hWF' head (by simp)),
              ih (fun b hb => hWF b (by simp [hb]))
                (fun b hb => hWF' b (by simp [hb]))]

/-- Re-signing commutes with committing to a branch.  An offer with no branches
never commits, so the statement is about a non-empty branch list. -/
theorem reannotate_parallelTypeBranchesSelecting
    (source target : PactTypeAlphabet) (selected : BareMessage × PactType)
    (head : BareMessage × PactType) (tail : List (BareMessage × PactType))
    (hWF : ∀ b ∈ head :: tail, b.2.AlphabetWellFormed)
    (hWF' : ∀ b ∈ head :: tail, (b.2.reannotate source).AlphabetWellFormed) :
    (parallelTypeBranchesSelecting source selected
        (head :: tail)).reannotate target =
      parallelTypeBranchesSelecting target selected (head :: tail) := by
  simp only [parallelTypeBranchesSelecting]
  exact reannotate_parallelTypeBranchesSelectingWithin source target selected
    (head :: tail) hWF hWF'


/-- Each branch of a well-formed conjunctive offer carries the enclosing
alphabet and is itself well formed. -/
theorem offerBranches_wellFormed_of_mem
    {alphabet : PactTypeAlphabet} {seen : Finset BareMessage}
    {branches : List (BareMessage × PactType)}
    (h : PactType.OfferBranchesWellFormed alphabet seen branches) :
    ∀ b ∈ branches, b.2.alphabet = alphabet ∧ b.2.AlphabetWellFormed := by
  induction branches with
  | nil => intro b hb; cases hb
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      simp only [PactType.OfferBranchesWellFormed] at h
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hTail
      · exact ⟨h.1, h.2.1⟩
      · exact ih h.2.2 b hTail

/-- Re-signing a conjunctive offer's branches gives each branch the enclosing
alphabet, so the list is a map. -/
theorem reannotateOfferBranches_eq_map' (alphabet : PactTypeAlphabet)
    (seen : Finset BareMessage) :
    ∀ branches : List (BareMessage × PactType),
      PactType.reannotateOfferBranches alphabet seen branches =
        branches.map fun branch => (branch.1, branch.2.reannotate alphabet) := by
  intro branches
  induction branches with
  | nil => rw [PactType.reannotateOfferBranches_nil, List.map_nil]
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      rw [PactType.reannotateOfferBranches_cons, List.map_cons, ih]

/-- The product only re-signs each branch body by the enclosing alphabet, so
pre-re-signing the branches changes nothing. -/
theorem parallelTypeBranchesWithin_map_reannotate
    (alphabet source : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      (∀ b ∈ branches, b.2.AlphabetWellFormed) →
      (∀ b ∈ branches, (b.2.reannotate source).AlphabetWellFormed) →
      parallelTypeBranchesWithin alphabet
          (branches.map fun b => (b.1, b.2.reannotate source)) =
        parallelTypeBranchesWithin alphabet branches := by
  intro branches
  induction branches with
  | nil => intro _ _; rfl
  | cons head rest ih =>
      intro hWF hWF'
      have hHead : singletonTypeXOfferAt alphabet
          (head.1, head.2.reannotate source) =
            singletonTypeXOfferAt alphabet head := by
        rcases head with ⟨action, body⟩
        simp only [singletonTypeXOfferAt]
        rw [PactType.reannotate_reannotate body source alphabet
          (hWF (action, body) (by simp)) (hWF' (action, body) (by simp))]
      cases rest with
      | nil =>
          simp only [List.map_cons, List.map_nil,
            parallelTypeBranchesWithin]
          exact hHead
      | cons next tail =>
          have hRest := ih (fun b hb => hWF b (by simp [hb]))
            (fun b hb => hWF' b (by simp [hb]))
          simp only [List.map_cons] at hRest
          simp only [List.map_cons, parallelTypeBranchesWithin]
          rw [hHead, hRest]

/-- The committed product likewise ignores pre-re-signing, provided the chosen
branch is re-signed the same way. -/
theorem parallelTypeBranchesSelectingWithin_map_reannotate
    (alphabet source : PactTypeAlphabet) (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType),
      (∀ b ∈ branches, b.2.AlphabetWellFormed) →
      (∀ b ∈ branches, (b.2.reannotate source).AlphabetWellFormed) →
      List.Pairwise (fun x y => x.1 ≠ y.1) branches →
      selected ∈ branches →
      parallelTypeBranchesSelectingWithin alphabet
          (selected.1, selected.2.reannotate source)
          (branches.map fun b => (b.1, b.2.reannotate source)) =
        parallelTypeBranchesSelectingWithin alphabet selected branches := by
  intro branches
  induction branches with
  | nil => intro _ _ _ hMem; cases hMem
  | cons head rest ih =>
      intro hWF hWF' hPair hMem
      have hHeadWF := hWF head (by simp)
      have hHeadWF' := hWF' head (by simp)
      have hSelIff : (head.1, head.2.reannotate source) =
          (selected.1, selected.2.reannotate source) ↔ head = selected := by
        constructor
        · intro hEq
          have hFst : head.1 = selected.1 := by
            simpa using congrArg Prod.fst hEq
          rcases List.mem_cons.mp hMem with hHd | hTail
          · exact hHd.symm
          · exact absurd hFst (List.rel_of_pairwise_cons hPair hTail)
        · intro hEq; rw [hEq]
      have hHead : singletonTypeXOfferAt alphabet
          (head.1, head.2.reannotate source) =
            singletonTypeXOfferAt alphabet head := by
        rcases head with ⟨action, body⟩
        simp only [singletonTypeXOfferAt]
        rw [PactType.reannotate_reannotate body source alphabet hHeadWF hHeadWF']
      have hSelHead : selectedTypeBranchAt alphabet
          (head.1, head.2.reannotate source) =
            selectedTypeBranchAt alphabet head := by
        rcases head with ⟨action, body⟩
        simp only [selectedTypeBranchAt]
        rw [PactType.reannotate_reannotate body source alphabet
          hHeadWF hHeadWF']
      cases rest with
      | nil =>
          simp only [List.map_cons, List.map_nil,
            parallelTypeBranchesSelectingWithin]
          by_cases hSel : head = selected
          · subst hSel
            rw [if_pos rfl, if_pos rfl, hSelHead]
          · rw [if_neg (fun h => hSel (hSelIff.mp h)), if_neg hSel, hHead]
      | cons next tail =>
          simp only [List.map_cons, parallelTypeBranchesSelectingWithin]
          by_cases hSel : head = selected
          · subst hSel
            have hRest := parallelTypeBranchesWithin_map_reannotate alphabet
              source (next :: tail) (fun b hb => hWF b (by simp [hb]))
              (fun b hb => hWF' b (by simp [hb]))
            simp only [List.map_cons] at hRest
            rw [if_pos rfl, if_pos rfl, hSelHead, hRest]
          · have hRest := ih (fun b hb => hWF b (by simp [hb]))
              (fun b hb => hWF' b (by simp [hb]))
              (List.pairwise_cons.mp hPair).2
              ((List.mem_cons.mp hMem).resolve_left (fun h => hSel h.symm))
            simp only [List.map_cons] at hRest
            rw [if_neg (fun h => hSel (hSelIff.mp h)), if_neg hSel, hHead,
              hRest]

/-- Interface scoping passes to every branch of an offer. -/
theorem interfaceScoped_of_mem_branches
    {branches : List (BareMessage × PactType)}
    (h : PactType.InterfaceScopedBranches branches) :
    ∀ b ∈ branches, b.2.InterfaceScoped := by
  induction branches with
  | nil => intro b hb; cases hb
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      simp only [PactType.InterfaceScopedBranches] at h
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hTail
      · exact h.1
      · exact ih h.2 b hTail

/-- Conjunctive ownership separates branch heads, so no two branches share one. -/
theorem branchHeadsPairwise_of_conjunctive
    {branches : List (BareMessage × PactType)}
    (h : PactType.ConjunctiveMessageOwnershipBranches branches) :
    List.Pairwise (fun x y => x.1 ≠ y.1) branches := by
  induction branches with
  | nil => exact List.Pairwise.nil
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      simp only [PactType.ConjunctiveMessageOwnershipBranches] at h
      refine List.Pairwise.cons ?_ (ih h.2.2)
      intro other hOther hEq
      have hOtherMem : other.1.1 ∈ PactType.BranchMessageIds tail :=
        branch_subset_branchMessageIds hOther
          (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      rw [← hEq] at hOtherMem
      exact Finset.disjoint_left.mp h.2.1
        (Finset.mem_union_left _ (Finset.mem_singleton_self _)) hOtherMem

/-- Substitution touches no alphabet annotation, so re-signing a substituted
type is the same as substituting the re-signed replacement into the re-signed
body. -/
theorem PactType.reannotate_replaceVar (name : String) :
    ∀ (processType : PactType) (target : PactTypeAlphabet)
      (replacement : PactType),
      processType.AlphabetWellFormed →
      replacement.alphabet = processType.alphabet →
      processType.TailOccurrences name True →
      (processType.replaceVar name replacement).reannotate target =
        (processType.reannotate target).replaceVar name
          (replacement.reannotate target) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hReplaceBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ (target : PactTypeAlphabet)
            (replacement : PactType) (alphabet : PactTypeAlphabet),
          PactType.BranchesAlphabetWellFormed alphabet branches →
          replacement.alphabet = alphabet →
          PactType.TailBranchOccurrences name True branches →
          PactType.reannotateBranches target
              (PactType.replaceBranches branches name replacement) =
            PactType.replaceBranches (PactType.reannotateBranches target branches)
              name (replacement.reannotate target) := by
        intro branches
        induction branches with
        | nil =>
            intro _ _ _ _ _ _ _
            simp [PactType.replaceBranches, PactType.reannotateBranches_nil]
        | cons head tail restIH =>
            intro hSizeCons target replacement alphabet hWFB hAlphaR hTailB
            rcases head with ⟨action, body⟩
            simp only [PactType.BranchesAlphabetWellFormed] at hWFB
            simp only [PactType.TailBranchOccurrences] at hTailB
            have hBodySize : sizeOf body < n := by
              have h1 : sizeOf body < sizeOf (action, body) := by simp_wf; omega
              have h2 : sizeOf (action, body) <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have : sizeOf tail < sizeOf ((action, body) :: tail) := by
                simp_wf; omega
              omega
            simp only [PactType.replaceBranches,
              PactType.reannotateBranches_cons]
            rw [ih (sizeOf body) hBodySize body rfl target replacement
                hWFB.2.1 (by rw [hAlphaR, hWFB.1]) hTailB.1,
              restIH hTailSize target replacement alphabet hWFB.2.2 hAlphaR
                hTailB.2]
      have hReplaceOfferBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ (target : PactTypeAlphabet)
            (replacement : PactType) (alphabet : PactTypeAlphabet)
            (seen : Finset BareMessage),
          PactType.OfferBranchesWellFormed alphabet seen branches →
          replacement.alphabet = alphabet →
          PactType.TailBranchOccurrences name True branches →
          PactType.reannotateOfferBranches target seen
              (PactType.replaceBranches branches name replacement) =
            PactType.replaceBranches
              (PactType.reannotateOfferBranches target seen branches)
              name (replacement.reannotate target) := by
        intro branches
        induction branches with
        | nil =>
            intro _ _ _ _ _ _ _ _
            simp [PactType.replaceBranches,
              PactType.reannotateOfferBranches_nil]
        | cons head tail restIH =>
            intro hSizeCons target replacement alphabet seen hWFB hAlphaR
              hTailB
            rcases head with ⟨action, body⟩
            simp only [PactType.OfferBranchesWellFormed] at hWFB
            simp only [PactType.TailBranchOccurrences] at hTailB
            have hBodySize : sizeOf body < n := by
              have h1 : sizeOf body < sizeOf (action, body) := by simp_wf; omega
              have h2 : sizeOf (action, body) <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have : sizeOf tail < sizeOf ((action, body) :: tail) := by
                simp_wf; omega
              omega
            simp only [PactType.replaceBranches,
              PactType.reannotateOfferBranches_cons]
            rw [ih (sizeOf body) hBodySize body rfl target replacement
                hWFB.2.1 (by rw [hAlphaR, hWFB.1]) hTailB.1,
              restIH hTailSize target replacement alphabet seen hWFB.2.2
                hAlphaR hTailB.2]
      intro target replacement hWF hAlpha hTail
      subst hSize
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ =>
          simp [PactType.replaceVar, PactType.reannotate]
      | var alphabet other =>
          by_cases hName : name = other
          · subst hName
            simp [PactType.replaceVar, PactType.reannotate]
          · simp [PactType.replaceVar, PactType.reannotate, hName]
      | recur alphabet other body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          have hB : sizeOf body < sizeOf
              (PactType.recur alphabet other body) := by simp_wf; omega
          by_cases hName : name = other
          · subst hName
            simp [PactType.replaceVar, PactType.reannotate]
          · simp only [PactType.replaceVar, PactType.reannotate, if_neg hName]
            simp only [PactType.TailOccurrences,
              if_neg (Ne.symm hName)] at hTail
            rw [ih (sizeOf body) hB body rfl target replacement hWF.2.2
              (by rw [hAlpha, hWF.2.1]; rfl) hTail]
      | choice alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          have hL : sizeOf left < sizeOf
              (PactType.choice alphabet left right) := by simp_wf; omega
          have hR : sizeOf right < sizeOf
              (PactType.choice alphabet left right) := by simp_wf; omega
          simp only [PactType.replaceVar, PactType.reannotate]
          simp only [PactType.TailOccurrences] at hTail
          rw [ih (sizeOf left) hL left rfl target replacement hWF.2.2.2.1
              (by rw [hAlpha, hWF.2.1]; rfl) hTail.1,
            ih (sizeOf right) hR right rfl target replacement hWF.2.2.2.2
              (by rw [hAlpha, hWF.2.2.1]; rfl) hTail.2]
      | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          have hL : sizeOf left < sizeOf
              (PactType.seq alphabet left right) := by simp_wf; omega
          have hR : sizeOf right < sizeOf
              (PactType.seq alphabet left right) := by simp_wf; omega
          simp only [PactType.replaceVar, PactType.reannotate]
          simp only [PactType.TailOccurrences] at hTail
          rw [ih (sizeOf left) hL left rfl target replacement hWF.2.2.2.1
              (by rw [hAlpha, hWF.2.1]; rfl)
              (PactType.tailOccurrences_mono name False.elim left hTail.1),
            ih (sizeOf right) hR right rfl target replacement hWF.2.2.2.2
              (by rw [hAlpha, hWF.2.2.1]; rfl) hTail.2]
      | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          have hL : sizeOf left < sizeOf
              (PactType.fairChoice alphabet bid left right) := by simp_wf; omega
          have hR : sizeOf right < sizeOf
              (PactType.fairChoice alphabet bid left right) := by simp_wf; omega
          simp only [PactType.replaceVar, PactType.reannotate]
          simp only [PactType.TailOccurrences] at hTail
          rw [ih (sizeOf left) hL left rfl target replacement hWF.2.2.2.1
              (by rw [hAlpha, hWF.2.1]; rfl) hTail.1,
            ih (sizeOf right) hR right rfl target replacement hWF.2.2.2.2
              (by rw [hAlpha, hWF.2.2.1]; rfl) hTail.2]
      | par alphabet left right interface =>
          -- No call occurs below a parallel node, so substitution is inert.
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.reannotate]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement left hTail.1,
            PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement right hTail.2]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
              (replacement.reannotate _)
              (left.reannotate (target.projectParallel left.alphabet interface))
              (PactType.reannotate_tailOccurrences name left _ False hTail.1),
            PactType.replaceVar_eq_self_of_tailOccurrences_false name
              (replacement.reannotate _)
              (right.reannotate
                (target.projectParallel right.alphabet interface))
              (PactType.reannotate_tailOccurrences name right _ False
                hTail.2)]
      | xoffer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          have hE : sizeOf elseType < sizeOf
              (PactType.xoffer alphabet elseType branches) := by simp_wf; omega
          have hB : sizeOf branches < sizeOf
              (PactType.xoffer alphabet elseType branches) := by simp_wf; omega
          simp only [PactType.replaceVar, PactType.reannotate]
          simp only [PactType.TailOccurrences] at hTail
          rw [ih (sizeOf elseType) hE elseType rfl target replacement
            hWF.2.2.1 (by rw [hAlpha, hWF.2.1]; rfl) hTail.1]
          congr 1
          exact hReplaceBranches branches hB target replacement alphabet
            hWF.2.2.2 (by rw [hAlpha]; rfl) hTail.2
      | offer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          have hE : sizeOf elseType < sizeOf
              (PactType.offer alphabet elseType branches) := by simp_wf; omega
          have hB : sizeOf branches < sizeOf
              (PactType.offer alphabet elseType branches) := by simp_wf; omega
          simp only [PactType.replaceVar, PactType.reannotate]
          simp only [PactType.TailOccurrences] at hTail
          rw [ih (sizeOf elseType) hE elseType rfl target replacement
            hWF.2.2.1 (by rw [hAlpha, hWF.2.1]; rfl) hTail.1]
          congr 1
          exact hReplaceOfferBranches branches hB target replacement alphabet ∅
            hWF.2.2.2 (by rw [hAlpha]; rfl)
            (PactType.tailBranchOccurrences_mono name False.elim branches
              hTail.2)

/-- Conjunctive offer.  The root and the default alternative mirror `xoffer`;
a committed state lives in the branch product, which re-signing rebuilds at the
new alphabet. -/
theorem survivorTransport_offer (a : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElse : SurvivorTransport elseType)
    (hProduct : ∀ selected ∈ branches,
      SurvivorTransport (parallelTypeBranchesSelecting a selected branches)) :
    SurvivorTransport (.offer a elseType branches) := by
  intro bound hWF target hTargetWF hAvoid rho q hRelated
  obtain ⟨hWFE, hWFB⟩ := typeWellFormedIn_offer hWF
  obtain ⟨hAlphaWF, -, -, -, -, -, -, -, -, -, -, -, hIScopAll, -, hCOwn⟩ :=
    id hWF
  simp only [PactType.AlphabetWellFormed] at hAlphaWF
  simp only [PactType.InterfaceScoped] at hIScopAll
  simp only [PactType.ConjunctiveMessageOwnership] at hCOwn
  have hIScop := hIScopAll.2
  simp only [PactType.ParallelInterfaces, Finset.mem_union, not_or] at hAvoid
  have hBodyData : ∀ b ∈ branches,
      b.2.alphabet = a ∧ b.2.AlphabetWellFormed :=
    offerBranches_wellFormed_of_mem hAlphaWF.2.2.2
  have hBodyWF : ∀ b ∈ branches, b.2.AlphabetWellFormed := fun b hb =>
    (hBodyData b hb).2
  have hBodyWF' : ∀ b ∈ branches, (b.2.reannotate a).AlphabetWellFormed := by
    intro b hb
    rw [← (hBodyData b hb).1,
      PactType.reannotate_own_alphabet b.2 (hBodyData b hb).2]
    exact (hBodyData b hb).2
  have hBodyWFTarget : ∀ b ∈ branches,
      (b.2.reannotate target).AlphabetWellFormed := by
    intro b hb
    refine PactType.reannotate_alphabetWellFormed_avoiding b.2 target
      (hBodyData b hb).2 hTargetWF ?_ ?_
    · exact interfaceScoped_of_mem_branches hIScop b hb
    · intro act hAct hIn
      exact (hAvoid act hAct).2
        (parallelInterfaces_subset_branches branches b hb hIn)
  have hPairHeads : List.Pairwise (fun x y => x.1 ≠ y.1) branches :=
    branchHeadsPairwise_of_conjunctive hCOwn.2
  rcases relationMembership_offer_cases a elseType branches hRelated with
    hRoot | ⟨q', hState, hChild⟩ |
    ⟨i, selected, q', hGet, hState, hChild⟩
  · rw [Prod.ext_iff] at hRoot
    obtain ⟨rfl, rfl⟩ := hRoot
    exact ⟨(PactType.offer a elseType branches).reannotate target,
      by simpa only [PactType.reannotate] using
        relationMembership_offer_root target (elseType.reannotate target)
          (PactType.reannotateOfferBranches target ∅ branches),
      PactType.liveEq_refl _⟩
  · simp only at hState hChild
    subst hState
    obtain ⟨theta, hMem, hLive⟩ := hElse bound hWFE target hTargetWF
      (fun act hAct => (hAvoid act hAct).1) rho q' hChild
    refine ⟨theta, ?_, hLive⟩
    simpa only [PactType.reannotate] using
      relationMembership_offer_else target (elseType.reannotate target)
        (PactType.reannotateOfferBranches target ∅ branches) hMem
  · simp only at hState hChild
    subst hState
    have hMemSelected : selected ∈ branches :=
      List.mem_iff_getElem?.mpr ⟨i, hGet⟩
    have hAvoidProduct : ∀ act ∈ target.actions,
        act.1 ∉ PactType.ParallelInterfaces
          (parallelTypeBranchesSelecting a selected branches) := by
      intro act hAct hIn
      exact (hAvoid act hAct).2 (by
        cases branches with
        | nil => cases hMemSelected
        | cons head tail =>
            rw [parallelTypeBranchesSelecting,
              parallelTypeBranchesSelectingWithin_parallelInterfaces] at hIn
            exact hIn)
    obtain ⟨theta, hMem, hLive⟩ := hProduct selected hMemSelected bound
      (hWFB selected hMemSelected) target hTargetWF hAvoidProduct rho q' hChild
    refine ⟨theta, ?_, hLive⟩
    have hGet' : (PactType.reannotateOfferBranches target ∅ branches)[i]? =
        some (selected.1, selected.2.reannotate target) := by
      rw [reannotateOfferBranches_eq_map', List.getElem?_map, hGet]
      rfl
    have hProductEq :
        parallelTypeBranchesSelecting target
            (selected.1, selected.2.reannotate target)
            (PactType.reannotateOfferBranches target ∅ branches) =
          (parallelTypeBranchesSelecting a selected branches).reannotate
            target := by
      rw [reannotateOfferBranches_eq_map']
      cases branches with
      | nil => cases hMemSelected
      | cons head tail =>
          rw [reannotate_parallelTypeBranchesSelecting a target selected head
            tail hBodyWF hBodyWF']
          simp only [parallelTypeBranchesSelecting, List.map_cons]
          exact parallelTypeBranchesSelectingWithin_map_reannotate target target
            selected (head :: tail) hBodyWF hBodyWFTarget hPairHeads
            hMemSelected
    rw [← hProductEq] at hMem
    simpa only [PactType.reannotate] using
      relationMembership_offer_selected target (elseType.reannotate target)
        (PactType.reannotateOfferBranches target ∅ branches) hGet' hMem


/-- Replacing a variable that occurs only in tail position preserves interface
scoping.  In particular, the replacement never crosses a parallel binder. -/
theorem PactType.replaceVar_interfaceScoped (name : String)
    (replacement : PactType) :
    ∀ processType : PactType,
      processType.InterfaceScoped →
      processType.TailOccurrences name True →
      replacement.InterfaceScoped →
      (processType.replaceVar name replacement).InterfaceScoped := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.InterfaceScopedBranches branches →
          PactType.TailBranchOccurrences name True branches →
          replacement.InterfaceScoped →
          PactType.InterfaceScopedBranches
            (PactType.replaceBranches branches name replacement) := by
        intro branches hBranchesSize hScoped hTail hReplacement
        induction branches with
        | nil => simp [PactType.replaceBranches,
            PactType.InterfaceScopedBranches]
        | cons head rest restIH =>
            rcases head with ⟨action, body⟩
            simp only [PactType.InterfaceScopedBranches] at hScoped
            simp only [PactType.TailBranchOccurrences] at hTail
            have hBodySize : sizeOf body < n := by
              have hPair : sizeOf body < sizeOf (action, body) := by
                simp_wf
                omega
              have hHead : sizeOf (action, body) <
                  sizeOf ((action, body) :: rest) := by
                simp_wf
                omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, body) :: rest) := by
                simp_wf
                omega
              omega
            simp only [PactType.replaceBranches,
              PactType.InterfaceScopedBranches]
            exact ⟨ih (sizeOf body) hBodySize body rfl hScoped.1 hTail.1
                hReplacement,
              restIH hRestSize hScoped.2 hTail.2⟩
      intro hScoped hTail hReplacement
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ =>
          simp [PactType.replaceVar, PactType.InterfaceScoped]
      | var alphabet current =>
          by_cases hName : name = current
          · simpa [PactType.replaceVar, hName] using hReplacement
          · simp [PactType.replaceVar, hName, PactType.InterfaceScoped]
      | recur alphabet current body =>
          by_cases hName : name = current
          · simpa [PactType.replaceVar, hName] using hScoped
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]
              simp_wf
              omega
            simp only [PactType.InterfaceScoped] at hScoped
            simp only [PactType.TailOccurrences,
              if_neg (fun h : current = name => hName h.symm)] at hTail
            simp only [PactType.replaceVar, if_neg hName,
              PactType.InterfaceScoped]
            exact ih (sizeOf body) hBodySize body rfl hScoped hTail hReplacement
      | choice alphabet left right | fairChoice alphabet _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.InterfaceScoped]
          exact ⟨ih (sizeOf left) hLeftSize left rfl hScoped.1 hTail.1
              hReplacement,
            ih (sizeOf right) hRightSize right rfl hScoped.2 hTail.2
              hReplacement⟩
      | seq alphabet left right =>
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.InterfaceScoped]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
            replacement left hTail.1]
          exact ⟨hScoped.1,
            ih (sizeOf right) hRightSize right rfl hScoped.2 hTail.2
              hReplacement⟩
      | par alphabet left right interface =>
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.InterfaceScoped]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement left hTail.1,
            PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement right hTail.2]
          exact hScoped
      | xoffer alphabet elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]
            simp_wf
            omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]
            simp_wf
            omega
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.InterfaceScoped]
          exact ⟨ih (sizeOf elseType) hElseSize elseType rfl hScoped.1 hTail.1
              hReplacement,
            hBranches branches hBranchesSize hScoped.2 hTail.2 hReplacement⟩
      | offer alphabet elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]
            simp_wf
            omega
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.InterfaceScoped]
          rw [PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false
            name replacement branches hTail.2]
          exact ⟨ih (sizeOf elseType) hElseSize elseType rfl hScoped.1 hTail.1
              hReplacement,
            hScoped.2⟩

/-- Interface scoping is preserved by every residual represented in the
compiled relation. -/
theorem relationMembership_interfaceScoped :
    ∀ (source residual : PactType) (state : TypeAutomatonState),
      source.InterfaceScoped →
      source.TailRecursive →
      relationMembership (buildRelationSet source (compileType source))
        residual state →
      residual.InterfaceScoped := by
  intro source
  induction hFuel : typeCompilationFuel source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
      intro residual state hScoped hTailRec hRelated
      cases source with
      | skip alphabet =>
          rw [(relationMembership_skip_cases alphabet hRelated).1]
          exact hScoped
      | var alphabet name =>
          rw [(relationMembership_var_cases alphabet name hRelated).1]
          exact hScoped
      | message alphabet msg dir =>
          rcases relationMembership_message_cases alphabet msg dir hRelated with
            hRoot | hFinal
          · rw [hRoot.1]
            exact hScoped
          · rw [hFinal.1]
            simp [PactType.InterfaceScoped]
      | tock alphabet =>
          rcases relationMembership_tock_cases alphabet hRelated with
            hRoot | hFinal
          · rw [hRoot.1]
            exact hScoped
          · rw [hFinal.1]
            simp [PactType.InterfaceScoped]
      | progress alphabet pid =>
          rcases relationMembership_progress_cases alphabet pid hRelated with
            hRoot | hFinal
          · rw [hRoot.1]
            exact hScoped
          · rw [hFinal.1]
            simp [PactType.InterfaceScoped]
      | choice alphabet left right =>
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.TailRecursive] at hTailRec
          rcases relationMembership_choice_cases alphabet left right hRelated with
            hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa [PactType.InterfaceScoped] using hScoped
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hScoped.1 hTailRec.1 hLeftRelated
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hScoped.2 hTailRec.2 hRightRelated
      | fairChoice alphabet bid left right =>
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.TailRecursive] at hTailRec
          rcases relationMembership_fairChoice_cases alphabet bid left right
              hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa [PactType.InterfaceScoped] using hScoped
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hScoped.1 hTailRec.1 hLeftRelated
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hScoped.2 hTailRec.2 hRightRelated
      | seq alphabet left right =>
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.TailRecursive] at hTailRec
          rcases relationMembership_seq_cases alphabet left right hRelated with
            hLeft | hRight
          · rcases hLeft with ⟨q, leftResidual, hEntry, hLeftRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            simp only [PactType.InterfaceScoped]
            exact ⟨ih (typeCompilationFuel left) hLeftFuel left rfl
                leftResidual q hScoped.1 hTailRec.1 hLeftRelated,
              hScoped.2⟩
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hScoped.2 hTailRec.2 hRightRelated
      | par alphabet left right interface =>
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.TailRecursive] at hTailRec
          rcases relationMembership_par_cases alphabet left right interface
              hRelated with hPair | hSurvL | hSurvR | hFinal
          · rcases hPair with ⟨q1, q2, leftResidual, rightResidual,
              hEntry, hLeftRelated, hRightRelated⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            have hLeftSub :=
              (relationMembership_ownership_subset left leftResidual q1
                hLeftRelated).2.2.2.2
            have hRightSub :=
              (relationMembership_ownership_subset right rightResidual q2
                hRightRelated).2.2.2.2
            simp only [PactType.InterfaceScoped]
            refine ⟨?_,
              ih (typeCompilationFuel left) hLeftFuel left rfl leftResidual q1
                hScoped.2.1 hTailRec.1 hLeftRelated,
              ih (typeCompilationFuel right) hRightFuel right rfl rightResidual
                q2 hScoped.2.2 hTailRec.2 hRightRelated⟩
            refine Finset.disjoint_left.mpr ?_
            intro msg hInterface hResidualInterfaces
            apply Finset.disjoint_left.mp hScoped.1 hInterface
            rcases Finset.mem_union.mp hResidualInterfaces with hLeft | hRight
            · exact Finset.mem_union_left _ (hLeftSub hLeft)
            · exact Finset.mem_union_right _ (hRightSub hRight)
          · rcases hSurvL with ⟨q1, residualLeft, hEntry, hLeftRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel :
                typeCompilationFuel (left.reannotate alphabet) < n := by
              rw [← hFuel, typeCompilationFuel_reannotate]
              simp only [typeCompilationFuel]
              omega
            exact ih (typeCompilationFuel (left.reannotate alphabet)) hLeftFuel
              (left.reannotate alphabet) rfl residualLeft q1
              (PactType.reannotate_interfaceScoped left alphabet hScoped.2.1)
              (PactType.reannotate_tailRecursive left alphabet hTailRec.1)
              hLeftRelated
          · rcases hSurvR with ⟨q2, residualRight, hEntry, hRightRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hRightFuel :
                typeCompilationFuel (right.reannotate alphabet) < n := by
              rw [← hFuel, typeCompilationFuel_reannotate]
              simp only [typeCompilationFuel]
              omega
            exact ih (typeCompilationFuel (right.reannotate alphabet))
              hRightFuel (right.reannotate alphabet) rfl residualRight q2
              (PactType.reannotate_interfaceScoped right alphabet hScoped.2.2)
              (PactType.reannotate_tailRecursive right alphabet hTailRec.2)
              hRightRelated
          · injection hFinal with hResidual _
            rw [hResidual]
            simp [PactType.InterfaceScoped]
      | recur alphabet name body =>
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.TailRecursive] at hTailRec
          rcases relationMembership_recur_cases alphabet name body hRelated with
            hRoot | hBody
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa [PactType.InterfaceScoped] using hScoped
          · rcases hBody with ⟨q, bodyResidual, hEntry, hBodyRelated⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hBodyFuel : typeCompilationFuel body < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            have hResidualScoped := ih (typeCompilationFuel body) hBodyFuel body
              rfl bodyResidual q hScoped hTailRec.2 hBodyRelated
            have hResidualTail : bodyResidual.TailOccurrences name True :=
              relationMembership_tailOccurrences body bodyResidual q name True
                hTailRec.2 hTailRec.1 hBodyRelated
            exact PactType.replaceVar_interfaceScoped name
              (.recur alphabet name body) bodyResidual hResidualScoped
              hResidualTail (by simpa [PactType.InterfaceScoped] using hScoped)
      | xoffer alphabet elseType branches =>
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.TailRecursive] at hTailRec
          rcases relationMembership_xoffer_cases alphabet elseType branches
              hRelated with hRoot | hElse | hBranch
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa [PactType.InterfaceScoped] using hScoped
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hScoped.1 hTailRec.1 hElseRelated
          · rcases hBranch with ⟨i, action, branchType, q, hGet, _,
              hBranchRelated⟩
            have hMember : (action, branchType) ∈ branches :=
              List.mem_of_getElem? hGet
            have hBranchFuel : typeCompilationFuel branchType < n := by
              have hLe : typeCompilationFuel branchType ≤
                  typeBranchCompilationFuel branches := by
                simpa using typeCompilationFuel_le_typeBranchCompilationFuel
                  branches (action, branchType) hMember
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact ih (typeCompilationFuel branchType) hBranchFuel branchType rfl
              residual q
              (interfaceScoped_of_mem_scopedBranches hScoped.2 hMember)
              (tailRecursive_of_mem_branches (branch := (action, branchType))
                hTailRec.2 hMember)
              hBranchRelated
      | offer alphabet elseType branches =>
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.TailRecursive] at hTailRec
          rcases relationMembership_offer_cases alphabet elseType branches
              hRelated with hRoot | hElse | hSelected
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa [PactType.InterfaceScoped] using hScoped
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hScoped.1 hTailRec.1 hElseRelated
          · rcases hSelected with ⟨i, selected, q, hGet, _, hSelectedRelated⟩
            have hMember : selected ∈ branches := List.mem_of_getElem? hGet
            have hSelectedFuel : typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches) < n := by
              rw [typeCompilationFuel_parallelTypeBranchesSelecting, ← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact ih (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches))
              hSelectedFuel
              (parallelTypeBranchesSelecting alphabet selected branches) rfl
              residual q
              (parallelTypeBranchesSelecting_interfaceScoped alphabet selected
                branches hScoped.2)
              (parallelTypeBranchesSelecting_tailRecursive alphabet selected
                branches
                (fun branch hBranch =>
                  tailRecursive_of_mem_branches hTailRec.2 hBranch)
                (tailRecursive_of_mem_branches hTailRec.2 hMember))
              hSelectedRelated

/-- The residual facts used by recursion survivor transport, assembled from
the independent relation invariants. -/
theorem relationMembership_survivorInvariant
    (name : String) (source residual : PactType) (state : TypeAutomatonState)
    (hAlphabet : source.AlphabetWellFormed)
    (hScoped : source.InterfaceScoped)
    (hAlphaScoped : source.InterfaceAlphabetScoped)
    (hTailRecursive : source.TailRecursive)
    (hDisjoint : source.OfferBranchesDisjoint)
    (hTail : source.TailOccurrences name True)
    (hRelated :
      relationMembership (buildRelationSet source (compileType source))
        residual state) :
    residual.AlphabetWellFormed ∧ residual.InterfaceScoped ∧
      residual.TailOccurrences name True ∧
      PactType.ParallelInterfaces residual ⊆
        PactType.ParallelInterfaces source ∧
      residual.alphabet = source.alphabet := by
  exact ⟨relationMembership_alphabetWellFormed
      committedOfferAlphabetWellFormed_holds committedOfferScoping_holds
      source residual state hAlphabet hScoped hAlphaScoped hTailRecursive
      hDisjoint hRelated,
    relationMembership_interfaceScoped source residual state hScoped
      hTailRecursive hRelated,
    relationMembership_tailOccurrences source residual state name True
      hTailRecursive hTail hRelated,
    (relationMembership_ownership_subset source residual state hRelated).2.2.2.2,
    relationMembership_alphabet_eq source residual state
      (PactType.alphabetCoherent_of_wellFormed source hAlphabet) hRelated⟩

/-- Recursion.  The fresh root re-signs to itself; a body state carries a
substituted residual, and re-signing commutes with that substitution. -/
theorem survivorTransport_recur (a : PactTypeAlphabet) (name : String)
    (body : PactType) (hBody : SurvivorTransport body) :
    SurvivorTransport (.recur a name body) := by
  intro bound hWF target hTargetWF hAvoid rho q hRelated
  have hWFBody := typeWellFormedIn_recur hWF
  have hWFBodyForTransport := hWFBody
  obtain ⟨hAlphaWF, -, -, -, -, hParentTailRecursive, -, -, -, -, -, -, -, -,
    -⟩ := id hWF
  obtain ⟨hBodyAlphabet, -, -, -, -, hBodyTailRecursive, -, -, -, hBodyMO,
    hBodyPO, hBodyFO, hBodyScoped, hBodyAlphaScoped, hBodyCMO⟩ := hWFBody
  have hBodyDisjoint : body.OfferBranchesDisjoint :=
    offerBranchesDisjoint_of_ownership body hBodyMO hBodyPO hBodyFO hBodyCMO
  simp only [PactType.AlphabetWellFormed] at hAlphaWF
  simp only [PactType.TailRecursive] at hParentTailRecursive
  simp only [PactType.ParallelInterfaces] at hAvoid
  rcases relationMembership_recur_cases a name body hRelated with
    hRoot | ⟨q', residual, hEntry, hChild⟩
  · rw [Prod.ext_iff] at hRoot
    obtain ⟨rfl, rfl⟩ := hRoot
    exact ⟨(PactType.recur a name body).reannotate target,
      by simpa only [PactType.reannotate] using
        relationMembership_recur_root target name (body.reannotate target),
      PactType.liveEq_refl _⟩
  · rw [Prod.ext_iff] at hEntry
    obtain ⟨hResidual, hState⟩ := hEntry
    subst hResidual
    subst hState
    obtain ⟨theta, hMem, hLive⟩ := hBody (name :: bound) hWFBodyForTransport target
      hTargetWF hAvoid residual q' hChild
    have hResidualData := relationMembership_survivorInvariant name body
      residual q' hBodyAlphabet hBodyScoped hBodyAlphaScoped
      hBodyTailRecursive hBodyDisjoint hParentTailRecursive.1 hChild
    have hReannotatedBodyData := relationMembership_survivorInvariant name
      (body.reannotate target) theta q'
      (PactType.reannotate_alphabetWellFormed_avoiding body target
        hBodyAlphabet hTargetWF hBodyScoped hAvoid)
      (PactType.reannotate_interfaceScoped body target hBodyScoped)
      (PactType.reannotate_interfaceAlphabetScoped body target hBodyAlphaScoped
        hAvoid)
      (PactType.reannotate_tailRecursive body target hBodyTailRecursive)
      (reannotate_offerBranchesDisjoint body target hBodyDisjoint)
      (PactType.reannotate_tailOccurrences name body target True
        hParentTailRecursive.1)
      hMem
    refine ⟨theta.replaceVar name (.recur target name (body.reannotate target)),
      ?_, ?_⟩
    · simpa only [PactType.reannotate] using
        relationMembership_recur_child target name (body.reannotate target)
          theta hMem
    · have hCommute :
          (residual.replaceVar name (.recur a name body)).reannotate target =
            (residual.reannotate target).replaceVar name
              ((PactType.recur a name body).reannotate target) :=
        PactType.reannotate_replaceVar name residual target
          (.recur a name body)
          hResidualData.1
          (by
            rw [hResidualData.2.2.2.2]
            simp only [PactType.alphabet]
            exact hAlphaWF.2.1.symm)
          hResidualData.2.2.1
      rw [hCommute]
      have hAlphaRes : (residual.reannotate target).alphabet = target :=
        PactType.reannotate_alphabet target residual
      have hAlphaTheta : theta.alphabet = target := by
        rw [← hLive.1, hAlphaRes]
      have hReplAlpha :
          ((PactType.recur a name body).reannotate target).alphabet =
            (residual.reannotate target).alphabet := by
        simp only [PactType.reannotate_alphabet, hAlphaRes]
      have hReplAlpha' :
          (PactType.recur target name (body.reannotate target)).alphabet =
            theta.alphabet := by
        rw [hAlphaTheta]
        rfl
      refine ⟨?_, ?_⟩
      · rw [PactType.replaceVar_alphabet_eq_of_replacement _ name hReplAlpha,
          PactType.replaceVar_alphabet_eq_of_replacement _ name hReplAlpha',
          hAlphaRes, hAlphaTheta]
      · refine PactType.liveEqBody_replaceVar hLive.2
          (by
            simp only [PactType.reannotate]
            exact PactType.liveEq_refl _)
          ?_ ?_ (by rw [hAlphaRes, hAlphaTheta]) ?_
        · exact PactType.reannotate_alphabetWellFormed_avoiding residual target
            hResidualData.1 hTargetWF hResidualData.2.1
            (fun act hAct hIn => hAvoid act hAct
              (hResidualData.2.2.2.1 hIn))
        · exact hReannotatedBodyData.1
        · exact PactType.reannotate_tailOccurrences name residual target True
            hResidualData.2.2.1

/-- Offer-branch disjointness is one of the ownership consequences carried by
`TypeWellFormedIn`. -/
theorem offerBranchesDisjoint_of_wellFormedIn {bound : List String}
    {processType : PactType} (h : TypeWellFormedIn bound processType) :
    processType.OfferBranchesDisjoint := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hMO, hPO, hFO, -, -, hCMO⟩ := h
  exact offerBranchesDisjoint_of_ownership processType hMO hPO hFO hCMO

/-- Re-signing leaves the deleted sequence states alone. -/
theorem sequenceDeleted_reannotate {processType : PactType}
    (hDisjoint : processType.OfferBranchesDisjoint)
    (alphabet : PactTypeAlphabet) :
    sequenceDeleted (compileTypeFuel
        (typeCompilationFuel (processType.reannotate alphabet))
        (processType.reannotate alphabet)) =
      sequenceDeleted (compileTypeFuel (typeCompilationFuel processType)
        processType) := by
  have hShape := CompiledShape.compileTypeFuel_shapeEq_reannotate
    (typeCompilationFuel processType) processType hDisjoint alphabet
  rw [typeCompilationFuel_reannotate]
  simp only [sequenceDeleted, hShape.2.1, hShape.2.2]

/-- Lift a left-child state that the sequence builder keeps. -/
theorem relationMembership_seq_left_of_not_deleted (alphabet : PactTypeAlphabet)
    (left right residual : PactType) {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet left (compileType left)) residual state)
    (hKept : state ∉ sequenceDeleted
      (compileTypeFuel (typeCompilationFuel left) left)) :
    relationMembership
      (buildRelationSet (.seq alphabet left right)
        (compileType (.seq alphabet left right)))
      (.seq alphabet residual right) (.child 0 state) := by
  have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  show ((.seq alphabet residual right : PactType), .child 0 state) ∈
    buildRelationSetCoreFuel
      (typeCompilationFuel (.seq alphabet left right))
      (.seq alphabet left right)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Prod.mk.injEq]
  left
  refine ⟨(residual, state), ⟨?_, ?_⟩, rfl, rfl⟩
  · rw [buildRelationSetCoreFuel_eq_of_sufficient left
      (le_max_left _ _) le_rfl]
    exact hRelated
  · rw [compileTypeFuel_eq_of_sufficient left
      (le_max_left (typeCompilationFuel left) (typeCompilationFuel right))
      le_rfl]
    exact hKept

theorem survivorTransport_seq (a : PactTypeAlphabet) (left right : PactType)
    (hLeft : SurvivorTransport left) (hRight : SurvivorTransport right) :
    SurvivorTransport (.seq a left right) := by
  intro bound hWF target hTargetWF hAvoid rho q hRelated
  obtain ⟨hWFL, hWFR⟩ := typeWellFormedIn_seq hWF
  simp only [PactType.ParallelInterfaces, Finset.mem_union, not_or] at hAvoid
  rcases relationMembership_seq_cases a left right hRelated with
    ⟨q1, residualLeft, hEntry, hChild, hKept⟩ | ⟨q2, hState, hChild⟩
  · rw [Prod.ext_iff] at hEntry
    obtain ⟨hRho, hQ⟩ := hEntry
    simp only at hRho hQ
    subst hRho
    subst hQ
    obtain ⟨theta, hMem, hLive⟩ := hLeft bound hWFL target hTargetWF
      (fun act hAct => (hAvoid act hAct).1) residualLeft q1 hChild
    refine ⟨.seq target theta (right.reannotate target), ?_, ?_⟩
    · have hKept' : q1 ∉ sequenceDeleted
          (compileTypeFuel
            (typeCompilationFuel (left.reannotate target))
            (left.reannotate target)) := by
        rw [sequenceDeleted_reannotate
          (offerBranchesDisjoint_of_wellFormedIn hWFL) target]
        simp only [sequenceDeleted, Finset.mem_sdiff, Finset.mem_singleton,
          not_and, not_not]
        intro hAccepting
        rcases hKept with hNot | hInit
        · exact absurd (by simpa [compileType] using hAccepting) hNot
        · simpa [compileType] using hInit
      simpa only [PactType.reannotate] using
        relationMembership_seq_left_of_not_deleted target
          (left.reannotate target) (right.reannotate target) theta hMem hKept'
    · refine ⟨?_, ?_⟩
      · simp only [PactType.reannotate, PactType.alphabet]
      · simp only [PactType.reannotate, PactType.LiveEqBody]
        exact ⟨PactTypeAlphabet.AgreeOn.refl _ _, hLive.2,
          PactType.liveEqBody_refl _⟩
  · simp only at hState hChild
    subst hState
    obtain ⟨theta, hMem, hLive⟩ := hRight bound hWFR target hTargetWF
      (fun act hAct => (hAvoid act hAct).2) rho q2 hChild
    refine ⟨theta, ?_, hLive⟩
    simpa only [PactType.reannotate] using
      relationMembership_seq_right target (left.reannotate target)
        (right.reannotate target) theta hMem


/-- A member of a well-formed branch list carries the list's alphabet. -/
theorem branchesAlphabetWellFormed_of_mem {alphabet : PactTypeAlphabet}
    {branches : List (BareMessage × PactType)}
    (hBranches : PactType.BranchesAlphabetWellFormed alphabet branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    branch.2.alphabet = alphabet ∧ branch.2.AlphabetWellFormed := by
  induction branches with
  | nil => exact absurd hMem (List.not_mem_nil)
  | cons head rest restIH =>
      rcases head with ⟨action, body⟩
      simp only [PactType.BranchesAlphabetWellFormed] at hBranches
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact ⟨hBranches.1, hBranches.2.1⟩
      · exact restIH hBranches.2.2 hRest

set_option maxHeartbeats 1000000 in
/-- Every residual of an alphabet-well-formed type carries that type's
alphabet. -/
theorem relationMembership_alphabet_eq_of_wellFormed :
    ∀ (source residual : PactType) (state : TypeAutomatonState),
      source.AlphabetWellFormed →
      relationMembership (buildRelationSet source (compileType source))
        residual state →
      residual.alphabet = source.alphabet := by
  intro source
  induction hFuel : typeCompilationFuel source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
      intro residual state hWF hRelated
      cases source with
      | skip alphabet =>
          rw [(relationMembership_skip_cases alphabet hRelated).1]
      | message alphabet msg dir =>
          rcases relationMembership_message_cases alphabet msg dir
              hRelated with hRoot | hFinal
          · rw [hRoot.1]
          · rw [hFinal.1]; simp only [PactType.alphabet]
      | tock alphabet =>
          rcases relationMembership_tock_cases alphabet hRelated with
            hRoot | hFinal
          · rw [hRoot.1]
          · rw [hFinal.1]; simp only [PactType.alphabet]
      | progress alphabet pid =>
          rcases relationMembership_progress_cases alphabet pid
              hRelated with hRoot | hFinal
          · rw [hRoot.1]
          · rw [hFinal.1]; simp only [PactType.alphabet]
      | var alphabet other =>
          rw [(relationMembership_var_cases alphabet other hRelated).1]
      | choice alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          rcases relationMembership_choice_cases alphabet left right
              hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hWF.2.2.2.1 hLeftRelated).trans hWF.2.1
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel right) hRightFuel right rfl residual
              q hWF.2.2.2.2 hRightRelated).trans hWF.2.2.1
      | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          rcases relationMembership_fairChoice_cases alphabet bid left
              right hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hWF.2.2.2.1 hLeftRelated).trans hWF.2.1
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel right) hRightFuel right rfl residual
              q hWF.2.2.2.2 hRightRelated).trans hWF.2.2.1
      | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          rcases relationMembership_seq_cases alphabet left right
              hRelated with hLeft | hRight
          · rcases hLeft with ⟨q, leftResidual, hEntry, hLeftRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]; simp only [PactType.alphabet]
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel right) hRightFuel right rfl residual
              q hWF.2.2.2.2 hRightRelated).trans hWF.2.2.1
      | par alphabet left right interface =>
          rcases relationMembership_par_cases alphabet left right
              interface hRelated with hPair | hSurvL | hSurvR | hFinal
          · rcases hPair with ⟨q1, q2, leftResidual, rightResidual,
              hEntry, hLeftRelated, hRightRelated⟩
            injection hEntry with hResidual _
            rw [hResidual]; simp only [PactType.alphabet]
          · rcases hSurvL with ⟨q1, residualLeft, hEntry, hLeftRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual,
              (reannotate_relation_alphabet
                  (typeCompilationFuel (left.reannotate alphabet))).1
                alphabet left residualLeft q1 hLeftRelated]
            simp only [PactType.alphabet]
          · rcases hSurvR with ⟨q2, residualRight, hEntry, hRightRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual,
              (reannotate_relation_alphabet
                  (typeCompilationFuel (right.reannotate alphabet))).1
                alphabet right residualRight q2 hRightRelated]
            simp only [PactType.alphabet]
          · injection hFinal with hResidual _
            rw [hResidual]; simp only [PactType.alphabet]
      | recur alphabet binder body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          rcases relationMembership_recur_cases alphabet binder body
              hRelated with hRoot | hBody
          · injection hRoot with hResidual _
            rw [hResidual]
          · rcases hBody with ⟨q, bodyResidual, hEntry, hBodyRelated⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hBodyFuel : typeCompilationFuel body < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            have hBodyAlpha : bodyResidual.alphabet = body.alphabet :=
              ih (typeCompilationFuel body) hBodyFuel body rfl bodyResidual q
                hWF.2.2 hBodyRelated
            have hRepl : (PactType.recur alphabet binder body).alphabet =
                bodyResidual.alphabet := by
              rw [hBodyAlpha]; exact hWF.2.1.symm
            rw [PactType.replaceVar_alphabet_eq_of_replacement bodyResidual
              binder hRepl]
            exact hBodyAlpha.trans hWF.2.1
      | xoffer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          rcases relationMembership_xoffer_cases alphabet elseType
              branches hRelated with hRoot | hElse | hBranch
          · injection hRoot with hResidual _
            rw [hResidual]
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hWF.2.2.1 hElseRelated).trans hWF.2.1
          · rcases hBranch with ⟨i, action, branchType, q, hGet, _,
              hBranchRelated⟩
            have hMember : (action, branchType) ∈ branches :=
              List.mem_of_getElem? hGet
            have hBranchFuel : typeCompilationFuel branchType < n := by
              have hLe : typeCompilationFuel branchType ≤
                  typeBranchCompilationFuel branches := by
                simpa using typeCompilationFuel_le_typeBranchCompilationFuel
                  branches (action, branchType) hMember
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            have hBranchWF := branchesAlphabetWellFormed_of_mem
              hWF.2.2.2 hMember
            exact (ih (typeCompilationFuel branchType) hBranchFuel branchType
              rfl residual q hBranchWF.2 hBranchRelated).trans hBranchWF.1
      | offer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          rcases relationMembership_offer_cases alphabet elseType
              branches hRelated with hRoot | hElse | hSelected
          · injection hRoot with hResidual _
            rw [hResidual]
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hWF.2.2.1 hElseRelated).trans hWF.2.1
          · rcases hSelected with ⟨i, selected, q, hGet, _, hSelectedRelated⟩
            have hMember : selected ∈ branches := List.mem_of_getElem? hGet
            cases branches with
            | nil => cases hMember
            | cons branch rest =>
                exact (reannotate_relation_alphabet
                    (typeCompilationFuel
                      (parallelTypeBranchesSelecting alphabet selected
                        (branch :: rest)))).2
                  alphabet selected branch rest residual q hSelectedRelated


/-- Lift a pair of child relation states into the product clause. -/
theorem relationMembership_par_product (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {leftResidual rightResidual : PactType}
    {leftState rightState : TypeAutomatonState}
    (hLeft : relationMembership (buildRelationSet left (compileType left))
      leftResidual leftState)
    (hRight : relationMembership (buildRelationSet right (compileType right))
      rightResidual rightState) :
    relationMembership
      (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface)))
      (.par alphabet leftResidual rightResidual interface)
      (.pair leftState rightState) := by
  have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  show ((.par alphabet leftResidual rightResidual interface : PactType),
    TypeAutomatonState.pair leftState rightState) ∈
    buildRelationSetCoreFuel
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel]
  refine Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
  refine Finset.mem_image.mpr ⟨((leftResidual, leftState),
    (rightResidual, rightState)), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
  · rw [buildRelationSetCoreFuel_eq_of_sufficient left (le_max_left _ _) le_rfl]
    exact hLeft
  · rw [buildRelationSetCoreFuel_eq_of_sufficient right (le_max_right _ _)
      le_rfl]
    exact hRight

/-- The projection reads the child only through the actions being compared,
so agreeing child alphabets give agreeing projections. -/
theorem agreeOn_projectParallel_of_actions
    {parent childA childB : PactTypeAlphabet}
    {interface : Interface} {used : Finset BareMessage}
    (hChild : PactTypeAlphabet.AgreeOn childA childB used) :
    PactTypeAlphabet.AgreeOn
      (PactTypeAlphabet.projectParallel parent childA interface)
      (PactTypeAlphabet.projectParallel parent childB interface)
      used := by
  intro action hAction
  simp only [PactTypeAlphabet.projectParallel, Finset.mem_union,
    Finset.mem_filter, hChild action hAction]

/-- Re-signing leaves the accepting states alone. -/
theorem accepting_reannotate {processType : PactType}
    (hDisjoint : processType.OfferBranchesDisjoint)
    (alphabet : PactTypeAlphabet) :
    (compileTypeFuel (typeCompilationFuel (processType.reannotate alphabet))
        (processType.reannotate alphabet)).accepting =
      (compileTypeFuel (typeCompilationFuel processType) processType).accepting := by
  have hShape := CompiledShape.compileTypeFuel_shapeEq_reannotate
    (typeCompilationFuel processType) processType hDisjoint alphabet
  rw [typeCompilationFuel_reannotate]
  exact hShape.2.2


set_option maxHeartbeats 1000000 in
theorem survivorTransport_par (a : PactTypeAlphabet) (left right : PactType)
    (interface : Interface) (hLeft : SurvivorTransport left)
    (hRight : SurvivorTransport right)
    (hSurvLeft : SurvivorTransport (left.reannotate a))
    (hSurvRight : SurvivorTransport (right.reannotate a)) :
    SurvivorTransport (.par a left right interface) := by
  intro bound hWF target hTargetWF hAvoid rho q hRelated
  obtain ⟨hWFL, hWFR⟩ := typeWellFormedIn_par hWF
  obtain ⟨hWFsL, hWFsR⟩ := typeWellFormedIn_survivor hWF
  obtain ⟨hA, -, -, -, -, -, -, -, -, hMO, -, -, hIS, hIAS, -⟩ := id hWF
  simp only [PactType.AlphabetWellFormed] at hA
  simp only [PactType.ParallelMessageOwnership] at hMO
  simp only [PactType.InterfaceScoped] at hIS
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  simp only [PactType.ParallelInterfaces, Finset.mem_union, not_or] at hAvoid
  have hDisjLeft : left.OfferBranchesDisjoint :=
    offerBranchesDisjoint_of_wellFormedIn hWFL
  have hDisjRight : right.OfferBranchesDisjoint :=
    offerBranchesDisjoint_of_wellFormedIn hWFR
  have hTargetHidden : ∀ act ∈ target.actions, act.1 ∉ interface :=
    fun act hAct => (hAvoid act hAct).1.1
  have hLeftAlphaWF : left.alphabet.WellFormed :=
    PactType.AlphabetWellFormed.alphabet_wellFormed hA.2.2.1
  have hRightAlphaWF : right.alphabet.WellFormed :=
    PactType.AlphabetWellFormed.alphabet_wellFormed hA.2.2.2
  have hOmegaLWF :
      (PactTypeAlphabet.projectParallel target left.alphabet interface).WellFormed :=
    PactTypeAlphabet.projectParallel_wellFormed hLeftAlphaWF hTargetWF
      hTargetHidden
  have hOmegaRWF :
      (PactTypeAlphabet.projectParallel target right.alphabet interface).WellFormed :=
    PactTypeAlphabet.projectParallel_wellFormed hRightAlphaWF hTargetWF
      hTargetHidden
  have hAvoidL : ∀ act ∈ (PactTypeAlphabet.projectParallel target left.alphabet interface).actions,
      act.1 ∉ PactType.ParallelInterfaces left := by
    intro act hAct
    simp only [PactTypeAlphabet.projectParallel, Finset.mem_union,
      Finset.mem_filter] at hAct
    rcases hAct with ⟨hIn, -⟩ | hIn
    · exact PactType.InterfaceAlphabetScoped.avoids hIAS.2.1 act hIn
    · exact (hAvoid act hIn).1.2
  have hAvoidR : ∀ act ∈ (PactTypeAlphabet.projectParallel target right.alphabet interface).actions,
      act.1 ∉ PactType.ParallelInterfaces right := by
    intro act hAct
    simp only [PactTypeAlphabet.projectParallel, Finset.mem_union,
      Finset.mem_filter] at hAct
    rcases hAct with ⟨hIn, -⟩ | hIn
    · exact PactType.InterfaceAlphabetScoped.avoids hIAS.2.2 act hIn
    · exact (hAvoid act hIn).2
  rcases relationMembership_par_cases a left right interface hRelated with
    hPair | hSurvL | hSurvR | hDone
  · obtain ⟨q1, q2, rhoL, rhoR, hEntry, hL, hR⟩ := hPair
    injection hEntry with hRho hQ
    subst hRho
    subst hQ
    obtain ⟨thetaL, hMemL, hLiveL⟩ := hLeft bound hWFL _ hOmegaLWF hAvoidL
      rhoL q1 hL
    obtain ⟨thetaR, hMemR, hLiveR⟩ := hRight bound hWFR _ hOmegaRWF hAvoidR
      rhoR q2 hR
    have hAlphaL : rhoL.alphabet = left.alphabet :=
      relationMembership_alphabet_eq_of_wellFormed left rhoL q1 hA.2.2.1 hL
    have hAlphaR : rhoR.alphabet = right.alphabet :=
      relationMembership_alphabet_eq_of_wellFormed right rhoR q2 hA.2.2.2 hR
    have hActL : PactType.MessageActions rhoL ⊆ PactType.MessageActions left :=
      (relationMembership_ownership_subset left rhoL q1 hL).1
    have hActR : PactType.MessageActions rhoR ⊆ PactType.MessageActions right :=
      (relationMembership_ownership_subset right rhoR q2 hR).1
    have hAgreeL := agreeOn_projectParallel_of_actions
      (parent := target) (childA := rhoL.alphabet) (childB := left.alphabet)
      (interface := interface) (used := PactType.MessageActions rhoL)
      (by rw [hAlphaL]; exact PactTypeAlphabet.AgreeOn.refl _ _)
    have hAgreeR := agreeOn_projectParallel_of_actions
      (parent := target) (childA := rhoR.alphabet) (childB := right.alphabet)
      (interface := interface) (used := PactType.MessageActions rhoR)
      (by rw [hAlphaR]; exact PactTypeAlphabet.AgreeOn.refl _ _)
    refine ⟨.par target thetaL thetaR interface, ?_, ?_, ?_⟩
    · simpa only [PactType.reannotate] using
        relationMembership_par_product target
          (left.reannotate (PactTypeAlphabet.projectParallel target left.alphabet interface))
          (right.reannotate (PactTypeAlphabet.projectParallel target right.alphabet interface)) interface hMemL hMemR
    · simp only [PactType.reannotate, PactType.alphabet]
    · simp only [PactType.reannotate, PactType.LiveEqBody]
      refine ⟨trivial, PactTypeAlphabet.AgreeOn.refl _ _, ?_, ?_⟩
      · exact PactType.liveEqBody_trans
          (liveEqBody_reannotate hAgreeL (PactType.liveEqBody_refl rhoL))
          hLiveL.2
      · exact PactType.liveEqBody_trans
          (liveEqBody_reannotate hAgreeR (PactType.liveEqBody_refl rhoR))
          hLiveR.2
  · obtain ⟨q1, residualLeft, hEntry, hChild, hNotAcc⟩ := hSurvL
    injection hEntry with hRho hQ
    subst hRho
    subst hQ
    have hAvoidSurv : ∀ act ∈ target.actions,
        act.1 ∉ PactType.ParallelInterfaces (left.reannotate a) := by
      intro act hAct
      rw [PactType.reannotate_parallelInterfaces]
      exact (hAvoid act hAct).1.2
    obtain ⟨theta, hMem, hLive⟩ := hSurvLeft bound hWFsL target hTargetWF
      hAvoidSurv rho q1 hChild
    refine ⟨theta, ?_, hLive⟩
    have hReWF : (left.reannotate (PactTypeAlphabet.projectParallel target left.alphabet interface)).AlphabetWellFormed :=
      PactType.reannotate_alphabetWellFormed_avoiding left _ hA.2.2.1
        hOmegaLWF hIS.2.1 hAvoidL
    have hC1 : (left.reannotate a).reannotate target =
        left.reannotate target :=
      PactType.reannotate_reannotate left a target hA.2.2.1 hWFsL.1
    have hC2 : (left.reannotate (PactTypeAlphabet.projectParallel target left.alphabet interface)).reannotate target =
        left.reannotate target :=
      PactType.reannotate_reannotate left _ target hA.2.2.1 hReWF
    have hNotS : q1 ∉
        (compileTypeFuel (typeCompilationFuel left) left).accepting := by
      intro hIn
      exact hNotAcc (by
        simpa only [compileType, accepting_reannotate hDisjLeft a] using hIn)
    refine (by
      simpa only [PactType.reannotate] using
        survivorLeft_relationMembership target
          (left.reannotate (PactTypeAlphabet.projectParallel target left.alphabet interface))
          (right.reannotate (PactTypeAlphabet.projectParallel target right.alphabet interface)) interface
          (reannotate_offerBranchesDisjoint left _ hDisjLeft)
          (by rw [hC2, ← hC1]; exact hMem)
          (by rw [accepting_reannotate hDisjLeft _]; exact hNotS))
  · obtain ⟨q2, residualRight, hEntry, hChild, hNotAcc⟩ := hSurvR
    injection hEntry with hRho hQ
    subst hRho
    subst hQ
    have hAvoidSurv : ∀ act ∈ target.actions,
        act.1 ∉ PactType.ParallelInterfaces (right.reannotate a) := by
      intro act hAct
      rw [PactType.reannotate_parallelInterfaces]
      exact (hAvoid act hAct).2
    obtain ⟨theta, hMem, hLive⟩ := hSurvRight bound hWFsR target hTargetWF
      hAvoidSurv rho q2 hChild
    refine ⟨theta, ?_, hLive⟩
    have hReWF : (right.reannotate
        (PactTypeAlphabet.projectParallel target right.alphabet interface)).AlphabetWellFormed :=
      PactType.reannotate_alphabetWellFormed_avoiding right _ hA.2.2.2
        hOmegaRWF hIS.2.2 hAvoidR
    have hC1 : (right.reannotate a).reannotate target =
        right.reannotate target :=
      PactType.reannotate_reannotate right a target hA.2.2.2 hWFsR.1
    have hC2 : (right.reannotate (PactTypeAlphabet.projectParallel target right.alphabet interface)).reannotate target =
        right.reannotate target :=
      PactType.reannotate_reannotate right _ target hA.2.2.2 hReWF
    have hNotS : q2 ∉
        (compileTypeFuel (typeCompilationFuel right) right).accepting := by
      intro hIn
      exact hNotAcc (by
        simpa only [compileType, accepting_reannotate hDisjRight a] using hIn)
    refine (by
      simpa only [PactType.reannotate] using
        survivorRight_relationMembership target
          (left.reannotate (PactTypeAlphabet.projectParallel target left.alphabet interface))
          (right.reannotate (PactTypeAlphabet.projectParallel target right.alphabet interface)) interface
          (reannotate_offerBranchesDisjoint right _ hDisjRight)
          (by rw [hC2, ← hC1]; exact hMem)
          (by rw [accepting_reannotate hDisjRight _]; exact hNotS))
  · injection hDone with hRho hQ
    subst hRho
    subst hQ
    refine ⟨PactType.skip target, ?_, ?_⟩
    · simpa only [PactType.reannotate] using
        relationMembership_par_final target
          (left.reannotate (PactTypeAlphabet.projectParallel target left.alphabet interface))
          (right.reannotate (PactTypeAlphabet.projectParallel target right.alphabet interface)) interface
    · simpa only [PactType.reannotate] using PactType.liveEq_refl
        (PactType.skip target)

end


/-- Survivor target transport, for every type.  The induction runs on
`typeCompilationFuel` rather than `sizeOf`: re-signing preserves it, which the
parallel case needs, and the conjunctive branch product sits strictly below the
offer that generates it, which the conjunctive case needs. -/
theorem survivorTransport_all
    : ∀ processType : PactType, SurvivorTransport processType := by
  intro processType
  induction hFuel : typeCompilationFuel processType
      using Nat.strong_induction_on generalizing processType with
  | _ n ih =>
      subst hFuel
      cases processType with
      | skip alphabet => exact survivorTransport_skip alphabet
      | var alphabet name => exact survivorTransport_var alphabet name
      | message alphabet msg dir =>
          exact survivorTransport_message alphabet msg dir
      | tock alphabet => exact survivorTransport_tock alphabet
      | progress alphabet pid => exact survivorTransport_progress alphabet pid
      | choice alphabet left right =>
          refine survivorTransport_choice alphabet left right
            (ih _ ?_ left rfl) (ih _ ?_ right rfl) <;>
            simp only [typeCompilationFuel] <;> omega
      | fairChoice alphabet bid left right =>
          refine survivorTransport_fairChoice alphabet bid left right
            (ih _ ?_ left rfl) (ih _ ?_ right rfl) <;>
            simp only [typeCompilationFuel] <;> omega
      | seq alphabet left right =>
          refine survivorTransport_seq alphabet left right
            (ih _ ?_ left rfl) (ih _ ?_ right rfl) <;>
            simp only [typeCompilationFuel] <;> omega
      | recur alphabet name body =>
          refine survivorTransport_recur alphabet name body
            (ih _ ?_ body rfl)
          simp only [typeCompilationFuel]; omega
      | par alphabet left right interface =>
          refine survivorTransport_par alphabet left right interface
            (ih _ ?_ left rfl) (ih _ ?_ right rfl)
            (ih _ ?_ (left.reannotate alphabet) rfl)
            (ih _ ?_ (right.reannotate alphabet) rfl) <;>
            simp only [typeCompilationFuel, typeCompilationFuel_reannotate] <;>
            omega
      | xoffer alphabet elseType branches =>
          refine survivorTransport_xoffer alphabet elseType branches
            (ih _ ?_ elseType rfl) (fun entry hEntry => ih _ ?_ entry.2 rfl)
          · simp only [typeCompilationFuel]; omega
          · have hLe : typeCompilationFuel entry.2 ≤
                typeBranchCompilationFuel branches :=
              typeCompilationFuel_le_typeBranchCompilationFuel branches entry hEntry
            simp only [typeCompilationFuel]
            omega
      | offer alphabet elseType branches =>
          refine survivorTransport_offer alphabet elseType branches
            (ih _ ?_ elseType rfl) (fun selected hSelected => ih _ ?_ _ rfl)
          · simp only [typeCompilationFuel]; omega
          · rw [typeCompilationFuel_parallelTypeBranchesSelecting]
            simp only [typeCompilationFuel]
            omega


end Pact
