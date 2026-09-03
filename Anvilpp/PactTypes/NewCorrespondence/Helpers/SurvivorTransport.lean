import Anvilpp.PactTypes.NewCorrespondence.Simultaneous

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

/-- Projecting to the left child twice keeps only the outer alphabet, provided
the intermediate one declares no interface action. -/
theorem projectParallelLeft_reannotate
    {parent child sibling source target : PactTypeAlphabet}
    {leftType rightType : PactType} {interface : Interface}
    (hCompat : ParallelCompatible parent child sibling leftType rightType
      interface)
    (hSourceHidden : ∀ action ∈ source.actions, action.1 ∉ interface) :
    projectParallelLeft target
        (projectParallelLeft source child rightType interface) rightType
        interface =
      projectParallelLeft target child rightType interface := by
  refine congrArg PactTypeAlphabet.mk (Finset.ext fun action => ?_)
  simp only [projectParallelLeft, projectParallelChild, Finset.mem_union,
    Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro (⟨hSU, hOuter⟩ | hOut)
    · rcases hSU with ⟨hChild, _⟩ | ⟨hSource, hNotRight⟩
      · exact Or.inl ⟨hChild, hOuter⟩
      · rcases hOuter with hIface | hOuter
        · exact absurd hIface (hSourceHidden action hSource)
        · exact Or.inr ⟨hOuter, hNotRight⟩
    · exact Or.inr hOut
  · rintro (⟨hChild, hOuter⟩ | hOut)
    · rcases hOuter with hIface | hTarget
      · exact Or.inl ⟨Or.inl ⟨hChild, Or.inl hIface⟩, Or.inl hIface⟩
      · by_cases hIface : action.1 ∈ interface
        · exact Or.inl ⟨Or.inl ⟨hChild, Or.inl hIface⟩, Or.inl hIface⟩
        · have hHide : action ∈ (hideInterface child interface).actions := by
            simp only [hideInterface, Finset.mem_filter]
            exact ⟨hChild, hIface⟩
          rw [← hCompat.parent_left, Finset.mem_sdiff] at hHide
          exact Or.inr ⟨hTarget, hHide.2⟩
    · exact Or.inr hOut

/-- Mirror of `projectParallelLeft_reannotate` for the right child. -/
theorem projectParallelRight_reannotate
    {parent child sibling source target : PactTypeAlphabet}
    {leftType rightType : PactType} {interface : Interface}
    (hCompat : ParallelCompatible parent sibling child leftType rightType
      interface)
    (hSourceHidden : ∀ action ∈ source.actions, action.1 ∉ interface) :
    projectParallelRight target
        (projectParallelRight source child leftType interface) leftType
        interface =
      projectParallelRight target child leftType interface := by
  refine congrArg PactTypeAlphabet.mk (Finset.ext fun action => ?_)
  simp only [projectParallelRight, projectParallelChild, Finset.mem_union,
    Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro (⟨hSU, hOuter⟩ | hOut)
    · rcases hSU with ⟨hChild, _⟩ | ⟨hSource, hNotLeft⟩
      · exact Or.inl ⟨hChild, hOuter⟩
      · rcases hOuter with hIface | hOuter
        · exact absurd hIface (hSourceHidden action hSource)
        · exact Or.inr ⟨hOuter, hNotLeft⟩
    · exact Or.inr hOut
  · rintro (⟨hChild, hOuter⟩ | hOut)
    · rcases hOuter with hIface | hTarget
      · exact Or.inl ⟨Or.inl ⟨hChild, Or.inl hIface⟩, Or.inl hIface⟩
      · by_cases hIface : action.1 ∈ interface
        · exact Or.inl ⟨Or.inl ⟨hChild, Or.inl hIface⟩, Or.inl hIface⟩
        · have hHide : action ∈ (hideInterface child interface).actions := by
            simp only [hideInterface, Finset.mem_filter]
            exact ⟨hChild, hIface⟩
          rw [← hCompat.parent_right, Finset.mem_sdiff] at hHide
          exact Or.inr ⟨hTarget, hHide.2⟩
    · exact Or.inr hOut

/-- The left projection reads the sibling only through its message actions. -/
theorem projectParallelLeft_congr (parent child : PactTypeAlphabet)
    (rightType rightType' : PactType) (interface : Interface)
    (h : PactType.MessageActions rightType =
      PactType.MessageActions rightType') :
    projectParallelLeft parent child rightType interface =
      projectParallelLeft parent child rightType' interface := by
  simp only [projectParallelLeft, h]

/-- The right projection reads the sibling only through its message actions. -/
theorem projectParallelRight_congr (parent child : PactTypeAlphabet)
    (leftType leftType' : PactType) (interface : Interface)
    (h : PactType.MessageActions leftType =
      PactType.MessageActions leftType') :
    projectParallelRight parent child leftType interface =
      projectParallelRight parent child leftType' interface := by
  simp only [projectParallelRight, h]

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
            simp only [OfferBranchesWellFormed, messageActions_reannotate,
              branchMessageActions_reannotateOfferBranches] at hWF hWF'
            simp only [messageActions_reannotate,
              branchMessageActions_reannotateOfferBranches]
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
          have hLeftProj := PactTypeAlphabet.projectParallelLeft_reannotate
            (parent := a) (child := left.alphabet) (sibling := right.alphabet)
            (source := source) (target := target) (leftType := left)
            (rightType := right) hWF.2.1 hHidden
          have hRightProj := PactTypeAlphabet.projectParallelRight_reannotate
            (parent := a) (child := right.alphabet) (sibling := left.alphabet)
            (source := source) (target := target) (leftType := left)
            (rightType := right) hWF.2.1 hHidden
          simp only [reannotate_alphabet]
          rw [PactTypeAlphabet.projectParallelLeft_congr _ _ _ right _
              (messageActions_reannotate _ right),
            PactTypeAlphabet.projectParallelRight_congr _ _ _ left _
              (messageActions_reannotate _ left),
            hLeftProj, hRightProj,
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


/-- Offer-branch disjointness is one of the ownership consequences carried by
`TypeWellFormedIn`. -/
theorem offerBranchesDisjoint_of_wellFormedIn {bound : List String}
    {processType : PactType} (h : TypeWellFormedIn bound processType) :
    processType.OfferBranchesDisjoint := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hMO, hPO, hFO, -, -⟩ := h
  exact offerBranchesDisjoint_of_ownership processType hMO hPO hFO

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

/-- The left projection only reads the sibling's message actions, so agreeing
child alphabets and matching sibling actions give agreeing projections. -/
theorem agreeOn_projectParallelLeft_of_actions
    {parent childA childB : PactTypeAlphabet} {rA rB : PactType}
    {interface : Interface} {used : Finset BareMessage}
    (hChild : PactTypeAlphabet.AgreeOn childA childB used)
    (hSibling : ∀ action ∈ used,
      (action ∈ PactType.MessageActions rA ↔
        action ∈ PactType.MessageActions rB)) :
    PactTypeAlphabet.AgreeOn
      (PactTypeAlphabet.projectParallelLeft parent childA rA interface)
      (PactTypeAlphabet.projectParallelLeft parent childB rB interface)
      used := by
  intro action hAction
  simp only [PactTypeAlphabet.projectParallelLeft,
    PactTypeAlphabet.projectParallelChild, Finset.mem_union, Finset.mem_filter,
    Finset.mem_sdiff, hChild action hAction, hSibling action hAction]

/-- Mirror of `agreeOn_projectParallelLeft_of_actions`. -/
theorem agreeOn_projectParallelRight_of_actions
    {parent childA childB : PactTypeAlphabet} {lA lB : PactType}
    {interface : Interface} {used : Finset BareMessage}
    (hChild : PactTypeAlphabet.AgreeOn childA childB used)
    (hSibling : ∀ action ∈ used,
      (action ∈ PactType.MessageActions lA ↔
        action ∈ PactType.MessageActions lB)) :
    PactTypeAlphabet.AgreeOn
      (PactTypeAlphabet.projectParallelRight parent childA lA interface)
      (PactTypeAlphabet.projectParallelRight parent childB lB interface)
      used := by
  intro action hAction
  simp only [PactTypeAlphabet.projectParallelRight,
    PactTypeAlphabet.projectParallelChild, Finset.mem_union, Finset.mem_filter,
    Finset.mem_sdiff, hChild action hAction, hSibling action hAction]

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
  obtain ⟨hA, -, -, -, -, -, -, -, -, hMO, -, -, hIS, hIAS⟩ := id hWF
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
      (PactTypeAlphabet.projectParallelLeft target left.alphabet right
        interface).WellFormed :=
    PactTypeAlphabet.projectParallelLeft_wellFormed hLeftAlphaWF hTargetWF
      hTargetHidden
  have hOmegaRWF :
      (PactTypeAlphabet.projectParallelRight target right.alphabet left
        interface).WellFormed :=
    PactTypeAlphabet.projectParallelRight_wellFormed hRightAlphaWF hTargetWF
      hTargetHidden
  have hAvoidL : ∀ act ∈ (PactTypeAlphabet.projectParallelLeft target
      left.alphabet right interface).actions,
      act.1 ∉ PactType.ParallelInterfaces left := by
    intro act hAct
    simp only [PactTypeAlphabet.projectParallelLeft,
      PactTypeAlphabet.projectParallelChild, Finset.mem_union,
      Finset.mem_filter, Finset.mem_sdiff] at hAct
    rcases hAct with ⟨hIn, -⟩ | ⟨hIn, -⟩
    · exact PactType.InterfaceAlphabetScoped.avoids hIAS.2.1 act hIn
    · exact (hAvoid act hIn).1.2
  have hAvoidR : ∀ act ∈ (PactTypeAlphabet.projectParallelRight target
      right.alphabet left interface).actions,
      act.1 ∉ PactType.ParallelInterfaces right := by
    intro act hAct
    simp only [PactTypeAlphabet.projectParallelRight,
      PactTypeAlphabet.projectParallelChild, Finset.mem_union,
      Finset.mem_filter, Finset.mem_sdiff] at hAct
    rcases hAct with ⟨hIn, -⟩ | ⟨hIn, -⟩
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
    have hSibL : ∀ action ∈ PactType.MessageActions rhoL,
        (action ∈ PactType.MessageActions rhoR ↔
          action ∈ PactType.MessageActions right) := by
      intro action hAction
      have hNot : action ∉ PactType.MessageActions right :=
        Finset.disjoint_left.mp hMO.2.1 (hActL hAction)
      exact ⟨fun h => absurd (hActR h) hNot, fun h => absurd h hNot⟩
    have hSibR : ∀ action ∈ PactType.MessageActions rhoR,
        (action ∈ PactType.MessageActions rhoL ↔
          action ∈ PactType.MessageActions left) := by
      intro action hAction
      have hNot : action ∉ PactType.MessageActions left :=
        Finset.disjoint_right.mp hMO.2.1 (hActR hAction)
      exact ⟨fun h => absurd (hActL h) hNot, fun h => absurd h hNot⟩
    have hAgreeL := agreeOn_projectParallelLeft_of_actions
      (parent := target) (childA := rhoL.alphabet) (childB := left.alphabet)
      (rA := rhoR) (rB := right) (interface := interface)
      (by rw [hAlphaL]; exact PactTypeAlphabet.AgreeOn.refl _ _) hSibL
    have hAgreeR := agreeOn_projectParallelRight_of_actions
      (parent := target) (childA := rhoR.alphabet) (childB := right.alphabet)
      (lA := rhoL) (lB := left) (interface := interface)
      (by rw [hAlphaR]; exact PactTypeAlphabet.AgreeOn.refl _ _) hSibR
    refine ⟨.par target thetaL thetaR interface, ?_, ?_, ?_⟩
    · simpa only [PactType.reannotate] using
        relationMembership_par_product target
          (left.reannotate (PactTypeAlphabet.projectParallelLeft target
            left.alphabet right interface))
          (right.reannotate (PactTypeAlphabet.projectParallelRight target
            right.alphabet left interface)) interface hMemL hMemR
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
    have hReWF : (left.reannotate (PactTypeAlphabet.projectParallelLeft target
        left.alphabet right interface)).AlphabetWellFormed :=
      PactType.reannotate_alphabetWellFormed_avoiding left _ hA.2.2.1
        hOmegaLWF hIS.2.1 hAvoidL
    have hC1 : (left.reannotate a).reannotate target =
        left.reannotate target :=
      PactType.reannotate_reannotate left a target hA.2.2.1 hWFsL.1
    have hC2 : (left.reannotate (PactTypeAlphabet.projectParallelLeft target
          left.alphabet right interface)).reannotate target =
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
          (left.reannotate (PactTypeAlphabet.projectParallelLeft target
            left.alphabet right interface))
          (right.reannotate (PactTypeAlphabet.projectParallelRight target
            right.alphabet left interface)) interface
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
        (PactTypeAlphabet.projectParallelRight target right.alphabet left
          interface)).AlphabetWellFormed :=
      PactType.reannotate_alphabetWellFormed_avoiding right _ hA.2.2.2
        hOmegaRWF hIS.2.2 hAvoidR
    have hC1 : (right.reannotate a).reannotate target =
        right.reannotate target :=
      PactType.reannotate_reannotate right a target hA.2.2.2 hWFsR.1
    have hC2 : (right.reannotate (PactTypeAlphabet.projectParallelRight target
          right.alphabet left interface)).reannotate target =
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
          (left.reannotate (PactTypeAlphabet.projectParallelLeft target
            left.alphabet right interface))
          (right.reannotate (PactTypeAlphabet.projectParallelRight target
            right.alphabet left interface)) interface
          (reannotate_offerBranchesDisjoint right _ hDisjRight)
          (by rw [hC2, ← hC1]; exact hMem)
          (by rw [accepting_reannotate hDisjRight _]; exact hNotS))
  · injection hDone with hRho hQ
    subst hRho
    subst hQ
    refine ⟨PactType.skip target, ?_, ?_⟩
    · simpa only [PactType.reannotate] using
        relationMembership_par_final target
          (left.reannotate (PactTypeAlphabet.projectParallelLeft target
            left.alphabet right interface))
          (right.reannotate (PactTypeAlphabet.projectParallelRight target
            right.alphabet left interface)) interface
    · simpa only [PactType.reannotate] using PactType.liveEq_refl
        (PactType.skip target)

end

end Pact
