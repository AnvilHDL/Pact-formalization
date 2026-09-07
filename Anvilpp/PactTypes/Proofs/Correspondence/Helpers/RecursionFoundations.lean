import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.ExclusiveOffer
import Anvilpp.PactTypes.Proofs.Syntax.DeclaredCompletionLemmas

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-- Lift a body relation pair through the recursion substitution and child
state tag. -/
lemma relationMembership_recur_child
     (alphabet : PactTypeAlphabet)
    (name : String) (body residual : PactType)
    {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet body (compileType body)) residual state) :
    relationMembership
      (buildRelationSet (.recur alphabet name body)
        (compileType (.recur alphabet name body)))
      (residual.replaceVar name (.recur alphabet name body)) (.child 0 state) := by
  show (residual.replaceVar name (.recur alphabet name body), .child 0 state) ∈
    buildRelationSetCoreFuel
      (typeCompilationFuel (.recur alphabet name body))
      (.recur alphabet name body)
  have hFuelEq : typeCompilationFuel (.recur alphabet name body) =
      typeCompilationFuel body + 1 := by
    simp only [typeCompilationFuel]
    omega
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_image,
    Prod.mk.injEq]
  exact Or.inr ⟨(residual, state), hRelated, rfl, rfl⟩

def recurRelationShape
     (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.recur alphabet name body, TypeAutomatonState.root) ∨
    (∃ q residual,
      entry =
        (residual.replaceVar name (.recur alphabet name body), .child 0 q) ∧
      relationMembership (buildRelationSet body (compileType body))
        residual q)

/-- Proves every related recursion pair has the recursion shape. -/
lemma relationMembership_recur_cases
     (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.recur alphabet name body)
          (compileType (.recur alphabet name body)))
        residual state) :
    recurRelationShape alphabet name body (residual, state) := by
  have hFuelEq : typeCompilationFuel (.recur alphabet name body) =
      typeCompilationFuel body + 1 := by
    simp only [typeCompilationFuel]; omega
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel
        (typeCompilationFuel (.recur alphabet name body))
        (.recur alphabet name body) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel, Finset.mem_insert,
    Finset.mem_image, Prod.mk.injEq] at hMem
  rcases hMem with ⟨hResidual, hState⟩ |
      ⟨entry, hEntry, hResidual, hState⟩
  · exact Or.inl (Prod.ext hResidual hState)
  · have hBodyRelated : relationMembership
        (buildRelationSet body (compileType body))
        entry.1 entry.2 := hEntry
    exact Or.inr ⟨entry.2, entry.1,
      Prod.ext hResidual.symm hState.symm, hBodyRelated⟩

/-- Substitution rewrites branch bodies only, so any predicate reading just the
branch heads is invariant. -/
theorem PactType.typeBranchNeeds_replaceBranches
    (branches : List (BareMessage × PactType)) (name : String)
    (replacement : PactType) :
    typeBranchNeeds (PactType.replaceBranches branches name replacement) =
      typeBranchNeeds branches := by
  induction branches with
  | nil => simp [PactType.replaceBranches]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      simp only [PactType.replaceBranches, typeBranchNeeds, List.map_cons] at *
      simp [ih]

/-- Branch membership survives substitution, at the substituted body. -/
theorem PactType.mem_replaceBranches
    {branches : List (BareMessage × PactType)}
    {action : BareMessage} {branchType : PactType}
    (name : String) (replacement : PactType)
    (hMem : (action, branchType) ∈ branches) :
    (action, branchType.replaceVar name replacement) ∈
      PactType.replaceBranches branches name replacement := by
  induction branches with
  | nil => cases hMem
  | cons branch rest ih =>
      rcases branch with ⟨headAction, headType⟩
      simp only [PactType.replaceBranches, List.mem_cons] at hMem ⊢
      rcases hMem with hHead | hRest
      · injection hHead with hAction hType
        subst hAction; subst hType
        exact Or.inl rfl
      · exact Or.inr (ih hRest)

end

/-- The same-cycle menu under a finite-control reading of one recursion
variable: `menuValue` is the menu the variable stands for and `completeValue`
whether it completes before a clock.  The sequence clause needs the second
because the menu only enters the right operand when the left can finish. -/
def typeFutureOffersFuelSubst (name : String) (menuValue : Finset BareMessage)
    (completeValue : Bool) : Nat → PactType → Finset BareMessage
  | 0, _ => ∅
  | fuel + 1, processType =>
      match processType with
      | .message alphabet msg dir =>
          if (msg, dir) ∈ alphabet.actions then {(msg, dir)} else ∅
      | .progress _ _ | .tock _ | .skip _ => ∅
      | .var _ other => if name = other then menuValue else ∅
      | .recur _ other body =>
          if name = other then typeFutureOffersFuel fuel body
          else typeFutureOffersFuelSubst name menuValue completeValue fuel body
      | .choice _ left right | .fairChoice _ _ left right =>
          typeFutureOffersFuelSubst name menuValue completeValue fuel left ∪
            typeFutureOffersFuelSubst name menuValue completeValue fuel right
      | .seq _ left right =>
          let leftOffers :=
            typeFutureOffersFuelSubst name menuValue completeValue fuel left
          if PactType.canCompleteBeforeTockSubst name completeValue left.completionView then
            leftOffers ∪
              typeFutureOffersFuelSubst name menuValue completeValue fuel right
          else leftOffers
      | .par _ left right interface =>
          hideTypeOffers interface
            (typeFutureOffersFuelSubst name menuValue completeValue fuel left ∪
              typeFutureOffersFuelSubst name menuValue completeValue fuel right)
      | .xoffer alphabet elseType branches | .offer alphabet elseType branches =>
          (branches.foldl (fun offers branch =>
              offers ∪ {branch.1} ∪
                typeFutureOffersFuelSubst name menuValue completeValue fuel
                  branch.2)
              (typeFutureOffersFuelSubst name menuValue completeValue fuel
                elseType)) ∩ alphabet.actions

/-- Substitution rewrites branch bodies only, so an offer's alphabet gate reads
the same before and after. -/
theorem replaceBranches_gate (name : String) (replacement : PactType)
    (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      (∀ b ∈ PactType.replaceBranches branches name replacement,
        b.1 ∈ alphabet.actions) ↔
      (∀ b ∈ branches, b.1 ∈ alphabet.actions) := by
  intro branches
  induction branches with
  | nil => simp [PactType.replaceBranches]
  | cons b rest ih =>
      rcases b with ⟨action, branchType⟩
      simp only [PactType.replaceBranches, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨hHead, hRest⟩; exact ⟨hHead, ih.mp hRest⟩
      · rintro ⟨hHead, hRest⟩; exact ⟨hHead, ih.mpr hRest⟩

/-- The menu of a substituted type is the substituted menu.  This is the menu
counterpart of `replaceVar_canCompleteDeclared`. -/
theorem typeFutureOffersFuel_replaceVar (name : String) (replacement : PactType) :
    ∀ (fuel : Nat) (processType : PactType),
      sizeOf (processType.replaceVar name replacement) + 1 ≤ fuel →
      typeFutureOffersFuel fuel (processType.replaceVar name replacement) =
        typeFutureOffersFuelSubst name (typeFutureOffers replacement)
          replacement.CanCompleteDeclared fuel processType := by
  intro fuel
  induction fuel with
  | zero => intro processType hSize; exfalso; omega
  | succ fuel ih =>
      intro processType hSize
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf (PactType.replaceBranches branches name replacement) ≤ fuel →
          ∀ init : Finset BareMessage,
          (PactType.replaceBranches branches name replacement).foldl
              (fun offers branch =>
                offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2) init =
            branches.foldl (fun offers branch =>
              offers ∪ {branch.1} ∪
                typeFutureOffersFuelSubst name (typeFutureOffers replacement)
                  replacement.CanCompleteDeclared fuel branch.2) init := by
        intro branches
        induction branches with
        | nil => intro _ init; simp [PactType.replaceBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            intro hBranchSize init
            simp only [PactType.replaceBranches, List.cons.sizeOf_spec,
              Prod.mk.sizeOf_spec] at hBranchSize
            simp only [PactType.replaceBranches, List.foldl_cons]
            rw [ih branchType (by omega)]
            exact restIH (by omega) _
      cases processType with
      | message alphabet msg dir =>
          simp [PactType.replaceVar, typeFutureOffersFuel,
            typeFutureOffersFuelSubst]
      | progress alphabet pid =>
          simp [PactType.replaceVar, typeFutureOffersFuel,
            typeFutureOffersFuelSubst]
      | tock alphabet =>
          simp [PactType.replaceVar, typeFutureOffersFuel,
            typeFutureOffersFuelSubst]
      | skip alphabet =>
          simp [PactType.replaceVar, typeFutureOffersFuel,
            typeFutureOffersFuelSubst]
      | var alphabet other =>
          by_cases hName : name = other
          · subst hName
            simp only [PactType.replaceVar, typeFutureOffersFuelSubst]
            refine typeFutureOffersFuel_eq_typeFutureOffers replacement _ ?_
            simpa [PactType.replaceVar] using hSize
          · simp [PactType.replaceVar, typeFutureOffersFuel,
              typeFutureOffersFuelSubst, hName]
      | recur alphabet other body =>
          by_cases hName : name = other
          · simp [PactType.replaceVar, typeFutureOffersFuelSubst, hName,
              typeFutureOffersFuel]
          · simp only [PactType.replaceVar, hName, if_neg,
              not_false_iff] at hSize
            simp at hSize
            simp only [PactType.replaceVar, hName, if_neg, not_false_iff,
              typeFutureOffersFuel, typeFutureOffersFuelSubst]
            exact ih body (by omega)
      | choice alphabet left right =>
          simp only [PactType.replaceVar] at hSize
          simp at hSize
          simp only [PactType.replaceVar, typeFutureOffersFuel,
            typeFutureOffersFuelSubst]
          rw [ih left (by omega), ih right (by omega)]
      | fairChoice alphabet bid left right =>
          simp only [PactType.replaceVar] at hSize
          simp at hSize
          simp only [PactType.replaceVar, typeFutureOffersFuel,
            typeFutureOffersFuelSubst]
          rw [ih left (by omega), ih right (by omega)]
      | par alphabet left right interface =>
          simp only [PactType.replaceVar] at hSize
          simp at hSize
          simp only [PactType.replaceVar, typeFutureOffersFuel,
            typeFutureOffersFuelSubst]
          rw [ih left (by omega), ih right (by omega)]
      | seq alphabet left right =>
          simp only [PactType.replaceVar] at hSize
          simp at hSize
          simp only [PactType.replaceVar, typeFutureOffersFuel,
            typeFutureOffersFuelSubst]
          have hGate : typeCanCompleteThisCycleFuel fuel
              (left.replaceVar name replacement) =
            PactType.canCompleteBeforeTockSubst name
              replacement.CanCompleteDeclared left.completionView := by
            rw [typeCanCompleteThisCycleFuel_eq_canCompleteDeclared fuel
              (left.replaceVar name replacement) (by omega)]
            exact PactType.replaceVar_canCompleteDeclared name replacement left
          rw [ih left (by omega), ih right (by omega), hGate]
      | xoffer alphabet elseType branches =>
          simp only [PactType.replaceVar] at hSize
          simp at hSize
          simp only [PactType.replaceVar, typeFutureOffersFuel,
            typeFutureOffersFuelSubst]
          rw [ih elseType (by omega), hBranches branches (by omega)]
      | offer alphabet elseType branches =>
          simp only [PactType.replaceVar] at hSize
          simp at hSize
          simp only [PactType.replaceVar, typeFutureOffersFuel,
            typeFutureOffersFuelSubst]
          rw [ih elseType (by omega), hBranches branches (by omega)]

#print axioms typeFutureOffersFuel_replaceVar


/-- The same-cycle menu of `processType` traverses a tail occurrence of `name`.
This is the syntactic side of "a marker source is reachable before the next
clock": the sequence clause advances only when the left can finish, exactly as
same-cycle reachability stops at a clock edge. -/
def menuReachesVarFuel (name : String) (completeValue : Bool) :
    Nat → PactType → Bool
  | 0, _ => false
  | fuel + 1, processType =>
      match processType with
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ => false
      | .var _ other => name == other
      | .recur _ other body =>
          if name = other then false
          else menuReachesVarFuel name completeValue fuel body
      | .choice _ left right | .fairChoice _ _ left right =>
          menuReachesVarFuel name completeValue fuel left ||
            menuReachesVarFuel name completeValue fuel right
      | .seq _ left right =>
          menuReachesVarFuel name completeValue fuel left ||
            (PactType.canCompleteBeforeTockSubst name completeValue left.completionView &&
              menuReachesVarFuel name completeValue fuel right)
      | .par _ left right _ =>
          menuReachesVarFuel name completeValue fuel left ||
            menuReachesVarFuel name completeValue fuel right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          menuReachesVarFuel name completeValue fuel elseType ||
            branches.any fun b => menuReachesVarFuel name completeValue fuel b.2

/-- A binder that does not occur is invisible to both the substituted menu and
the reach test. -/
theorem typeFutureOffersFuelSubst_of_absent (name : String)
    (menuValue : Finset BareMessage) (completeValue : Bool) :
    ∀ (fuel : Nat) (processType : PactType),
      sizeOf processType < fuel →
      processType.TailOccurrences name False →
      typeFutureOffersFuelSubst name menuValue completeValue fuel processType =
          typeFutureOffersFuel fuel processType ∧
        menuReachesVarFuel name completeValue fuel processType = false := by
  intro fuel
  induction fuel with
  | zero => intro processType hFuel _; exact absurd hFuel (by omega)
  | succ fuel ih =>
      intro processType hFuel hTail
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < fuel →
          PactType.TailBranchOccurrences name False branches →
          (branches.foldl (fun offers branch =>
              offers ∪ {branch.1} ∪ typeFutureOffersFuelSubst name menuValue
                completeValue fuel branch.2) = fun init =>
            branches.foldl (fun offers branch =>
              offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2) init) ∧
          (branches.any fun b =>
            menuReachesVarFuel name completeValue fuel b.2) = false := by
        intro branches
        induction branches with
        | nil => intro _ _; exact ⟨rfl, rfl⟩
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            intro hBranchSize hBranchTail
            simp only [PactType.TailBranchOccurrences] at hBranchTail
            simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hBranchSize
            obtain ⟨hHeadEq, hHeadReach⟩ :=
              ih branchType (by omega) hBranchTail.1
            obtain ⟨hRestEq, hRestReach⟩ := restIH (by omega) hBranchTail.2
            constructor
            · funext init
              simp only [List.foldl_cons, hHeadEq]
              exact congrFun hRestEq _
            · simp [List.any_cons, hHeadReach, hRestReach]
      cases processType with
      | message alphabet msg dir =>
          exact ⟨rfl, rfl⟩
      | progress alphabet pid => exact ⟨rfl, rfl⟩
      | tock alphabet => exact ⟨rfl, rfl⟩
      | skip alphabet => exact ⟨rfl, rfl⟩
      | var alphabet other =>
          simp only [PactType.TailOccurrences] at hTail
          have hNe : ¬ (name = other) := fun h => hTail h.symm
          simp [typeFutureOffersFuelSubst, typeFutureOffersFuel,
            menuReachesVarFuel, hNe]
      | recur alphabet other body =>
          simp only [PactType.TailOccurrences] at hTail
          by_cases hName : name = other
          · refine ⟨?_, ?_⟩
            · simp only [typeFutureOffersFuelSubst, typeFutureOffersFuel,
                if_pos hName]
            · simp only [menuReachesVarFuel, if_pos hName]
          · have hName' : ¬ (other = name) := fun h => hName h.symm
            simp only [hName', if_neg, not_false_iff] at hTail
            obtain ⟨hEq, hReach⟩ := ih body (by simp at hFuel; omega) hTail
            simp only [typeFutureOffersFuelSubst, typeFutureOffersFuel,
              menuReachesVarFuel, hName, if_neg, not_false_iff]
            exact ⟨hEq, hReach⟩
      | choice alphabet left right =>
          simp only [PactType.TailOccurrences] at hTail
          obtain ⟨hL, hRL⟩ := ih left (by simp at hFuel; omega) hTail.1
          obtain ⟨hR, hRR⟩ := ih right (by simp at hFuel; omega) hTail.2
          simp [typeFutureOffersFuelSubst, typeFutureOffersFuel,
            menuReachesVarFuel, hL, hR, hRL, hRR]
      | fairChoice alphabet bid left right =>
          simp only [PactType.TailOccurrences] at hTail
          obtain ⟨hL, hRL⟩ := ih left (by simp at hFuel; omega) hTail.1
          obtain ⟨hR, hRR⟩ := ih right (by simp at hFuel; omega) hTail.2
          simp [typeFutureOffersFuelSubst, typeFutureOffersFuel,
            menuReachesVarFuel, hL, hR, hRL, hRR]
      | par alphabet left right interface =>
          simp only [PactType.TailOccurrences] at hTail
          obtain ⟨hL, hRL⟩ := ih left (by simp at hFuel; omega) hTail.1
          obtain ⟨hR, hRR⟩ := ih right (by simp at hFuel; omega) hTail.2
          simp [typeFutureOffersFuelSubst, typeFutureOffersFuel,
            menuReachesVarFuel, hL, hR, hRL, hRR]
      | seq alphabet left right =>
          simp only [PactType.TailOccurrences] at hTail
          obtain ⟨hL, hRL⟩ := ih left (by simp at hFuel; omega) hTail.1
          obtain ⟨hR, hRR⟩ := ih right (by simp at hFuel; omega) hTail.2
          have hGate : PactType.canCompleteBeforeTockSubst name completeValue
              left.completionView = left.CanCompleteDeclared :=
            PactType.canCompleteDeclaredSubst_eq_of_tailOccurrences_false name
              completeValue left hTail.1
          have hFuelGate : typeCanCompleteThisCycleFuel fuel left =
              left.CanCompleteDeclared :=
            typeCanCompleteThisCycleFuel_eq_canCompleteDeclared fuel left
              (by simp at hFuel; omega)
          simp only [typeFutureOffersFuelSubst, typeFutureOffersFuel,
            menuReachesVarFuel, hL, hR, hRL, hRR, hGate, hFuelGate]
          simp
      | xoffer alphabet elseType branches =>
          simp only [PactType.TailOccurrences] at hTail
          obtain ⟨hE, hRE⟩ := ih elseType (by simp at hFuel; omega) hTail.1
          obtain ⟨hB, hRB⟩ := hBranches branches (by simp at hFuel; omega) hTail.2
          simp only [typeFutureOffersFuelSubst, typeFutureOffersFuel,
            menuReachesVarFuel, hE, hRE, hRB]
          exact ⟨congrArg (fun offers : Finset BareMessage => offers ∩ alphabet.actions)
            (congrFun hB _), by simp⟩
      | offer alphabet elseType branches =>
          simp only [PactType.TailOccurrences] at hTail
          obtain ⟨hE, hRE⟩ := ih elseType (by simp at hFuel; omega) hTail.1
          obtain ⟨hB, hRB⟩ := hBranches branches (by simp at hFuel; omega) hTail.2
          simp only [typeFutureOffersFuelSubst, typeFutureOffersFuel,
            menuReachesVarFuel, hE, hRE, hRB]
          exact ⟨congrArg (fun offers : Finset BareMessage => offers ∩ alphabet.actions)
            (congrFun hB _), by simp⟩


/-- The substituted menu is the unsubstituted one plus the variable's menu,
contributed exactly when the recursion is reached before the next clock.  The
tail condition is what rules out a parallel component, where the interface
would hide the variable's contribution on one side only. -/
theorem typeFutureOffersFuelSubst_split (name : String)
    (menuValue : Finset BareMessage) (completeValue : Bool) :
    ∀ (fuel : Nat) (processType : PactType),
      sizeOf processType < fuel →
      processType.TailOccurrences name True →
      processType.AlphabetWellFormed →
      menuValue ⊆ processType.alphabet.actions →
      typeFutureOffersFuelSubst name menuValue completeValue fuel processType =
        typeFutureOffersFuelSubst name ∅ completeValue fuel processType ∪
          (if menuReachesVarFuel name completeValue fuel processType then
            menuValue else ∅) := by
  intro fuel
  induction fuel with
  | zero => intro processType hFuel _ _ _; exact absurd hFuel (by omega)
  | succ fuel ih =>
      intro processType hFuel hTail hWF hMenu
      have hAbsent := typeFutureOffersFuelSubst_of_absent name menuValue
        completeValue fuel
      have hAbsent0 := typeFutureOffersFuelSubst_of_absent name ∅
        completeValue fuel
      have hFoldInit : ∀ (bs : List (BareMessage × PactType))
          (g : BareMessage × PactType → Finset BareMessage)
          (a c : Finset BareMessage),
          bs.foldl (fun offers b => offers ∪ {b.1} ∪ g b) (a ∪ c) =
            bs.foldl (fun offers b => offers ∪ {b.1} ∪ g b) a ∪ c := by
        intro bs g
        induction bs with
        | nil => intro a c; rfl
        | cons b rest restIH =>
            intro a c
            simp only [List.foldl_cons]
            rw [show a ∪ c ∪ {b.1} ∪ g b = (a ∪ {b.1} ∪ g b) ∪ c by
              ext x; simp; tauto]
            exact restIH _ _
      cases processType with
      | message alphabet msg dir =>
          simp [typeFutureOffersFuelSubst, menuReachesVarFuel]
      | progress alphabet pid =>
          simp [typeFutureOffersFuelSubst, menuReachesVarFuel]
      | tock alphabet => simp [typeFutureOffersFuelSubst, menuReachesVarFuel]
      | skip alphabet => simp [typeFutureOffersFuelSubst, menuReachesVarFuel]
      | var alphabet other =>
          by_cases hName : name = other
          · simp [typeFutureOffersFuelSubst, menuReachesVarFuel, hName]
          · simp [typeFutureOffersFuelSubst, menuReachesVarFuel, hName]
      | recur alphabet other body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.alphabet] at hMenu
          simp only [PactType.TailOccurrences] at hTail
          by_cases hName : name = other
          · simp only [typeFutureOffersFuelSubst, menuReachesVarFuel,
              if_pos hName, if_neg, Bool.false_eq_true, not_false_iff]
            simp
          · have hName' : ¬ (other = name) := fun h => hName h.symm
            simp only [hName', if_neg, not_false_iff] at hTail
            simp only [typeFutureOffersFuelSubst, menuReachesVarFuel,
              if_neg hName]
            exact ih body (by simp at hFuel; omega) hTail hWF.2.2
              (by simpa only [hWF.2.1] using hMenu)
      | choice alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.alphabet] at hMenu
          simp only [PactType.TailOccurrences] at hTail
          simp only [typeFutureOffersFuelSubst, menuReachesVarFuel,
            ih left (by simp at hFuel; omega) hTail.1 hWF.2.2.2.1
              (by simpa only [hWF.2.1] using hMenu),
            ih right (by simp at hFuel; omega) hTail.2 hWF.2.2.2.2
              (by simpa only [hWF.2.2.1] using hMenu)]
          by_cases hL : menuReachesVarFuel name completeValue fuel left <;>
            by_cases hR : menuReachesVarFuel name completeValue fuel right <;>
            simp [hL, hR, Finset.union_assoc, Finset.union_left_comm,
              Finset.union_comm]
      | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.alphabet] at hMenu
          simp only [PactType.TailOccurrences] at hTail
          simp only [typeFutureOffersFuelSubst, menuReachesVarFuel,
            ih left (by simp at hFuel; omega) hTail.1 hWF.2.2.2.1
              (by simpa only [hWF.2.1] using hMenu),
            ih right (by simp at hFuel; omega) hTail.2 hWF.2.2.2.2
              (by simpa only [hWF.2.2.1] using hMenu)]
          by_cases hL : menuReachesVarFuel name completeValue fuel left <;>
            by_cases hR : menuReachesVarFuel name completeValue fuel right <;>
            simp [hL, hR, Finset.union_assoc, Finset.union_left_comm,
              Finset.union_comm]
      | par alphabet left right interface =>
          simp only [PactType.TailOccurrences] at hTail
          obtain ⟨hLEq, hLReach⟩ :=
            hAbsent left (by simp at hFuel ⊢; omega) hTail.1
          obtain ⟨hREq, hRReach⟩ :=
            hAbsent right (by simp at hFuel ⊢; omega) hTail.2
          obtain ⟨hLEq0, -⟩ :=
            hAbsent0 left (by simp at hFuel ⊢; omega) hTail.1
          obtain ⟨hREq0, -⟩ :=
            hAbsent0 right (by simp at hFuel ⊢; omega) hTail.2
          simp [typeFutureOffersFuelSubst, menuReachesVarFuel, hLEq, hREq,
            hLEq0, hREq0, hLReach, hRReach]
      | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.alphabet] at hMenu
          simp only [PactType.TailOccurrences] at hTail
          obtain ⟨hLEq, hLReach⟩ :=
            hAbsent left (by simp at hFuel ⊢; omega) hTail.1
          obtain ⟨hLEq0, -⟩ :=
            hAbsent0 left (by simp at hFuel ⊢; omega) hTail.1
          simp only [typeFutureOffersFuelSubst, menuReachesVarFuel, hLEq,
            hLEq0, hLReach, Bool.false_or,
            ih right (by simp at hFuel; omega) hTail.2 hWF.2.2.2.2
              (by simpa only [hWF.2.2.1] using hMenu)]
          by_cases hGate : PactType.canCompleteBeforeTockSubst name
              completeValue left.completionView <;>
            by_cases hR : menuReachesVarFuel name completeValue fuel right <;>
            simp [hGate, hR, Finset.union_assoc]
      | xoffer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.alphabet] at hMenu
          simp only [PactType.TailOccurrences] at hTail
          have hFold : ∀ bs : List (BareMessage × PactType),
              sizeOf bs < fuel + 1 →
              PactType.TailBranchOccurrences name True bs →
              PactType.BranchesAlphabetWellFormed alphabet bs →
              ∀ initV init0 : Finset BareMessage, ∀ flag : Bool,
                initV = init0 ∪ (if flag then menuValue else ∅) →
                bs.foldl (fun offers b => offers ∪ {b.1} ∪
                    typeFutureOffersFuelSubst name menuValue completeValue fuel
                      b.2) initV =
                  bs.foldl (fun offers b => offers ∪ {b.1} ∪
                      typeFutureOffersFuelSubst name ∅ completeValue fuel b.2)
                    init0 ∪
                    (if (flag || bs.any fun b =>
                        menuReachesVarFuel name completeValue fuel b.2) then
                      menuValue else ∅) := by
            intro bs
            induction bs with
            | nil => intro _ _ _ initV init0 flag hInit; simpa using hInit
            | cons b rest restIH =>
                rcases b with ⟨action, branchType⟩
                intro hBsSize hBsTail hBsWF initV init0 flag hInit
                simp only [List.cons.sizeOf_spec,
                  Prod.mk.sizeOf_spec] at hBsSize
                simp only [PactType.TailBranchOccurrences] at hBsTail
                simp only [PactType.BranchesAlphabetWellFormed] at hBsWF
                simp only [List.foldl_cons, List.any_cons, ← Bool.or_assoc]
                refine restIH (by omega) hBsTail.2 hBsWF.2.2 _ _
                  (flag || menuReachesVarFuel name completeValue fuel
                    branchType) ?_
                rw [hInit, ih branchType (by omega) hBsTail.1 hBsWF.2.1
                  (by simpa only [hBsWF.1] using hMenu)]
                by_cases hFlag : flag <;>
                  by_cases hB : menuReachesVarFuel name completeValue fuel
                    branchType <;>
                  simp [hFlag, hB, Finset.union_assoc, Finset.union_left_comm,
                    Finset.union_comm]
          simp only [typeFutureOffersFuelSubst, menuReachesVarFuel]
          rw [hFold branches (by simp at hFuel ⊢; omega) hTail.2 hWF.2.2.2 _ _
            (menuReachesVarFuel name completeValue fuel elseType)
            (ih elseType (by simp at hFuel; omega) hTail.1 hWF.2.2.1
              (by simpa only [hWF.2.1] using hMenu))]
          split_ifs <;> simp [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hMenu]
      | offer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.alphabet] at hMenu
          simp only [PactType.TailOccurrences] at hTail
          have hFold : ∀ bs : List (BareMessage × PactType),
              sizeOf bs < fuel + 1 →
              PactType.TailBranchOccurrences name False bs →
              ∀ init : Finset BareMessage,
                bs.foldl (fun offers b => offers ∪ {b.1} ∪
                    typeFutureOffersFuelSubst name menuValue completeValue fuel
                      b.2) init =
                  bs.foldl (fun offers b => offers ∪ {b.1} ∪
                      typeFutureOffersFuelSubst name ∅ completeValue fuel b.2)
                    init ∧
                (bs.any fun b =>
                  menuReachesVarFuel name completeValue fuel b.2) = false := by
            intro bs
            induction bs with
            | nil => intro _ _ init; exact ⟨rfl, rfl⟩
            | cons b rest restIH =>
                rcases b with ⟨action, branchType⟩
                intro hBsSize hBsTail init
                simp only [List.cons.sizeOf_spec,
                  Prod.mk.sizeOf_spec] at hBsSize
                simp only [PactType.TailBranchOccurrences] at hBsTail
                obtain ⟨hHeadV, hHeadReach⟩ :=
                  hAbsent branchType (by omega) hBsTail.1
                obtain ⟨hHead0, -⟩ :=
                  hAbsent0 branchType (by omega) hBsTail.1
                obtain ⟨hRestEq, hRestReach⟩ := restIH (by omega) hBsTail.2 _
                refine ⟨?_, by simp [List.any_cons, hHeadReach, hRestReach]⟩
                simp only [List.foldl_cons, hHeadV, hHead0]
                exact hRestEq
          simp only [typeFutureOffersFuelSubst, menuReachesVarFuel]
          obtain ⟨hFoldEq, hFoldReach⟩ :=
            hFold branches (by simp at hFuel ⊢; omega) hTail.2
              (typeFutureOffersFuelSubst name menuValue completeValue fuel elseType)
          rw [hFoldEq, ih elseType (by simp at hFuel; omega) hTail.1 hWF.2.2.1
            (by simpa only [hWF.2.1] using hMenu), hFoldInit]
          simp only [hFoldReach, Bool.or_false]
          split_ifs <;> simp [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hMenu]

/-- With the binder absent from every non-tail position, the `∅` reading of the
substituted menu is the ordinary menu. -/
theorem typeFutureOffersFuelSubst_empty (name : String) (completeValue : Bool) :
    ∀ (fuel : Nat) (processType : PactType),
      sizeOf processType < fuel →
      processType.TailOccurrences name True →
      typeFutureOffersFuelSubst name ∅ completeValue fuel processType =
        typeFutureOffersFuel fuel processType := by
  intro fuel
  induction fuel with
  | zero => intro processType hFuel _; exact absurd hFuel (by omega)
  | succ fuel ih =>
      intro processType hFuel hTail
      have hAbsent := typeFutureOffersFuelSubst_of_absent name ∅
        completeValue fuel
      have hBranches : ∀ bs : List (BareMessage × PactType),
          sizeOf bs < fuel + 1 →
          PactType.TailBranchOccurrences name True bs →
          ∀ init : Finset BareMessage,
            bs.foldl (fun offers b => offers ∪ {b.1} ∪
                typeFutureOffersFuelSubst name ∅ completeValue fuel b.2) init =
              bs.foldl (fun offers b => offers ∪ {b.1} ∪
                typeFutureOffersFuel fuel b.2) init := by
        intro bs
        induction bs with
        | nil => intro _ _ init; rfl
        | cons b rest restIH =>
            rcases b with ⟨action, branchType⟩
            intro hBsSize hBsTail init
            simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hBsSize
            simp only [PactType.TailBranchOccurrences] at hBsTail
            simp only [List.foldl_cons,
              ih branchType (by omega) hBsTail.1]
            exact restIH (by omega) hBsTail.2 _
      cases processType with
      | message alphabet msg dir => rfl
      | progress alphabet pid => rfl
      | tock alphabet => rfl
      | skip alphabet => rfl
      | var alphabet other =>
          simp [typeFutureOffersFuelSubst, typeFutureOffersFuel]
      | recur alphabet other body =>
          simp only [PactType.TailOccurrences] at hTail
          by_cases hName : name = other
          · simp only [typeFutureOffersFuelSubst, typeFutureOffersFuel,
              if_pos hName]
          · have hName' : ¬ (other = name) := fun h => hName h.symm
            simp only [hName', if_neg, not_false_iff] at hTail
            simp only [typeFutureOffersFuelSubst, typeFutureOffersFuel,
              if_neg hName]
            exact ih body (by simp at hFuel; omega) hTail
      | choice alphabet left right =>
          simp only [PactType.TailOccurrences] at hTail
          simp only [typeFutureOffersFuelSubst, typeFutureOffersFuel,
            ih left (by simp at hFuel; omega) hTail.1,
            ih right (by simp at hFuel; omega) hTail.2]
      | fairChoice alphabet bid left right =>
          simp only [PactType.TailOccurrences] at hTail
          simp only [typeFutureOffersFuelSubst, typeFutureOffersFuel,
            ih left (by simp at hFuel; omega) hTail.1,
            ih right (by simp at hFuel; omega) hTail.2]
      | par alphabet left right interface =>
          simp only [PactType.TailOccurrences] at hTail
          obtain ⟨hLEq, -⟩ := hAbsent left (by simp at hFuel ⊢; omega) hTail.1
          obtain ⟨hREq, -⟩ := hAbsent right (by simp at hFuel ⊢; omega) hTail.2
          simp only [typeFutureOffersFuelSubst, typeFutureOffersFuel, hLEq,
            hREq]
      | seq alphabet left right =>
          simp only [PactType.TailOccurrences] at hTail
          obtain ⟨hLEq, -⟩ := hAbsent left (by simp at hFuel ⊢; omega) hTail.1
          have hGate : PactType.canCompleteBeforeTockSubst name completeValue
              left.completionView = left.CanCompleteDeclared :=
            PactType.canCompleteDeclaredSubst_eq_of_tailOccurrences_false name
              completeValue left hTail.1
          have hFuelGate : typeCanCompleteThisCycleFuel fuel left =
              left.CanCompleteDeclared :=
            typeCanCompleteThisCycleFuel_eq_canCompleteDeclared fuel left
              (by simp at hFuel; omega)
          simp only [typeFutureOffersFuelSubst, typeFutureOffersFuel, hLEq,
            hGate, hFuelGate,
            ih right (by simp at hFuel; omega) hTail.2]
      | xoffer alphabet elseType branches =>
          simp only [PactType.TailOccurrences] at hTail
          simp only [typeFutureOffersFuelSubst, typeFutureOffersFuel,
            ih elseType (by simp at hFuel; omega) hTail.1]
          exact congrArg (fun offers : Finset BareMessage => offers ∩ alphabet.actions)
            (hBranches branches (by simp at hFuel ⊢; omega) hTail.2 _)
      | offer alphabet elseType branches =>
          simp only [PactType.TailOccurrences] at hTail
          have hBranchesFalse : ∀ bs : List (BareMessage × PactType),
              sizeOf bs < fuel + 1 →
              PactType.TailBranchOccurrences name False bs →
              ∀ init : Finset BareMessage,
                bs.foldl (fun offers b => offers ∪ {b.1} ∪
                    typeFutureOffersFuelSubst name ∅ completeValue fuel b.2)
                    init =
                  bs.foldl (fun offers b => offers ∪ {b.1} ∪
                    typeFutureOffersFuel fuel b.2) init := by
            intro bs
            induction bs with
            | nil => intro _ _ init; rfl
            | cons b rest restIH =>
                rcases b with ⟨action, branchType⟩
                intro hBsSize hBsTail init
                simp only [List.cons.sizeOf_spec,
                  Prod.mk.sizeOf_spec] at hBsSize
                simp only [PactType.TailBranchOccurrences] at hBsTail
                obtain ⟨hHead, -⟩ := hAbsent branchType (by omega) hBsTail.1
                simp only [List.foldl_cons, hHead]
                exact restIH (by omega) hBsTail.2 _
          simp only [typeFutureOffersFuelSubst, typeFutureOffersFuel,
            ih elseType (by simp at hFuel; omega) hTail.1]
          exact congrArg (fun offers : Finset BareMessage => offers ∩ alphabet.actions)
            (hBranchesFalse branches (by simp at hFuel ⊢; omega) hTail.2 _)

#print axioms typeFutureOffersFuelSubst_split

end Pact
