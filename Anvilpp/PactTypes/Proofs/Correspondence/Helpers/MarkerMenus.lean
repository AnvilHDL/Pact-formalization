import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.RecursionFoundations

namespace Pact

noncomputable section

open Classical

/-- On tail occurrences, the paper's test depends on neither fuel nor the
completion value substituted for the variable. Sequence-left tests are closed
with respect to that variable. -/
theorem menuReachesVarFuel_eq_of_tail (name : String) :
    ∀ fuel otherFuel ty (complete otherComplete : Bool),
      sizeOf ty < fuel → sizeOf ty < otherFuel →
      ty.TailOccurrences name True →
      menuReachesVarFuel name complete fuel ty =
        menuReachesVarFuel name otherComplete otherFuel ty := by
  intro fuel
  induction fuel with
  | zero => intro otherFuel ty c d h; omega
  | succ fuel ih =>
      intro otherFuel ty c d hSize hOther hTail
      cases otherFuel with
      | zero => omega
      | succ otherFuel =>
        have hBranches : ∀ branches : List (BareMessage × PactType),
            sizeOf branches < fuel → sizeOf branches < otherFuel →
            PactType.TailBranchOccurrences name True branches →
            (branches.any fun b => menuReachesVarFuel name c fuel b.2) =
              branches.any fun b => menuReachesVarFuel name d otherFuel b.2 := by
          intro branches
          induction branches with
          | nil => intros; rfl
          | cons branch rest restIH =>
            rcases branch with ⟨action, body⟩
            intro hSize hOther hTail
            simp only [PactType.TailBranchOccurrences] at hTail
            simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hSize hOther
            simp only [List.any_cons]
            rw [ih otherFuel body c d (by omega) (by omega) hTail.1,
              restIH (by omega) (by omega) hTail.2]
        cases ty with
        | message a m d => rfl
        | progress a p => rfl
        | tock a => rfl
        | skip a => rfl
        | var a x => rfl
        | recur a x body =>
          simp only [menuReachesVarFuel]
          split_ifs with hName
          · rfl
          · apply ih
            · simp at hSize; omega
            · simp at hOther; omega
            · simpa [PactType.TailOccurrences, Ne.symm hName] using hTail
        | choice a left right | fairChoice a tag left right =>
          simp only [PactType.TailOccurrences] at hTail
          simp only [menuReachesVarFuel]
          rw [ih otherFuel left c d (by simp at hSize; omega)
                (by simp at hOther; omega) hTail.1,
              ih otherFuel right c d (by simp at hSize; omega)
                (by simp at hOther; omega) hTail.2]
        | seq a left right =>
          simp only [PactType.TailOccurrences] at hTail
          have hL := (typeFutureOffersFuelSubst_of_absent name ∅ c fuel left
            (by simp at hSize; omega) hTail.1).2
          have hL' := (typeFutureOffersFuelSubst_of_absent name ∅ d otherFuel left
            (by simp at hOther; omega) hTail.1).2
          simp only [menuReachesVarFuel, hL, hL', Bool.false_or,
            PactType.canCompleteDeclaredSubst_eq_of_tailOccurrences_false
              name c left hTail.1,
            PactType.canCompleteDeclaredSubst_eq_of_tailOccurrences_false
              name d left hTail.1]
          rw [ih otherFuel right c d (by simp at hSize; omega)
            (by simp at hOther; omega) hTail.2]
        | par a left right interface =>
          simp only [PactType.TailOccurrences] at hTail
          simp only [menuReachesVarFuel,
            (typeFutureOffersFuelSubst_of_absent name ∅ c fuel left
              (by simp at hSize; omega) hTail.1).2,
            (typeFutureOffersFuelSubst_of_absent name ∅ c fuel right
              (by simp at hSize; omega) hTail.2).2,
            (typeFutureOffersFuelSubst_of_absent name ∅ d otherFuel left
              (by simp at hOther; omega) hTail.1).2,
            (typeFutureOffersFuelSubst_of_absent name ∅ d otherFuel right
              (by simp at hOther; omega) hTail.2).2]
        | xoffer a body branches =>
          simp only [PactType.TailOccurrences] at hTail
          simp only [menuReachesVarFuel]
          rw [ih otherFuel body c d (by simp at hSize; omega)
              (by simp at hOther; omega) hTail.1,
            hBranches branches (by simp at hSize; omega)
              (by simp at hOther; omega) hTail.2]
        | offer a body branches =>
          simp only [PactType.TailOccurrences] at hTail
          simp only [menuReachesVarFuel]
          rw [ih otherFuel body c d (by simp at hSize; omega)
              (by simp at hOther; omega) hTail.1,
            hBranches branches (by simp at hSize; omega)
              (by simp at hOther; omega)
              (PactType.tailBranchOccurrences_mono name (fun _ => True.intro)
                branches hTail.2)]

/-- The syntax test `b_X` in the recursion-menu proof. -/
def menuReachesVar (name : String) (ty : PactType) : Bool :=
  menuReachesVarFuel name false (sizeOf ty + 1) ty

theorem menuReachesVarFuel_eq_menuReachesVar (name : String) (complete : Bool)
    (fuel : Nat) (ty : PactType) (hSize : sizeOf ty < fuel)
    (hTail : ty.TailOccurrences name True) :
    menuReachesVarFuel name complete fuel ty = menuReachesVar name ty :=
  menuReachesVarFuel_eq_of_tail name fuel (sizeOf ty + 1) ty complete false
    hSize (by omega) hTail

theorem menuReachesVar_of_absent (name : String) (ty : PactType)
    (hTail : ty.TailOccurrences name False) : menuReachesVar name ty = false :=
  (typeFutureOffersFuelSubst_of_absent name ∅ false (sizeOf ty + 1) ty
    (by omega) hTail).2

private theorem menuReachesVarFuel_branches (name : String) (fuel : Nat)
    (branches : List (BareMessage × PactType))
    (hSize : sizeOf branches < fuel)
    (hTail : PactType.TailBranchOccurrences name True branches) :
    (branches.any fun b => menuReachesVarFuel name false fuel b.2) =
      branches.any fun b => menuReachesVar name b.2 := by
  induction branches with
  | nil => rfl
  | cons b rest ih =>
    rcases b with ⟨a, ty⟩
    simp only [PactType.TailBranchOccurrences] at hTail
    simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hSize
    simp only [List.any_cons]
    rw [menuReachesVarFuel_eq_menuReachesVar name false fuel ty (by omega) hTail.1,
      ih (by omega) hTail.2]

@[simp] theorem menuReachesVar_var (name other : String) (a : PactTypeAlphabet) :
    menuReachesVar name (.var a other) = (name == other) := rfl

theorem menuReachesVar_recur (name other : String) (a : PactTypeAlphabet)
    (body : PactType) (hTail : body.TailOccurrences name True) :
    menuReachesVar name (.recur a other body) =
      if name = other then false else menuReachesVar name body := by
  conv_lhs => unfold menuReachesVar
  rw [menuReachesVarFuel]
  rw [menuReachesVarFuel_eq_menuReachesVar name false _ body (by simp; omega) hTail]

theorem menuReachesVar_choice (name : String) (a : PactTypeAlphabet)
    (left right : PactType) (hL : left.TailOccurrences name True)
    (hR : right.TailOccurrences name True) :
    menuReachesVar name (.choice a left right) =
      (menuReachesVar name left || menuReachesVar name right) := by
  conv_lhs => unfold menuReachesVar
  rw [menuReachesVarFuel,
    menuReachesVarFuel_eq_menuReachesVar name false _ left (by simp; omega) hL,
    menuReachesVarFuel_eq_menuReachesVar name false _ right (by simp; omega) hR]

theorem menuReachesVar_fairChoice (name : String) (a : PactTypeAlphabet)
    (tag : BranchId) (left right : PactType) (hL : left.TailOccurrences name True)
    (hR : right.TailOccurrences name True) :
    menuReachesVar name (.fairChoice a tag left right) =
      (menuReachesVar name left || menuReachesVar name right) := by
  conv_lhs => unfold menuReachesVar
  rw [menuReachesVarFuel,
    menuReachesVarFuel_eq_menuReachesVar name false _ left (by simp; omega) hL,
    menuReachesVarFuel_eq_menuReachesVar name false _ right (by simp; omega) hR]

theorem menuReachesVar_seq (name : String) (a : PactTypeAlphabet)
    (left right : PactType) (hL : left.TailOccurrences name False)
    (hR : right.TailOccurrences name True) :
    menuReachesVar name (.seq a left right) =
      (left.CanCompleteDeclared && menuReachesVar name right) := by
  conv_lhs => unfold menuReachesVar
  rw [menuReachesVarFuel,
    (typeFutureOffersFuelSubst_of_absent name ∅ false _ left (by simp; omega) hL).2,
    menuReachesVarFuel_eq_menuReachesVar name false _ right (by simp; omega) hR,
    PactType.canCompleteDeclaredSubst_eq_of_tailOccurrences_false name false left hL]
  rfl

theorem menuReachesVar_xoffer (name : String) (a : PactTypeAlphabet)
    (body : PactType) (branches : List (BareMessage × PactType))
    (hBody : body.TailOccurrences name True)
    (hBranches : PactType.TailBranchOccurrences name True branches) :
    menuReachesVar name (.xoffer a body branches) =
      if ∀ b ∈ branches, b.1 ∈ a.actions then
        menuReachesVar name body || branches.any (fun b => menuReachesVar name b.2)
      else false := by
  conv_lhs => unfold menuReachesVar
  rw [menuReachesVarFuel,
    menuReachesVarFuel_eq_menuReachesVar name false _ body (by simp; omega) hBody,
    menuReachesVarFuel_branches name _ branches (by simp; omega) hBranches]

theorem menuReachesVar_offer (name : String) (a : PactTypeAlphabet)
    (body : PactType) (branches : List (BareMessage × PactType))
    (hBody : body.TailOccurrences name True)
    (hBranches : PactType.TailBranchOccurrences name False branches) :
    menuReachesVar name (.offer a body branches) =
      if ∀ b ∈ branches, b.1 ∈ a.actions then menuReachesVar name body else false := by
  have hAbsent : (branches.any fun b => menuReachesVar name b.2) = false := by
    induction branches with
    | nil => rfl
    | cons b rest ih =>
      rcases b with ⟨action, ty⟩
      simp only [PactType.TailBranchOccurrences] at hBranches
      simp only [List.any_cons, menuReachesVar_of_absent name ty hBranches.1,
        ih hBranches.2, Bool.false_or]
  conv_lhs => unfold menuReachesVar
  rw [menuReachesVarFuel,
    menuReachesVarFuel_eq_menuReachesVar name false _ body (by simp; omega) hBody,
    menuReachesVarFuel_branches name _ branches (by simp; omega)
      (PactType.tailBranchOccurrences_mono name (fun _ => True.intro) branches hBranches),
    hAbsent, Bool.or_false]

/-- The nested-recursion equation in the paper: a path reaches `name`
directly, or reaches `other` and continues through its replacement. -/
theorem menuReachesVar_replaceVar (name other : String) (replacement : PactType)
    (hNe : name ≠ other) (hReplacement : replacement.TailOccurrences name True)
    (bound : List String) (hMem : name ∈ bound) :
    ∀ ty, ty.TailOccurrences name True → ty.TailOccurrences other True →
      PactType.BinderFreshFor bound ty →
      menuReachesVar name (ty.replaceVar other replacement) =
        (menuReachesVar name ty ||
          (menuReachesVar other ty && menuReachesVar name replacement)) := by
  intro ty
  induction hSize : sizeOf ty using Nat.strong_induction_on generalizing ty with
  | h n ih =>
    intro hName hOther hFresh
    have hTailSubst := fun (rho : PactType) hX hY =>
      PactType.tailOccurrences_replaceVar name other rho True hReplacement hY (Or.inr hX)
    have hBranches : ∀ branches : List (BareMessage × PactType),
        sizeOf branches < n →
        PactType.TailBranchOccurrences name True branches →
        PactType.TailBranchOccurrences other True branches →
        PactType.BinderFreshForBranches bound branches →
        PactType.TailBranchOccurrences name True
            (PactType.replaceBranches branches other replacement) ∧
          ((PactType.replaceBranches branches other replacement).any
              (fun b => menuReachesVar name b.2)) =
            ((branches.any fun b => menuReachesVar name b.2) ||
              ((branches.any fun b => menuReachesVar other b.2) &&
                menuReachesVar name replacement)) := by
      intro branches
      induction branches with
      | nil => intros; simp [PactType.replaceBranches, PactType.TailBranchOccurrences]
      | cons b rest restIH =>
        rcases b with ⟨action, body⟩
        intro hSize hName hOther hFresh
        simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hSize
        simp only [PactType.TailBranchOccurrences] at hName hOther
        simp only [PactType.BinderFreshForBranches] at hFresh
        obtain ⟨hRestTail, hRest⟩ := restIH (by omega) hName.2 hOther.2 hFresh.2
        refine ⟨?_, ?_⟩
        · simpa only [PactType.replaceBranches, PactType.TailBranchOccurrences] using
            And.intro (hTailSubst body hName.1 hOther.1) hRestTail
        simp only [PactType.replaceBranches, List.any_cons]
        rw [ih (sizeOf body) (by omega) body rfl hName.1 hOther.1 hFresh.1, hRest]
        cases hS : menuReachesVar name replacement <;>
          simp [hS, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
    by_cases hAbsent : ty.TailOccurrences other False
    · rw [PactType.replaceVar_eq_self_of_tailOccurrences_false other replacement ty hAbsent,
        menuReachesVar_of_absent other ty hAbsent]
      simp
    cases ty with
    | message a m d | progress a p | tock a | skip a =>
      exact False.elim (hAbsent (by simp [PactType.TailOccurrences]))
    | var a x =>
      have hEq : other = x := by
        by_contra h
        exact hAbsent (by simpa [PactType.TailOccurrences] using Ne.symm h)
      subst x
      simp [PactType.replaceVar, hNe]
    | recur a binder body =>
      by_cases hBinder : other = binder
      · exact False.elim (hAbsent (by simp [PactType.TailOccurrences, hBinder]))
      simp only [PactType.BinderFreshFor] at hFresh
      have hBinderName : name ≠ binder := fun h => hFresh.1 (h ▸ hMem)
      simp only [PactType.TailOccurrences, if_neg (Ne.symm hBinderName),
        if_neg (Ne.symm hBinder)] at hName hOther
      simp only [PactType.replaceVar, if_neg hBinder]
      rw [menuReachesVar_recur name binder a _ (hTailSubst body hName hOther),
        menuReachesVar_recur name binder a body hName,
        menuReachesVar_recur other binder a body hOther,
        if_neg hBinderName, if_neg hBinder,
        ih (sizeOf body) (by rw [← hSize]; simp; omega) body rfl hName hOther hFresh.2]
      simp only [if_neg hBinderName]
    | choice a left right | fairChoice a tag left right =>
      simp only [PactType.TailOccurrences] at hName hOther
      simp only [PactType.BinderFreshFor] at hFresh
      simp only [PactType.replaceVar]
      first
      | rw [menuReachesVar_choice name a _ _ (hTailSubst left hName.1 hOther.1)
            (hTailSubst right hName.2 hOther.2),
          menuReachesVar_choice name a left right hName.1 hName.2,
          menuReachesVar_choice other a left right hOther.1 hOther.2]
      | rw [menuReachesVar_fairChoice name a tag _ _ (hTailSubst left hName.1 hOther.1)
            (hTailSubst right hName.2 hOther.2),
          menuReachesVar_fairChoice name a tag left right hName.1 hName.2,
          menuReachesVar_fairChoice other a tag left right hOther.1 hOther.2]
      rw [ih (sizeOf left) (by rw [← hSize]; simp; omega) left rfl hName.1 hOther.1 hFresh.1,
        ih (sizeOf right) (by rw [← hSize]; simp; omega) right rfl hName.2 hOther.2 hFresh.2]
      cases hS : menuReachesVar name replacement <;>
        simp [hS, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
    | seq a left right =>
      simp only [PactType.TailOccurrences] at hName hOther
      simp only [PactType.BinderFreshFor] at hFresh
      simp only [PactType.replaceVar]
      rw [PactType.replaceVar_eq_self_of_tailOccurrences_false other replacement left hOther.1,
        menuReachesVar_seq name a left _ hName.1 (hTailSubst right hName.2 hOther.2),
        menuReachesVar_seq name a left right hName.1 hName.2,
        menuReachesVar_seq other a left right hOther.1 hOther.2,
        ih (sizeOf right) (by rw [← hSize]; simp; omega) right rfl hName.2 hOther.2 hFresh.2]
      cases hL : left.CanCompleteDeclared <;> simp [hL]
    | par a left right interface =>
      exact False.elim (hAbsent (by simpa only [PactType.TailOccurrences] using hOther))
    | xoffer a body branches =>
      simp only [PactType.TailOccurrences] at hName hOther
      simp only [PactType.BinderFreshFor] at hFresh
      obtain ⟨hBTail, hB⟩ := hBranches branches (by rw [← hSize]; simp; omega)
        hName.2 hOther.2 hFresh.2
      simp only [PactType.replaceVar]
      rw [menuReachesVar_xoffer name a _ _ (hTailSubst body hName.1 hOther.1) hBTail,
        menuReachesVar_xoffer name a body branches hName.1 hName.2,
        menuReachesVar_xoffer other a body branches hOther.1 hOther.2]
      simp only [replaceBranches_gate]
      rw [ih (sizeOf body) (by rw [← hSize]; simp; omega) body rfl hName.1 hOther.1 hFresh.1, hB]
      split_ifs <;> cases hS : menuReachesVar name replacement <;>
        simp_all only [Bool.and_true, Bool.and_false, Bool.false_and,
          Bool.or_false, Bool.false_or, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
    | offer a body branches =>
      simp only [PactType.TailOccurrences] at hName hOther
      simp only [PactType.BinderFreshFor] at hFresh
      simp only [PactType.replaceVar]
      rw [PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false
          other replacement branches hOther.2,
        menuReachesVar_offer name a _ branches (hTailSubst body hName.1 hOther.1) hName.2,
        menuReachesVar_offer name a body branches hName.1 hName.2,
        menuReachesVar_offer other a body branches hOther.1 hOther.2,
        ih (sizeOf body) (by rw [← hSize]; simp; omega) body rfl hName.1 hOther.1 hFresh.1]
      split_ifs <;> simp

end

end Pact
