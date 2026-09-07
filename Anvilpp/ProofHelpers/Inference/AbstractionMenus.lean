import Anvilpp.PactTypes.Proofs.Syntax.PactTypeFutureOffersLemmas

/-!
# Abstraction preserves the menu data

`abs` preserves `canCompleteThisCycle`, `FutOff`, `Act_B`, `Need(B)` and the
optimistic waiting set, so every `Off` clause reads the same menus on both
sides.
-/

namespace Pact

noncomputable section

open Classical

/-! ## Branch heads -/

@[simp] theorem inferBranches_action (branch : ChoiceBranch)
    (rest : List ChoiceBranch) :
    inferBranches (branch :: rest) =
      (ChoiceBranch.action branch, inferProcess (ChoiceBranch.continuation branch)) ::
        inferBranches rest := by
  cases branch <;>
    simp [inferBranches, ChoiceBranch.action, ChoiceBranch.getMessageId,
      ChoiceBranch.getDir, ChoiceBranch.continuation]

theorem inferBranches_map_fst (branches : List ChoiceBranch) :
    (inferBranches branches).map Prod.fst = branches.map ChoiceBranch.action := by
  induction branches with
  | nil => simp [inferBranches]
  | cons branch rest ih => simp [inferBranches_action, ih]

/-- `Act_B` is unchanged by abstraction. -/
theorem typeBranchActions_inferBranches (branches : List ChoiceBranch) :
    typeBranchActions (inferBranches branches) = branchActions branches := by
  simp [typeBranchActions, branchActions, inferBranches_map_fst]

/-- `Need(B)` is unchanged by abstraction. -/
theorem typeBranchNeeds_inferBranches (branches : List ChoiceBranch) :
    typeBranchNeeds (inferBranches branches) = branchNeeds branches := by
  have hMap : (inferBranches branches).map (fun branch => typeNeed branch.1) =
      branches.map ChoiceBranch.need := by
    induction branches with
    | nil => simp [inferBranches]
    | cons branch rest ih =>
        rw [inferBranches_action]
        simp only [List.map_cons, ih]
        cases branch <;> rfl
  simp [typeBranchNeeds, branchNeeds, hMap]

/-- Every branch head is declared exactly when its abstraction is. -/
theorem branchesDeclared_inferBranches (alphabet : PactTypeAlphabet)
    (branches : List ChoiceBranch) :
    (∀ b ∈ inferBranches branches, b.1 ∈ alphabet.actions) ↔
      BranchesDeclared alphabet branches := by
  constructor
  · intro hAll branch hMem
    have : ChoiceBranch.action branch ∈ (inferBranches branches).map Prod.fst := by
      rw [inferBranches_map_fst]
      exact List.mem_map_of_mem hMem
    obtain ⟨b, hb, hEq⟩ := List.mem_map.1 this
    exact hEq ▸ hAll b hb
  · intro hAll b hMem
    have : b.1 ∈ (inferBranches branches).map Prod.fst := List.mem_map_of_mem hMem
    rw [inferBranches_map_fst] at this
    obtain ⟨branch, hBranch, hEq⟩ := List.mem_map.1 this
    exact hEq ▸ hAll branch hBranch

/-- `branchesDeclared` is the boolean companion of `BranchesDeclared`. -/
theorem branchesDeclared_eq_decide (alphabet : PactTypeAlphabet)
    (branches : List ChoiceBranch) :
    branchesDeclared alphabet branches = decide (BranchesDeclared alphabet branches) := by
  rw [Bool.eq_iff_iff]
  simp [branchesDeclared, BranchesDeclared]

/-! ## Optimistic completion -/

@[simp] theorem canCompleteDeclared_message (alphabet : PactTypeAlphabet)
    (msg : MessageId) (dir : MessageDir) :
    (PactType.message alphabet msg dir).CanCompleteDeclared =
      decide ((msg, dir) ∈ alphabet.actions) := by
  rw [PactType.canCompleteDeclared_eq]

@[simp] theorem canCompleteDeclared_skip (alphabet : PactTypeAlphabet) :
    (PactType.skip alphabet).CanCompleteDeclared = true := by
  rw [PactType.canCompleteDeclared_eq]

private theorem canComplete_aux : ∀ n : Nat,
    (∀ process : Proc, sizeOf process < n →
      Proc.CanCompleteBeforeTock process =
        (inferProcess process).CanCompleteDeclared) ∧
    (∀ branches : List ChoiceBranch, sizeOf branches < n →
      Proc.BranchCanCompleteBeforeTock branches =
        PactType.BranchCanCompleteDeclared (inferBranches branches)) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ h => absurd h (by omega), fun _ h => absurd h (by omega)⟩
  | succ n ih =>
      obtain ⟨ihProc, ihBranch⟩ := ih
      refine ⟨?_, ?_⟩
      · intro process hSize
        cases process with
        | send alphabet msg expr p =>
            rw [Proc.CanCompleteBeforeTock, inferProcess,
              PactType.canCompleteDeclared_eq, ihProc p (by simp at hSize ⊢; omega)]
            simp
        | recv alphabet msg varName p =>
            rw [Proc.CanCompleteBeforeTock, inferProcess,
              PactType.canCompleteDeclared_eq, ihProc p (by simp at hSize ⊢; omega)]
            simp
        | var alphabet name =>
            rw [Proc.CanCompleteBeforeTock, inferProcess,
              PactType.canCompleteDeclared_eq]
        | skip alphabet =>
            rw [Proc.CanCompleteBeforeTock, inferProcess,
              PactType.canCompleteDeclared_eq]
        | endp alphabet pid =>
            rw [Proc.CanCompleteBeforeTock, inferProcess,
              PactType.canCompleteDeclared_eq]
        | cycle alphabet =>
            rw [Proc.CanCompleteBeforeTock, inferProcess,
              PactType.canCompleteDeclared_eq]
        | par alphabet left right interface =>
            rw [Proc.CanCompleteBeforeTock, inferProcess,
              PactType.canCompleteDeclared_eq,
              ihProc left (by simp at hSize ⊢; omega),
              ihProc right (by simp at hSize ⊢; omega)]
        | seq alphabet left right =>
            rw [Proc.CanCompleteBeforeTock, inferProcess,
              PactType.canCompleteDeclared_eq,
              ihProc left (by simp at hSize ⊢; omega),
              ihProc right (by simp at hSize ⊢; omega)]
        | letp alphabet varName expr p =>
            rw [Proc.CanCompleteBeforeTock, inferProcess,
              PactType.canCompleteDeclared_eq, ihProc p (by simp at hSize ⊢; omega)]
            simp
        | ifunfair alphabet expr left right =>
            rw [Proc.CanCompleteBeforeTock, inferProcess,
              PactType.canCompleteDeclared_eq,
              ihProc left (by simp at hSize ⊢; omega),
              ihProc right (by simp at hSize ⊢; omega)]
        | iffair alphabet bid expr left right =>
            rw [Proc.CanCompleteBeforeTock, inferProcess,
              PactType.canCompleteDeclared_eq,
              ihProc left (by simp at hSize ⊢; omega),
              ihProc right (by simp at hSize ⊢; omega)]
        | recur alphabet name body =>
            rw [Proc.CanCompleteBeforeTock, inferProcess,
              PactType.canCompleteDeclared_eq,
              ihProc body (by simp at hSize ⊢; omega)]
        | xoffer alphabet elseProcess branches =>
            rw [Proc.CanCompleteBeforeTock, inferProcess,
              PactType.canCompleteDeclared_eq,
              ihProc elseProcess (by simp at hSize ⊢; omega),
              ihBranch branches (by simp at hSize ⊢; omega),
              branchesDeclared_eq_decide]
            congr 1
            exact decide_eq_decide.2 (branchesDeclared_inferBranches alphabet branches).symm
        | offer alphabet elseProcess branches =>
            rw [Proc.CanCompleteBeforeTock, inferProcess,
              PactType.canCompleteDeclared_eq,
              ihProc elseProcess (by simp at hSize ⊢; omega),
              ihBranch branches (by simp at hSize ⊢; omega),
              branchesDeclared_eq_decide]
            congr 1
            exact decide_eq_decide.2 (branchesDeclared_inferBranches alphabet branches).symm
      · intro branches hSize
        cases branches with
        | nil =>
            rw [Proc.BranchCanCompleteBeforeTock, inferBranches,
              PactType.branchCanCompleteDeclared_nil]
        | cons branch rest =>
            rw [Proc.BranchCanCompleteBeforeTock, inferBranches_action,
              PactType.branchCanCompleteDeclared_cons,
              ihProc (ChoiceBranch.continuation branch)
                (by have := ChoiceBranch.continuation_sizeOf_lt branch
                    simp at hSize ⊢; omega),
              ihBranch rest (by simp at hSize ⊢; omega)]

/-- `canCompleteThisCycle` is preserved by abstraction. -/
theorem canCompleteBeforeTock_inferProcess (process : Proc) :
    Proc.CanCompleteBeforeTock process = (inferProcess process).CanCompleteDeclared :=
  (canComplete_aux (sizeOf process + 1)).1 process (by omega)

theorem branchCanCompleteBeforeTock_inferBranches (branches : List ChoiceBranch) :
    Proc.BranchCanCompleteBeforeTock branches =
      PactType.BranchCanCompleteDeclared (inferBranches branches) :=
  (canComplete_aux (sizeOf branches + 1)).2 branches (by omega)

/-! ## Atomic type menus -/

theorem typeFutureOffers_message (alphabet : PactTypeAlphabet)
    (msg : MessageId) (dir : MessageDir) :
    typeFutureOffers (.message alphabet msg dir) =
      if (msg, dir) ∈ alphabet.actions then {(msg, dir)} else ∅ := by
  change typeFutureOffersFuel (sizeOf (PactType.message alphabet msg dir) + 1) _ = _
  simp only [typeFutureOffersFuel]

@[simp] theorem typeFutureOffers_skip (alphabet : PactTypeAlphabet) :
    typeFutureOffers (.skip alphabet) = ∅ := by
  change typeFutureOffersFuel (sizeOf (PactType.skip alphabet) + 1) _ = _
  simp only [typeFutureOffersFuel]

@[simp] theorem typeFutureOffers_tock (alphabet : PactTypeAlphabet) :
    typeFutureOffers (.tock alphabet) = ∅ := by
  change typeFutureOffersFuel (sizeOf (PactType.tock alphabet) + 1) _ = _
  simp only [typeFutureOffersFuel]

@[simp] theorem typeFutureOffers_progress (alphabet : PactTypeAlphabet)
    (pid : ProcId) : typeFutureOffers (.progress alphabet pid) = ∅ := by
  change typeFutureOffersFuel (sizeOf (PactType.progress alphabet pid) + 1) _ = _
  simp only [typeFutureOffersFuel]

@[simp] theorem typeFutureOffers_var (alphabet : PactTypeAlphabet)
    (name : String) : typeFutureOffers (.var alphabet name) = ∅ := by
  change typeFutureOffersFuel (sizeOf (PactType.var alphabet name) + 1) _ = _
  simp only [typeFutureOffersFuel]

theorem typeFutureOffers_xoffer_of_undeclared (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hGate : ¬ ∀ b ∈ branches, b.1 ∈ alphabet.actions) :
    typeFutureOffers (.xoffer alphabet elseType branches) = ∅ := by
  change typeFutureOffersFuel
    (sizeOf (PactType.xoffer alphabet elseType branches) + 1) _ = _
  simp only [typeFutureOffersFuel, if_neg hGate]

theorem typeFutureOffers_offer_of_undeclared (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hGate : ¬ ∀ b ∈ branches, b.1 ∈ alphabet.actions) :
    typeFutureOffers (.offer alphabet elseType branches) = ∅ := by
  change typeFutureOffersFuel
    (sizeOf (PactType.offer alphabet elseType branches) + 1) _ = _
  simp only [typeFutureOffersFuel, if_neg hGate]

/-- The two hiding operators coincide on bare menus. -/
theorem hideProcOffers_eq (interface : Interface) (offers : Finset BareMessage) :
    hideProcOffers interface offers = hideTypeOffers interface offers := rfl

/-- The two interface restrictions coincide on bare menus. -/
theorem restrictFuture_eq (interface : Interface) (offers : Finset BareMessage) :
    restrictFuture interface offers = restrictTypeOffers interface offers := rfl

/-! ## `FutOff` -/

private theorem futureOffers_aux : ∀ n : Nat,
    (∀ (fuel : Nat) (process : Proc), sizeOf process < n → sizeOf process < fuel →
      procFutureOffersFuel fuel process = typeFutureOffers (inferProcess process)) ∧
    (∀ (fuel : Nat) (branches : List ChoiceBranch) (initial : Finset BareMessage),
      sizeOf branches < n →
      (∀ branch ∈ branches, sizeOf (ChoiceBranch.continuation branch) < fuel) →
      branches.foldl (fun offers branch =>
          offers ∪ {ChoiceBranch.action branch} ∪
            procFutureOffersFuel fuel (ChoiceBranch.continuation branch)) initial =
        (inferBranches branches).foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffers branch.2) initial) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ h => absurd h (by omega), fun _ _ _ h => absurd h (by omega)⟩
  | succ n ih =>
      obtain ⟨ihProc, ihBranch⟩ := ih
      refine ⟨?_, ?_⟩
      · intro fuel process hSize hFuel
        obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        cases process with
        | send alphabet msg expr p =>
            have hp : sizeOf p < n ∧ sizeOf p < fuel := by
              simp at hSize hFuel ⊢; omega
            rw [inferProcess, typeFutureOffers_sequence, canCompleteDeclared_message,
              typeFutureOffers_message]
            simp only [procFutureOffersFuel, ihProc fuel p hp.1 hp.2]
            by_cases hMem : (msg, MessageDir.send) ∈ alphabet.actions <;>
              simp [hMem]
        | recv alphabet msg varName p =>
            have hp : sizeOf p < n ∧ sizeOf p < fuel := by
              simp at hSize hFuel ⊢; omega
            rw [inferProcess, typeFutureOffers_sequence, canCompleteDeclared_message,
              typeFutureOffers_message]
            simp only [procFutureOffersFuel, ihProc fuel p hp.1 hp.2]
            by_cases hMem : (msg, MessageDir.recv) ∈ alphabet.actions <;>
              simp [hMem]
        | var alphabet name => simp [procFutureOffersFuel, inferProcess]
        | skip alphabet => simp [procFutureOffersFuel, inferProcess]
        | endp alphabet pid => simp [procFutureOffersFuel, inferProcess]
        | cycle alphabet => simp [procFutureOffersFuel, inferProcess]
        | recur alphabet name body =>
            have hp : sizeOf body < n ∧ sizeOf body < fuel := by
              simp at hSize hFuel ⊢; omega
            rw [inferProcess, typeFutureOffers_recur]
            simp only [procFutureOffersFuel, ihProc fuel body hp.1 hp.2]
        | par alphabet left right interface =>
            have hl : sizeOf left < n ∧ sizeOf left < fuel := by
              simp at hSize hFuel ⊢; omega
            have hr : sizeOf right < n ∧ sizeOf right < fuel := by
              simp at hSize hFuel ⊢; omega
            rw [inferProcess, typeFutureOffers_parallel]
            simp only [procFutureOffersFuel, ihProc fuel left hl.1 hl.2,
              ihProc fuel right hr.1 hr.2, hideProcOffers_eq]
        | seq alphabet left right =>
            have hl : sizeOf left < n ∧ sizeOf left < fuel := by
              simp at hSize hFuel ⊢; omega
            have hr : sizeOf right < n ∧ sizeOf right < fuel := by
              simp at hSize hFuel ⊢; omega
            rw [inferProcess, typeFutureOffers_sequence,
              ← canCompleteBeforeTock_inferProcess]
            simp only [procFutureOffersFuel, ihProc fuel left hl.1 hl.2,
              ihProc fuel right hr.1 hr.2]
        | letp alphabet varName expr p =>
            have hp : sizeOf p < n ∧ sizeOf p < fuel := by
              simp at hSize hFuel ⊢; omega
            rw [inferProcess, typeFutureOffers_sequence]
            simp only [procFutureOffersFuel, ihProc fuel p hp.1 hp.2,
              canCompleteDeclared_skip, typeFutureOffers_skip, if_true,
              Finset.empty_union]
        | ifunfair alphabet expr left right =>
            have hl : sizeOf left < n ∧ sizeOf left < fuel := by
              simp at hSize hFuel ⊢; omega
            have hr : sizeOf right < n ∧ sizeOf right < fuel := by
              simp at hSize hFuel ⊢; omega
            rw [inferProcess, typeFutureOffers_choice]
            simp only [procFutureOffersFuel, ihProc fuel left hl.1 hl.2,
              ihProc fuel right hr.1 hr.2]
        | iffair alphabet bid expr left right =>
            have hl : sizeOf left < n ∧ sizeOf left < fuel := by
              simp at hSize hFuel ⊢; omega
            have hr : sizeOf right < n ∧ sizeOf right < fuel := by
              simp at hSize hFuel ⊢; omega
            rw [inferProcess, typeFutureOffers_fairChoice]
            simp only [procFutureOffersFuel, ihProc fuel left hl.1 hl.2,
              ihProc fuel right hr.1 hr.2]
        | xoffer alphabet elseProcess branches =>
            have hp : sizeOf elseProcess < n ∧ sizeOf elseProcess < fuel := by
              simp at hSize hFuel ⊢; omega
            have hb : sizeOf branches < n ∧
                ∀ branch ∈ branches,
                  sizeOf (ChoiceBranch.continuation branch) < fuel := by
              refine ⟨by simp at hSize ⊢; omega, ?_⟩
              intro branch hBranch
              have hMem := List.sizeOf_lt_of_mem hBranch
              have hCont := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hFuel ⊢; omega
            rw [inferProcess]
            by_cases hGate : BranchesDeclared alphabet branches
            · rw [typeFutureOffers_xoffer _ _ _
                ((branchesDeclared_inferBranches alphabet branches).2 hGate)]
              simp only [procFutureOffersFuel,
                branchesDeclared_eq_decide, decide_eq_true_eq, if_pos hGate,
                ihProc fuel elseProcess hp.1 hp.2]
              exact ihBranch fuel branches _ hb.1 hb.2
            · rw [typeFutureOffers_xoffer_of_undeclared _ _ _
                (fun h => hGate ((branchesDeclared_inferBranches alphabet branches).1 h))]
              simp only [procFutureOffersFuel,
                branchesDeclared_eq_decide, decide_eq_true_eq, if_neg hGate]
        | offer alphabet elseProcess branches =>
            have hp : sizeOf elseProcess < n ∧ sizeOf elseProcess < fuel := by
              simp at hSize hFuel ⊢; omega
            have hb : sizeOf branches < n ∧
                ∀ branch ∈ branches,
                  sizeOf (ChoiceBranch.continuation branch) < fuel := by
              refine ⟨by simp at hSize ⊢; omega, ?_⟩
              intro branch hBranch
              have hMem := List.sizeOf_lt_of_mem hBranch
              have hCont := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hFuel ⊢; omega
            rw [inferProcess]
            by_cases hGate : BranchesDeclared alphabet branches
            · rw [typeFutureOffers_offer _ _ _
                ((branchesDeclared_inferBranches alphabet branches).2 hGate)]
              simp only [procFutureOffersFuel,
                branchesDeclared_eq_decide, decide_eq_true_eq, if_pos hGate,
                ihProc fuel elseProcess hp.1 hp.2]
              exact ihBranch fuel branches _ hb.1 hb.2
            · rw [typeFutureOffers_offer_of_undeclared _ _ _
                (fun h => hGate ((branchesDeclared_inferBranches alphabet branches).1 h))]
              simp only [procFutureOffersFuel,
                branchesDeclared_eq_decide, decide_eq_true_eq, if_neg hGate]
      · intro fuel branches initial hSize hFuel
        cases branches with
        | nil => simp [inferBranches]
        | cons branch rest =>
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            rw [inferBranches_action]
            simp only [List.foldl_cons,
              ihProc fuel (ChoiceBranch.continuation branch) hCont
                (hFuel branch (by simp))]
            exact ihBranch fuel rest _ hRest
              (fun b hb => hFuel b (by simp [hb]))

/-- `FutOff` is preserved by abstraction. -/
theorem procFutureOffers_inferProcess (process : Proc) :
    procFutureOffers process = typeFutureOffers (inferProcess process) :=
  (futureOffers_aux (sizeOf process + 1)).1 (sizeOf process + 1) process
    (by omega) (by omega)

/-- The sequence right-hand menu agrees with its type-level counterpart. -/
theorem procSequenceRightMenu_inferProcess (left right : Proc) :
    procSequenceRightMenu left right =
      sequenceRightMenu (inferProcess left) (inferProcess right) := by
  unfold procSequenceRightMenu sequenceRightMenu
  rw [canCompleteBeforeTock_inferProcess, procFutureOffers_inferProcess]

end

end Pact
