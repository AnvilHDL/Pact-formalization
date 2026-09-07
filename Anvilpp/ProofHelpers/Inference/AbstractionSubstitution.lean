import Anvilpp.ProofHelpers.Inference.ErasureSideConditions

/-!
# Abstraction and substitution

The equations of the paper's first helper for Lemma 4.2: abstraction copies
the written alphabet, ignores value substitution, commutes with recursive
process substitution and with re-signing, and reflects `skip`.
-/

namespace Pact

noncomputable section

open Classical

/-! ## Value substitution -/

private theorem inferProcess_exprReplace_aux : ∀ n : Nat,
    (∀ (process : Proc) (name : String) (value : Bool), sizeOf process < n →
      inferProcess (Semantics.procExprReplace process name value) =
        inferProcess process) ∧
    (∀ (branches : List ChoiceBranch) (name : String) (value : Bool),
      sizeOf branches < n →
      inferBranches (Semantics.choiceBranchesExprReplace branches name value) =
        inferBranches branches) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ h => absurd h (by omega),
      fun _ _ _ h => absurd h (by omega)⟩
  | succ n ih =>
      obtain ⟨ihProc, ihBranch⟩ := ih
      refine ⟨?_, ?_⟩
      · intro process name value hSize
        cases process with
        | send alphabet msg expr p =>
            rw [Semantics.procExprReplace, inferProcess, inferProcess,
              ihProc p name value (by simp at hSize ⊢; omega)]
        | recv alphabet msg varName p =>
            rw [Semantics.procExprReplace, inferProcess, inferProcess]
            by_cases hName : name = varName
            · rw [if_pos hName]
            · rw [if_neg hName, ihProc p name value (by simp at hSize ⊢; omega)]
        | var alphabet name' => rw [Semantics.procExprReplace]
        | skip alphabet => rw [Semantics.procExprReplace]
        | endp alphabet pid => rw [Semantics.procExprReplace]
        | cycle alphabet => rw [Semantics.procExprReplace]
        | par alphabet left right interface =>
            rw [Semantics.procExprReplace, inferProcess, inferProcess,
              ihProc left name value (by simp at hSize ⊢; omega),
              ihProc right name value (by simp at hSize ⊢; omega)]
        | seq alphabet left right =>
            rw [Semantics.procExprReplace, inferProcess, inferProcess,
              ihProc left name value (by simp at hSize ⊢; omega),
              ihProc right name value (by simp at hSize ⊢; omega)]
        | letp alphabet varName expr p =>
            rw [Semantics.procExprReplace, inferProcess, inferProcess]
            by_cases hName : name = varName
            · rw [if_pos hName]
            · rw [if_neg hName, ihProc p name value (by simp at hSize ⊢; omega)]
        | ifunfair alphabet expr left right =>
            rw [Semantics.procExprReplace, inferProcess, inferProcess,
              ihProc left name value (by simp at hSize ⊢; omega),
              ihProc right name value (by simp at hSize ⊢; omega)]
        | iffair alphabet bid expr left right =>
            rw [Semantics.procExprReplace, inferProcess, inferProcess,
              ihProc left name value (by simp at hSize ⊢; omega),
              ihProc right name value (by simp at hSize ⊢; omega)]
        | recur alphabet varName body =>
            rw [Semantics.procExprReplace, inferProcess, inferProcess,
              ihProc body name value (by simp at hSize ⊢; omega)]
        | xoffer alphabet elseProcess branches =>
            rw [Semantics.procExprReplace, inferProcess, inferProcess,
              ihProc elseProcess name value (by simp at hSize ⊢; omega),
              ihBranch branches name value (by simp at hSize ⊢; omega)]
        | offer alphabet elseProcess branches =>
            rw [Semantics.procExprReplace, inferProcess, inferProcess,
              ihProc elseProcess name value (by simp at hSize ⊢; omega),
              ihBranch branches name value (by simp at hSize ⊢; omega)]
      · intro branches name value hSize
        cases branches with
        | nil => rw [Semantics.choiceBranchesExprReplace]
        | cons branch rest =>
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            rw [Semantics.choiceBranchesExprReplace, inferBranches_action,
              inferBranches_action,
              ihBranch rest name value hRest]
            cases branch with
            | send msg expr p =>
                rw [Semantics.choiceBranchExprReplace]
                simp only [ChoiceBranch.action, ChoiceBranch.getMessageId,
                  ChoiceBranch.getDir, ChoiceBranch.continuation]
                rw [ihProc p name value (by simpa [ChoiceBranch.continuation] using hCont)]
            | recv msg varName p =>
                rw [Semantics.choiceBranchExprReplace]
                simp only [ChoiceBranch.action, ChoiceBranch.getMessageId,
                  ChoiceBranch.getDir, ChoiceBranch.continuation]
                by_cases hName : name = varName
                · rw [if_pos hName]
                · rw [if_neg hName,
                    ihProc p name value (by simpa [ChoiceBranch.continuation] using hCont)]

/-- `abs(P[x ↦ v]) = abs(P)`. -/
theorem inferProcess_procExprReplace (process : Proc) (name : String)
    (value : Bool) :
    inferProcess (Semantics.procExprReplace process name value) =
      inferProcess process :=
  (inferProcess_exprReplace_aux (sizeOf process + 1)).1 process name value (by omega)

theorem inferBranches_choiceBranchesExprReplace (branches : List ChoiceBranch)
    (name : String) (value : Bool) :
    inferBranches (Semantics.choiceBranchesExprReplace branches name value) =
      inferBranches branches :=
  (inferProcess_exprReplace_aux (sizeOf branches + 1)).2 branches name value (by omega)

/-- Value substitution does not change the optimistic menu. -/
theorem procFutureOffers_procExprReplace (process : Proc) (name : String)
    (value : Bool) :
    procFutureOffers (Semantics.procExprReplace process name value) =
      procFutureOffers process := by
  rw [procFutureOffers_inferProcess, procFutureOffers_inferProcess,
    inferProcess_procExprReplace]

/-! ## Recursive process substitution -/

private theorem inferProcess_procReplace_aux : ∀ n : Nat,
    (∀ (process replacement : Proc) (name : String), sizeOf process < n →
      inferProcess (Semantics.procReplace process name replacement) =
        (inferProcess process).replaceVar name (inferProcess replacement)) ∧
    (∀ (branches : List ChoiceBranch) (replacement : Proc) (name : String),
      sizeOf branches < n →
      inferBranches (Semantics.choiceBranchesProcReplace branches name replacement) =
        PactType.replaceBranches (inferBranches branches) name
          (inferProcess replacement)) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ h => absurd h (by omega),
      fun _ _ _ h => absurd h (by omega)⟩
  | succ n ih =>
      obtain ⟨ihProc, ihBranch⟩ := ih
      refine ⟨?_, ?_⟩
      · intro process replacement name hSize
        cases process with
        | send alphabet msg expr p =>
            rw [Semantics.procReplace, inferProcess, inferProcess,
              PactType.replaceVar, PactType.replaceVar,
              ihProc p replacement name (by simp at hSize ⊢; omega)]
        | recv alphabet msg varName p =>
            rw [Semantics.procReplace, inferProcess, inferProcess,
              PactType.replaceVar, PactType.replaceVar,
              ihProc p replacement name (by simp at hSize ⊢; omega)]
        | var alphabet varName =>
            rw [Semantics.procReplace, inferProcess, PactType.replaceVar]
            by_cases hName : name = varName
            · rw [if_pos hName, if_pos hName]
            · rw [if_neg hName, if_neg hName, inferProcess]
        | skip alphabet => rw [Semantics.procReplace, inferProcess, PactType.replaceVar]
        | endp alphabet pid =>
            rw [Semantics.procReplace, inferProcess, PactType.replaceVar]
        | cycle alphabet => rw [Semantics.procReplace, inferProcess, PactType.replaceVar]
        | par alphabet left right interface =>
            rw [Semantics.procReplace, inferProcess, inferProcess,
              PactType.replaceVar,
              ihProc left replacement name (by simp at hSize ⊢; omega),
              ihProc right replacement name (by simp at hSize ⊢; omega)]
        | seq alphabet left right =>
            rw [Semantics.procReplace, inferProcess, inferProcess,
              PactType.replaceVar,
              ihProc left replacement name (by simp at hSize ⊢; omega),
              ihProc right replacement name (by simp at hSize ⊢; omega)]
        | letp alphabet varName expr p =>
            rw [Semantics.procReplace, inferProcess, inferProcess,
              PactType.replaceVar, PactType.replaceVar,
              ihProc p replacement name (by simp at hSize ⊢; omega)]
        | ifunfair alphabet expr left right =>
            rw [Semantics.procReplace, inferProcess, inferProcess,
              PactType.replaceVar,
              ihProc left replacement name (by simp at hSize ⊢; omega),
              ihProc right replacement name (by simp at hSize ⊢; omega)]
        | iffair alphabet bid expr left right =>
            rw [Semantics.procReplace, inferProcess, inferProcess,
              PactType.replaceVar,
              ihProc left replacement name (by simp at hSize ⊢; omega),
              ihProc right replacement name (by simp at hSize ⊢; omega)]
        | recur alphabet varName body =>
            rw [Semantics.procReplace, inferProcess, PactType.replaceVar]
            by_cases hName : name = varName
            · rw [if_pos hName, if_pos hName, inferProcess]
            · rw [if_neg hName, if_neg hName, inferProcess,
                ihProc body replacement name (by simp at hSize ⊢; omega)]
        | xoffer alphabet elseProcess branches =>
            rw [Semantics.procReplace, inferProcess, inferProcess,
              PactType.replaceVar,
              ihProc elseProcess replacement name (by simp at hSize ⊢; omega),
              ihBranch branches replacement name (by simp at hSize ⊢; omega)]
        | offer alphabet elseProcess branches =>
            rw [Semantics.procReplace, inferProcess, inferProcess,
              PactType.replaceVar,
              ihProc elseProcess replacement name (by simp at hSize ⊢; omega),
              ihBranch branches replacement name (by simp at hSize ⊢; omega)]
      · intro branches replacement name hSize
        cases branches with
        | nil =>
            rw [Semantics.choiceBranchesProcReplace, inferBranches,
              PactType.replaceBranches]
        | cons branch rest =>
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            rw [Semantics.choiceBranchesProcReplace, inferBranches_action,
              inferBranches_action, PactType.replaceBranches,
              ihBranch rest replacement name hRest]
            cases branch with
            | send msg expr p =>
                rw [Semantics.choiceBranchProcReplace]
                simp only [ChoiceBranch.action, ChoiceBranch.getMessageId,
                  ChoiceBranch.getDir, ChoiceBranch.continuation]
                rw [ihProc p replacement name
                  (by simpa [ChoiceBranch.continuation] using hCont)]
            | recv msg varName p =>
                rw [Semantics.choiceBranchProcReplace]
                simp only [ChoiceBranch.action, ChoiceBranch.getMessageId,
                  ChoiceBranch.getDir, ChoiceBranch.continuation]
                rw [ihProc p replacement name
                  (by simpa [ChoiceBranch.continuation] using hCont)]

/-- `abs(P[X ↦ Q]) = abs(P)[X ↦ abs(Q)]`. -/
theorem inferProcess_procReplace (process replacement : Proc) (name : String) :
    inferProcess (Semantics.procReplace process name replacement) =
      (inferProcess process).replaceVar name (inferProcess replacement) :=
  (inferProcess_procReplace_aux (sizeOf process + 1)).1 process replacement name
    (by omega)

/-! ## Abstraction reflects `skip` -/

/-- `Body(abs(P)) = skip` exactly when `Body(P) = skip`. -/
theorem inferProcess_eq_skip_iff (process : Proc) (alphabet : PactTypeAlphabet) :
    inferProcess process = .skip alphabet ↔ process = Proc.skip alphabet := by
  constructor
  · intro h
    cases process <;> simp_all [inferProcess]
  · intro h
    subst h
    rw [inferProcess]

theorem inferProcess_ne_skip (process : Proc)
    (hSkip : process ≠ Proc.skip process.alphabet) :
    inferProcess process ≠ .skip (inferProcess process).alphabet := by
  rw [alphabet_inferProcess]
  intro h
  exact hSkip ((inferProcess_eq_skip_iff process process.alphabet).1 h)

theorem ne_skip_of_inferProcess_ne (process : Proc)
    (hSkip : inferProcess process ≠ .skip (inferProcess process).alphabet) :
    process ≠ Proc.skip process.alphabet := by
  rw [alphabet_inferProcess] at hSkip
  intro h
  exact hSkip ((inferProcess_eq_skip_iff process process.alphabet).2 h)

/-! ## Re-signing -/

theorem PactType.reannotateOfferBranches_eq (alphabet : PactTypeAlphabet)
    (seen : Finset BareMessage) (branches : List (BareMessage × PactType)) :
    PactType.reannotateOfferBranches alphabet seen branches =
      PactType.reannotateBranches alphabet branches := by
  induction branches with
  | nil => rw [PactType.reannotateOfferBranches, PactType.reannotateBranches]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      rw [PactType.reannotateOfferBranches, PactType.reannotateBranches, ih]

private theorem inferProcess_reannotate_aux : ∀ n : Nat,
    (∀ (process : Proc) (alphabet : PactTypeAlphabet), sizeOf process < n →
      inferProcess (Proc.reannotate alphabet process) =
        (inferProcess process).reannotate alphabet) ∧
    (∀ (branches : List ChoiceBranch) (alphabet : PactTypeAlphabet),
      sizeOf branches < n →
      inferBranches (Proc.reannotateBranches alphabet branches) =
        PactType.reannotateBranches alphabet (inferBranches branches)) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ h => absurd h (by omega), fun _ _ h => absurd h (by omega)⟩
  | succ n ih =>
      obtain ⟨ihProc, ihBranch⟩ := ih
      refine ⟨?_, ?_⟩
      · intro process alphabet hSize
        cases process with
        | send alpha msg expr p =>
            rw [Proc.reannotate, inferProcess, inferProcess, PactType.reannotate,
              PactType.reannotate, ihProc p alphabet (by simp at hSize ⊢; omega)]
        | recv alpha msg varName p =>
            rw [Proc.reannotate, inferProcess, inferProcess, PactType.reannotate,
              PactType.reannotate, ihProc p alphabet (by simp at hSize ⊢; omega)]
        | var alpha name =>
            rw [Proc.reannotate, inferProcess, inferProcess, PactType.reannotate]
        | skip alpha =>
            rw [Proc.reannotate, inferProcess, inferProcess, PactType.reannotate]
        | endp alpha pid =>
            rw [Proc.reannotate, inferProcess, inferProcess, PactType.reannotate]
        | cycle alpha =>
            rw [Proc.reannotate, inferProcess, inferProcess, PactType.reannotate]
        | par alpha left right interface =>
            rw [Proc.reannotate, inferProcess, inferProcess, PactType.reannotate,
              ihProc left _ (by simp at hSize ⊢; omega),
              ihProc right _ (by simp at hSize ⊢; omega),
              alphabet_inferProcess, alphabet_inferProcess]
        | seq alpha left right =>
            rw [Proc.reannotate, inferProcess, inferProcess, PactType.reannotate,
              ihProc left alphabet (by simp at hSize ⊢; omega),
              ihProc right alphabet (by simp at hSize ⊢; omega)]
        | letp alpha varName expr p =>
            rw [Proc.reannotate, inferProcess, inferProcess, PactType.reannotate,
              PactType.reannotate, ihProc p alphabet (by simp at hSize ⊢; omega)]
        | ifunfair alpha expr left right =>
            rw [Proc.reannotate, inferProcess, inferProcess, PactType.reannotate,
              ihProc left alphabet (by simp at hSize ⊢; omega),
              ihProc right alphabet (by simp at hSize ⊢; omega)]
        | iffair alpha bid expr left right =>
            rw [Proc.reannotate, inferProcess, inferProcess, PactType.reannotate,
              ihProc left alphabet (by simp at hSize ⊢; omega),
              ihProc right alphabet (by simp at hSize ⊢; omega)]
        | recur alpha name body =>
            rw [Proc.reannotate, inferProcess, inferProcess, PactType.reannotate,
              ihProc body alphabet (by simp at hSize ⊢; omega)]
        | xoffer alpha elseProcess branches =>
            rw [Proc.reannotate, inferProcess, inferProcess, PactType.reannotate,
              ihProc elseProcess alphabet (by simp at hSize ⊢; omega),
              ihBranch branches alphabet (by simp at hSize ⊢; omega)]
        | offer alpha elseProcess branches =>
            rw [Proc.reannotate, inferProcess, inferProcess, PactType.reannotate,
              PactType.reannotateOfferBranches_eq,
              ihProc elseProcess alphabet (by simp at hSize ⊢; omega),
              ihBranch branches alphabet (by simp at hSize ⊢; omega)]
      · intro branches alphabet hSize
        cases branches with
        | nil =>
            rw [Proc.reannotateBranches, inferBranches, PactType.reannotateBranches]
        | cons branch rest =>
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            rw [inferBranches_action, PactType.reannotateBranches,
              ← ihBranch rest alphabet hRest]
            cases branch with
            | send msg expr p =>
                rw [Proc.reannotateBranches, inferBranches_action]
                simp only [ChoiceBranch.action, ChoiceBranch.getMessageId,
                  ChoiceBranch.getDir, ChoiceBranch.continuation]
                rw [ihProc p alphabet (by simpa [ChoiceBranch.continuation] using hCont)]
            | recv msg varName p =>
                rw [Proc.reannotateBranches, inferBranches_action]
                simp only [ChoiceBranch.action, ChoiceBranch.getMessageId,
                  ChoiceBranch.getDir, ChoiceBranch.continuation]
                rw [ihProc p alphabet (by simpa [ChoiceBranch.continuation] using hCont)]

/-- `abs(P[Ω]) = abs(P)[Ω]`. -/
theorem inferProcess_reannotate (process : Proc) (alphabet : PactTypeAlphabet) :
    inferProcess (Proc.reannotate alphabet process) =
      (inferProcess process).reannotate alphabet :=
  (inferProcess_reannotate_aux (sizeOf process + 1)).1 process alphabet (by omega)

end

end Pact
