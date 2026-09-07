import Anvilpp.ProofHelpers.Inference.AbstractionSubstitution

/-!
# Written alphabets under abstraction

`AlphaWF_P(P)` iff `AlphaWF(abs(P))`, and a process whose alphabets are well
formed is already re-signed by its own alphabet.  The second fact is what
makes the re-signing inside the type-level conjunctive commitment a no-op,
matching the paper's `conjunctCompatible` premise.
-/

namespace Pact

noncomputable section

open Classical

/-- `Π_I(Ω,Ω_c) = Ω_c` for a compatible child. -/
theorem PactTypeAlphabet.projectParallel_left
    {parent left right : PactTypeAlphabet} {interface : Interface}
    (hCompatible : PactTypeAlphabet.ParallelCompatible parent left right interface) :
    PactTypeAlphabet.projectParallel parent left interface = left := by
  have hHide : PactTypeAlphabet.hideInterface left interface = parent :=
    hCompatible.parent_eq_left
  have hActions : parent.actions =
      left.actions.filter fun action => action.1 ∉ interface := by
    rw [← hHide]; rfl
  cases left with
  | mk actions =>
      simp only [PactTypeAlphabet.projectParallel, hActions,
        PactTypeAlphabet.mk.injEq]
      exact Finset.filter_union_filter_neg_eq _ _

theorem PactTypeAlphabet.projectParallel_right
    {parent left right : PactTypeAlphabet} {interface : Interface}
    (hCompatible : PactTypeAlphabet.ParallelCompatible parent left right interface) :
    PactTypeAlphabet.projectParallel parent right interface = right := by
  have hHide : PactTypeAlphabet.hideInterface right interface = parent :=
    hCompatible.parent_eq_right
  have hActions : parent.actions =
      right.actions.filter fun action => action.1 ∉ interface := by
    rw [← hHide]; rfl
  cases right with
  | mk actions =>
      simp only [PactTypeAlphabet.projectParallel, hActions,
        PactTypeAlphabet.mk.injEq]
      exact Finset.filter_union_filter_neg_eq _ _

private theorem reannotate_eq_self_aux : ∀ n : Nat,
    (∀ (process : Proc) (alphabet : PactTypeAlphabet), sizeOf process < n →
      Proc.AlphabetWellFormed process → process.alphabet = alphabet →
      Proc.reannotate alphabet process = process) ∧
    (∀ (branches : List ChoiceBranch) (alphabet : PactTypeAlphabet),
      sizeOf branches < n →
      Proc.BranchesAlphabetWellFormed alphabet branches →
      Proc.reannotateBranches alphabet branches = branches) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ h => absurd h (by omega), fun _ _ h => absurd h (by omega)⟩
  | succ n ih =>
      obtain ⟨ihProc, ihBranch⟩ := ih
      refine ⟨?_, ?_⟩
      · intro process alphabet hSize hWF hAlpha
        cases process with
        | send alpha msg expr p =>
            rw [Proc.AlphabetWellFormed] at hWF
            rw [Proc.alphabet] at hAlpha
            subst hAlpha
            rw [Proc.reannotate,
              ihProc p _ (by simp at hSize ⊢; omega) hWF.2.2 hWF.2.1]
        | recv alpha msg varName p =>
            rw [Proc.AlphabetWellFormed] at hWF
            rw [Proc.alphabet] at hAlpha
            subst hAlpha
            rw [Proc.reannotate,
              ihProc p _ (by simp at hSize ⊢; omega) hWF.2.2 hWF.2.1]
        | var alpha name => rw [Proc.alphabet] at hAlpha; subst hAlpha; rw [Proc.reannotate]
        | skip alpha => rw [Proc.alphabet] at hAlpha; subst hAlpha; rw [Proc.reannotate]
        | endp alpha pid => rw [Proc.alphabet] at hAlpha; subst hAlpha; rw [Proc.reannotate]
        | cycle alpha => rw [Proc.alphabet] at hAlpha; subst hAlpha; rw [Proc.reannotate]
        | par alpha left right interface =>
            rw [Proc.AlphabetWellFormed] at hWF
            rw [Proc.alphabet] at hAlpha
            subst hAlpha
            rw [Proc.reannotate]
            simp only [PactTypeAlphabet.projectParallel_left hWF.2.1,
              PactTypeAlphabet.projectParallel_right hWF.2.1]
            rw [ihProc left _ (by simp at hSize ⊢; omega) hWF.2.2.1 rfl,
              ihProc right _ (by simp at hSize ⊢; omega) hWF.2.2.2 rfl]
        | seq alpha left right =>
            rw [Proc.AlphabetWellFormed] at hWF
            rw [Proc.alphabet] at hAlpha
            subst hAlpha
            rw [Proc.reannotate,
              ihProc left _ (by simp at hSize ⊢; omega) hWF.2.2.2.1 hWF.2.1,
              ihProc right _ (by simp at hSize ⊢; omega) hWF.2.2.2.2 hWF.2.2.1]
        | letp alpha varName expr p =>
            rw [Proc.AlphabetWellFormed] at hWF
            rw [Proc.alphabet] at hAlpha
            subst hAlpha
            rw [Proc.reannotate,
              ihProc p _ (by simp at hSize ⊢; omega) hWF.2.2 hWF.2.1]
        | ifunfair alpha expr left right =>
            rw [Proc.AlphabetWellFormed] at hWF
            rw [Proc.alphabet] at hAlpha
            subst hAlpha
            rw [Proc.reannotate,
              ihProc left _ (by simp at hSize ⊢; omega) hWF.2.2.2.1 hWF.2.1,
              ihProc right _ (by simp at hSize ⊢; omega) hWF.2.2.2.2 hWF.2.2.1]
        | iffair alpha bid expr left right =>
            rw [Proc.AlphabetWellFormed] at hWF
            rw [Proc.alphabet] at hAlpha
            subst hAlpha
            rw [Proc.reannotate,
              ihProc left _ (by simp at hSize ⊢; omega) hWF.2.2.2.1 hWF.2.1,
              ihProc right _ (by simp at hSize ⊢; omega) hWF.2.2.2.2 hWF.2.2.1]
        | recur alpha name body =>
            rw [Proc.AlphabetWellFormed] at hWF
            rw [Proc.alphabet] at hAlpha
            subst hAlpha
            rw [Proc.reannotate,
              ihProc body _ (by simp at hSize ⊢; omega) hWF.2.2 hWF.2.1]
        | xoffer alpha elseProcess branches =>
            rw [Proc.AlphabetWellFormed] at hWF
            rw [Proc.alphabet] at hAlpha
            subst hAlpha
            rw [Proc.reannotate,
              ihProc elseProcess _ (by simp at hSize ⊢; omega) hWF.2.2.1 hWF.2.1,
              ihBranch branches _ (by simp at hSize ⊢; omega) hWF.2.2.2]
        | offer alpha elseProcess branches =>
            rw [Proc.AlphabetWellFormed] at hWF
            rw [Proc.alphabet] at hAlpha
            subst hAlpha
            rw [Proc.reannotate,
              ihProc elseProcess _ (by simp at hSize ⊢; omega) hWF.2.2.1 hWF.2.1,
              ihBranch branches _ (by simp at hSize ⊢; omega) hWF.2.2.2]
      · intro branches alphabet hSize hWF
        cases branches with
        | nil => rw [Proc.reannotateBranches]
        | cons branch rest =>
            rw [Proc.BranchesAlphabetWellFormed] at hWF
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            cases branch with
            | send msg expr p =>
                simp only [ChoiceBranch.continuation] at hWF hCont
                rw [Proc.reannotateBranches, ihProc p _ hCont hWF.2.1 hWF.1,
                  ihBranch rest _ hRest hWF.2.2]
            | recv msg varName p =>
                simp only [ChoiceBranch.continuation] at hWF hCont
                rw [Proc.reannotateBranches, ihProc p _ hCont hWF.2.1 hWF.1,
                  ihBranch rest _ hRest hWF.2.2]

/-- A process signed by well-formed alphabets is fixed by re-signing with its
own alphabet. -/
theorem Proc.reannotate_eq_self {process : Proc} {alphabet : PactTypeAlphabet}
    (hWF : Proc.AlphabetWellFormed process) (hAlpha : process.alphabet = alphabet) :
    Proc.reannotate alphabet process = process :=
  (reannotate_eq_self_aux (sizeOf process + 1)).1 process alphabet (by omega)
    hWF hAlpha

theorem Proc.reannotateBranches_eq_self {branches : List ChoiceBranch}
    {alphabet : PactTypeAlphabet}
    (hWF : Proc.BranchesAlphabetWellFormed alphabet branches) :
    Proc.reannotateBranches alphabet branches = branches :=
  (reannotate_eq_self_aux (sizeOf branches + 1)).2 branches alphabet (by omega) hWF

/-- The abstraction of an alphabet-well-formed process is fixed by re-signing. -/
theorem PactType.reannotate_inferProcess_eq_self {process : Proc}
    {alphabet : PactTypeAlphabet} (hWF : Proc.AlphabetWellFormed process)
    (hAlpha : process.alphabet = alphabet) :
    (inferProcess process).reannotate alphabet = inferProcess process := by
  rw [← inferProcess_reannotate, Proc.reannotate_eq_self hWF hAlpha]

/-! ## `AlphaWF_P(P)` iff `AlphaWF(abs(P))` -/

private theorem alphabetWellFormed_inferProcess_aux : ∀ n : Nat,
    (∀ process : Proc, sizeOf process < n →
      (Proc.AlphabetWellFormed process ↔
        PactType.AlphabetWellFormed (inferProcess process))) ∧
    (∀ (branches : List ChoiceBranch) (alphabet : PactTypeAlphabet),
      sizeOf branches < n →
      (Proc.BranchesAlphabetWellFormed alphabet branches ↔
        PactType.BranchesAlphabetWellFormed alphabet (inferBranches branches))) ∧
    (∀ (branches : List ChoiceBranch) (alphabet : PactTypeAlphabet)
      (seen : Finset BareMessage), sizeOf branches < n →
      (Proc.BranchesAlphabetWellFormed alphabet branches ↔
        PactType.OfferBranchesWellFormed alphabet seen (inferBranches branches))) := by
  intro n
  induction n with
  | zero =>
      exact ⟨fun _ h => absurd h (by omega), fun _ _ h => absurd h (by omega),
        fun _ _ _ h => absurd h (by omega)⟩
  | succ n ih =>
      obtain ⟨ihProc, ihBranch, ihOfferBranch⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · intro process hSize
        cases process with
        | send alphabet msg expr p =>
            rw [Proc.AlphabetWellFormed, inferProcess, PactType.AlphabetWellFormed,
              PactType.AlphabetWellFormed, PactType.alphabet,
              alphabet_inferProcess, ihProc p (by simp at hSize ⊢; omega)]
            tauto
        | recv alphabet msg varName p =>
            rw [Proc.AlphabetWellFormed, inferProcess, PactType.AlphabetWellFormed,
              PactType.AlphabetWellFormed, PactType.alphabet,
              alphabet_inferProcess, ihProc p (by simp at hSize ⊢; omega)]
            tauto
        | var alphabet name =>
            rw [Proc.AlphabetWellFormed, inferProcess, PactType.AlphabetWellFormed]
        | skip alphabet =>
            rw [Proc.AlphabetWellFormed, inferProcess, PactType.AlphabetWellFormed]
        | endp alphabet pid =>
            rw [Proc.AlphabetWellFormed, inferProcess, PactType.AlphabetWellFormed]
        | cycle alphabet =>
            rw [Proc.AlphabetWellFormed, inferProcess, PactType.AlphabetWellFormed]
        | par alphabet left right interface =>
            rw [Proc.AlphabetWellFormed, inferProcess, PactType.AlphabetWellFormed,
              alphabet_inferProcess, alphabet_inferProcess,
              ihProc left (by simp at hSize ⊢; omega),
              ihProc right (by simp at hSize ⊢; omega)]
        | seq alphabet left right =>
            rw [Proc.AlphabetWellFormed, inferProcess, PactType.AlphabetWellFormed,
              alphabet_inferProcess, alphabet_inferProcess,
              ihProc left (by simp at hSize ⊢; omega),
              ihProc right (by simp at hSize ⊢; omega)]
        | letp alphabet varName expr p =>
            rw [Proc.AlphabetWellFormed, inferProcess, PactType.AlphabetWellFormed,
              PactType.AlphabetWellFormed, PactType.alphabet,
              alphabet_inferProcess, ihProc p (by simp at hSize ⊢; omega)]
            tauto
        | ifunfair alphabet expr left right =>
            rw [Proc.AlphabetWellFormed, inferProcess, PactType.AlphabetWellFormed,
              alphabet_inferProcess, alphabet_inferProcess,
              ihProc left (by simp at hSize ⊢; omega),
              ihProc right (by simp at hSize ⊢; omega)]
        | iffair alphabet bid expr left right =>
            rw [Proc.AlphabetWellFormed, inferProcess, PactType.AlphabetWellFormed,
              alphabet_inferProcess, alphabet_inferProcess,
              ihProc left (by simp at hSize ⊢; omega),
              ihProc right (by simp at hSize ⊢; omega)]
        | recur alphabet name body =>
            rw [Proc.AlphabetWellFormed, inferProcess, PactType.AlphabetWellFormed,
              alphabet_inferProcess, ihProc body (by simp at hSize ⊢; omega)]
        | xoffer alphabet elseProcess branches =>
            rw [Proc.AlphabetWellFormed, inferProcess, PactType.AlphabetWellFormed,
              alphabet_inferProcess,
              ihProc elseProcess (by simp at hSize ⊢; omega),
              ihBranch branches alphabet (by simp at hSize ⊢; omega)]
        | offer alphabet elseProcess branches =>
            rw [Proc.AlphabetWellFormed, inferProcess, PactType.AlphabetWellFormed,
              alphabet_inferProcess,
              ihProc elseProcess (by simp at hSize ⊢; omega),
              ihOfferBranch branches alphabet ∅ (by simp at hSize ⊢; omega)]
      · intro branches alphabet hSize
        cases branches with
        | nil =>
            rw [Proc.BranchesAlphabetWellFormed, inferBranches,
              PactType.BranchesAlphabetWellFormed]
        | cons branch rest =>
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            rw [Proc.BranchesAlphabetWellFormed, inferBranches_action,
              PactType.BranchesAlphabetWellFormed, alphabet_inferProcess,
              ihProc (ChoiceBranch.continuation branch) hCont,
              ihBranch rest alphabet hRest]
      · intro branches alphabet seen hSize
        cases branches with
        | nil =>
            rw [Proc.BranchesAlphabetWellFormed, inferBranches,
              PactType.OfferBranchesWellFormed]
        | cons branch rest =>
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            rw [Proc.BranchesAlphabetWellFormed, inferBranches_action,
              PactType.OfferBranchesWellFormed, alphabet_inferProcess,
              ihProc (ChoiceBranch.continuation branch) hCont,
              ihOfferBranch rest alphabet seen hRest]

/-- `AlphaWF_P(P)` iff `AlphaWF(abs(P))`. -/
theorem Proc.alphabetWellFormed_iff (process : Proc) :
    Proc.AlphabetWellFormed process ↔
      PactType.AlphabetWellFormed (inferProcess process) :=
  (alphabetWellFormed_inferProcess_aux (sizeOf process + 1)).1 process (by omega)

theorem Proc.branchesAlphabetWellFormed_iff (branches : List ChoiceBranch)
    (alphabet : PactTypeAlphabet) :
    Proc.BranchesAlphabetWellFormed alphabet branches ↔
      PactType.BranchesAlphabetWellFormed alphabet (inferBranches branches) :=
  (alphabetWellFormed_inferProcess_aux (sizeOf branches + 1)).2.1 branches alphabet
    (by omega)

end

end Pact
