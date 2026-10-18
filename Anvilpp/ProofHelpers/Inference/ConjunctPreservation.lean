import Anvilpp.ProofHelpers.Inference.OneStepAbstraction

/-!
# `ConjMsgOwn` along a step

Distinct conjunctive heads survive every process rule: substitution and
re-signing leave branch heads untouched, and a conjunctive commitment produces
singleton exclusive offers rather than new conjunctive offers.
-/

namespace Pact

noncomputable section

open Classical

theorem branchHeadsDistinct_iff (branches : List ChoiceBranch) :
    BranchHeadsDistinct branches ↔
      (branches.map ChoiceBranch.action).Pairwise (· ≠ ·) := by
  rw [BranchHeadsDistinct, List.pairwise_map]

theorem branchHeadsDistinct_of_map_eq {branches branches' : List ChoiceBranch}
    (hMap : branches'.map ChoiceBranch.action = branches.map ChoiceBranch.action)
    (hDistinct : BranchHeadsDistinct branches) : BranchHeadsDistinct branches' := by
  rw [branchHeadsDistinct_iff] at hDistinct ⊢
  rwa [hMap]

theorem map_action_choiceBranchesExprReplace (branches : List ChoiceBranch)
    (name : String) (value : Bool) :
    (Semantics.choiceBranchesExprReplace branches name value).map
        ChoiceBranch.action = branches.map ChoiceBranch.action := by
  induction branches with
  | nil => rw [Semantics.choiceBranchesExprReplace]
  | cons branch rest ih =>
      rw [Semantics.choiceBranchesExprReplace, List.map_cons, List.map_cons, ih]
      cases branch <;> (rw [Semantics.choiceBranchExprReplace]; rfl)

theorem map_action_choiceBranchesProcReplace (branches : List ChoiceBranch)
    (name : String) (replacement : Proc) :
    (Semantics.choiceBranchesProcReplace branches name replacement).map
        ChoiceBranch.action = branches.map ChoiceBranch.action := by
  induction branches with
  | nil => rw [Semantics.choiceBranchesProcReplace]
  | cons branch rest ih =>
      rw [Semantics.choiceBranchesProcReplace, List.map_cons, List.map_cons, ih]
      cases branch <;> (rw [Semantics.choiceBranchProcReplace]; rfl)

theorem map_action_reannotateBranches (alphabet : PactTypeAlphabet)
    (branches : List ChoiceBranch) :
    (Proc.reannotateBranches alphabet branches).map ChoiceBranch.action =
      branches.map ChoiceBranch.action := by
  induction branches with
  | nil => rw [Proc.reannotateBranches]
  | cons branch rest ih =>
      cases branch <;>
        (rw [Proc.reannotateBranches, List.map_cons, List.map_cons, ih]; rfl)

/-! ## Substitution and re-signing -/

private theorem conjunctRegular_transform_aux : ∀ n : Nat,
    (∀ (process : Proc) (name : String) (value : Bool), sizeOf process < n →
      Proc.ConjunctRegular process →
      Proc.ConjunctRegular (Semantics.procExprReplace process name value)) ∧
    (∀ (branches : List ChoiceBranch) (name : String) (value : Bool),
      sizeOf branches < n → Proc.ConjunctRegularBranches branches →
      Proc.ConjunctRegularBranches
        (Semantics.choiceBranchesExprReplace branches name value)) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ h => absurd h (by omega),
      fun _ _ _ h => absurd h (by omega)⟩
  | succ n ih =>
      obtain ⟨ihProc, ihBranch⟩ := ih
      refine ⟨?_, ?_⟩
      · intro process name value hSize hRegular
        cases process with
        | send alphabet msg expr p =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procExprReplace, Proc.ConjunctRegular]
            exact ihProc p _ _ (by simp at hSize ⊢; omega) hRegular
        | recv alphabet msg varName p =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procExprReplace, Proc.ConjunctRegular]
            by_cases hName : name = varName
            · rw [if_pos hName]; exact hRegular
            · rw [if_neg hName]
              exact ihProc p _ _ (by simp at hSize ⊢; omega) hRegular
        | var alphabet other => rw [Semantics.procExprReplace]; trivial
        | skip alphabet => rw [Semantics.procExprReplace]; trivial
        | endp alphabet pid => rw [Semantics.procExprReplace]; trivial
        | cycle alphabet => rw [Semantics.procExprReplace]; trivial
        | par alphabet left right interface =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procExprReplace, Proc.ConjunctRegular]
            exact ⟨ihProc left _ _ (by simp at hSize ⊢; omega) hRegular.1,
              ihProc right _ _ (by simp at hSize ⊢; omega) hRegular.2⟩
        | seq alphabet left right =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procExprReplace, Proc.ConjunctRegular]
            exact ⟨ihProc left _ _ (by simp at hSize ⊢; omega) hRegular.1,
              ihProc right _ _ (by simp at hSize ⊢; omega) hRegular.2⟩
        | letp alphabet varName expr p =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procExprReplace, Proc.ConjunctRegular]
            by_cases hName : name = varName
            · rw [if_pos hName]; exact hRegular
            · rw [if_neg hName]
              exact ihProc p _ _ (by simp at hSize ⊢; omega) hRegular
        | ifunfair alphabet expr left right =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procExprReplace, Proc.ConjunctRegular]
            exact ⟨ihProc left _ _ (by simp at hSize ⊢; omega) hRegular.1,
              ihProc right _ _ (by simp at hSize ⊢; omega) hRegular.2⟩
        | iffair alphabet bid expr left right =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procExprReplace, Proc.ConjunctRegular]
            exact ⟨ihProc left _ _ (by simp at hSize ⊢; omega) hRegular.1,
              ihProc right _ _ (by simp at hSize ⊢; omega) hRegular.2⟩
        | recur alphabet other body =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procExprReplace, Proc.ConjunctRegular]
            exact ihProc body _ _ (by simp at hSize ⊢; omega) hRegular
        | xoffer alphabet elseProcess branches =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procExprReplace, Proc.ConjunctRegular]
            exact ⟨ihProc elseProcess _ _ (by simp at hSize ⊢; omega) hRegular.1,
              ihBranch branches _ _ (by simp at hSize ⊢; omega) hRegular.2⟩
        | offer alphabet elseProcess branches =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procExprReplace, Proc.ConjunctRegular]
            exact ⟨branchHeadsDistinct_of_map_eq
                (map_action_choiceBranchesExprReplace branches name value)
                hRegular.1,
              ihProc elseProcess _ _ (by simp at hSize ⊢; omega) hRegular.2.1,
              ihBranch branches _ _ (by simp at hSize ⊢; omega) hRegular.2.2⟩
      · intro branches name value hSize hRegular
        cases branches with
        | nil => rw [Semantics.choiceBranchesExprReplace]; trivial
        | cons branch rest =>
            rw [Proc.ConjunctRegularBranches] at hRegular
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            rw [Semantics.choiceBranchesExprReplace, Proc.ConjunctRegularBranches]
            refine ⟨?_, ihBranch rest _ _ hRest hRegular.2⟩
            cases branch with
            | send msg expr p =>
                simp only [ChoiceBranch.continuation] at hRegular hCont
                rw [Semantics.choiceBranchExprReplace]
                simp only [ChoiceBranch.continuation]
                exact ihProc p _ _ hCont hRegular.1
            | recv msg varName p =>
                simp only [ChoiceBranch.continuation] at hRegular hCont
                rw [Semantics.choiceBranchExprReplace]
                simp only [ChoiceBranch.continuation]
                by_cases hName : name = varName
                · rw [if_pos hName]; exact hRegular.1
                · rw [if_neg hName]; exact ihProc p _ _ hCont hRegular.1

theorem Proc.conjunctRegular_procExprReplace {process : Proc} {name : String}
    {value : Bool} (hRegular : Proc.ConjunctRegular process) :
    Proc.ConjunctRegular (Semantics.procExprReplace process name value) :=
  (conjunctRegular_transform_aux (sizeOf process + 1)).1 process name value
    (by omega) hRegular

private theorem conjunctRegular_procReplace_aux : ∀ n : Nat,
    (∀ (process replacement : Proc) (name : String), sizeOf process < n →
      Proc.ConjunctRegular process → Proc.ConjunctRegular replacement →
      Proc.ConjunctRegular (Semantics.procReplace process name replacement)) ∧
    (∀ (branches : List ChoiceBranch) (replacement : Proc) (name : String),
      sizeOf branches < n → Proc.ConjunctRegularBranches branches →
      Proc.ConjunctRegular replacement →
      Proc.ConjunctRegularBranches
        (Semantics.choiceBranchesProcReplace branches name replacement)) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ h => absurd h (by omega),
      fun _ _ _ h => absurd h (by omega)⟩
  | succ n ih =>
      obtain ⟨ihProc, ihBranch⟩ := ih
      refine ⟨?_, ?_⟩
      · intro process replacement name hSize hRegular hReplacement
        cases process with
        | send alphabet msg expr p =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procReplace, Proc.ConjunctRegular]
            exact ihProc p _ _ (by simp at hSize ⊢; omega) hRegular hReplacement
        | recv alphabet msg varName p =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procReplace, Proc.ConjunctRegular]
            exact ihProc p _ _ (by simp at hSize ⊢; omega) hRegular hReplacement
        | var alphabet other =>
            rw [Semantics.procReplace]
            by_cases hName : name = other
            · rw [if_pos hName]; exact hReplacement
            · rw [if_neg hName]; trivial
        | skip alphabet => rw [Semantics.procReplace]; trivial
        | endp alphabet pid => rw [Semantics.procReplace]; trivial
        | cycle alphabet => rw [Semantics.procReplace]; trivial
        | par alphabet left right interface =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procReplace, Proc.ConjunctRegular]
            exact ⟨ihProc left _ _ (by simp at hSize ⊢; omega) hRegular.1 hReplacement,
              ihProc right _ _ (by simp at hSize ⊢; omega) hRegular.2 hReplacement⟩
        | seq alphabet left right =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procReplace, Proc.ConjunctRegular]
            exact ⟨ihProc left _ _ (by simp at hSize ⊢; omega) hRegular.1 hReplacement,
              ihProc right _ _ (by simp at hSize ⊢; omega) hRegular.2 hReplacement⟩
        | letp alphabet varName expr p =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procReplace, Proc.ConjunctRegular]
            exact ihProc p _ _ (by simp at hSize ⊢; omega) hRegular hReplacement
        | ifunfair alphabet expr left right =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procReplace, Proc.ConjunctRegular]
            exact ⟨ihProc left _ _ (by simp at hSize ⊢; omega) hRegular.1 hReplacement,
              ihProc right _ _ (by simp at hSize ⊢; omega) hRegular.2 hReplacement⟩
        | iffair alphabet bid expr left right =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procReplace, Proc.ConjunctRegular]
            exact ⟨ihProc left _ _ (by simp at hSize ⊢; omega) hRegular.1 hReplacement,
              ihProc right _ _ (by simp at hSize ⊢; omega) hRegular.2 hReplacement⟩
        | recur alphabet other body =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procReplace]
            by_cases hName : name = other
            · rw [if_pos hName, Proc.ConjunctRegular]; exact hRegular
            · rw [if_neg hName, Proc.ConjunctRegular]
              exact ihProc body _ _ (by simp at hSize ⊢; omega) hRegular hReplacement
        | xoffer alphabet elseProcess branches =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procReplace, Proc.ConjunctRegular]
            exact ⟨ihProc elseProcess _ _ (by simp at hSize ⊢; omega) hRegular.1
                hReplacement,
              ihBranch branches _ _ (by simp at hSize ⊢; omega) hRegular.2
                hReplacement⟩
        | offer alphabet elseProcess branches =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Semantics.procReplace, Proc.ConjunctRegular]
            exact ⟨branchHeadsDistinct_of_map_eq
                (map_action_choiceBranchesProcReplace branches name replacement)
                hRegular.1,
              ihProc elseProcess _ _ (by simp at hSize ⊢; omega) hRegular.2.1
                hReplacement,
              ihBranch branches _ _ (by simp at hSize ⊢; omega) hRegular.2.2
                hReplacement⟩
      · intro branches replacement name hSize hRegular hReplacement
        cases branches with
        | nil => rw [Semantics.choiceBranchesProcReplace]; trivial
        | cons branch rest =>
            rw [Proc.ConjunctRegularBranches] at hRegular
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            rw [Semantics.choiceBranchesProcReplace, Proc.ConjunctRegularBranches]
            refine ⟨?_, ihBranch rest _ _ hRest hRegular.2 hReplacement⟩
            cases branch with
            | send msg expr p =>
                simp only [ChoiceBranch.continuation] at hRegular hCont
                rw [Semantics.choiceBranchProcReplace]
                simp only [ChoiceBranch.continuation]
                exact ihProc p _ _ hCont hRegular.1 hReplacement
            | recv msg varName p =>
                simp only [ChoiceBranch.continuation] at hRegular hCont
                rw [Semantics.choiceBranchProcReplace]
                simp only [ChoiceBranch.continuation]
                exact ihProc p _ _ hCont hRegular.1 hReplacement

theorem Proc.conjunctRegular_procReplace {process replacement : Proc}
    {name : String} (hRegular : Proc.ConjunctRegular process)
    (hReplacement : Proc.ConjunctRegular replacement) :
    Proc.ConjunctRegular (Semantics.procReplace process name replacement) :=
  (conjunctRegular_procReplace_aux (sizeOf process + 1)).1 process replacement name
    (by omega) hRegular hReplacement

private theorem conjunctRegular_reannotate_aux : ∀ n : Nat,
    (∀ (process : Proc) (alphabet : PactTypeAlphabet), sizeOf process < n →
      Proc.ConjunctRegular process →
      Proc.ConjunctRegular (Proc.reannotate alphabet process)) ∧
    (∀ (branches : List ChoiceBranch) (alphabet : PactTypeAlphabet),
      sizeOf branches < n → Proc.ConjunctRegularBranches branches →
      Proc.ConjunctRegularBranches (Proc.reannotateBranches alphabet branches)) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ h => absurd h (by omega), fun _ _ h => absurd h (by omega)⟩
  | succ n ih =>
      obtain ⟨ihProc, ihBranch⟩ := ih
      refine ⟨?_, ?_⟩
      · intro process alphabet hSize hRegular
        cases process with
        | send alpha msg expr p =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Proc.reannotate, Proc.ConjunctRegular]
            exact ihProc p _ (by simp at hSize ⊢; omega) hRegular
        | recv alpha msg varName p =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Proc.reannotate, Proc.ConjunctRegular]
            exact ihProc p _ (by simp at hSize ⊢; omega) hRegular
        | var alpha other => rw [Proc.reannotate, Proc.ConjunctRegular]; trivial
        | skip alpha => rw [Proc.reannotate, Proc.ConjunctRegular]; trivial
        | endp alpha pid => rw [Proc.reannotate, Proc.ConjunctRegular]; trivial
        | cycle alpha => rw [Proc.reannotate, Proc.ConjunctRegular]; trivial
        | par alpha left right interface =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Proc.reannotate, Proc.ConjunctRegular]
            exact ⟨ihProc left _ (by simp at hSize ⊢; omega) hRegular.1,
              ihProc right _ (by simp at hSize ⊢; omega) hRegular.2⟩
        | seq alpha left right =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Proc.reannotate, Proc.ConjunctRegular]
            exact ⟨ihProc left _ (by simp at hSize ⊢; omega) hRegular.1,
              ihProc right _ (by simp at hSize ⊢; omega) hRegular.2⟩
        | letp alpha varName expr p =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Proc.reannotate, Proc.ConjunctRegular]
            exact ihProc p _ (by simp at hSize ⊢; omega) hRegular
        | ifunfair alpha expr left right =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Proc.reannotate, Proc.ConjunctRegular]
            exact ⟨ihProc left _ (by simp at hSize ⊢; omega) hRegular.1,
              ihProc right _ (by simp at hSize ⊢; omega) hRegular.2⟩
        | iffair alpha bid expr left right =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Proc.reannotate, Proc.ConjunctRegular]
            exact ⟨ihProc left _ (by simp at hSize ⊢; omega) hRegular.1,
              ihProc right _ (by simp at hSize ⊢; omega) hRegular.2⟩
        | recur alpha other body =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Proc.reannotate, Proc.ConjunctRegular]
            exact ihProc body _ (by simp at hSize ⊢; omega) hRegular
        | xoffer alpha elseProcess branches =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Proc.reannotate, Proc.ConjunctRegular]
            exact ⟨ihProc elseProcess _ (by simp at hSize ⊢; omega) hRegular.1,
              ihBranch branches _ (by simp at hSize ⊢; omega) hRegular.2⟩
        | offer alpha elseProcess branches =>
            rw [Proc.ConjunctRegular] at hRegular
            rw [Proc.reannotate, Proc.ConjunctRegular]
            exact ⟨branchHeadsDistinct_of_map_eq
                (map_action_reannotateBranches alphabet branches) hRegular.1,
              ihProc elseProcess _ (by simp at hSize ⊢; omega) hRegular.2.1,
              ihBranch branches _ (by simp at hSize ⊢; omega) hRegular.2.2⟩
      · intro branches alphabet hSize hRegular
        cases branches with
        | nil => rw [Proc.reannotateBranches]; trivial
        | cons branch rest =>
            rw [Proc.ConjunctRegularBranches] at hRegular
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            cases branch with
            | send msg expr p =>
                simp only [ChoiceBranch.continuation] at hRegular hCont
                rw [Proc.reannotateBranches, Proc.ConjunctRegularBranches]
                simp only [ChoiceBranch.continuation]
                exact ⟨ihProc p _ hCont hRegular.1,
                  ihBranch rest _ hRest hRegular.2⟩
            | recv msg varName p =>
                simp only [ChoiceBranch.continuation] at hRegular hCont
                rw [Proc.reannotateBranches, Proc.ConjunctRegularBranches]
                simp only [ChoiceBranch.continuation]
                exact ⟨ihProc p _ hCont hRegular.1,
                  ihBranch rest _ hRest hRegular.2⟩

theorem Proc.conjunctRegular_reannotate {process : Proc}
    {alphabet : PactTypeAlphabet} (hRegular : Proc.ConjunctRegular process) :
    Proc.ConjunctRegular (Proc.reannotate alphabet process) :=
  (conjunctRegular_reannotate_aux (sizeOf process + 1)).1 process alphabet
    (by omega) hRegular

/-! ## The conjunctive commitment -/

theorem conjunctRegular_toXOffer {alphabet : PactTypeAlphabet}
    {branch : ChoiceBranch}
    (hRegular : Proc.ConjunctRegular (ChoiceBranch.continuation branch)) :
    Proc.ConjunctRegular (ChoiceBranch.toXOffer alphabet branch) := by
  rw [ChoiceBranch.toXOffer, Proc.ConjunctRegular, Proc.ConjunctRegularBranches,
    Proc.ConjunctRegularBranches, Proc.ConjunctRegular]
  exact ⟨trivial, hRegular, trivial⟩

theorem conjunctRegular_selectedProcessBranchAt {alphabet : PactTypeAlphabet}
    {branch : ChoiceBranch}
    (hRegular : Proc.ConjunctRegular (ChoiceBranch.continuation branch)) :
    Proc.ConjunctRegular (selectedProcessBranchAt alphabet branch) := by
  cases branch with
  | send msg expr process =>
      simp only [ChoiceBranch.continuation] at hRegular
      rw [selectedProcessBranchAt, Proc.ConjunctRegular]
      exact hRegular
  | recv msg varName process =>
      simp only [ChoiceBranch.continuation] at hRegular
      rw [selectedProcessBranchAt, Proc.ConjunctRegular]
      exact hRegular

theorem conjunctRegular_parallelProcessBranchesWithin
    {alphabet : PactTypeAlphabet} :
    ∀ branches : List ChoiceBranch, Proc.ConjunctRegularBranches branches →
      Proc.ConjunctRegular (parallelProcessBranchesWithin alphabet branches) := by
  intro branches
  induction branches with
  | nil => intro _; rw [parallelProcessBranchesWithin, Proc.ConjunctRegular]; trivial
  | cons head rest ih =>
      intro hRegular
      rw [Proc.ConjunctRegularBranches] at hRegular
      cases rest with
      | nil =>
          rw [parallelProcessBranchesWithin]
          exact conjunctRegular_toXOffer hRegular.1
      | cons second tail =>
          rw [parallelProcessBranchesWithin_cons_cons, Proc.ConjunctRegular]
          exact ⟨conjunctRegular_toXOffer hRegular.1, ih hRegular.2⟩

theorem conjunctRegular_parallelProcessBranchesSelectingWithin
    {alphabet : PactTypeAlphabet} {selected : ChoiceBranch} :
    ∀ branches : List ChoiceBranch, Proc.ConjunctRegularBranches branches →
      Proc.ConjunctRegular
        (parallelProcessBranchesSelectingWithin alphabet selected branches) := by
  intro branches
  induction branches with
  | nil => intro _; rw [parallelProcessBranchesSelectingWithin, Proc.ConjunctRegular]; trivial
  | cons head rest ih =>
      intro hRegular
      rw [Proc.ConjunctRegularBranches] at hRegular
      cases rest with
      | nil =>
          rw [parallelProcessBranchesSelectingWithin]
          by_cases hEq : head = selected
          · rw [if_pos hEq]
            exact conjunctRegular_selectedProcessBranchAt hRegular.1
          · rw [if_neg hEq]
            exact conjunctRegular_toXOffer hRegular.1
      | cons second tail =>
          rw [parallelProcessBranchesSelectingWithin_cons_cons]
          by_cases hEq : head = selected
          · rw [if_pos hEq, Proc.ConjunctRegular]
            exact ⟨conjunctRegular_selectedProcessBranchAt hRegular.1,
              conjunctRegular_parallelProcessBranchesWithin _ hRegular.2⟩
          · rw [if_neg hEq, Proc.ConjunctRegular]
            exact ⟨conjunctRegular_toXOffer hRegular.1, ih hRegular.2⟩

theorem conjunctRegular_parallelProcessBranchesSelecting
    {alphabet : PactTypeAlphabet} {selected : ChoiceBranch}
    {branches : List ChoiceBranch}
    (hRegular : Proc.ConjunctRegularBranches branches) :
    Proc.ConjunctRegular
      (parallelProcessBranchesSelecting alphabet selected branches) := by
  cases branches with
  | nil => rw [parallelProcessBranchesSelecting, Proc.ConjunctRegular]; trivial
  | cons head rest =>
      rw [parallelProcessBranchesSelecting]
      exact conjunctRegular_parallelProcessBranchesSelectingWithin _ hRegular

/-- Atomic consumption preserves regularity in each residual factor. -/
theorem conjunctRegular_parallelProcessBranchesFiringFrom
    (alphabet : PactTypeAlphabet) (selected : Finset Nat) (values : Nat → Bool)
    (branches : List ChoiceBranch) (hRegular : Proc.ConjunctRegularBranches branches) :
    ∀ index, Proc.ConjunctRegular
      (parallelProcessBranchesFiringFrom alphabet selected values index branches) := by
  induction branches with
  | nil => intro index; simp [parallelProcessBranchesFiringFrom, Proc.ConjunctRegular]
  | cons head rest ih =>
      rw [Proc.ConjunctRegularBranches] at hRegular
      intro index
      have hHead : Proc.ConjunctRegular
          (if index ∈ selected then consumedProcessBranchAt alphabet head (values index)
           else optionalProcessBranchAt alphabet head) := by
        split
        · cases head with
          | send msg expr process =>
              exact Proc.conjunctRegular_reannotate hRegular.1
          | recv msg name process =>
              exact Proc.conjunctRegular_reannotate
                (Proc.conjunctRegular_procExprReplace hRegular.1)
        · simpa only [optionalProcessBranchAt, ChoiceBranch.toXOffer, Proc.reannotate] using
            (Proc.conjunctRegular_reannotate (alphabet := alphabet)
              (conjunctRegular_toXOffer (alphabet := alphabet) hRegular.1))
      cases rest with
      | nil => exact hHead
      | cons next rest =>
          rw [parallelProcessBranchesFiringFrom, Proc.ConjunctRegular]
          exact ⟨hHead, ih hRegular.2 (index + 1)⟩

/-! ## Along a step -/

theorem conjunctRegular_skip (alphabet : PactTypeAlphabet) :
    Proc.ConjunctRegular (Proc.skip alphabet) := by
  rw [Proc.ConjunctRegular]; trivial

/-- Distinct conjunctive heads are preserved by every process rule. -/
theorem conjunctRegular_offers {env : Environment} {source target : Proc}
    {label : Label} {current : Finset Offer} {future : Finset BareMessage}
    (hOffers : Offers env source label target current future)
    (hRegular : Proc.ConjunctRegular source) : Proc.ConjunctRegular target := by
  induction hOffers with
  | send _ _ _ _ _ _ _ => rwa [Proc.ConjunctRegular] at hRegular
  | send_wait _ _ _ _ _ _ _ => exact hRegular
  | recv _ _ _ _ _ _ _ =>
      rw [Proc.ConjunctRegular] at hRegular
      exact Proc.conjunctRegular_procExprReplace hRegular
  | recv_wait _ _ _ _ _ _ => exact hRegular
  | cycle _ alphabet _ => exact conjunctRegular_skip alphabet
  | cycle_wait _ _ _ => exact hRegular
  | skip _ _ _ => exact hRegular
  | progress _ alphabet _ _ => exact conjunctRegular_skip alphabet
  | letp _ _ _ _ _ _ _ =>
      rw [Proc.ConjunctRegular] at hRegular
      exact Proc.conjunctRegular_procExprReplace hRegular
  | if_true _ _ _ _ _ _ => rw [Proc.ConjunctRegular] at hRegular; exact hRegular.1
  | if_false _ _ _ _ _ _ => rw [Proc.ConjunctRegular] at hRegular; exact hRegular.2
  | fair_true _ _ _ _ _ _ _ => rw [Proc.ConjunctRegular] at hRegular; exact hRegular.1
  | fair_false _ _ _ _ _ _ _ => rw [Proc.ConjunctRegular] at hRegular; exact hRegular.2
  | recur _ _ _ _ _ =>
      have hBody := hRegular
      rw [Proc.ConjunctRegular] at hBody
      exact Proc.conjunctRegular_procReplace hBody hRegular
  | seq _ _ _ _ _ _ _ _ _ _ _ ih =>
      rw [Proc.ConjunctRegular] at hRegular
      rw [Proc.ConjunctRegular]
      exact ⟨ih hRegular.1, hRegular.2⟩
  | seq_tock _ _ _ _ _ _ _ _ _ ih =>
      rw [Proc.ConjunctRegular] at hRegular
      rw [Proc.ConjunctRegular]
      exact ⟨ih hRegular.1, hRegular.2⟩
  | seq_fuse _ _ _ _ _ _ _ _ _ _ _ =>
      rw [Proc.ConjunctRegular] at hRegular
      exact hRegular.2
  | seq_fuse_tock _ _ _ _ _ _ _ _ _ =>
      rw [Proc.ConjunctRegular] at hRegular
      exact hRegular.2
  | xoffer_send _ _ _ _ _ _ _ _ hPrem =>
      rw [Proc.ConjunctRegular] at hRegular
      exact Proc.conjunctRegular_of_mem_branches hRegular.2 hPrem.2.1
  | xoffer_recv _ _ _ _ _ _ _ _ hPrem =>
      rw [Proc.ConjunctRegular] at hRegular
      exact Proc.conjunctRegular_procExprReplace
        (Proc.conjunctRegular_of_mem_branches hRegular.2 hPrem.2.1)
  | xoffer_else _ _ _ _ _ =>
      rw [Proc.ConjunctRegular] at hRegular
      exact hRegular.1
  | xoffer_wait _ _ _ _ _ => exact hRegular
  | offer_some _ alphabet _ branches selected values _ =>
      rw [Proc.ConjunctRegular] at hRegular
      exact conjunctRegular_parallelProcessBranchesFiringFrom
        alphabet selected values branches hRegular.2.2 0
  | offer_else _ _ _ _ _ =>
      rw [Proc.ConjunctRegular] at hRegular
      exact hRegular.2.1
  | offer_wait _ _ _ _ _ => exact hRegular
  | par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihLeft ihRight =>
      rw [Proc.ConjunctRegular] at hRegular
      rw [Proc.ConjunctRegular]
      exact ⟨ihLeft hRegular.1, ihRight hRegular.2⟩
  | par_fuse _ _ _ _ alphabet _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact conjunctRegular_skip alphabet
  | par_fuse_tock _ _ _ _ alphabet _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact conjunctRegular_skip alphabet
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihRight =>
      rw [Proc.ConjunctRegular] at hRegular
      exact Proc.conjunctRegular_reannotate (ihRight hRegular.2)
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihLeft =>
      rw [Proc.ConjunctRegular] at hRegular
      exact Proc.conjunctRegular_reannotate (ihLeft hRegular.1)

/-! ## `ConjMsgOwn` supplies the distinctness -/

theorem mem_branchMessageIds :
    ∀ {branches : List (BareMessage × PactType)} {branch : BareMessage × PactType},
      branch ∈ branches → branch.1.1 ∈ PactType.BranchMessageIds branches := by
  intro branches
  induction branches with
  | nil => intro branch hMem; exact absurd hMem (by simp)
  | cons head rest ih =>
      intro branch hMem
      rcases head with ⟨action, branchType⟩
      rw [PactType.BranchMessageIds]
      rcases List.mem_cons.1 hMem with rfl | hTail
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))
      · exact Finset.mem_union_right _ (ih hTail)

theorem branchHeadsDistinct_of_conjunctiveMessageOwnership :
    ∀ {branches : List ChoiceBranch},
      PactType.ConjunctiveMessageOwnershipBranches (inferBranches branches) →
      BranchHeadsDistinct branches := by
  intro branches
  induction branches with
  | nil => intro _; exact List.Pairwise.nil
  | cons head rest ih =>
      intro hOwn
      rw [inferBranches_cons] at hOwn
      rcases hInfer : inferBranch head with ⟨action, branchType⟩
      rw [hInfer, PactType.ConjunctiveMessageOwnershipBranches] at hOwn
      refine List.Pairwise.cons ?_ (ih hOwn.2.2)
      intro other hOther
      have hMem : (inferBranch other).1.1 ∈
          PactType.BranchMessageIds (inferBranches rest) :=
        mem_branchMessageIds (inferBranch_mem hOther)
      have hHead : action.1 ∈ ({action.1} ∪ PactType.MessageIds branchType) :=
        Finset.mem_union_left _ (by simp)
      have hNe : action.1 ≠ (inferBranch other).1.1 := by
        intro hEq
        exact (Finset.disjoint_left.1 hOwn.2.1 hHead) (hEq ▸ hMem)
      have hAction : ChoiceBranch.action head = action :=
        congrArg Prod.fst hInfer
      have hOtherAction : ChoiceBranch.action other = (inferBranch other).1 := rfl
      intro hAbsurd
      exact hNe (by rw [← hAction, ← hOtherAction, hAbsurd])

private theorem conjunctRegular_of_ownership_aux : ∀ n : Nat,
    (∀ process : Proc, sizeOf process < n →
      PactType.ConjunctiveMessageOwnership (inferProcess process) →
      Proc.ConjunctRegular process) ∧
    (∀ branches : List ChoiceBranch, sizeOf branches < n →
      PactType.ConjunctiveMessageOwnershipBodies (inferBranches branches) →
      Proc.ConjunctRegularBranches branches) ∧
    (∀ branches : List ChoiceBranch, sizeOf branches < n →
      PactType.ConjunctiveMessageOwnershipBranches (inferBranches branches) →
      Proc.ConjunctRegularBranches branches) := by
  intro n
  induction n with
  | zero =>
      exact ⟨fun _ h => absurd h (by omega), fun _ h => absurd h (by omega),
        fun _ h => absurd h (by omega)⟩
  | succ n ih =>
      obtain ⟨ihProc, ihBodies, ihBranches⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · intro process hSize hOwn
        cases process with
        | send alphabet msg expr p =>
            rw [inferProcess, PactType.ConjunctiveMessageOwnership] at hOwn
            rw [Proc.ConjunctRegular]
            exact ihProc p (by simp at hSize ⊢; omega) hOwn.2
        | recv alphabet msg varName p =>
            rw [inferProcess, PactType.ConjunctiveMessageOwnership] at hOwn
            rw [Proc.ConjunctRegular]
            exact ihProc p (by simp at hSize ⊢; omega) hOwn.2
        | var alphabet name => rw [Proc.ConjunctRegular]; trivial
        | skip alphabet => rw [Proc.ConjunctRegular]; trivial
        | endp alphabet pid => rw [Proc.ConjunctRegular]; trivial
        | cycle alphabet => rw [Proc.ConjunctRegular]; trivial
        | par alphabet left right interface =>
            rw [inferProcess, PactType.ConjunctiveMessageOwnership] at hOwn
            rw [Proc.ConjunctRegular]
            exact ⟨ihProc left (by simp at hSize ⊢; omega) hOwn.1,
              ihProc right (by simp at hSize ⊢; omega) hOwn.2⟩
        | seq alphabet left right =>
            rw [inferProcess, PactType.ConjunctiveMessageOwnership] at hOwn
            rw [Proc.ConjunctRegular]
            exact ⟨ihProc left (by simp at hSize ⊢; omega) hOwn.1,
              ihProc right (by simp at hSize ⊢; omega) hOwn.2⟩
        | letp alphabet varName expr p =>
            rw [inferProcess, PactType.ConjunctiveMessageOwnership] at hOwn
            rw [Proc.ConjunctRegular]
            exact ihProc p (by simp at hSize ⊢; omega) hOwn.2
        | ifunfair alphabet expr left right =>
            rw [inferProcess, PactType.ConjunctiveMessageOwnership] at hOwn
            rw [Proc.ConjunctRegular]
            exact ⟨ihProc left (by simp at hSize ⊢; omega) hOwn.1,
              ihProc right (by simp at hSize ⊢; omega) hOwn.2⟩
        | iffair alphabet bid expr left right =>
            rw [inferProcess, PactType.ConjunctiveMessageOwnership] at hOwn
            rw [Proc.ConjunctRegular]
            exact ⟨ihProc left (by simp at hSize ⊢; omega) hOwn.1,
              ihProc right (by simp at hSize ⊢; omega) hOwn.2⟩
        | recur alphabet name body =>
            rw [inferProcess, PactType.ConjunctiveMessageOwnership] at hOwn
            rw [Proc.ConjunctRegular]
            exact ihProc body (by simp at hSize ⊢; omega) hOwn
        | xoffer alphabet elseProcess branches =>
            rw [inferProcess, PactType.ConjunctiveMessageOwnership] at hOwn
            rw [Proc.ConjunctRegular]
            exact ⟨ihProc elseProcess (by simp at hSize ⊢; omega) hOwn.1,
              ihBodies branches (by simp at hSize ⊢; omega) hOwn.2⟩
        | offer alphabet elseProcess branches =>
            rw [inferProcess, PactType.ConjunctiveMessageOwnership] at hOwn
            rw [Proc.ConjunctRegular]
            exact ⟨branchHeadsDistinct_of_conjunctiveMessageOwnership hOwn.2,
              ihProc elseProcess (by simp at hSize ⊢; omega) hOwn.1,
              ihBranches branches (by simp at hSize ⊢; omega) hOwn.2⟩
      · intro branches hSize hOwn
        cases branches with
        | nil => rw [Proc.ConjunctRegularBranches]; trivial
        | cons branch rest =>
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            rw [inferBranches_cons] at hOwn
            rcases hInfer : inferBranch branch with ⟨action, branchType⟩
            rw [hInfer, PactType.ConjunctiveMessageOwnershipBodies] at hOwn
            rw [Proc.ConjunctRegularBranches]
            refine ⟨ihProc _ hCont ?_, ihBodies rest hRest hOwn.2⟩
            have : branchType = inferProcess (ChoiceBranch.continuation branch) :=
              (congrArg Prod.snd hInfer).symm
            exact this ▸ hOwn.1
      · intro branches hSize hOwn
        cases branches with
        | nil => rw [Proc.ConjunctRegularBranches]; trivial
        | cons branch rest =>
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            rw [inferBranches_cons] at hOwn
            rcases hInfer : inferBranch branch with ⟨action, branchType⟩
            rw [hInfer, PactType.ConjunctiveMessageOwnershipBranches] at hOwn
            rw [Proc.ConjunctRegularBranches]
            refine ⟨ihProc _ hCont ?_, ihBranches rest hRest hOwn.2.2⟩
            have : branchType = inferProcess (ChoiceBranch.continuation branch) :=
              (congrArg Prod.snd hInfer).symm
            exact this ▸ hOwn.1

/-- `ConjMsgOwn(abs(P))` gives every conjunctive offer of `P` distinct heads. -/
theorem Proc.conjunctRegular_of_conjunctiveMessageOwnership {process : Proc}
    (hOwn : PactType.ConjunctiveMessageOwnership (inferProcess process)) :
    Proc.ConjunctRegular process :=
  (conjunctRegular_of_ownership_aux (sizeOf process + 1)).1 process (by omega) hOwn

end

end Pact
