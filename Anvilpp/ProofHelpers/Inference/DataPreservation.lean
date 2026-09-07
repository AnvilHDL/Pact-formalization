import Anvilpp.ProofHelpers.Inference.AbstractionSubstitution

/-!
# Data preservation

The last clause of the paper's first helper for Lemma 4.2: `DataWF(P)` and
`E ⊢ P →^α P'` imply `DataWF(P')`.  The only substitutions a rule performs
are a value for a data variable and a closed recursive process for its own
binder.
-/

namespace Pact

noncomputable section

open Classical

/-! ## Weakening -/

theorem Expr.allVariablesBound_mono {bound bound' : List String}
    (hSubset : bound ⊆ bound') :
    ∀ expr : Expr, Expr.AllVariablesBound bound expr →
      Expr.AllVariablesBound bound' expr := by
  intro expr
  induction expr with
  | var name => exact fun h => hSubset h
  | val _ => exact fun _ => trivial
  | bin left _ right ihLeft ihRight =>
      exact fun h => ⟨ihLeft h.1, ihRight h.2⟩

/-- The per-branch clause of `AllBranchVariablesBound`. -/
def BranchBound (procVars dataVars : List String) (branch : ChoiceBranch) : Prop :=
  match branch with
  | ChoiceBranch.send _ expr process =>
      Expr.AllVariablesBound dataVars expr ∧
        Proc.AllVariablesBound procVars dataVars process
  | ChoiceBranch.recv _ varName process =>
      Proc.AllVariablesBound procVars (varName :: dataVars) process

@[simp] theorem allBranchVariablesBound_cons (procVars dataVars : List String)
    (branch : ChoiceBranch) (rest : List ChoiceBranch) :
    Proc.AllBranchVariablesBound procVars dataVars (branch :: rest) ↔
      BranchBound procVars dataVars branch ∧
        Proc.AllBranchVariablesBound procVars dataVars rest := by
  cases branch with
  | send msg expr process =>
      rw [Proc.AllBranchVariablesBound, BranchBound]
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
  | recv msg varName process =>
      rw [Proc.AllBranchVariablesBound, BranchBound]

private theorem allVariablesBound_mono_aux : ∀ n : Nat,
    (∀ (process : Proc) (procVars procVars' dataVars dataVars' : List String),
      sizeOf process < n → procVars ⊆ procVars' → dataVars ⊆ dataVars' →
      Proc.AllVariablesBound procVars dataVars process →
      Proc.AllVariablesBound procVars' dataVars' process) ∧
    (∀ (branches : List ChoiceBranch)
      (procVars procVars' dataVars dataVars' : List String),
      sizeOf branches < n → procVars ⊆ procVars' → dataVars ⊆ dataVars' →
      Proc.AllBranchVariablesBound procVars dataVars branches →
      Proc.AllBranchVariablesBound procVars' dataVars' branches) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ h => absurd h (by omega),
      fun _ _ _ _ _ h => absurd h (by omega)⟩
  | succ n ih =>
      obtain ⟨ihProc, ihBranch⟩ := ih
      refine ⟨?_, ?_⟩
      · intro process procVars procVars' dataVars dataVars' hSize hProcSub hDataSub hBound
        cases process with
        | send alphabet msg expr p =>
            rw [Proc.AllVariablesBound] at hBound ⊢
            exact ⟨Expr.allVariablesBound_mono hDataSub _ hBound.1,
              ihProc p _ _ _ _ (by simp at hSize ⊢; omega) hProcSub hDataSub hBound.2⟩
        | recv alphabet msg varName p =>
            rw [Proc.AllVariablesBound] at hBound ⊢
            exact ihProc p _ _ _ _ (by simp at hSize ⊢; omega) hProcSub
              (List.cons_subset_cons _ hDataSub) hBound
        | var alphabet name =>
            rw [Proc.AllVariablesBound] at hBound ⊢
            exact hProcSub hBound
        | skip alphabet => trivial
        | endp alphabet pid => trivial
        | cycle alphabet => trivial
        | par alphabet left right interface =>
            rw [Proc.AllVariablesBound] at hBound ⊢
            exact ⟨ihProc left _ _ _ _ (by simp at hSize ⊢; omega) hProcSub hDataSub hBound.1,
              ihProc right _ _ _ _ (by simp at hSize ⊢; omega) hProcSub hDataSub hBound.2⟩
        | seq alphabet left right =>
            rw [Proc.AllVariablesBound] at hBound ⊢
            exact ⟨ihProc left _ _ _ _ (by simp at hSize ⊢; omega) hProcSub hDataSub hBound.1,
              ihProc right _ _ _ _ (by simp at hSize ⊢; omega) hProcSub hDataSub hBound.2⟩
        | letp alphabet varName expr p =>
            rw [Proc.AllVariablesBound] at hBound ⊢
            exact ⟨Expr.allVariablesBound_mono hDataSub _ hBound.1,
              ihProc p _ _ _ _ (by simp at hSize ⊢; omega) hProcSub
                (List.cons_subset_cons _ hDataSub) hBound.2⟩
        | ifunfair alphabet expr left right =>
            rw [Proc.AllVariablesBound] at hBound ⊢
            exact ⟨Expr.allVariablesBound_mono hDataSub _ hBound.1,
              ihProc left _ _ _ _ (by simp at hSize ⊢; omega) hProcSub hDataSub hBound.2.1,
              ihProc right _ _ _ _ (by simp at hSize ⊢; omega) hProcSub hDataSub hBound.2.2⟩
        | iffair alphabet bid expr left right =>
            rw [Proc.AllVariablesBound] at hBound ⊢
            exact ⟨Expr.allVariablesBound_mono hDataSub _ hBound.1,
              ihProc left _ _ _ _ (by simp at hSize ⊢; omega) hProcSub hDataSub hBound.2.1,
              ihProc right _ _ _ _ (by simp at hSize ⊢; omega) hProcSub hDataSub hBound.2.2⟩
        | recur alphabet name body =>
            rw [Proc.AllVariablesBound] at hBound ⊢
            exact ihProc body _ _ _ _ (by simp at hSize ⊢; omega)
              (List.cons_subset_cons _ hProcSub) hDataSub hBound
        | xoffer alphabet elseProcess branches =>
            rw [Proc.AllVariablesBound] at hBound ⊢
            exact ⟨ihProc elseProcess _ _ _ _ (by simp at hSize ⊢; omega) hProcSub
                hDataSub hBound.1,
              ihBranch branches _ _ _ _ (by simp at hSize ⊢; omega) hProcSub
                hDataSub hBound.2⟩
        | offer alphabet elseProcess branches =>
            rw [Proc.AllVariablesBound] at hBound ⊢
            exact ⟨ihProc elseProcess _ _ _ _ (by simp at hSize ⊢; omega) hProcSub
                hDataSub hBound.1,
              ihBranch branches _ _ _ _ (by simp at hSize ⊢; omega) hProcSub
                hDataSub hBound.2⟩
      · intro branches procVars procVars' dataVars dataVars' hSize hProcSub hDataSub hBound
        cases branches with
        | nil => trivial
        | cons branch rest =>
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            rw [allBranchVariablesBound_cons] at hBound ⊢
            refine ⟨?_, ihBranch rest _ _ _ _ hRest hProcSub hDataSub hBound.2⟩
            obtain ⟨hHead, -⟩ := hBound
            cases branch with
            | send msg expr p =>
                rw [BranchBound] at hHead ⊢
                exact ⟨Expr.allVariablesBound_mono hDataSub _ hHead.1,
                  ihProc p _ _ _ _ (by simpa [ChoiceBranch.continuation] using hCont)
                    hProcSub hDataSub hHead.2⟩
            | recv msg varName p =>
                rw [BranchBound] at hHead ⊢
                exact ihProc p _ _ _ _ (by simpa [ChoiceBranch.continuation] using hCont)
                  hProcSub (List.cons_subset_cons _ hDataSub) hHead

theorem Proc.allVariablesBound_mono {process : Proc}
    {procVars procVars' dataVars dataVars' : List String}
    (hProcSub : procVars ⊆ procVars') (hDataSub : dataVars ⊆ dataVars')
    (hBound : Proc.AllVariablesBound procVars dataVars process) :
    Proc.AllVariablesBound procVars' dataVars' process :=
  (allVariablesBound_mono_aux (sizeOf process + 1)).1 process _ _ _ _ (by omega)
    hProcSub hDataSub hBound

theorem Proc.allBranchVariablesBound_mono {branches : List ChoiceBranch}
    {procVars procVars' dataVars dataVars' : List String}
    (hProcSub : procVars ⊆ procVars') (hDataSub : dataVars ⊆ dataVars')
    (hBound : Proc.AllBranchVariablesBound procVars dataVars branches) :
    Proc.AllBranchVariablesBound procVars' dataVars' branches :=
  (allVariablesBound_mono_aux (sizeOf branches + 1)).2 branches _ _ _ _ (by omega)
    hProcSub hDataSub hBound

/-! ## Value substitution -/

private theorem cons_swap_subset (a b : String) (l : List String) :
    a :: b :: l ⊆ b :: a :: l := by
  intro name hName
  simp only [List.mem_cons] at hName ⊢
  tauto

private theorem cons_dup_subset (a : String) (l : List String) :
    a :: a :: l ⊆ a :: l := by
  intro name hName
  simp only [List.mem_cons] at hName ⊢
  tauto

theorem Expr.allVariablesBound_exprReplace {dataVars : List String}
    {name : String} {value : Bool} :
    ∀ expr : Expr, Expr.AllVariablesBound (name :: dataVars) expr →
      Expr.AllVariablesBound dataVars (Semantics.exprReplace expr name value) := by
  intro expr
  induction expr with
  | var other =>
      intro hBound
      rw [Semantics.exprReplace]
      by_cases hName : name = other
      · rw [if_pos hName]; trivial
      · rw [if_neg hName]
        rcases List.mem_cons.1 hBound with h | h
        · exact absurd h.symm hName
        · exact h
  | val _ => intro _; trivial
  | bin left bop right ihLeft ihRight =>
      intro hBound
      exact ⟨ihLeft hBound.1, ihRight hBound.2⟩

private theorem allVariablesBound_procExprReplace_aux : ∀ n : Nat,
    (∀ (process : Proc) (procVars dataVars : List String) (name : String)
      (value : Bool), sizeOf process < n →
      Proc.AllVariablesBound procVars (name :: dataVars) process →
      Proc.AllVariablesBound procVars dataVars
        (Semantics.procExprReplace process name value)) ∧
    (∀ (branches : List ChoiceBranch) (procVars dataVars : List String)
      (name : String) (value : Bool), sizeOf branches < n →
      Proc.AllBranchVariablesBound procVars (name :: dataVars) branches →
      Proc.AllBranchVariablesBound procVars dataVars
        (Semantics.choiceBranchesExprReplace branches name value)) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ h => absurd h (by omega),
      fun _ _ _ _ _ h => absurd h (by omega)⟩
  | succ n ih =>
      obtain ⟨ihProc, ihBranch⟩ := ih
      refine ⟨?_, ?_⟩
      · intro process procVars dataVars name value hSize hBound
        cases process with
        | send alphabet msg expr p =>
            rw [Semantics.procExprReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨Expr.allVariablesBound_exprReplace _ hBound.1,
              ihProc p _ _ _ _ (by simp at hSize ⊢; omega) hBound.2⟩
        | recv alphabet msg varName p =>
            rw [Semantics.procExprReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            by_cases hName : name = varName
            · rw [if_pos hName]
              subst hName
              exact Proc.allVariablesBound_mono (fun _ h => h)
                (cons_dup_subset _ _) hBound
            · rw [if_neg hName]
              exact ihProc p _ _ _ _ (by simp at hSize ⊢; omega)
                (Proc.allVariablesBound_mono (fun _ h => h)
                  (cons_swap_subset _ _ _) hBound)
        | var alphabet other =>
            rw [Semantics.procExprReplace]; exact hBound
        | skip alphabet => rw [Semantics.procExprReplace]; trivial
        | endp alphabet pid => rw [Semantics.procExprReplace]; trivial
        | cycle alphabet => rw [Semantics.procExprReplace]; trivial
        | par alphabet left right interface =>
            rw [Semantics.procExprReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨ihProc left _ _ _ _ (by simp at hSize ⊢; omega) hBound.1,
              ihProc right _ _ _ _ (by simp at hSize ⊢; omega) hBound.2⟩
        | seq alphabet left right =>
            rw [Semantics.procExprReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨ihProc left _ _ _ _ (by simp at hSize ⊢; omega) hBound.1,
              ihProc right _ _ _ _ (by simp at hSize ⊢; omega) hBound.2⟩
        | letp alphabet varName expr p =>
            rw [Semantics.procExprReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            refine ⟨Expr.allVariablesBound_exprReplace _ hBound.1, ?_⟩
            by_cases hName : name = varName
            · rw [if_pos hName]
              subst hName
              exact Proc.allVariablesBound_mono (fun _ h => h)
                (cons_dup_subset _ _) hBound.2
            · rw [if_neg hName]
              exact ihProc p _ _ _ _ (by simp at hSize ⊢; omega)
                (Proc.allVariablesBound_mono (fun _ h => h)
                  (cons_swap_subset _ _ _) hBound.2)
        | ifunfair alphabet expr left right =>
            rw [Semantics.procExprReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨Expr.allVariablesBound_exprReplace _ hBound.1,
              ihProc left _ _ _ _ (by simp at hSize ⊢; omega) hBound.2.1,
              ihProc right _ _ _ _ (by simp at hSize ⊢; omega) hBound.2.2⟩
        | iffair alphabet bid expr left right =>
            rw [Semantics.procExprReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨Expr.allVariablesBound_exprReplace _ hBound.1,
              ihProc left _ _ _ _ (by simp at hSize ⊢; omega) hBound.2.1,
              ihProc right _ _ _ _ (by simp at hSize ⊢; omega) hBound.2.2⟩
        | recur alphabet other body =>
            rw [Semantics.procExprReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ihProc body _ _ _ _ (by simp at hSize ⊢; omega) hBound
        | xoffer alphabet elseProcess branches =>
            rw [Semantics.procExprReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨ihProc elseProcess _ _ _ _ (by simp at hSize ⊢; omega) hBound.1,
              ihBranch branches _ _ _ _ (by simp at hSize ⊢; omega) hBound.2⟩
        | offer alphabet elseProcess branches =>
            rw [Semantics.procExprReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨ihProc elseProcess _ _ _ _ (by simp at hSize ⊢; omega) hBound.1,
              ihBranch branches _ _ _ _ (by simp at hSize ⊢; omega) hBound.2⟩
      · intro branches procVars dataVars name value hSize hBound
        cases branches with
        | nil => rw [Semantics.choiceBranchesExprReplace]; trivial
        | cons branch rest =>
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            rw [allBranchVariablesBound_cons] at hBound
            rw [Semantics.choiceBranchesExprReplace, allBranchVariablesBound_cons]
            refine ⟨?_, ihBranch rest _ _ _ _ hRest hBound.2⟩
            obtain ⟨hHead, -⟩ := hBound
            cases branch with
            | send msg expr p =>
                rw [BranchBound] at hHead
                rw [Semantics.choiceBranchExprReplace, BranchBound]
                exact ⟨Expr.allVariablesBound_exprReplace _ hHead.1,
                  ihProc p _ _ _ _ (by simpa [ChoiceBranch.continuation] using hCont)
                    hHead.2⟩
            | recv msg varName p =>
                rw [BranchBound] at hHead
                rw [Semantics.choiceBranchExprReplace, BranchBound]
                by_cases hName : name = varName
                · rw [if_pos hName]
                  subst hName
                  exact Proc.allVariablesBound_mono (fun _ h => h)
                    (cons_dup_subset _ _) hHead
                · rw [if_neg hName]
                  exact ihProc p _ _ _ _
                    (by simpa [ChoiceBranch.continuation] using hCont)
                    (Proc.allVariablesBound_mono (fun _ h => h)
                      (cons_swap_subset _ _ _) hHead)

theorem Proc.allVariablesBound_procExprReplace {process : Proc}
    {procVars dataVars : List String} {name : String} {value : Bool}
    (hBound : Proc.AllVariablesBound procVars (name :: dataVars) process) :
    Proc.AllVariablesBound procVars dataVars
      (Semantics.procExprReplace process name value) :=
  (allVariablesBound_procExprReplace_aux (sizeOf process + 1)).1 process _ _ _ _
    (by omega) hBound

/-! ## Recursive process substitution -/

private theorem allVariablesBound_procReplace_aux : ∀ n : Nat,
    (∀ (process replacement : Proc) (procVars dataVars : List String)
      (name : String), sizeOf process < n →
      Proc.AllVariablesBound (name :: procVars) dataVars process →
      Proc.AllVariablesBound [] [] replacement →
      Proc.AllVariablesBound procVars dataVars
        (Semantics.procReplace process name replacement)) ∧
    (∀ (branches : List ChoiceBranch) (replacement : Proc)
      (procVars dataVars : List String) (name : String), sizeOf branches < n →
      Proc.AllBranchVariablesBound (name :: procVars) dataVars branches →
      Proc.AllVariablesBound [] [] replacement →
      Proc.AllBranchVariablesBound procVars dataVars
        (Semantics.choiceBranchesProcReplace branches name replacement)) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ h => absurd h (by omega),
      fun _ _ _ _ _ h => absurd h (by omega)⟩
  | succ n ih =>
      obtain ⟨ihProc, ihBranch⟩ := ih
      refine ⟨?_, ?_⟩
      · intro process replacement procVars dataVars name hSize hBound hReplacement
        cases process with
        | send alphabet msg expr p =>
            rw [Semantics.procReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨hBound.1,
              ihProc p _ _ _ _ (by simp at hSize ⊢; omega) hBound.2 hReplacement⟩
        | recv alphabet msg varName p =>
            rw [Semantics.procReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ihProc p _ _ _ _ (by simp at hSize ⊢; omega) hBound hReplacement
        | var alphabet other =>
            rw [Semantics.procReplace]
            rw [Proc.AllVariablesBound] at hBound
            by_cases hName : name = other
            · rw [if_pos hName]
              exact Proc.allVariablesBound_mono (List.nil_subset _)
                (List.nil_subset _) hReplacement
            · rw [if_neg hName, Proc.AllVariablesBound]
              rcases List.mem_cons.1 hBound with h | h
              · exact absurd h.symm hName
              · exact h
        | skip alphabet => rw [Semantics.procReplace]; trivial
        | endp alphabet pid => rw [Semantics.procReplace]; trivial
        | cycle alphabet => rw [Semantics.procReplace]; trivial
        | par alphabet left right interface =>
            rw [Semantics.procReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨ihProc left _ _ _ _ (by simp at hSize ⊢; omega) hBound.1 hReplacement,
              ihProc right _ _ _ _ (by simp at hSize ⊢; omega) hBound.2 hReplacement⟩
        | seq alphabet left right =>
            rw [Semantics.procReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨ihProc left _ _ _ _ (by simp at hSize ⊢; omega) hBound.1 hReplacement,
              ihProc right _ _ _ _ (by simp at hSize ⊢; omega) hBound.2 hReplacement⟩
        | letp alphabet varName expr p =>
            rw [Semantics.procReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨hBound.1,
              ihProc p _ _ _ _ (by simp at hSize ⊢; omega) hBound.2 hReplacement⟩
        | ifunfair alphabet expr left right =>
            rw [Semantics.procReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨hBound.1,
              ihProc left _ _ _ _ (by simp at hSize ⊢; omega) hBound.2.1 hReplacement,
              ihProc right _ _ _ _ (by simp at hSize ⊢; omega) hBound.2.2 hReplacement⟩
        | iffair alphabet bid expr left right =>
            rw [Semantics.procReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨hBound.1,
              ihProc left _ _ _ _ (by simp at hSize ⊢; omega) hBound.2.1 hReplacement,
              ihProc right _ _ _ _ (by simp at hSize ⊢; omega) hBound.2.2 hReplacement⟩
        | recur alphabet other body =>
            rw [Semantics.procReplace]
            rw [Proc.AllVariablesBound] at hBound
            by_cases hName : name = other
            · rw [if_pos hName, Proc.AllVariablesBound]
              subst hName
              exact Proc.allVariablesBound_mono (cons_dup_subset _ _)
                (fun _ h => h) hBound
            · rw [if_neg hName, Proc.AllVariablesBound]
              exact ihProc body _ _ _ _ (by simp at hSize ⊢; omega)
                (Proc.allVariablesBound_mono (cons_swap_subset _ _ _)
                  (fun _ h => h) hBound) hReplacement
        | xoffer alphabet elseProcess branches =>
            rw [Semantics.procReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨ihProc elseProcess _ _ _ _ (by simp at hSize ⊢; omega) hBound.1
                hReplacement,
              ihBranch branches _ _ _ _ (by simp at hSize ⊢; omega) hBound.2
                hReplacement⟩
        | offer alphabet elseProcess branches =>
            rw [Semantics.procReplace, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨ihProc elseProcess _ _ _ _ (by simp at hSize ⊢; omega) hBound.1
                hReplacement,
              ihBranch branches _ _ _ _ (by simp at hSize ⊢; omega) hBound.2
                hReplacement⟩
      · intro branches replacement procVars dataVars name hSize hBound hReplacement
        cases branches with
        | nil => rw [Semantics.choiceBranchesProcReplace]; trivial
        | cons branch rest =>
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            rw [allBranchVariablesBound_cons] at hBound
            rw [Semantics.choiceBranchesProcReplace, allBranchVariablesBound_cons]
            refine ⟨?_, ihBranch rest _ _ _ _ hRest hBound.2 hReplacement⟩
            obtain ⟨hHead, -⟩ := hBound
            cases branch with
            | send msg expr p =>
                rw [BranchBound] at hHead
                rw [Semantics.choiceBranchProcReplace, BranchBound]
                exact ⟨hHead.1,
                  ihProc p _ _ _ _ (by simpa [ChoiceBranch.continuation] using hCont)
                    hHead.2 hReplacement⟩
            | recv msg varName p =>
                rw [BranchBound] at hHead
                rw [Semantics.choiceBranchProcReplace, BranchBound]
                exact ihProc p _ _ _ _
                  (by simpa [ChoiceBranch.continuation] using hCont) hHead hReplacement

theorem Proc.allVariablesBound_procReplace {process replacement : Proc}
    {procVars dataVars : List String} {name : String}
    (hBound : Proc.AllVariablesBound (name :: procVars) dataVars process)
    (hReplacement : Proc.AllVariablesBound [] [] replacement) :
    Proc.AllVariablesBound procVars dataVars
      (Semantics.procReplace process name replacement) :=
  (allVariablesBound_procReplace_aux (sizeOf process + 1)).1 process _ _ _ _
    (by omega) hBound hReplacement

/-! ## Re-signing -/

private theorem allVariablesBound_reannotate_aux : ∀ n : Nat,
    (∀ (process : Proc) (alphabet : PactTypeAlphabet)
      (procVars dataVars : List String), sizeOf process < n →
      Proc.AllVariablesBound procVars dataVars process →
      Proc.AllVariablesBound procVars dataVars (Proc.reannotate alphabet process)) ∧
    (∀ (branches : List ChoiceBranch) (alphabet : PactTypeAlphabet)
      (procVars dataVars : List String), sizeOf branches < n →
      Proc.AllBranchVariablesBound procVars dataVars branches →
      Proc.AllBranchVariablesBound procVars dataVars
        (Proc.reannotateBranches alphabet branches)) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ _ h => absurd h (by omega),
      fun _ _ _ _ h => absurd h (by omega)⟩
  | succ n ih =>
      obtain ⟨ihProc, ihBranch⟩ := ih
      refine ⟨?_, ?_⟩
      · intro process alphabet procVars dataVars hSize hBound
        cases process with
        | send alpha msg expr p =>
            rw [Proc.reannotate, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨hBound.1, ihProc p _ _ _ (by simp at hSize ⊢; omega) hBound.2⟩
        | recv alpha msg varName p =>
            rw [Proc.reannotate, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ihProc p _ _ _ (by simp at hSize ⊢; omega) hBound
        | var alpha other => rw [Proc.reannotate]; exact hBound
        | skip alpha => rw [Proc.reannotate]; trivial
        | endp alpha pid => rw [Proc.reannotate]; trivial
        | cycle alpha => rw [Proc.reannotate]; trivial
        | par alpha left right interface =>
            rw [Proc.reannotate, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨ihProc left _ _ _ (by simp at hSize ⊢; omega) hBound.1,
              ihProc right _ _ _ (by simp at hSize ⊢; omega) hBound.2⟩
        | seq alpha left right =>
            rw [Proc.reannotate, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨ihProc left _ _ _ (by simp at hSize ⊢; omega) hBound.1,
              ihProc right _ _ _ (by simp at hSize ⊢; omega) hBound.2⟩
        | letp alpha varName expr p =>
            rw [Proc.reannotate, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨hBound.1, ihProc p _ _ _ (by simp at hSize ⊢; omega) hBound.2⟩
        | ifunfair alpha expr left right =>
            rw [Proc.reannotate, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨hBound.1, ihProc left _ _ _ (by simp at hSize ⊢; omega) hBound.2.1,
              ihProc right _ _ _ (by simp at hSize ⊢; omega) hBound.2.2⟩
        | iffair alpha bid expr left right =>
            rw [Proc.reannotate, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨hBound.1, ihProc left _ _ _ (by simp at hSize ⊢; omega) hBound.2.1,
              ihProc right _ _ _ (by simp at hSize ⊢; omega) hBound.2.2⟩
        | recur alpha other body =>
            rw [Proc.reannotate, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ihProc body _ _ _ (by simp at hSize ⊢; omega) hBound
        | xoffer alpha elseProcess branches =>
            rw [Proc.reannotate, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨ihProc elseProcess _ _ _ (by simp at hSize ⊢; omega) hBound.1,
              ihBranch branches _ _ _ (by simp at hSize ⊢; omega) hBound.2⟩
        | offer alpha elseProcess branches =>
            rw [Proc.reannotate, Proc.AllVariablesBound]
            rw [Proc.AllVariablesBound] at hBound
            exact ⟨ihProc elseProcess _ _ _ (by simp at hSize ⊢; omega) hBound.1,
              ihBranch branches _ _ _ (by simp at hSize ⊢; omega) hBound.2⟩
      · intro branches alphabet procVars dataVars hSize hBound
        cases branches with
        | nil => rw [Proc.reannotateBranches]; trivial
        | cons branch rest =>
            have hCont : sizeOf (ChoiceBranch.continuation branch) < n := by
              have := ChoiceBranch.continuation_sizeOf_lt branch
              simp at hSize ⊢; omega
            have hRest : sizeOf rest < n := by simp at hSize ⊢; omega
            rw [allBranchVariablesBound_cons] at hBound
            obtain ⟨hHead, hTail⟩ := hBound
            cases branch with
            | send msg expr p =>
                rw [BranchBound] at hHead
                rw [Proc.reannotateBranches, allBranchVariablesBound_cons, BranchBound]
                exact ⟨⟨hHead.1,
                    ihProc p _ _ _ (by simpa [ChoiceBranch.continuation] using hCont)
                      hHead.2⟩,
                  ihBranch rest _ _ _ hRest hTail⟩
            | recv msg varName p =>
                rw [BranchBound] at hHead
                rw [Proc.reannotateBranches, allBranchVariablesBound_cons, BranchBound]
                exact ⟨ihProc p _ _ _
                    (by simpa [ChoiceBranch.continuation] using hCont) hHead,
                  ihBranch rest _ _ _ hRest hTail⟩

theorem Proc.allVariablesBound_reannotate {process : Proc}
    {alphabet : PactTypeAlphabet} {procVars dataVars : List String}
    (hBound : Proc.AllVariablesBound procVars dataVars process) :
    Proc.AllVariablesBound procVars dataVars (Proc.reannotate alphabet process) :=
  (allVariablesBound_reannotate_aux (sizeOf process + 1)).1 process _ _ _
    (by omega) hBound

/-! ## `DataWF` at each constructor -/

theorem dataWFProc_send_iff (alphabet : PactTypeAlphabet) (msg : MessageId)
    (expr : Expr) (process : Proc) :
    DataWFProc (Proc.send alphabet msg expr process) ↔
      Expr.AllVariablesBound [] expr ∧ DataWFProc process := by
  rw [DataWFProc, DataWFProc, Proc.AllVariablesBound]

theorem dataWFProc_recv_iff (alphabet : PactTypeAlphabet) (msg : MessageId)
    (varName : String) (process : Proc) :
    DataWFProc (Proc.recv alphabet msg varName process) ↔
      Proc.AllVariablesBound [] [varName] process := by
  rw [DataWFProc, Proc.AllVariablesBound]

theorem dataWFProc_seq_iff (alphabet : PactTypeAlphabet) (left right : Proc) :
    DataWFProc (Proc.seq alphabet left right) ↔
      DataWFProc left ∧ DataWFProc right := by
  rw [DataWFProc, DataWFProc, DataWFProc, Proc.AllVariablesBound]

theorem dataWFProc_par_iff (alphabet : PactTypeAlphabet) (left right : Proc)
    (interface : Interface) :
    DataWFProc (Proc.par alphabet left right interface) ↔
      DataWFProc left ∧ DataWFProc right := by
  rw [DataWFProc, DataWFProc, DataWFProc, Proc.AllVariablesBound]

theorem dataWFProc_letp_iff (alphabet : PactTypeAlphabet) (varName : String)
    (expr : Expr) (process : Proc) :
    DataWFProc (Proc.letp alphabet varName expr process) ↔
      Expr.AllVariablesBound [] expr ∧
        Proc.AllVariablesBound [] [varName] process := by
  rw [DataWFProc, Proc.AllVariablesBound]

theorem dataWFProc_ifunfair_iff (alphabet : PactTypeAlphabet) (expr : Expr)
    (left right : Proc) :
    DataWFProc (Proc.ifunfair alphabet expr left right) ↔
      Expr.AllVariablesBound [] expr ∧ DataWFProc left ∧ DataWFProc right := by
  rw [DataWFProc, DataWFProc, DataWFProc, Proc.AllVariablesBound]

theorem dataWFProc_iffair_iff (alphabet : PactTypeAlphabet) (bid : BranchId)
    (expr : Expr) (left right : Proc) :
    DataWFProc (Proc.iffair alphabet bid expr left right) ↔
      Expr.AllVariablesBound [] expr ∧ DataWFProc left ∧ DataWFProc right := by
  rw [DataWFProc, DataWFProc, DataWFProc, Proc.AllVariablesBound]

theorem dataWFProc_recur_iff (alphabet : PactTypeAlphabet) (name : String)
    (body : Proc) :
    DataWFProc (Proc.recur alphabet name body) ↔
      Proc.AllVariablesBound [name] [] body := by
  rw [DataWFProc, Proc.AllVariablesBound]

theorem dataWFProc_xoffer_iff (alphabet : PactTypeAlphabet) (elseProcess : Proc)
    (branches : List ChoiceBranch) :
    DataWFProc (Proc.xoffer alphabet elseProcess branches) ↔
      DataWFProc elseProcess ∧ Proc.AllBranchVariablesBound [] [] branches := by
  rw [DataWFProc, DataWFProc, Proc.AllVariablesBound]

theorem dataWFProc_offer_iff (alphabet : PactTypeAlphabet) (elseProcess : Proc)
    (branches : List ChoiceBranch) :
    DataWFProc (Proc.offer alphabet elseProcess branches) ↔
      DataWFProc elseProcess ∧ Proc.AllBranchVariablesBound [] [] branches := by
  rw [DataWFProc, DataWFProc, Proc.AllVariablesBound]

theorem dataWFProc_skip (alphabet : PactTypeAlphabet) :
    DataWFProc (Proc.skip alphabet) := by
  rw [DataWFProc, Proc.AllVariablesBound]; trivial

/-! ## Conjunctive commitment -/

theorem branchBound_of_mem {procVars dataVars : List String}
    {branches : List ChoiceBranch} {branch : ChoiceBranch}
    (hBound : Proc.AllBranchVariablesBound procVars dataVars branches)
    (hMem : branch ∈ branches) : BranchBound procVars dataVars branch := by
  induction branches with
  | nil => exact absurd hMem (by simp)
  | cons head rest ih =>
      rw [allBranchVariablesBound_cons] at hBound
      rcases List.mem_cons.1 hMem with hHead | hTail
      · exact hHead ▸ hBound.1
      · exact ih hBound.2 hTail

theorem allVariablesBound_toXOffer {procVars dataVars : List String}
    {alphabet : PactTypeAlphabet} {branch : ChoiceBranch}
    (hBound : BranchBound procVars dataVars branch) :
    Proc.AllVariablesBound procVars dataVars
      (ChoiceBranch.toXOffer alphabet branch) := by
  rw [ChoiceBranch.toXOffer, Proc.AllVariablesBound, allBranchVariablesBound_cons]
  exact ⟨trivial, hBound, trivial⟩

theorem allVariablesBound_selectedProcessBranchAt {procVars dataVars : List String}
    {alphabet : PactTypeAlphabet} {branch : ChoiceBranch}
    (hBound : BranchBound procVars dataVars branch) :
    Proc.AllVariablesBound procVars dataVars
      (selectedProcessBranchAt alphabet branch) := by
  cases branch with
  | send msg expr process =>
      rw [BranchBound] at hBound
      rw [selectedProcessBranchAt, Proc.AllVariablesBound]
      exact hBound
  | recv msg varName process =>
      rw [BranchBound] at hBound
      rw [selectedProcessBranchAt, Proc.AllVariablesBound]
      exact hBound

theorem allVariablesBound_parallelProcessBranchesWithin
    {procVars dataVars : List String} {alphabet : PactTypeAlphabet} :
    ∀ branches : List ChoiceBranch,
      Proc.AllBranchVariablesBound procVars dataVars branches →
      Proc.AllVariablesBound procVars dataVars
        (parallelProcessBranchesWithin alphabet branches) := by
  intro branches
  induction branches with
  | nil => intro _; rw [parallelProcessBranchesWithin]; trivial
  | cons head rest ih =>
      intro hBound
      rw [allBranchVariablesBound_cons] at hBound
      cases rest with
      | nil =>
          rw [parallelProcessBranchesWithin]
          exact allVariablesBound_toXOffer hBound.1
      | cons second tail =>
          rw [parallelProcessBranchesWithin, Proc.AllVariablesBound]
          exact ⟨allVariablesBound_toXOffer hBound.1, ih hBound.2⟩
          simp

theorem allVariablesBound_parallelProcessBranchesSelectingWithin
    {procVars dataVars : List String} {alphabet : PactTypeAlphabet}
    {selected : ChoiceBranch} :
    ∀ branches : List ChoiceBranch,
      Proc.AllBranchVariablesBound procVars dataVars branches →
      BranchBound procVars dataVars selected →
      Proc.AllVariablesBound procVars dataVars
        (parallelProcessBranchesSelectingWithin alphabet selected branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _ _
      rw [parallelProcessBranchesSelectingWithin]; trivial
  | cons head rest ih =>
      intro hBound hSelected
      rw [allBranchVariablesBound_cons] at hBound
      cases rest with
      | nil =>
          rw [parallelProcessBranchesSelectingWithin]
          by_cases hEq : head = selected
          · rw [if_pos hEq]
            exact allVariablesBound_selectedProcessBranchAt hBound.1
          · rw [if_neg hEq]
            exact allVariablesBound_toXOffer hBound.1
      | cons second tail =>
          rw [parallelProcessBranchesSelectingWithin]
          · by_cases hEq : head = selected
            · rw [if_pos hEq, Proc.AllVariablesBound]
              exact ⟨allVariablesBound_selectedProcessBranchAt hBound.1,
                allVariablesBound_parallelProcessBranchesWithin _ hBound.2⟩
            · rw [if_neg hEq, Proc.AllVariablesBound]
              exact ⟨allVariablesBound_toXOffer hBound.1, ih hBound.2 hSelected⟩
          · simp

theorem dataWFProc_parallelProcessBranchesSelecting
    {alphabet : PactTypeAlphabet} {selected : ChoiceBranch}
    {branches : List ChoiceBranch}
    (hBound : Proc.AllBranchVariablesBound [] [] branches)
    (hMem : selected ∈ branches) :
    DataWFProc (parallelProcessBranchesSelecting alphabet selected branches) := by
  cases branches with
  | nil => exact absurd hMem (by simp)
  | cons head rest =>
      rw [parallelProcessBranchesSelecting, DataWFProc]
      exact allVariablesBound_parallelProcessBranchesSelectingWithin _ hBound
        (branchBound_of_mem hBound hMem)

/-! ## Data preservation along a step -/

/-- `DataWF(P)` and `E ⊢ P →^α P'` imply `DataWF(P')`. -/
theorem dataWFProc_offers {env : Environment} {source target : Proc}
    {label : Label} {current : Finset Offer} {future : Finset BareMessage}
    (hOffers : Offers env source label target current future)
    (hData : DataWFProc source) : DataWFProc target := by
  induction hOffers with
  | send _ alphabet msg expr process value _ _ =>
      exact ((dataWFProc_send_iff alphabet msg expr process).1 hData).2
  | send_wait _ _ _ _ _ _ _ _ => exact hData
  | recv _ alphabet msg varName process value _ _ =>
      exact Proc.allVariablesBound_procExprReplace
        ((dataWFProc_recv_iff alphabet msg varName process).1 hData)
  | recv_wait _ _ _ _ _ _ _ => exact hData
  | cycle _ alphabet _ => exact dataWFProc_skip alphabet
  | cycle_wait _ _ _ => exact hData
  | skip _ _ _ => exact hData
  | progress _ alphabet _ _ => exact dataWFProc_skip alphabet
  | letp _ alphabet varName expr process value _ =>
      exact Proc.allVariablesBound_procExprReplace
        ((dataWFProc_letp_iff alphabet varName expr process).1 hData).2
  | if_true _ alphabet expr ifTrue ifFalse _ =>
      exact ((dataWFProc_ifunfair_iff alphabet expr ifTrue ifFalse).1 hData).2.1
  | if_false _ alphabet expr ifTrue ifFalse _ =>
      exact ((dataWFProc_ifunfair_iff alphabet expr ifTrue ifFalse).1 hData).2.2
  | fair_true _ alphabet bid expr ifTrue ifFalse _ =>
      exact ((dataWFProc_iffair_iff alphabet bid expr ifTrue ifFalse).1 hData).2.1
  | fair_false _ alphabet bid expr ifTrue ifFalse _ =>
      exact ((dataWFProc_iffair_iff alphabet bid expr ifTrue ifFalse).1 hData).2.2
  | recur _ alphabet varName body _ =>
      exact Proc.allVariablesBound_procReplace
        ((dataWFProc_recur_iff alphabet varName body).1 hData) hData
  | seq _ alphabet left left' right _ _ _ _ _ _ ih =>
      exact (dataWFProc_seq_iff alphabet left' right).2
        ⟨ih ((dataWFProc_seq_iff alphabet left right).1 hData).1,
          ((dataWFProc_seq_iff alphabet left right).1 hData).2⟩
  | seq_tock _ alphabet left left' right _ _ _ _ ih =>
      exact (dataWFProc_seq_iff alphabet left' right).2
        ⟨ih ((dataWFProc_seq_iff alphabet left right).1 hData).1,
          ((dataWFProc_seq_iff alphabet left right).1 hData).2⟩
  | seq_fuse _ alphabet _ left right _ _ _ _ _ _ =>
      exact ((dataWFProc_seq_iff alphabet left right).1 hData).2
  | seq_fuse_tock _ alphabet _ left right _ _ _ _ =>
      exact ((dataWFProc_seq_iff alphabet left right).1 hData).2
  | xoffer_send _ alphabet elseProcess branches _ _ _ _ hPrem _ =>
      have hBranch := branchBound_of_mem
        ((dataWFProc_xoffer_iff alphabet elseProcess branches).1 hData).2 hPrem.2.1
      rw [BranchBound] at hBranch
      exact hBranch.2
  | xoffer_recv _ alphabet elseProcess branches _ _ _ _ hPrem _ =>
      have hBranch := branchBound_of_mem
        ((dataWFProc_xoffer_iff alphabet elseProcess branches).1 hData).2 hPrem.2.1
      rw [BranchBound] at hBranch
      exact Proc.allVariablesBound_procExprReplace hBranch
  | xoffer_else _ alphabet elseProcess branches _ _ =>
      exact ((dataWFProc_xoffer_iff alphabet elseProcess branches).1 hData).1
  | xoffer_wait _ _ _ _ _ _ => exact hData
  | offer_some _ alphabet elseProcess branches _ hPrem _ =>
      exact dataWFProc_parallelProcessBranchesSelecting
        ((dataWFProc_offer_iff alphabet elseProcess branches).1 hData).2 hPrem.2.1
  | offer_else _ alphabet elseProcess branches _ _ =>
      exact ((dataWFProc_offer_iff alphabet elseProcess branches).1 hData).1
  | offer_wait _ _ _ _ _ _ => exact hData
  | par _ _ _ interface alphabet left left' right right' _ _ _ _ _ _
      _ _ _ _ _ _ _ _ ihLeft ihRight =>
      exact (dataWFProc_par_iff alphabet left' right' interface).2
        ⟨ihLeft ((dataWFProc_par_iff alphabet left right interface).1 hData).1,
          ihRight ((dataWFProc_par_iff alphabet left right interface).1 hData).2⟩
  | par_fuse _ _ _ _ alphabet _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact dataWFProc_skip alphabet
  | par_fuse_tock _ _ _ _ alphabet _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact dataWFProc_skip alphabet
  | left_complete _ _ _ interface alphabet left right _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ ihRight =>
      exact Proc.allVariablesBound_reannotate
        (ihRight ((dataWFProc_par_iff alphabet left right interface).1 hData).2)
  | right_complete _ _ _ interface alphabet left _ right _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ ihLeft =>
      exact Proc.allVariablesBound_reannotate
        (ihLeft ((dataWFProc_par_iff alphabet left right interface).1 hData).1)

end

end Pact
