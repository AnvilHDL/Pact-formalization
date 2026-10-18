import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.Offers

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-!
The `.recur` case of the simultaneous induction: the paper's
recursion-substitution transport, the environment-indexed form of the
recursion marker invariant, and the current-offer correspondence assembled
from them.
-/

/-- Replacing branch bodies leaves branch-head actions unchanged. -/
theorem PactType.typeBranchActions_replaceBranches
    (branches : List (BareMessage × PactType)) (name : String)
    (replacement : PactType) :
    typeBranchActions (PactType.replaceBranches branches name replacement) =
      typeBranchActions branches := by
  induction branches with
  | nil => simp [PactType.replaceBranches, typeBranchActions]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      simp only [PactType.replaceBranches, typeBranchActions, List.map_cons,
        List.toFinset_cons]
      change insert action
          (typeBranchActions (PactType.replaceBranches rest name replacement)) =
        insert action (typeBranchActions rest)
      rw [ih]

/-- Branch-head alphabet premises are invariant under body substitution. -/
theorem PactType.replaceBranches_heads
    {branches : List (BareMessage × PactType)} {alphabet : PactTypeAlphabet}
    {name : String} {replacement : PactType}
    (hHeads : ∀ b ∈ branches, b.1 ∈ alphabet.actions) :
    ∀ b ∈ PactType.replaceBranches branches name replacement,
      b.1 ∈ alphabet.actions := by
  intro b hb
  induction branches generalizing b with
  | nil => simp [PactType.replaceBranches] at hb
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      simp only [PactType.replaceBranches, List.mem_cons] at hb
      rcases hb with hb | hb
      · subst hb
        exact hHeads (action, branchType) (by simp)
      · exact ih (fun c hc => hHeads c (List.mem_cons_of_mem _ hc)) b hb

theorem TypeResolved_replaceBranches
    (env : TypeEnvironment) (branches : List (BareMessage × PactType))
    (name : String) (replacement : PactType) :
    TypeResolved env (PactType.replaceBranches branches name replacement) ↔
      TypeResolved env branches := by
  simp [TypeResolved, PactType.typeBranchNeeds_replaceBranches]

theorem TypeNoImmediateBranch_replaceBranches
    (env : TypeEnvironment) (branches : List (BareMessage × PactType))
    (name : String) (replacement : PactType) :
    TypeNoImmediateBranch env
        (PactType.replaceBranches branches name replacement) ↔
      TypeNoImmediateBranch env branches := by
  simp [TypeNoImmediateBranch, PactType.typeBranchNeeds_replaceBranches]

theorem typeWaitingOffers_replaceBranches
    (env : TypeEnvironment) (branches : List (BareMessage × PactType))
    (name : String) (replacement : PactType) :
    typeWaitingOffers env (PactType.replaceBranches branches name replacement) =
      typeWaitingOffers env branches := by
  simp [typeWaitingOffers, PactType.typeBranchActions_replaceBranches]

/-- Adding a duplicate forbidden name does not change binder freshness. -/
theorem PactType.binderFreshFor_cons_dup (name : String) :
    ∀ (bound : List String) (processType : PactType),
      PactType.BinderFreshFor (name :: bound) processType →
        PactType.BinderFreshFor (name :: name :: bound) processType := by
  intro bound processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | h n ih =>
      intro hFresh
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.BinderFreshForBranches (name :: bound) branches →
            PactType.BinderFreshForBranches (name :: name :: bound)
              branches := by
        intro branches hBranchesSize hBranchesFresh
        induction branches with
        | nil => simp [PactType.BinderFreshForBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BinderFreshForBranches] at hBranchesFresh ⊢
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl
                hBranchesFresh.1,
              restIH hRestSize hBranchesFresh.2⟩
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
          simp [PactType.BinderFreshFor]
      | choice _ left right | fairChoice _ _ left right | seq _ left right
      | par _ left right _ =>
          simp only [PactType.BinderFreshFor] at hFresh ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize left rfl hFresh.1,
            ih (sizeOf right) hRightSize right rfl hFresh.2⟩
      | recur _ binder body =>
          simp only [PactType.BinderFreshFor] at hFresh ⊢
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          exact ⟨by simpa [List.mem_cons] using hFresh.1,
            ih (sizeOf body) hBodySize body rfl hFresh.2⟩
      | xoffer _ elseType branches | offer _ elseType branches =>
          simp only [PactType.BinderFreshFor] at hFresh ⊢
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hElseSize elseType rfl hFresh.1,
            hBranches branches hBranchesSize hFresh.2⟩

/-- The recursion header edge exposed by the compiler. -/
theorem compileType_recur_root_hasEdge
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    {env : TypeEnvironment}
    (hEnv : env.WellFormed alphabet) (hClock : env.clock = false) :
    (compileType (.recur alphabet name body)).HasEdge .root env TypeLabel.silent
      { current := ∅,
        future := computeFutureOf (.recur alphabet name body)
          (.child 0 (compileTypeFuel (typeCompilationFuel body) body).initial) }
      (.child 0 (compileTypeFuel (typeCompilationFuel body) body).initial) := by
  classical
  rw [compileType_hasEdge_iff_hasResolvedEdge]
  refine ⟨
    { source := .root,
      environment := env,
      label := .visible TypeLabel.silent,
      current := ∅,
      future := .at (.child 0 (compileTypeFuel (typeCompilationFuel body) body).initial) ∅,
      target := .child 0 (compileTypeFuel (typeCompilationFuel body) body).initial },
    ?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · rw [compileTypeFuel_recur_eq]
    simp only [buildRecursionAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter]
    exact Or.inl ⟨env,
      ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hEnv, hClock⟩, rfl⟩
  · simp

/-- A public copy retains its future expression and moves each menu read to
the corresponding body-copy state. -/
theorem compileType_recur_child_pending_lift
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel (typeCompilationFuel body) body).edges)
    {label : TypeLabel} (hLabel : edge.label = .visible label) :
    (compileType (.recur alphabet name body)).HasEdge (.child 0 edge.source)
      edge.environment label
      ⟨edge.current, resolveFutureSpec
        (fun q => computeFutureOf (.recur alphabet name body) (.child 0 q)) edge.future⟩
      (.child 0 edge.target) := by
  rw [compileType_hasEdge_iff_hasResolvedEdge]
  refine ⟨childPendingEdge 0 edge, ?_, rfl, rfl, hLabel, rfl, ?_, rfl⟩
  · rw [compileTypeFuel_recur_eq]
    simp only [buildRecursionAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image]
    exact Or.inr ⟨edge, hEdge, by simp [hLabel, childPendingEdge]⟩
  · exact resolve_childFutureSpec 0 edge.future _ _ (fun _ _ => rfl)

/-- An installed marker reads the body-entry menu, not its old future field. -/
theorem compileType_recur_backedge_hasEdge
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel (typeCompilationFuel body) body).edges)
    (hLabel : edge.label = .variable name) :
    (compileType (.recur alphabet name body)).HasEdge (.child 0 edge.source)
      edge.environment TypeLabel.silent
      ⟨∅, computeFutureOf (.recur alphabet name body)
        (.child 0 (compileTypeFuel (typeCompilationFuel body) body).initial)⟩
      (.child 0 (compileTypeFuel (typeCompilationFuel body) body).initial) := by
  rw [compileType_hasEdge_iff_hasResolvedEdge]
  refine ⟨⟨.child 0 edge.source, edge.environment, .visible TypeLabel.silent, ∅,
    .at (.child 0 (compileTypeFuel (typeCompilationFuel body) body).initial) ∅,
    .child 0 (compileTypeFuel (typeCompilationFuel body) body).initial⟩,
    ?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · rw [compileTypeFuel_recur_eq]
    simp only [buildRecursionAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image]
    exact Or.inr ⟨edge, hEdge, by simp [hLabel, childState]⟩
  · simp

/-- A public body edge lifts to the installed recursion body with the same
environment, label and current offer.  The future field is recomputed in the
parent automaton, so it is existential. -/
theorem compileType_recur_child_edge_lift_current
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType body).HasEdge q env label
      { current := current, future := future } q') :
    ∃ future',
      (compileType (.recur alphabet name body)).HasEdge (.child 0 q) env label
        { current := current, future := future' } (.child 0 q') := by
  classical
  obtain ⟨bodyEdge, hBodyEdge, hSource, hEnv, hLabel, hCurrent, -, hTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge body q q' env label
      { current := current, future := future }).mp hEdge
  refine ⟨resolveFutureSpec
    (fun q => computeFutureOf (.recur alphabet name body) (.child 0 q)) bodyEdge.future, ?_⟩
  simpa only [hSource, hEnv, hCurrent, hTarget] using
    compileType_recur_child_pending_lift alphabet name body bodyEdge hBodyEdge hLabel

/-- Capture-avoiding substitutions commute when every binder in the source is
fresh for the free variables of the two inserted terms.  This is the syntactic
equation used by the nested-recursion branch of the paper's substitution
transport lemma. -/
theorem PactType.replaceVar_comm_of_bound
    (name other : String) (replacement binderReplacement processType : PactType)
    (bound : List String)
    (hNe : name ≠ other)
    (hOtherFresh : other ∉ bound)
    (hReplacementBound : PactType.AllVariablesBound bound replacement)
    (hBinderReplacementBound :
      PactType.AllVariablesBound bound binderReplacement)
    (hSourceFresh : processType.BinderFreshFor (name :: bound)) :
    (processType.replaceVar name replacement).replaceVar other
        (binderReplacement.replaceVar name replacement) =
      (processType.replaceVar other binderReplacement).replaceVar name
        replacement := by
  classical
  have hMain : ∀ n (processType : PactType) (bound : List String),
      sizeOf processType = n →
      other ∉ bound →
      PactType.AllVariablesBound bound replacement →
      PactType.AllVariablesBound bound binderReplacement →
      processType.BinderFreshFor (name :: bound) →
      (processType.replaceVar name replacement).replaceVar other
          (binderReplacement.replaceVar name replacement) =
        (processType.replaceVar other binderReplacement).replaceVar name
          replacement := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro processType bound hSize hOtherFresh hReplacementBound
        hBinderReplacementBound hSourceFresh
      have hReplacementNoOther :
          replacement.TailOccurrences other False :=
        PactType.tailOccurrences_false_of_allVariablesBound_not_mem other bound
          replacement hReplacementBound hOtherFresh
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.BinderFreshForBranches (name :: bound) branches →
          PactType.replaceBranches
              (PactType.replaceBranches branches name replacement)
              other (binderReplacement.replaceVar name replacement) =
            PactType.replaceBranches
              (PactType.replaceBranches branches other binderReplacement)
              name replacement := by
        intro branches hBranchesSize hFreshBranches
        induction branches with
        | nil =>
            simp [PactType.replaceBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BinderFreshForBranches] at hFreshBranches
            simp only [PactType.replaceBranches]
            have hBranchSize : sizeOf branchType < n := by
              simp at hBranchesSize
              omega
            have hRestSize : sizeOf rest < n := by
              simp at hBranchesSize
              omega
            rw [ih (sizeOf branchType) hBranchSize branchType bound rfl
                hOtherFresh hReplacementBound hBinderReplacementBound
                hFreshBranches.1,
              restIH hRestSize hFreshBranches.2]
      cases processType with
      | message alphabet msg dir =>
          simp [PactType.replaceVar]
      | progress alphabet pid =>
          simp [PactType.replaceVar]
      | tock alphabet =>
          simp [PactType.replaceVar]
      | skip alphabet =>
          simp [PactType.replaceVar]
      | var alphabet varName =>
          by_cases hName : name = varName
          · have hOtherNe : other ≠ varName := by
              intro h
              exact hNe (hName.trans h.symm)
            simp only [PactType.replaceVar, if_pos hName, if_neg hOtherNe]
            exact PactType.replaceVar_eq_self_of_tailOccurrences_false other
              (binderReplacement.replaceVar name replacement)
              replacement hReplacementNoOther
          · have hName' : ¬ (varName = name) := fun h => hName h.symm
            by_cases hOther : other = varName
            · subst hOther
              simp [PactType.replaceVar, hName]
            · have hOther' : ¬ (varName = other) := fun h => hOther h.symm
              simp [PactType.replaceVar, hName, hOther]
      | choice alphabet left right =>
          simp only [PactType.BinderFreshFor] at hSourceFresh
          simp only [PactType.replaceVar]
          rw [ih (sizeOf left) (by rw [← hSize]; simp; omega) left bound
              rfl hOtherFresh hReplacementBound hBinderReplacementBound
              hSourceFresh.1,
            ih (sizeOf right) (by rw [← hSize]; simp; omega) right bound
              rfl hOtherFresh hReplacementBound hBinderReplacementBound
              hSourceFresh.2]
      | fairChoice alphabet bid left right =>
          simp only [PactType.BinderFreshFor] at hSourceFresh
          simp only [PactType.replaceVar]
          rw [ih (sizeOf left) (by rw [← hSize]; simp; omega) left bound
              rfl hOtherFresh hReplacementBound hBinderReplacementBound
              hSourceFresh.1,
            ih (sizeOf right) (by rw [← hSize]; simp; omega) right bound
              rfl hOtherFresh hReplacementBound hBinderReplacementBound
              hSourceFresh.2]
      | seq alphabet left right =>
          simp only [PactType.BinderFreshFor] at hSourceFresh
          simp only [PactType.replaceVar]
          rw [ih (sizeOf left) (by rw [← hSize]; simp; omega) left bound
              rfl hOtherFresh hReplacementBound hBinderReplacementBound
              hSourceFresh.1,
            ih (sizeOf right) (by rw [← hSize]; simp; omega) right bound
              rfl hOtherFresh hReplacementBound hBinderReplacementBound
              hSourceFresh.2]
      | par alphabet left right interface =>
          simp only [PactType.BinderFreshFor] at hSourceFresh
          simp only [PactType.replaceVar]
          rw [ih (sizeOf left) (by rw [← hSize]; simp; omega) left bound
              rfl hOtherFresh hReplacementBound hBinderReplacementBound
              hSourceFresh.1,
            ih (sizeOf right) (by rw [← hSize]; simp; omega) right bound
              rfl hOtherFresh hReplacementBound hBinderReplacementBound
              hSourceFresh.2]
      | recur alphabet binder body =>
          simp only [PactType.BinderFreshFor] at hSourceFresh
          have hBinderNeName : binder ≠ name := by
            intro h
            exact hSourceFresh.1 (by simp [h])
          by_cases hBinderOther : binder = other
          · subst hBinderOther
            simp [PactType.replaceVar, hNe]
          · have hNameNeBinder : name ≠ binder := fun h => hBinderNeName h.symm
            have hOtherNeBinder : other ≠ binder := fun h => hBinderOther h.symm
            simp only [PactType.replaceVar, if_neg hNameNeBinder,
              if_neg hOtherNeBinder]
            rw [ih (sizeOf body) (by rw [← hSize]; simp; omega) body bound
                rfl hOtherFresh hReplacementBound hBinderReplacementBound
                hSourceFresh.2]
      | xoffer alphabet elseType branches =>
          simp only [PactType.BinderFreshFor] at hSourceFresh
          simp only [PactType.replaceVar]
          rw [ih (sizeOf elseType) (by rw [← hSize]; simp; omega)
              elseType bound rfl hOtherFresh hReplacementBound
              hBinderReplacementBound hSourceFresh.1,
            hBranches branches (by rw [← hSize]; simp; omega) hSourceFresh.2]
      | offer alphabet elseType branches =>
          simp only [PactType.BinderFreshFor] at hSourceFresh
          simp only [PactType.replaceVar]
          rw [ih (sizeOf elseType) (by rw [← hSize]; simp; omega)
              elseType bound rfl hOtherFresh hReplacementBound
              hBinderReplacementBound hSourceFresh.1,
            hBranches branches (by rw [← hSize]; simp; omega) hSourceFresh.2]
  exact hMain (sizeOf processType) processType bound rfl hOtherFresh
    hReplacementBound hBinderReplacementBound hSourceFresh

/-- Substituting a term whose variables are bound by `bound` for `name` drops
`name` from the source context.  This is the closure fact used by the nested
recursion branch of the substitution transport. -/
theorem PactType.allVariablesBound_replaceVar_drop
    (name : String) (replacement : PactType) :
    ∀ (bound : List String) (processType : PactType),
      PactType.AllVariablesBound bound replacement →
      PactType.AllVariablesBound (name :: bound) processType →
      PactType.AllVariablesBound bound
        (processType.replaceVar name replacement) := by
  intro bound processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType bound with
  | _ n ih =>
    intro hReplacement hSource
    have hBranches : ∀ (bound : List String)
        (branches : List (BareMessage × PactType)),
        sizeOf branches < n →
        PactType.AllVariablesBound bound replacement →
        PactType.AllBranchVariablesBound (name :: bound) branches →
        PactType.AllBranchVariablesBound bound
          (PactType.replaceBranches branches name replacement) := by
      intro bound branches hBranchesSize hReplacement hBranchBound
      induction branches with
      | nil =>
          simp [PactType.replaceBranches, PactType.AllBranchVariablesBound]
      | cons branch rest restIH =>
          rcases branch with ⟨action, branchType⟩
          simp only [PactType.AllBranchVariablesBound] at hBranchBound
          simp only [PactType.replaceBranches, PactType.AllBranchVariablesBound]
          have hBranchSize : sizeOf branchType < n := by
            have hPair : sizeOf branchType < sizeOf (action, branchType) := by
              simp_wf
              omega
            have hHead : sizeOf (action, branchType) <
                sizeOf ((action, branchType) :: rest) := by
              simp_wf
              omega
            omega
          have hRestSize : sizeOf rest < n := by
            have hTail : sizeOf rest <
                sizeOf ((action, branchType) :: rest) := by
              simp_wf
              omega
            omega
          exact ⟨ih (sizeOf branchType) hBranchSize bound branchType rfl
              hReplacement hBranchBound.1,
            restIH hRestSize hBranchBound.2⟩
    cases processType with
    | message alphabet msg dir =>
        simp [PactType.replaceVar, PactType.AllVariablesBound]
    | progress alphabet pid =>
        simp [PactType.replaceVar, PactType.AllVariablesBound]
    | tock alphabet =>
        simp [PactType.replaceVar, PactType.AllVariablesBound]
    | skip alphabet =>
        simp [PactType.replaceVar, PactType.AllVariablesBound]
    | var alphabet other =>
        by_cases hEq : name = other
        · subst hEq
          simpa [PactType.replaceVar, PactType.AllVariablesBound]
            using hReplacement
        · have hOther : other ∈ bound := by
            simp only [PactType.AllVariablesBound, List.mem_cons] at hSource
            rcases hSource with hName | hBound
            · exact absurd hName.symm hEq
            · exact hBound
          simp [PactType.replaceVar, PactType.AllVariablesBound, hEq, hOther]
    | choice alphabet left right =>
        simp only [PactType.AllVariablesBound] at hSource
        simp only [PactType.replaceVar, PactType.AllVariablesBound]
        exact ⟨ih (sizeOf left) (by rw [← hSize]; simp; omega) bound left rfl
            hReplacement hSource.1,
          ih (sizeOf right) (by rw [← hSize]; simp; omega) bound right rfl
            hReplacement hSource.2⟩
    | fairChoice alphabet bid left right =>
        simp only [PactType.AllVariablesBound] at hSource
        simp only [PactType.replaceVar, PactType.AllVariablesBound]
        exact ⟨ih (sizeOf left) (by rw [← hSize]; simp; omega) bound left rfl
            hReplacement hSource.1,
          ih (sizeOf right) (by rw [← hSize]; simp; omega) bound right rfl
            hReplacement hSource.2⟩
    | seq alphabet left right =>
        simp only [PactType.AllVariablesBound] at hSource
        simp only [PactType.replaceVar, PactType.AllVariablesBound]
        exact ⟨ih (sizeOf left) (by rw [← hSize]; simp; omega) bound left rfl
            hReplacement hSource.1,
          ih (sizeOf right) (by rw [← hSize]; simp; omega) bound right rfl
            hReplacement hSource.2⟩
    | par alphabet left right interface =>
        simp only [PactType.AllVariablesBound] at hSource
        simp only [PactType.replaceVar, PactType.AllVariablesBound]
        exact ⟨ih (sizeOf left) (by rw [← hSize]; simp; omega) bound left rfl
            hReplacement hSource.1,
          ih (sizeOf right) (by rw [← hSize]; simp; omega) bound right rfl
            hReplacement hSource.2⟩
    | recur alphabet binder body =>
        by_cases hShadow : name = binder
        · subst hShadow
          have hBody : PactType.AllVariablesBound (name :: name :: bound) body := by
            simpa only [PactType.AllVariablesBound] using hSource
          simpa [PactType.replaceVar, PactType.AllVariablesBound] using
            PactType.allVariablesBound_mono
              (smaller := name :: name :: bound) (larger := name :: bound)
              (processType := body)
              (fun varName hMem => by
                simp only [List.mem_cons] at hMem ⊢
                rcases hMem with hMem | hMem | hMem
                · exact Or.inl hMem
                · exact Or.inl hMem
                · exact Or.inr hMem) hBody
        · simp only [PactType.replaceVar, if_neg hShadow,
            PactType.AllVariablesBound]
          have hBodyRaw :
              PactType.AllVariablesBound (binder :: name :: bound) body := by
            simpa only [PactType.AllVariablesBound] using hSource
          have hBody :
              PactType.AllVariablesBound (name :: binder :: bound) body :=
            PactType.allVariablesBound_mono (processType := body)
              (smaller := binder :: name :: bound)
              (larger := name :: binder :: bound)
              (fun varName hMem => by
                simp only [List.mem_cons] at hMem ⊢
                rcases hMem with hMem | hMem | hMem
                · exact Or.inr (Or.inl hMem)
                · exact Or.inl hMem
                · exact Or.inr (Or.inr hMem)) hBodyRaw
          have hReplacement' :
              PactType.AllVariablesBound (binder :: bound) replacement :=
            PactType.allVariablesBound_mono (processType := replacement)
              (smaller := bound) (larger := binder :: bound)
              (fun varName hMem => by
                exact List.mem_cons_of_mem binder hMem) hReplacement
          exact ih (sizeOf body) (by rw [← hSize]; simp; omega)
            (binder :: bound) body rfl hReplacement' hBody
    | xoffer alphabet elseType branches =>
        simp only [PactType.AllVariablesBound] at hSource
        simp only [PactType.replaceVar, PactType.AllVariablesBound]
        exact ⟨ih (sizeOf elseType) (by rw [← hSize]; simp; omega)
            bound elseType rfl hReplacement hSource.1,
          hBranches bound branches (by rw [← hSize]; simp; omega)
            hReplacement hSource.2⟩
    | offer alphabet elseType branches =>
        simp only [PactType.AllVariablesBound] at hSource
        simp only [PactType.replaceVar, PactType.AllVariablesBound]
        exact ⟨ih (sizeOf elseType) (by rw [← hSize]; simp; omega)
            bound elseType rfl hReplacement hSource.1,
          hBranches bound branches (by rw [← hSize]; simp; omega)
            hReplacement hSource.2⟩

theorem singletonTypeXOfferAt_allVariablesBound
    {bound : List String} (alphabet : PactTypeAlphabet)
    (branch : BareMessage × PactType)
    (hBranch : PactType.AllVariablesBound bound branch.2) :
    PactType.AllVariablesBound bound (singletonTypeXOfferAt alphabet branch) := by
  rcases branch with ⟨action, body⟩
  simp only [singletonTypeXOfferAt, PactType.AllVariablesBound,
    PactType.AllBranchVariablesBound]
  exact ⟨trivial,
    PactType.reannotate_allVariablesBound bound body alphabet hBranch,
    trivial⟩

theorem selectedTypeBranchAt_allVariablesBound
    {bound : List String} (alphabet : PactTypeAlphabet)
    (branch : BareMessage × PactType)
    (hBranch : PactType.AllVariablesBound bound branch.2) :
    PactType.AllVariablesBound bound (selectedTypeBranchAt alphabet branch) := by
  rcases branch with ⟨action, body⟩
  simp only [selectedTypeBranchAt, PactType.AllVariablesBound]
  exact ⟨trivial,
    PactType.reannotate_allVariablesBound bound body alphabet hBranch⟩

theorem parallelTypeBranchesWithin_allVariablesBound
    {bound : List String} (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      (∀ branch ∈ branches,
        PactType.AllVariablesBound bound branch.2) →
      PactType.AllVariablesBound bound
        (parallelTypeBranchesWithin alphabet branches)
  | [] => by
      intro _
      simp [parallelTypeBranchesWithin, PactType.AllVariablesBound]
  | branch :: rest => by
      intro hBranches
      cases rest with
      | nil =>
          simpa [parallelTypeBranchesWithin] using
            singletonTypeXOfferAt_allVariablesBound alphabet branch
              (hBranches branch (by simp))
      | cons next tail =>
          have hRest : ∀ branch ∈ next :: tail,
              PactType.AllVariablesBound bound branch.2 := by
            intro branch hMem
            exact hBranches branch (by simp [hMem])
          simp only [parallelTypeBranchesWithin, PactType.AllVariablesBound]
          exact ⟨singletonTypeXOfferAt_allVariablesBound alphabet branch
              (hBranches branch (by simp)),
            parallelTypeBranchesWithin_allVariablesBound alphabet
              (next :: tail) hRest⟩

theorem parallelTypeBranchesSelectingWithin_allVariablesBound
    {bound : List String} (alphabet : PactTypeAlphabet)
    (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType),
      (∀ branch ∈ branches,
        PactType.AllVariablesBound bound branch.2) →
      PactType.AllVariablesBound bound
        (parallelTypeBranchesSelectingWithin alphabet selected branches)
  | [] => by
      intro _
      simp [parallelTypeBranchesSelectingWithin, PactType.AllVariablesBound]
  | branch :: rest => by
      intro hBranches
      cases rest with
      | nil =>
          by_cases hSelected : branch = selected
          · simp only [parallelTypeBranchesSelectingWithin, if_pos hSelected]
            exact selectedTypeBranchAt_allVariablesBound alphabet branch
              (hBranches branch (by simp))
          · simp only [parallelTypeBranchesSelectingWithin, if_neg hSelected]
            exact singletonTypeXOfferAt_allVariablesBound alphabet branch
              (hBranches branch (by simp))
      | cons next tail =>
          have hRest : ∀ branch ∈ next :: tail,
              PactType.AllVariablesBound bound branch.2 := by
            intro branch hMem
            exact hBranches branch (by simp [hMem])
          by_cases hSelected : branch = selected
          · simp only [parallelTypeBranchesSelectingWithin, if_pos hSelected,
              PactType.AllVariablesBound]
            exact ⟨selectedTypeBranchAt_allVariablesBound alphabet branch
                (hBranches branch (by simp)),
              parallelTypeBranchesWithin_allVariablesBound alphabet
                (next :: tail) hRest⟩
          · simp only [parallelTypeBranchesSelectingWithin, if_neg hSelected,
              PactType.AllVariablesBound]
            exact ⟨singletonTypeXOfferAt_allVariablesBound alphabet branch
                (hBranches branch (by simp)),
              parallelTypeBranchesSelectingWithin_allVariablesBound alphabet
                selected (next :: tail) hRest⟩

theorem parallelTypeBranchesSelecting_allVariablesBound
    {bound : List String} (alphabet : PactTypeAlphabet)
    (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hBranches : ∀ branch ∈ branches,
      PactType.AllVariablesBound bound branch.2) :
    PactType.AllVariablesBound bound
      (parallelTypeBranchesSelecting alphabet selected branches) := by
  cases branches with
  | nil =>
      simp [parallelTypeBranchesSelecting, PactType.AllVariablesBound]
  | cons branch rest =>
      simpa [parallelTypeBranchesSelecting] using
        parallelTypeBranchesSelectingWithin_allVariablesBound alphabet selected
          (branch :: rest) hBranches

/-- Atomic residuals preserve the variables bound in every continuation. -/
theorem parallelTypeBranchesFiring_allVariablesBound
    (alphabet : PactTypeAlphabet) (selected : Finset Nat)
    (branches : List (BareMessage × PactType)) {bound : List String}
    (hBound : ∀ branch ∈ branches, PactType.AllVariablesBound bound branch.2) :
    PactType.AllVariablesBound bound (parallelTypeBranchesFiring alphabet selected branches) := by
  have hFrom : ∀ index, PactType.AllVariablesBound bound
      (parallelTypeBranchesFiringFrom alphabet selected index branches) := by
    induction branches with
    | nil => intro index; simp [parallelTypeBranchesFiringFrom, PactType.AllVariablesBound]
    | cons head rest ih =>
        intro index
        have hBody := PactType.reannotate_allVariablesBound bound head.2 alphabet
          (hBound head (by simp))
        have hFactor : PactType.AllVariablesBound bound
            (if index ∈ selected then head.2.reannotate alphabet
              else singletonTypeXOfferAt alphabet head) := by
          split_ifs
          · exact hBody
          · rcases head with ⟨action, body⟩
            simp only [singletonTypeXOfferAt, PactType.AllVariablesBound,
              PactType.AllBranchVariablesBound]
            exact ⟨trivial, hBody, trivial⟩
        cases rest with
        | nil => exact hFactor
        | cons next tail =>
            rw [parallelTypeBranchesFiringFrom, PactType.AllVariablesBound]
            exact ⟨hFactor, ih (fun b hb => hBound b (by simp [hb])) (index + 1)⟩
  exact hFrom 0


/-- Closure is preserved by the compiler relation.  The recursion relation is
the only constructor that changes syntax: it substitutes the binder by the
recursive type, and `allVariablesBound_replaceVar_drop` removes that binder
from the residual context. -/
theorem relationMembership_allVariablesBound :
    ∀ (source residual : PactType) (state : TypeAutomatonState)
      (bound : List String),
      PactType.AllVariablesBound bound source →
      relationMembership (buildRelationSet source (compileType source))
        residual state →
      PactType.AllVariablesBound bound residual := by
  intro source
  induction hFuel : typeCompilationFuel source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
    intro residual state bound hBound hRelated
    have hMemBranches : ∀ (branches : List (BareMessage × PactType))
        (branch : BareMessage × PactType),
        PactType.AllBranchVariablesBound bound branches → branch ∈ branches →
        PactType.AllVariablesBound bound branch.2 := by
      intro branches
      induction branches with
      | nil => intro branch hBranchBound hMem; cases hMem
      | cons head rest restIH =>
          rcases head with ⟨headAction, headType⟩
          intro branch hBranchBound hMem
          simp only [PactType.AllBranchVariablesBound] at hBranchBound
          simp only [List.mem_cons] at hMem
          rcases hMem with hEq | hMem
          · subst hEq; exact hBranchBound.1
          · exact restIH branch hBranchBound.2 hMem
    cases source with
    | skip alphabet =>
        rw [(relationMembership_skip_cases alphabet hRelated).1]
        exact hBound
    | message alphabet msg dir =>
        rcases relationMembership_message_cases alphabet msg dir hRelated with
          hRoot | hFinal
        · rw [hRoot.1]; exact hBound
        · rw [hFinal.1]; simp [PactType.AllVariablesBound]
    | tock alphabet =>
        rcases relationMembership_tock_cases alphabet hRelated with hRoot | hFinal
        · rw [hRoot.1]; exact hBound
        · rw [hFinal.1]; simp [PactType.AllVariablesBound]
    | progress alphabet pid =>
        rcases relationMembership_progress_cases alphabet pid hRelated with
          hRoot | hFinal
        · rw [hRoot.1]; exact hBound
        · rw [hFinal.1]; simp [PactType.AllVariablesBound]
    | var alphabet other =>
        rw [(relationMembership_var_cases alphabet other hRelated).1]
        exact hBound
    | choice alphabet left right =>
        have hFields : PactType.AllVariablesBound bound left ∧
            PactType.AllVariablesBound bound right := by
          simpa only [PactType.AllVariablesBound] using hBound
        rcases relationMembership_choice_cases alphabet left right hRelated with
          hRoot | hLeft | hRight
        · injection hRoot with hResidual _
          rw [hResidual]
          exact hBound
        · rcases hLeft with ⟨q, _, hLeftRelated⟩
          have hLeftFuel : typeCompilationFuel left < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          exact ih (typeCompilationFuel left) hLeftFuel left rfl residual q
            bound hFields.1 hLeftRelated
        · rcases hRight with ⟨q, _, hRightRelated⟩
          have hRightFuel : typeCompilationFuel right < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
            bound hFields.2 hRightRelated
    | fairChoice alphabet bid left right =>
        have hFields : PactType.AllVariablesBound bound left ∧
            PactType.AllVariablesBound bound right := by
          simpa only [PactType.AllVariablesBound] using hBound
        rcases relationMembership_fairChoice_cases alphabet bid left right
            hRelated with hRoot | hLeft | hRight
        · injection hRoot with hResidual _
          rw [hResidual]
          exact hBound
        · rcases hLeft with ⟨q, _, hLeftRelated⟩
          have hLeftFuel : typeCompilationFuel left < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          exact ih (typeCompilationFuel left) hLeftFuel left rfl residual q
            bound hFields.1 hLeftRelated
        · rcases hRight with ⟨q, _, hRightRelated⟩
          have hRightFuel : typeCompilationFuel right < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
            bound hFields.2 hRightRelated
    | seq alphabet left right =>
        have hFields : PactType.AllVariablesBound bound left ∧
            PactType.AllVariablesBound bound right := by
          simpa only [PactType.AllVariablesBound] using hBound
        rcases relationMembership_seq_cases alphabet left right hRelated with
          hLeft | hRight
        · rcases hLeft with ⟨q, leftResidual, hEntry, hLeftRelated, _⟩
          injection hEntry with hResidual _
          rw [hResidual]
          have hLeftFuel : typeCompilationFuel left < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          simpa only [PactType.AllVariablesBound] using
            And.intro (ih (typeCompilationFuel left) hLeftFuel left rfl
                leftResidual q bound hFields.1 hLeftRelated) hFields.2
        · rcases hRight with ⟨q, _, hRightRelated⟩
          have hRightFuel : typeCompilationFuel right < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
            bound hFields.2 hRightRelated
    | par alphabet left right interface =>
        have hFields : PactType.AllVariablesBound bound left ∧
            PactType.AllVariablesBound bound right := by
          simpa only [PactType.AllVariablesBound] using hBound
        rcases relationMembership_par_cases alphabet left right interface
            hRelated with hPair | hSurvL | hSurvR | hFinal
        · rcases hPair with ⟨q1, q2, leftResidual, rightResidual,
            hEntry, hLeftRelated, hRightRelated⟩
          injection hEntry with hResidual _
          rw [hResidual]
          have hLeftFuel : typeCompilationFuel left < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          have hRightFuel : typeCompilationFuel right < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          simpa only [PactType.AllVariablesBound] using
            And.intro (ih (typeCompilationFuel left) hLeftFuel left rfl
                leftResidual q1 bound hFields.1 hLeftRelated)
              (ih (typeCompilationFuel right) hRightFuel right rfl
                rightResidual q2 bound hFields.2 hRightRelated)
        · rcases hSurvL with ⟨q1, residualLeft, hEntry, hLeftRelated, _⟩
          injection hEntry with hResidual _
          rw [hResidual]
          have hLeftFuel : typeCompilationFuel (left.reannotate alphabet) < n := by
            rw [← hFuel, typeCompilationFuel_reannotate]
            simp only [typeCompilationFuel]; omega
          exact ih (typeCompilationFuel (left.reannotate alphabet)) hLeftFuel
            (left.reannotate alphabet) rfl residualLeft q1 bound
            (PactType.reannotate_allVariablesBound bound left alphabet hFields.1)
            hLeftRelated
        · rcases hSurvR with ⟨q2, residualRight, hEntry, hRightRelated, _⟩
          injection hEntry with hResidual _
          rw [hResidual]
          have hRightFuel : typeCompilationFuel (right.reannotate alphabet) < n := by
            rw [← hFuel, typeCompilationFuel_reannotate]
            simp only [typeCompilationFuel]; omega
          exact ih (typeCompilationFuel (right.reannotate alphabet)) hRightFuel
            (right.reannotate alphabet) rfl residualRight q2 bound
            (PactType.reannotate_allVariablesBound bound right alphabet hFields.2)
            hRightRelated
        · injection hFinal with hResidual _
          rw [hResidual]
          simp [PactType.AllVariablesBound]
    | recur alphabet binder body =>
        have hBodyBound : PactType.AllVariablesBound (binder :: bound) body := by
          simpa only [PactType.AllVariablesBound] using hBound
        rcases relationMembership_recur_cases alphabet binder body hRelated with
          hRoot | hBody
        · injection hRoot with hResidual _
          rw [hResidual]
          exact hBound
        · rcases hBody with ⟨q, bodyResidual, hEntry, hBodyRelated⟩
          injection hEntry with hResidual _
          rw [hResidual]
          have hBodyFuel : typeCompilationFuel body < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          have hResidualBound :
              PactType.AllVariablesBound (binder :: bound) bodyResidual :=
            ih (typeCompilationFuel body) hBodyFuel body rfl bodyResidual q
              (binder :: bound) hBodyBound hBodyRelated
          exact PactType.allVariablesBound_replaceVar_drop binder
            (.recur alphabet binder body) bound bodyResidual hBound hResidualBound
    | xoffer alphabet elseType branches =>
        have hFields : PactType.AllVariablesBound bound elseType ∧
            PactType.AllBranchVariablesBound bound branches := by
          simpa only [PactType.AllVariablesBound] using hBound
        rcases relationMembership_xoffer_cases alphabet elseType branches
            hRelated with hRoot | hElse | hBranch
        · injection hRoot with hResidual _
          rw [hResidual]
          exact hBound
        · rcases hElse with ⟨q, _, hElseRelated⟩
          have hElseFuel : typeCompilationFuel elseType < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          exact ih (typeCompilationFuel elseType) hElseFuel elseType rfl
            residual q bound hFields.1 hElseRelated
        · rcases hBranch with ⟨i, action, branchType, q, hGet, _, hBranchRelated⟩
          have hMember : (action, branchType) ∈ branches :=
            List.mem_of_getElem? hGet
          have hBranchFuel : typeCompilationFuel branchType < n := by
            have hLe : typeCompilationFuel branchType ≤
                typeBranchCompilationFuel branches := by
              simpa using typeCompilationFuel_le_typeBranchCompilationFuel
                branches (action, branchType) hMember
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          exact ih (typeCompilationFuel branchType) hBranchFuel branchType rfl
            residual q bound
            (hMemBranches branches (action, branchType) hFields.2 hMember)
            hBranchRelated
    | offer alphabet elseType branches =>
        have hFields : PactType.AllVariablesBound bound elseType ∧
            PactType.AllBranchVariablesBound bound branches := by
          simpa only [PactType.AllVariablesBound] using hBound
        rcases relationMembership_offer_cases alphabet elseType branches
            hRelated with hRoot | hElse | hSelected
        · injection hRoot with hResidual _
          rw [hResidual]
          exact hBound
        · rcases hElse with ⟨q, _, hElseRelated⟩
          have hElseFuel : typeCompilationFuel elseType < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          exact ih (typeCompilationFuel elseType) hElseFuel elseType rfl
            residual q bound hFields.1 hElseRelated
        · rcases hSelected with ⟨i, selected, q, hGet, _, hSelectedRelated⟩
          have hSelectedFuel :
              typeCompilationFuel
                  (parallelTypeBranchesFiring alphabet selected branches) < n := by
            rw [← hFuel]
            exact typeCompilationFuel_firing_lt_offer alphabet elseType selected branches
          have hSelectedBound : PactType.AllVariablesBound bound
              (parallelTypeBranchesFiring alphabet selected branches) :=
            parallelTypeBranchesFiring_allVariablesBound alphabet selected
              branches (fun branch hBranch =>
                hMemBranches branches branch hFields.2 hBranch)
          exact ih (typeCompilationFuel
              (parallelTypeBranchesFiring alphabet selected branches))
            hSelectedFuel (parallelTypeBranchesFiring alphabet selected branches)
            rfl residual q bound hSelectedBound hSelectedRelated

/-- A marker edge for `name` carrying a prescribed environment: the
environment-indexed form of `MarkerSource` used by the paper's recursion
marker invariant, which fixes a non-clock `E ∈ Env`. -/
def MarkerSourceFor (fragment : AutomatonFragment) (name : String)
    (env : TypeEnvironment) (state : TypeAutomatonState) : Prop :=
  ∃ edge ∈ fragment.edges,
    edge.source = state ∧ edge.environment = env ∧
    edge.label = AutomatonConstructionLabel.variable name

theorem MarkerSourceFor.markerSource {fragment : AutomatonFragment}
    {name : String} {env : TypeEnvironment} {state : TypeAutomatonState}
    (h : MarkerSourceFor fragment name env state) :
    MarkerSource fragment name state := by
  obtain ⟨edge, hEdge, hSource, -, hLabel⟩ := h
  exact ⟨edge, hEdge, hSource, hLabel⟩

/-- Any builder that copies a child's edges verbatim carries an
environment-indexed marker along with the tag. -/
theorem markerSourceFor_child {parent child : AutomatonFragment} {index : Nat}
    {name : String} {env : TypeEnvironment} {q : TypeAutomatonState}
    (hSubset : ∀ edge ∈ childPendingEdges index child, edge ∈ parent.edges)
    (h : MarkerSourceFor child name env q) :
    MarkerSourceFor parent name env (childState index q) := by
  classical
  obtain ⟨edge, hEdge, hSource, hEnv, hLabel⟩ := h
  refine ⟨childPendingEdge index edge, hSubset _ ?_, ?_, ?_, ?_⟩
  · simpa [childPendingEdges] using
      Finset.mem_image_of_mem (childPendingEdge index) hEdge
  · simp [childPendingEdge, hSource]
  · simpa [childPendingEdge] using hEnv
  · simpa [childPendingEdge] using hLabel

theorem childPendingEdges_subset_choice_left
    (alphabet : PactTypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) :
    ∀ edge ∈ childPendingEdges 0 left,
      edge ∈ (buildChoiceAutomaton alphabet left right selectionLeft
        selectionRight).edges := by
  intro edge hEdge
  simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union]
  exact Or.inl (Or.inl hEdge)

theorem childPendingEdges_subset_choice_right
    (alphabet : PactTypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) :
    ∀ edge ∈ childPendingEdges 1 right,
      edge ∈ (buildChoiceAutomaton alphabet left right selectionLeft
        selectionRight).edges := by
  intro edge hEdge
  simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union]
  exact Or.inl (Or.inr hEdge)

theorem childPendingEdges_subset_sequence_right
    (left right : AutomatonFragment)
    {leftFuture : TypeAutomatonState → Finset BareMessage}
    {leftCompletes : TypeAutomatonState → Bool} :
    ∀ edge ∈ childPendingEdges 1 right,
      edge ∈ (buildSequenceAutomaton left right leftFuture leftCompletes).edges := by
  intro edge hEdge
  simp only [buildSequenceAutomaton, finishAutomatonFragment, Finset.mem_union,
    sequenceRightEdges]
  exact Or.inl (Or.inr hEdge)

theorem childPendingEdges_subset_indexedFragmentEdges
    (automata : List (BareMessage × AutomatonFragment)) (i : Nat)
    (entry : BareMessage × AutomatonFragment)
    (hEntry : automata[i]? = some entry) :
    ∀ edge ∈ childPendingEdges (i + 1) entry.2,
      edge ∈ indexedFragmentEdges automata := by
  intro edge hEdge
  simp only [indexedFragmentEdges, mem_foldl_union_iff]
  refine Or.inr ⟨(entry, i), ?_, hEdge⟩
  rw [List.mk_mem_zipIdx_iff_getElem?]
  exact hEntry

theorem childPendingEdges_subset_xoffer_else
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) :
    ∀ edge ∈ childPendingEdges 0 elseAutomaton,
      edge ∈ (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
        branchAutomata).edges := by
  intro edge hEdge
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl hEdge)))

theorem indexedFragmentEdges_subset_xoffer
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) :
    ∀ edge ∈ indexedFragmentEdges branchAutomata,
      edge ∈ (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
        branchAutomata).edges := by
  intro edge hEdge
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inr hEdge)))

theorem childPendingEdges_subset_conjunctive_else
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (Finset Nat × AutomatonFragment)) :
    ∀ edge ∈ childPendingEdges 0 elseAutomaton,
      edge ∈ (buildAtomicConjunctiveOfferAutomaton alphabet branches
        elseAutomaton selectedConjunctions).edges := by
  intro edge hEdge
  simp only [buildAtomicConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl hEdge)))

/-- The recursion builder rewrites only its own binder's markers, so a marker
for any other name is copied with its environment. -/
theorem markerSourceFor_buildRecursionAutomaton_child
    (alphabet : PactTypeAlphabet) (binder name : String)
    (body : AutomatonFragment) (hNe : name ≠ binder)
    {env : TypeEnvironment} {q : TypeAutomatonState}
    (h : MarkerSourceFor body name env q) :
    MarkerSourceFor (buildRecursionAutomaton alphabet binder body) name env
      (childState 0 q) := by
  classical
  obtain ⟨edge, hEdge, hSource, hEnv, hLabel⟩ := h
  have hNotBinder :
      edge.label ≠ AutomatonConstructionLabel.variable binder := by
    rw [hLabel]
    intro hEq
    exact hNe (by injection hEq)
  refine ⟨childPendingEdge 0 edge, ?_, ?_, ?_, ?_⟩
  · simp only [buildRecursionAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image]
    exact Or.inr ⟨edge, hEdge, by rw [if_neg hNotBinder]; rfl⟩
  · simp [childPendingEdge, hSource]
  · simpa [childPendingEdge] using hEnv
  · simpa [childPendingEdge] using hLabel

/-- Paper helper 13, environment-indexed: the state standing for a recursive
call sources a marker edge carrying any non-clock environment of the call's
alphabet. -/
theorem markerSourceFor_of_var_residual
    (processType : PactType) (name : String)
    (env : TypeEnvironment) (varAlphabet : PactTypeAlphabet)
    (hTail : PactType.TailOccurrences name True processType)
    (hEnvMem : env ∈ varAlphabet.localEnvironments)
    (hClock : env.clock = false)
    {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType processType))
        (.var varAlphabet name) state) :
    MarkerSourceFor
      (compileTypeFuel (typeCompilationFuel processType) processType)
      name env state := by
  classical
  induction hSize : typeCompilationFuel processType using Nat.strong_induction_on
      generalizing processType state with
  | _ n ih =>
    subst hSize
    have atomic : ∀ (ty : PactType) (q' : TypeAutomatonState),
        PactType.TailOccurrences name False ty →
        ¬ MarkerSource (compileTypeFuel (typeCompilationFuel ty) ty) name q' := by
      intro ty q' hAbsent hMarker
      obtain ⟨edge, hEdge, -, hLabel⟩ := hMarker
      exact absurd hLabel
        (compileTypeFuel_noMarkerFor name (typeCompilationFuel ty) ty hAbsent
          edge hEdge)
    cases processType with
    | skip alphabet =>
        exact absurd (NewCorrespondence.relationMembership_skip_cases alphabet
          hRelated).1 (by simp)
    | message alphabet msg dir =>
        rcases NewCorrespondence.relationMembership_message_cases alphabet msg
          dir hRelated with ⟨hR, -⟩ | ⟨hR, -⟩ <;> simp at hR
    | tock alphabet =>
        rcases NewCorrespondence.relationMembership_tock_cases alphabet
          hRelated with ⟨hR, -⟩ | ⟨hR, -⟩ <;> simp at hR
    | progress alphabet pid =>
        rcases NewCorrespondence.relationMembership_progress_cases alphabet pid
          hRelated with ⟨hR, -⟩ | ⟨hR, -⟩ <;> simp at hR
    | var alphabet other =>
        obtain ⟨hResidual, hState⟩ :=
          relationMembership_var_cases alphabet other hRelated
        obtain ⟨hAlphabet, hName⟩ : varAlphabet = alphabet ∧ name = other := by
          injection hResidual with hA hN
          exact ⟨hA, hN⟩
        subst hState
        refine ⟨{ source := .root
                  environment := env
                  label := .variable other
                  current := ∅
                  future := .at .final ∅
                  target := .final }, ?_, rfl, rfl, by rw [hName]⟩
        simp only [typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment, Finset.mem_image, Finset.mem_filter]
        exact ⟨env, ⟨by rw [← hAlphabet]; exact hEnvMem, hClock⟩, rfl⟩
    | choice alphabet left right =>
        have hFuelEq : typeCompilationFuel (PactType.choice alphabet left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hCompileEq := compileTypeFuel_choice_eq alphabet left right
        rw [PactType.TailOccurrences] at hTail
        rcases relationMembership_choice_cases alphabet left right hRelated with
          hRoot | ⟨q, hState, hChild⟩ | ⟨q, hState, hChild⟩
        · exact absurd (congrArg Prod.fst hRoot) (by simp)
        · subst hState
          rw [hCompileEq]
          exact markerSourceFor_child
            (childPendingEdges_subset_choice_left alphabet _ _ _ _)
            (ih (typeCompilationFuel left) (by rw [hFuelEq]; omega) left
              hTail.1 hChild rfl)
        · subst hState
          rw [hCompileEq]
          exact markerSourceFor_child
            (childPendingEdges_subset_choice_right alphabet _ _ _ _)
            (ih (typeCompilationFuel right) (by rw [hFuelEq]; omega) right
              hTail.2 hChild rfl)
    | fairChoice alphabet bid left right =>
        have hFuelEq :
            typeCompilationFuel (PactType.fairChoice alphabet bid left right) =
              max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hCompileEq :
            compileTypeFuel (typeCompilationFuel
                (PactType.fairChoice alphabet bid left right))
                (PactType.fairChoice alphabet bid left right) =
              buildChoiceAutomaton alphabet
                (compileTypeFuel (typeCompilationFuel left) left)
                (compileTypeFuel (typeCompilationFuel right) right)
                (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
          rw [hFuelEq, compileTypeFuel.eq_def]
          show buildChoiceAutomaton alphabet
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            (TypeLabel.fair bid true) (TypeLabel.fair bid false) = _
          rw [compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
        rw [PactType.TailOccurrences] at hTail
        rcases relationMembership_fairChoice_cases alphabet bid left right
            hRelated with hRoot | ⟨q, hState, hChild⟩ | ⟨q, hState, hChild⟩
        · exact absurd (congrArg Prod.fst hRoot) (by simp)
        · subst hState
          rw [hCompileEq]
          exact markerSourceFor_child
            (childPendingEdges_subset_choice_left alphabet _ _ _ _)
            (ih (typeCompilationFuel left) (by rw [hFuelEq]; omega) left
              hTail.1 hChild rfl)
        · subst hState
          rw [hCompileEq]
          exact markerSourceFor_child
            (childPendingEdges_subset_choice_right alphabet _ _ _ _)
            (ih (typeCompilationFuel right) (by rw [hFuelEq]; omega) right
              hTail.2 hChild rfl)
    | seq alphabet left right =>
        have hFuelEq : typeCompilationFuel (PactType.seq alphabet left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hCompileEq := compileTypeFuel_sequence_eq_build alphabet left right
        rw [PactType.TailOccurrences] at hTail
        rcases relationMembership_seq_cases alphabet left right hRelated with
          ⟨q, residualLeft, hEntry, -, -⟩ | ⟨q, hState, hChild⟩
        · exact absurd (congrArg Prod.fst hEntry) (by simp)
        · subst hState
          rw [hCompileEq]
          exact markerSourceFor_child
            (childPendingEdges_subset_sequence_right _ _)
            (ih (typeCompilationFuel right) (by rw [hFuelEq]; omega) right
              hTail.2 hChild rfl)
    | par alphabet left right interface =>
        have hFuelEq :
            typeCompilationFuel (PactType.par alphabet left right interface) =
              max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        rw [PactType.TailOccurrences] at hTail
        exfalso
        rcases relationMembership_par_cases alphabet left right interface
            hRelated with
          ⟨q1, q2, rL, rR, hEntry, -, -⟩ | ⟨q1, rL, hEntry, hChild, -⟩ |
          ⟨q2, rR, hEntry, hChild, -⟩ | hDone
        · exact absurd (congrArg Prod.fst hEntry) (by simp)
        · have hResidual : (PactType.var varAlphabet name) = rL :=
            congrArg Prod.fst hEntry
          have hAbsentChild : PactType.TailOccurrences name False
              (left.reannotate alphabet) :=
            PactType.reannotate_tailOccurrences name left alphabet False hTail.1
          refine absurd ?_ (atomic (left.reannotate alphabet) q1 hAbsentChild)
          exact MarkerSourceFor.markerSource
            (ih (typeCompilationFuel (left.reannotate alphabet))
              (by rw [hFuelEq, typeCompilationFuel_reannotate]; omega)
              (left.reannotate alphabet)
              (PactType.tailOccurrences_mono name False.elim _ hAbsentChild)
              (by rw [hResidual]; exact hChild) rfl)
        · have hResidual : (PactType.var varAlphabet name) = rR :=
            congrArg Prod.fst hEntry
          have hAbsentChild : PactType.TailOccurrences name False
              (right.reannotate alphabet) :=
            PactType.reannotate_tailOccurrences name right alphabet False hTail.2
          refine absurd ?_ (atomic (right.reannotate alphabet) q2 hAbsentChild)
          exact MarkerSourceFor.markerSource
            (ih (typeCompilationFuel (right.reannotate alphabet))
              (by rw [hFuelEq, typeCompilationFuel_reannotate]; omega)
              (right.reannotate alphabet)
              (PactType.tailOccurrences_mono name False.elim _ hAbsentChild)
              (by rw [hResidual]; exact hChild) rfl)
        · exact absurd (congrArg Prod.fst hDone) (by simp)
    | xoffer alphabet elseType branches =>
        have hFuelEq :
            typeCompilationFuel (PactType.xoffer alphabet elseType branches) =
              max (typeCompilationFuel elseType)
                (typeBranchCompilationFuel branches) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hCompileEq := compileTypeFuel_xoffer_eq alphabet elseType branches
        rw [PactType.TailOccurrences] at hTail
        obtain ⟨hElse, hBranches⟩ := hTail
        have hEach : ∀ branch ∈ branches,
            PactType.TailOccurrences name True branch.2 :=
          tailBranchOccurrences_forall name True branches hBranches
        rcases relationMembership_xoffer_cases alphabet elseType branches
            hRelated with hRoot | ⟨q, hState, hChild⟩ |
            ⟨i, action, branchType, q, hGet, hState, hChild⟩
        · exact absurd (congrArg Prod.fst hRoot) (by simp)
        · subst hState
          rw [hCompileEq]
          exact markerSourceFor_child
            (childPendingEdges_subset_xoffer_else alphabet branches _ _)
            (ih (typeCompilationFuel elseType) (by rw [hFuelEq]; omega)
              elseType hElse hChild rfl)
        · have hBranchMem : (action, branchType) ∈ branches :=
            List.mem_of_getElem? hGet
          have hLeBranch : typeCompilationFuel branchType ≤
              typeBranchCompilationFuel branches :=
            typeCompilationFuel_le_typeBranchCompilationFuel branches
              (action, branchType) hBranchMem
          have hEntry :
              (List.map (fun branch => (branch.1,
                compileTypeFuel (typeCompilationFuel branch.2) branch.2))
                branches)[i]? =
                some (action,
                  compileTypeFuel (typeCompilationFuel branchType) branchType) :=
            (branches_map_getElem?_eq_some_iff branches i action _).mpr
              ⟨branchType, hGet, rfl⟩
          subst hState
          rw [hCompileEq]
          refine markerSourceFor_child (index := i + 1) ?_
            (ih (typeCompilationFuel branchType) (by rw [hFuelEq]; omega)
              branchType (hEach _ hBranchMem) hChild rfl)
          intro edge hEdge
          refine indexedFragmentEdges_subset_xoffer alphabet branches _ _ edge ?_
          exact childPendingEdges_subset_indexedFragmentEdges _ i
            (action, compileTypeFuel (typeCompilationFuel branchType) branchType)
            hEntry edge hEdge
    | offer alphabet elseType branches =>
        have hFuelEq :
            typeCompilationFuel (PactType.offer alphabet elseType branches) =
              max (typeCompilationFuel elseType)
                (conjunctiveCompilationFuel branches) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hCompileEq := compileTypeFuel_offer_eq alphabet elseType branches
        rw [PactType.TailOccurrences] at hTail
        obtain ⟨hElse, hBranches⟩ := hTail
        have hEach : ∀ branch ∈ branches,
            PactType.TailOccurrences name False branch.2 :=
          tailBranchOccurrences_forall name False branches hBranches
        rcases relationMembership_offer_cases alphabet elseType branches
            hRelated with hRoot | ⟨q, hState, hChild⟩ |
            ⟨i, selected, q, hGet, hState, hChild⟩
        · exact absurd (congrArg Prod.fst hRoot) (by simp)
        · subst hState
          rw [hCompileEq]
          exact markerSourceFor_child
            (childPendingEdges_subset_conjunctive_else alphabet branches _ _)
            (ih (typeCompilationFuel elseType) (by rw [hFuelEq]; omega)
              elseType hElse hChild rfl)
        · exfalso
          have hAbsentChild : PactType.TailOccurrences name False
              (parallelTypeBranchesFiring alphabet selected branches) :=
            parallelTypeBranchesFiring_tailOccurrences name alphabet selected
              branches False hEach
          refine absurd ?_ (atomic _ q hAbsentChild)
          exact MarkerSourceFor.markerSource
            (ih (typeCompilationFuel
                (parallelTypeBranchesFiring alphabet selected branches))
              (typeCompilationFuel_firing_lt_offer alphabet elseType selected branches)
              _ (PactType.tailOccurrences_mono name False.elim _ hAbsentChild)
              hChild rfl)
    | recur alphabet binder body =>
        have hFuelEq : typeCompilationFuel (PactType.recur alphabet binder body) =
            typeCompilationFuel body + 1 := by
          simp only [typeCompilationFuel]; omega
        have hCompileEq :
            compileTypeFuel (typeCompilationFuel
                (PactType.recur alphabet binder body))
                (PactType.recur alphabet binder body) =
              buildRecursionAutomaton alphabet binder
                (compileTypeFuel (typeCompilationFuel body) body) := by
          rw [hFuelEq, compileTypeFuel.eq_def]
        rw [PactType.TailOccurrences] at hTail
        rcases relationMembership_recur_cases alphabet binder body hRelated with
          hRoot | ⟨q, rho, hEntry, hBody⟩
        · exact absurd (congrArg Prod.fst hRoot) (by simp)
        · have hResidual : (PactType.var varAlphabet name) =
              rho.replaceVar binder (.recur alphabet binder body) :=
            congrArg Prod.fst hEntry
          have hStateEq : state = TypeAutomatonState.child 0 q :=
            congrArg Prod.snd hEntry
          obtain ⟨hRho, hBinderNe⟩ :
              rho = PactType.var varAlphabet name ∧ binder ≠ name := by
            cases rho with
            | var b m =>
                by_cases hb : binder = m
                · rw [PactType.replaceVar, if_pos hb] at hResidual
                  simp at hResidual
                · rw [PactType.replaceVar, if_neg hb] at hResidual
                  injection hResidual with hA hM
                  subst hA
                  subst hM
                  exact ⟨rfl, hb⟩
            | recur b m t =>
                simp only [PactType.replaceVar] at hResidual
                split_ifs at hResidual
            | _ => simp [PactType.replaceVar] at hResidual
          subst hStateEq
          rw [hCompileEq]
          refine markerSourceFor_buildRecursionAutomaton_child alphabet binder
            name _ (fun hEq => hBinderNe hEq.symm) ?_
          exact ih (typeCompilationFuel body) (by rw [hFuelEq]; omega) body
            (by simpa [hBinderNe] using hTail) (by rw [← hRho]; exact hBody) rfl

/-- Offer derivations preserve the same tail-occurrence classification as
their transition component. -/
theorem TypeOffers.preserves_tailOccurrences :
    ∀ (tracked : String) (tail : Prop)
      {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
      {current future : Finset BareMessage},
      TypeOffers env source label target current future →
      source.TailRecursive →
      source.TailOccurrences tracked tail →
        target.TailOccurrences tracked tail := by
  classical
  intro tracked tail env source
  induction hSize : sizeOf source using Nat.strong_induction_on
      generalizing source env tracked tail with
  | h n ih =>
      intro target label current future hOffers hTailRec hTail
      cases hOffers with
      | action | action_wait | cycle | cycle_wait | skip | progress =>
          simp [PactType.TailOccurrences]
      | choice_left env alphabet left right hConds =>
          simp only [PactType.TailOccurrences] at hTail
          exact hTail.1
      | choice_right env alphabet left right hConds =>
          simp only [PactType.TailOccurrences] at hTail
          exact hTail.2
      | fair_left env alphabet bid left right hConds =>
          simp only [PactType.TailOccurrences] at hTail
          exact hTail.1
      | fair_right env alphabet bid left right hConds =>
          simp only [PactType.TailOccurrences] at hTail
          exact hTail.2
      | recur env alphabet binder body hConds =>
          simp only [PactType.TailRecursive] at hTailRec
          by_cases hBinder : binder = tracked
          · subst hBinder
            exact PactType.tailOccurrences_replaceVar binder binder
              (replacement := PactType.recur alphabet binder body) body tail
              (by simp [PactType.TailOccurrences]) hTailRec.1 (Or.inl rfl)
          · have hBodyTail : body.TailOccurrences tracked tail := by
              simpa only [PactType.TailOccurrences, if_neg hBinder] using hTail
            have hReplacementTail :
                (PactType.recur alphabet binder body).TailOccurrences tracked
                  tail := by
              simpa only [PactType.TailOccurrences, if_neg hBinder] using hBodyTail
            exact PactType.tailOccurrences_replaceVar tracked binder
              (replacement := PactType.recur alphabet binder body) body tail
              hReplacementTail hTailRec.1 (Or.inr hBodyTail)
      | seq env alphabet left left' right label current childFuture hLeftOffers
          hNotSkip hNotTock =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.TailOccurrences] at hTail ⊢
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize tracked False
              (env := env) (source := left) rfl hLeftOffers
              hTailRec.1 hTail.1,
            hTail.2⟩
      | seq_tock env alphabet left left' right current childFuture hLeftOffers
          hNotSkip =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.TailOccurrences] at hTail ⊢
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize tracked False
              (env := env) (source := left) rfl hLeftOffers
              hTailRec.1 hTail.1,
            hTail.2⟩
      | seq_fuse env alphabet skipAlphabet left right label current childFuture
          hLeftOffers hNotTock =>
          simp only [PactType.TailOccurrences] at hTail
          exact hTail.2
      | seq_fuse_tock env alphabet skipAlphabet left right current childFuture
          hLeftOffers =>
          simp only [PactType.TailOccurrences] at hTail
          exact hTail.2
      | xoffer_branch env alphabet elseType branches action processType hConds =>
          simp only [PactType.TailOccurrences] at hTail
          exact PactType.tailOccurrences_of_mem_branches tracked tail hTail.2
            hConds.2.1
      | xoffer_else env alphabet elseType branches hConds =>
          simp only [PactType.TailOccurrences] at hTail
          exact hTail.1
      | xoffer_wait env alphabet elseType branches hConds =>
          exact hTail
      | offer_some env alphabet elseType branches enabled hConds =>
          simp only [PactType.TailOccurrences] at hTail
          exact parallelTypeBranchesFiring_tailOccurrences tracked alphabet
            enabled branches tail
            (fun branch hBranch =>
              PactType.tailOccurrences_of_mem_branches tracked False hTail.2
                hBranch)
      | offer_else env alphabet elseType branches hConds =>
          simp only [PactType.TailOccurrences] at hTail
          exact hTail.1
      | offer_wait env alphabet elseType branches hConds =>
          exact hTail
      | par outer leftEnv rightEnv interface alphabet left left' right right'
          leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
          hLeftNotSkip hRightNotSkip hLeftOffers hRightOffers hNotBoth hLocalLeft
          hLocalRight hSync =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.TailOccurrences] at hTail ⊢
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize tracked False
              (env := leftEnv) (source := left) rfl hLeftOffers
              hTailRec.1 hTail.1,
            ih (sizeOf right) hRightSize tracked False
              (env := rightEnv) (source := right) rfl hRightOffers
              hTailRec.2 hTail.2⟩
      | par_fuse | par_fuse_tock =>
          simp [PactType.TailOccurrences]
      | left_complete outer leftEnv rightEnv interface alphabet left right right'
          rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftSkip
          hRightNotSkip hLeftOffers hRightOffers hRightTargetNotSkip hLocalLeft
          hLocalRight hWF hSync =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.TailOccurrences] at hTail
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          exact PactType.tailOccurrences_mono tracked False.elim _
            (PactType.reannotate_tailOccurrences tracked right' alphabet False
              (ih (sizeOf right) hRightSize tracked False
                (env := rightEnv) (source := right) rfl hRightOffers
                hTailRec.2 hTail.2))
      | right_complete outer leftEnv rightEnv interface alphabet left left' right
          leftLabel leftCurrent leftFuture rightCurrent rightFuture hRightSkip
          hLeftNotSkip hRightOffers hLeftOffers hLeftTargetNotSkip hLocalLeft
          hLocalRight hWF hSync =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.TailOccurrences] at hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          exact PactType.tailOccurrences_mono tracked False.elim _
            (PactType.reannotate_tailOccurrences tracked left' alphabet False
              (ih (sizeOf left) hLeftSize tracked False
                (env := leftEnv) (source := left) rfl hLeftOffers
                hTailRec.1 hTail.1))

/-- An absent variable leaves both the source and its step target unchanged. -/
theorem TypeOffers.replaceVar_of_tailOccurrences_false (name : String)
    (replacement : PactType) {env : TypeEnvironment} {source target : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future)
    (hTailRec : source.TailRecursive)
    (hTail : source.TailOccurrences name False) :
    TypeOffers env (source.replaceVar name replacement) label
      (target.replaceVar name replacement) current future := by
  rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement source hTail,
    PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement target
      (hOffers.preserves_tailOccurrences name False hTailRec hTail)]
  exact hOffers

/-- Offer summaries are stable under the same recursion substitution as
transitions. The current offer is unchanged; future fields are recomputed
at their specified source, target, or component. -/
theorem TypeOffers.replaceVar_tail (name : String)
    (replacement : PactType) {bound : List String}
    (hReplacementBound :
      PactType.AllVariablesBound (name :: bound) replacement) :
    ∀ {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
      {current future : Finset BareMessage},
      TypeOffers env source label target current future →
      source.TailRecursive →
      source.TailOccurrences name True →
      PactType.AllVariablesBound (name :: bound) source →
      PactType.BinderFreshFor (name :: bound) source →
        ∃ future', TypeOffers env (source.replaceVar name replacement) label
          (target.replaceVar name replacement) current future' := by
  classical
  intro env source
  induction hSize : sizeOf source using Nat.strong_induction_on
      generalizing source env with
  | h n ih =>
      intro target label current future hOffers hTailRec hTail hBound hFresh
      cases hOffers with
      | action env alphabet msg dir hConds =>
          refine ⟨typeFutureOffers (.skip alphabet), ?_⟩
          simpa [PactType.replaceVar] using
            TypeOffers.action env alphabet msg dir hConds
      | action_wait env alphabet msg dir hConds =>
          refine ⟨typeFutureOffers (.message alphabet msg dir) \ ({(msg, dir)} ∩ alphabet.actions), ?_⟩
          simpa [PactType.replaceVar] using
            TypeOffers.action_wait env alphabet msg dir hConds
      | choice_left env alphabet left right hConds =>
          refine ⟨typeFutureOffers (.choice alphabet
            (target.replaceVar name replacement) (right.replaceVar name replacement)), ?_⟩
          simpa [PactType.replaceVar] using
            TypeOffers.choice_left env alphabet _ _ hConds
      | choice_right env alphabet left right hConds =>
          refine ⟨typeFutureOffers (.choice alphabet
            (left.replaceVar name replacement) (target.replaceVar name replacement)), ?_⟩
          simpa [PactType.replaceVar] using
            TypeOffers.choice_right env alphabet _ _ hConds
      | fair_left env alphabet bid left right hConds =>
          refine ⟨typeFutureOffers (.fairChoice alphabet bid
            (target.replaceVar name replacement) (right.replaceVar name replacement)), ?_⟩
          simpa [PactType.replaceVar] using
            TypeOffers.fair_left env alphabet bid _ _ hConds
      | fair_right env alphabet bid left right hConds =>
          refine ⟨typeFutureOffers (.fairChoice alphabet bid
            (left.replaceVar name replacement) (target.replaceVar name replacement)), ?_⟩
          simpa [PactType.replaceVar] using
            TypeOffers.fair_right env alphabet bid _ _ hConds
      | cycle env alphabet hConds =>
          refine ⟨∅, ?_⟩
          simpa [PactType.replaceVar] using TypeOffers.cycle env alphabet hConds
      | cycle_wait env alphabet hConds =>
          refine ⟨typeFutureOffers (.tock alphabet), ?_⟩
          simpa [PactType.replaceVar] using
            TypeOffers.cycle_wait env alphabet hConds
      | skip env alphabet hConds =>
          refine ⟨typeFutureOffers (.skip alphabet), ?_⟩
          simpa [PactType.replaceVar] using TypeOffers.skip env alphabet hConds
      | progress env alphabet pid hConds =>
          refine ⟨typeFutureOffers (.skip alphabet), ?_⟩
          simpa [PactType.replaceVar] using
            TypeOffers.progress env alphabet pid hConds
      | recur env alphabet binder body hConds =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.AllVariablesBound] at hBound
          simp only [PactType.BinderFreshFor] at hFresh
          by_cases hBinder : name = binder
          · exfalso
            exact hFresh.1 (by simp [hBinder])
          · have hBodyFresh : body.BinderFreshFor (name :: name :: bound) :=
              PactType.binderFreshFor_cons_dup name bound body hFresh.2
            have hComm := PactType.replaceVar_comm_of_bound name binder
              replacement (PactType.recur alphabet binder body) body
              (name :: bound) hBinder hFresh.1 hReplacementBound
              (by simpa [PactType.AllVariablesBound] using hBound)
              hBodyFresh
            have hNested :
                (PactType.recur alphabet binder body).replaceVar name
                    replacement =
                  PactType.recur alphabet binder
                    (PactType.replaceVar body name replacement) := by
              simp [PactType.replaceVar, hBinder]
            refine ⟨typeFutureOffers
                ((PactType.replaceVar body name replacement).replaceVar binder
                  (PactType.recur alphabet binder
                    (PactType.replaceVar body name replacement))), ?_⟩
            rw [← hComm, hNested]
            simpa [PactType.replaceVar, hBinder] using
              TypeOffers.recur env alphabet binder
                (PactType.replaceVar body name replacement) hConds
      | seq env alphabet left left' right label current childFuture hLeftOffers
          hNotSkip hNotTock =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.TailOccurrences] at hTail
          have hLeftInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement left hTail.1
          have hLeft'Tail := TypeOffers.preserves_tailOccurrences name False
            hLeftOffers hTailRec.1 hTail.1
          have hLeft'Inert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement left' hLeft'Tail
          refine ⟨(childFuture ∪ sequenceRightMenu left
            (right.replaceVar name replacement)) \ current, ?_⟩
          simpa [PactType.replaceVar, hLeftInert, hLeft'Inert] using
            TypeOffers.seq env alphabet left left'
              (PactType.replaceVar right name replacement) label current
              childFuture hLeftOffers hNotSkip hNotTock
      | seq_tock env alphabet left left' right current childFuture hLeftOffers
          hNotSkip =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.TailOccurrences] at hTail
          have hLeftInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement left hTail.1
          have hLeft'Tail := TypeOffers.preserves_tailOccurrences name False
            hLeftOffers hTailRec.1 hTail.1
          have hLeft'Inert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement left' hLeft'Tail
          refine ⟨∅, ?_⟩
          simpa [PactType.replaceVar, hLeftInert, hLeft'Inert] using
            TypeOffers.seq_tock env alphabet left left'
              (PactType.replaceVar right name replacement) current childFuture
              hLeftOffers hNotSkip
      | seq_fuse env alphabet skipAlphabet left right label current childFuture
          hLeftOffers hNotTock =>
          simp only [PactType.TailOccurrences] at hTail
          have hLeftInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement left hTail.1
          refine ⟨(childFuture ∪ sequenceRightMenu left
            (target.replaceVar name replacement)) \ current, ?_⟩
          simpa [PactType.replaceVar, hLeftInert] using
            TypeOffers.seq_fuse env alphabet skipAlphabet left
              (PactType.replaceVar target name replacement) label current
              childFuture hLeftOffers hNotTock
      | seq_fuse_tock env alphabet skipAlphabet left right current childFuture
          hLeftOffers =>
          simp only [PactType.TailOccurrences] at hTail
          have hLeftInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement left hTail.1
          refine ⟨∅, ?_⟩
          simpa [PactType.replaceVar, hLeftInert] using
            TypeOffers.seq_fuse_tock env alphabet skipAlphabet left
              (PactType.replaceVar target name replacement) current childFuture
              hLeftOffers
      | xoffer_branch env alphabet elseType branches action processType hConds =>
          have hConds' :
              env.WellFormed alphabet ∧
                (action, PactType.replaceVar target name replacement) ∈
                  PactType.replaceBranches branches name replacement ∧
                TypeBranchEnabled env
                  (action, PactType.replaceVar target name replacement) ∧
                TypeResolved env
                  (PactType.replaceBranches branches name replacement) := by
            exact ⟨hConds.1,
              PactType.mem_replaceBranches name replacement hConds.2.1,
              by simpa [TypeBranchEnabled] using hConds.2.2.1,
              (TypeResolved_replaceBranches env branches name replacement).mpr
                hConds.2.2.2⟩
          refine ⟨typeFutureOffers (.xoffer alphabet
            (elseType.replaceVar name replacement)
            (PactType.replaceBranches branches name replacement)) \
              typeBranchActions (PactType.replaceBranches branches name replacement), ?_⟩
          simpa [PactType.replaceVar] using
            TypeOffers.xoffer_branch env alphabet _
              (PactType.replaceBranches branches name replacement) action
              (PactType.replaceVar target name replacement) hConds'
      | xoffer_else env alphabet elseType branches hConds =>
          have hConds' :
              env.WellFormed alphabet ∧ env.clock = false ∧
                TypeNoImmediateBranch env
                  (PactType.replaceBranches branches name replacement) ∧
                TypeResolved env
                  (PactType.replaceBranches branches name replacement) := by
            exact ⟨hConds.1, hConds.2.1,
              (TypeNoImmediateBranch_replaceBranches env branches name
                replacement).mpr hConds.2.2.1,
              (TypeResolved_replaceBranches env branches name replacement).mpr
                hConds.2.2.2⟩
          refine ⟨typeFutureOffers (.xoffer alphabet
            (target.replaceVar name replacement)
            (PactType.replaceBranches branches name replacement)) \
              typeBranchActions (PactType.replaceBranches branches name replacement), ?_⟩
          simpa only [PactType.replaceVar, PactType.typeBranchActions_replaceBranches] using
            TypeOffers.xoffer_else env alphabet
              (PactType.replaceVar target name replacement)
              (PactType.replaceBranches branches name replacement) hConds'
      | xoffer_wait env alphabet elseType branches hConds =>
          have hConds' :
              env.WellFormed alphabet ∧
                ¬ TypeResolved env
                  (PactType.replaceBranches branches name replacement) ∧
                env.clock = false := by
            exact ⟨hConds.1,
              fun hResolved => hConds.2.1
                ((TypeResolved_replaceBranches env branches name replacement).mp
                  hResolved),
              hConds.2.2⟩
          refine ⟨typeFutureOffers
              (.xoffer alphabet (PactType.replaceVar elseType name replacement)
                (PactType.replaceBranches branches name replacement)) \
                typeWaitingOffers env
                  (PactType.replaceBranches branches name replacement), ?_⟩
          simpa [PactType.replaceVar, typeWaitingOffers_replaceBranches] using
            TypeOffers.xoffer_wait env alphabet
              (PactType.replaceVar elseType name replacement)
              (PactType.replaceBranches branches name replacement) hConds'
      | offer_some env alphabet elseType branches enabled hConds =>
          simp only [PactType.TailOccurrences] at hTail
          have hBranchesInert :=
            PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false
              name replacement branches hTail.2
          have hBranchFalse : ∀ branch ∈ branches,
              branch.2.TailOccurrences name False := fun branch hBranch =>
            PactType.tailOccurrences_of_mem_branches name False hTail.2 hBranch
          have hTargetTail := parallelTypeBranchesFiring_tailOccurrences
            name alphabet enabled branches False hBranchFalse
          have hTargetInert :=
            PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement (parallelTypeBranchesFiring alphabet enabled branches)
              hTargetTail
          refine ⟨typeFutureOffers
              (parallelTypeBranchesFiring alphabet enabled branches) \
                (typeBranchActions branches ∩ alphabet.actions), ?_⟩
          simpa [PactType.replaceVar, hBranchesInert, hTargetInert] using
            TypeOffers.offer_some env alphabet _ branches enabled hConds
      | offer_else env alphabet elseType branches hConds =>
          simp only [PactType.TailOccurrences] at hTail
          have hBranchesInert :=
            PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false
              name replacement branches hTail.2
          refine ⟨typeFutureOffers (PactType.replaceVar target name replacement) \
              (typeBranchActions branches ∩ alphabet.actions), ?_⟩
          simpa [PactType.replaceVar, hBranchesInert] using
            TypeOffers.offer_else env alphabet
              (PactType.replaceVar target name replacement) branches hConds
      | offer_wait env alphabet elseType branches hConds =>
          simp only [PactType.TailOccurrences] at hTail
          have hBranchesInert :=
            PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false
              name replacement branches hTail.2
          refine ⟨typeFutureOffers
              (.offer alphabet (PactType.replaceVar elseType name replacement)
                branches) \
              (typeBranchActions branches ∩ alphabet.actions), ?_⟩
          simpa [PactType.replaceVar, hBranchesInert] using
            TypeOffers.offer_wait env alphabet
              (PactType.replaceVar elseType name replacement) branches hConds
      | par outer leftEnv rightEnv interface alphabet left left' right right'
          leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
          hLeftNotSkip hRightNotSkip hLeftOffers hRightOffers hNotBoth
          hLocalLeft hLocalRight hSync =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.TailOccurrences] at hTail
          have hLeftInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement left hTail.1
          have hRightInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement right hTail.2
          have hLeft'Tail := TypeOffers.preserves_tailOccurrences name False
            hLeftOffers hTailRec.1 hTail.1
          have hRight'Tail := TypeOffers.preserves_tailOccurrences name False
            hRightOffers hTailRec.2 hTail.2
          have hLeft'Inert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement left' hLeft'Tail
          have hRight'Inert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement right' hRight'Tail
          refine ⟨if TypeLabel.combine interface leftLabel rightLabel = TypeLabel.tock
            then ∅ else hideTypeOffers interface (leftFuture ∪ rightFuture), ?_⟩
          simpa [PactType.replaceVar, hLeftInert, hRightInert, hLeft'Inert,
            hRight'Inert] using
            TypeOffers.par env leftEnv rightEnv interface alphabet left left'
              right right' leftLabel rightLabel leftCurrent leftFuture
              rightCurrent rightFuture hLeftNotSkip hRightNotSkip hLeftOffers
              hRightOffers hNotBoth hLocalLeft hLocalRight hSync
      | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel
          rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftOffers
          hRightOffers hLocalLeft hLocalRight hSync hNotTock =>
          simp only [PactType.TailOccurrences] at hTail
          have hLeftInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement left hTail.1
          have hRightInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement right hTail.2
          refine ⟨hideTypeOffers interface (leftFuture ∪ rightFuture), ?_⟩
          simpa [PactType.replaceVar, hLeftInert, hRightInert] using
            TypeOffers.par_fuse env leftEnv rightEnv interface alphabet left
              right leftLabel rightLabel leftCurrent leftFuture rightCurrent
              rightFuture hLeftOffers hRightOffers hLocalLeft hLocalRight hSync
              hNotTock
      | par_fuse_tock outer leftEnv rightEnv interface alphabet left right
          leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
          hLeftOffers hRightOffers hLocalLeft hLocalRight hSync hTock =>
          simp only [PactType.TailOccurrences] at hTail
          have hLeftInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement left hTail.1
          have hRightInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement right hTail.2
          refine ⟨∅, ?_⟩
          simpa [PactType.replaceVar, hLeftInert, hRightInert] using
            TypeOffers.par_fuse_tock env leftEnv rightEnv interface alphabet
              left right leftLabel rightLabel leftCurrent leftFuture
              rightCurrent rightFuture hLeftOffers hRightOffers hLocalLeft
              hLocalRight hSync hTock
      | left_complete outer leftEnv rightEnv interface alphabet left right right'
          rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftSkip
          hRightNotSkip hLeftOffers hRightOffers hRightTargetNotSkip hLocalLeft
          hLocalRight hWF hSync =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.TailOccurrences] at hTail
          have hLeftInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement left hTail.1
          have hRightInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement right hTail.2
          have hRight'Tail := TypeOffers.preserves_tailOccurrences name False
            hRightOffers hTailRec.2 hTail.2
          have hTargetTail := PactType.reannotate_tailOccurrences name right'
            alphabet False hRight'Tail
          have hTargetInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement (right'.reannotate alphabet) hTargetTail
          refine ⟨hideTypeOffers interface rightFuture, ?_⟩
          simpa [PactType.replaceVar, hLeftInert, hRightInert, hTargetInert]
            using TypeOffers.left_complete env leftEnv rightEnv interface alphabet
              left right right' label leftCurrent leftFuture rightCurrent
              rightFuture hLeftSkip hRightNotSkip hLeftOffers hRightOffers
              hRightTargetNotSkip hLocalLeft hLocalRight hWF hSync
      | right_complete outer leftEnv rightEnv interface alphabet left left' right
          leftLabel leftCurrent leftFuture rightCurrent rightFuture hRightSkip
          hLeftNotSkip hRightOffers hLeftOffers hLeftTargetNotSkip hLocalLeft
          hLocalRight hWF hSync =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.TailOccurrences] at hTail
          have hLeftInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement left hTail.1
          have hRightInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement right hTail.2
          have hLeft'Tail := TypeOffers.preserves_tailOccurrences name False
            hLeftOffers hTailRec.1 hTail.1
          have hTargetTail := PactType.reannotate_tailOccurrences name left'
            alphabet False hLeft'Tail
          have hTargetInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
            name replacement (left'.reannotate alphabet) hTargetTail
          refine ⟨hideTypeOffers interface leftFuture, ?_⟩
          simpa [PactType.replaceVar, hLeftInert, hRightInert, hTargetInert]
            using TypeOffers.right_complete env leftEnv rightEnv interface alphabet
              left left' right label leftCurrent leftFuture rightCurrent
              rightFuture hRightSkip hLeftNotSkip hRightOffers hLeftOffers
              hLeftTargetNotSkip hLocalLeft hLocalRight hWF hSync

/-- A branch of a substituted branch list comes from a branch of the original. -/
theorem PactType.mem_replaceBranches_inv
    {branches : List (BareMessage × PactType)}
    {action : BareMessage} {branchType : PactType}
    (name : String) (replacement : PactType)
    (hMem : (action, branchType) ∈
      PactType.replaceBranches branches name replacement) :
    ∃ original, (action, original) ∈ branches ∧
      branchType = original.replaceVar name replacement := by
  induction branches with
  | nil => simp [PactType.replaceBranches] at hMem
  | cons branch rest ih =>
      rcases branch with ⟨headAction, headType⟩
      simp only [PactType.replaceBranches, List.mem_cons, Prod.mk.injEq] at hMem
      rcases hMem with ⟨hAction, hType⟩ | hRest
      · exact ⟨headType, by simp [hAction], hType⟩
      · obtain ⟨original, hOriginal, hEq⟩ := ih hRest
        exact ⟨original, List.mem_cons_of_mem _ hOriginal, hEq⟩

/-- Paper helper 12, forward direction of the first equivalence: a step of a
substituted residual is a step of the residual, with the substituted target,
unless the residual is the recursive call itself. -/
theorem TypeOffers.replaceVar_tail_inv (name : String)
    (replacement : PactType) {bound : List String}
    (hReplacementBound :
      PactType.AllVariablesBound (name :: bound) replacement) :
    ∀ {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
      {current future : Finset BareMessage},
      TypeOffers env (source.replaceVar name replacement) label target current
        future →
      source.TailRecursive →
      source.TailOccurrences name True →
      PactType.AllVariablesBound (name :: bound) source →
      PactType.BinderFreshFor (name :: bound) source →
        (∃ sourceTarget sourceFuture,
            TypeOffers env source label sourceTarget current sourceFuture ∧
            target = sourceTarget.replaceVar name replacement) ∨
          ∃ varAlphabet, source = .var varAlphabet name := by
  classical
  intro env source target label current future hOffers hTailRec hTail hBound
    hFresh
  -- A source with no tail occurrence at all is untouched, and so is its target.
  have inert : source.TailOccurrences name False →
      (∃ sourceTarget sourceFuture,
          TypeOffers env source label sourceTarget current sourceFuture ∧
          target = sourceTarget.replaceVar name replacement) := by
    intro hFalse
    have hSourceInert :=
      PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement
        source hFalse
    rw [hSourceInert] at hOffers
    have hTargetTail := TypeOffers.preserves_tailOccurrences name False hOffers
      hTailRec hFalse
    exact ⟨target, future, hOffers,
      (PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement
        target hTargetTail).symm⟩
  cases source with
  | message alphabet msg dir =>
      exact Or.inl (inert (by rw [PactType.TailOccurrences]; trivial))
  | progress alphabet pid =>
      exact Or.inl (inert (by rw [PactType.TailOccurrences]; trivial))
  | tock alphabet =>
      exact Or.inl (inert (by rw [PactType.TailOccurrences]; trivial))
  | skip alphabet =>
      exact Or.inl (inert (by rw [PactType.TailOccurrences]; trivial))
  | par alphabet left right interface =>
      refine Or.inl (inert ?_)
      simp only [PactType.TailOccurrences] at hTail ⊢
      exact hTail
  | var alphabet other =>
      by_cases hEq : name = other
      · subst hEq
        exact Or.inr ⟨alphabet, rfl⟩
      · left
        have hSource : (PactType.var alphabet other).replaceVar name
            replacement = .var alphabet other := by
          simp [PactType.replaceVar, hEq]
        rw [hSource] at hOffers
        cases hOffers
  | choice alphabet left right =>
      left
      have hSource : (PactType.choice alphabet left right).replaceVar name
          replacement =
            .choice alphabet (left.replaceVar name replacement)
              (right.replaceVar name replacement) := by
        simp [PactType.replaceVar]
      rw [hSource] at hOffers
      cases hOffers with
      | choice_left _ _ _ _ hConds =>
          exact ⟨left, _,
            TypeOffers.choice_left env alphabet left right hConds, rfl⟩
      | choice_right _ _ _ _ hConds =>
          exact ⟨right, _,
            TypeOffers.choice_right env alphabet left right hConds, rfl⟩
  | fairChoice alphabet bid left right =>
      left
      have hSource : (PactType.fairChoice alphabet bid left right).replaceVar
          name replacement =
            .fairChoice alphabet bid (left.replaceVar name replacement)
              (right.replaceVar name replacement) := by
        simp [PactType.replaceVar]
      rw [hSource] at hOffers
      cases hOffers with
      | fair_left _ _ _ _ _ hConds =>
          exact ⟨left, _,
            TypeOffers.fair_left env alphabet bid left right hConds, rfl⟩
      | fair_right _ _ _ _ _ hConds =>
          exact ⟨right, _,
            TypeOffers.fair_right env alphabet bid left right hConds, rfl⟩
  | recur alphabet binder body =>
      left
      simp only [PactType.BinderFreshFor] at hFresh
      simp only [PactType.AllVariablesBound] at hBound
      have hBinderNe : name ≠ binder := by
        intro hEq
        exact hFresh.1 (by simp [hEq])
      have hNested : (PactType.recur alphabet binder body).replaceVar name
          replacement =
            .recur alphabet binder (body.replaceVar name replacement) := by
        simp [PactType.replaceVar, hBinderNe]
      rw [hNested] at hOffers
      cases hOffers with
      | recur _ _ _ _ hConds =>
          have hComm := PactType.replaceVar_comm_of_bound name binder
            replacement (PactType.recur alphabet binder body) body
            (name :: bound) hBinderNe hFresh.1 hReplacementBound
            (by simpa [PactType.AllVariablesBound] using hBound)
            (PactType.binderFreshFor_cons_dup name bound body hFresh.2)
          refine ⟨body.replaceVar binder (.recur alphabet binder body),
            typeFutureOffers
              (body.replaceVar binder (.recur alphabet binder body)),
            TypeOffers.recur env alphabet binder body hConds, ?_⟩
          rw [← hComm, hNested]
  | seq alphabet left right =>
      left
      simp only [PactType.TailRecursive] at hTailRec
      simp only [PactType.TailOccurrences] at hTail
      have hLeftInert := PactType.replaceVar_eq_self_of_tailOccurrences_false
        name replacement left hTail.1
      have hSource : (PactType.seq alphabet left right).replaceVar name
          replacement = .seq alphabet left (right.replaceVar name replacement) := by
        simp [PactType.replaceVar, hLeftInert]
      rw [hSource] at hOffers
      cases hOffers with
      | seq _ _ _ left' _ _ _ childFuture hLeftOffers hNotSkip hNotTock =>
          have hLeft'Tail := TypeOffers.preserves_tailOccurrences name False
            hLeftOffers hTailRec.1 hTail.1
          have hLeft'Inert :=
            PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement left' hLeft'Tail
          refine ⟨.seq alphabet left' right,
            _,
            TypeOffers.seq env alphabet left left' right label current
              childFuture hLeftOffers hNotSkip hNotTock, ?_⟩
          simp [PactType.replaceVar, hLeft'Inert]
      | seq_tock _ _ _ left' _ stepCurrent childFuture hLeftOffers hNotSkip =>
          have hLeft'Tail := TypeOffers.preserves_tailOccurrences name False
            hLeftOffers hTailRec.1 hTail.1
          have hLeft'Inert :=
            PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement left' hLeft'Tail
          refine ⟨.seq alphabet left' right, ∅,
            TypeOffers.seq_tock env alphabet left left' right stepCurrent
              childFuture hLeftOffers hNotSkip, ?_⟩
          simp [PactType.replaceVar, hLeft'Inert]
      | seq_fuse _ _ skipAlphabet _ _ _ _ childFuture hLeftOffers hNotTock =>
          exact ⟨right, _,
            TypeOffers.seq_fuse env alphabet skipAlphabet left right label
              current childFuture hLeftOffers hNotTock, rfl⟩
      | seq_fuse_tock _ _ skipAlphabet _ _ stepCurrent childFuture
          hLeftOffers =>
          exact ⟨right, ∅,
            TypeOffers.seq_fuse_tock env alphabet skipAlphabet left right
              stepCurrent childFuture hLeftOffers, rfl⟩
  | xoffer alphabet elseType branches =>
      left
      have hSource : (PactType.xoffer alphabet elseType branches).replaceVar
          name replacement =
            .xoffer alphabet (elseType.replaceVar name replacement)
              (PactType.replaceBranches branches name replacement) := by
        simp [PactType.replaceVar]
      rw [hSource] at hOffers
      cases hOffers with
      | xoffer_branch _ _ _ _ action processType hConds =>
          obtain ⟨original, hOriginal, hEq⟩ :=
            PactType.mem_replaceBranches_inv name replacement hConds.2.1
          subst hEq
          refine ⟨original, _,
            TypeOffers.xoffer_branch env alphabet elseType branches action
              original
              ⟨hConds.1, hOriginal, by simpa [TypeBranchEnabled] using
                hConds.2.2.1,
                (TypeResolved_replaceBranches env branches name replacement).mp
                  hConds.2.2.2⟩, rfl⟩
      | xoffer_else _ _ _ _ hConds =>
          rw [PactType.typeBranchActions_replaceBranches]
          exact ⟨elseType, _,
            TypeOffers.xoffer_else env alphabet elseType branches
              ⟨hConds.1, hConds.2.1,
                (TypeNoImmediateBranch_replaceBranches env branches name
                  replacement).mp hConds.2.2.1,
                (TypeResolved_replaceBranches env branches name replacement).mp
                  hConds.2.2.2⟩, rfl⟩
      | xoffer_wait _ _ _ _ hConds =>
          rw [typeWaitingOffers_replaceBranches]
          refine ⟨.xoffer alphabet elseType branches,
            typeFutureOffers (.xoffer alphabet elseType branches) \
              typeWaitingOffers env branches,
            TypeOffers.xoffer_wait env alphabet elseType branches
              ⟨hConds.1,
                fun hResolved => hConds.2.1
                  ((TypeResolved_replaceBranches env branches name
                    replacement).mpr hResolved),
                hConds.2.2⟩, ?_⟩
          simp [PactType.replaceVar]
  | offer alphabet elseType branches =>
      left
      simp only [PactType.TailOccurrences] at hTail
      have hBranchesInert :=
        PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false name
          replacement branches hTail.2
      have hSource : (PactType.offer alphabet elseType branches).replaceVar
          name replacement =
            .offer alphabet (elseType.replaceVar name replacement) branches := by
        simp [PactType.replaceVar, hBranchesInert]
      rw [hSource] at hOffers
      cases hOffers with
      | offer_some _ _ _ _ enabled hConds =>
          have hBranchFalse : ∀ branch ∈ branches,
              branch.2.TailOccurrences name False := fun branch hBranch =>
            PactType.tailOccurrences_of_mem_branches name False hTail.2 hBranch
          have hTargetTail := parallelTypeBranchesFiring_tailOccurrences
            name alphabet enabled branches False hBranchFalse
          refine ⟨parallelTypeBranchesFiring alphabet enabled branches,
            typeFutureOffers
              (parallelTypeBranchesFiring alphabet enabled branches) \
                (typeBranchActions branches ∩ alphabet.actions),
            TypeOffers.offer_some env alphabet elseType branches enabled hConds, ?_⟩
          exact (PactType.replaceVar_eq_self_of_tailOccurrences_false name
            replacement _ hTargetTail).symm
      | offer_else _ _ _ _ hConds =>
          exact ⟨elseType, typeFutureOffers elseType \ (typeBranchActions branches ∩ alphabet.actions),
            TypeOffers.offer_else env alphabet elseType branches hConds,
            rfl⟩
      | offer_wait _ _ _ _ hConds =>
          refine ⟨.offer alphabet elseType branches,
            typeFutureOffers (.offer alphabet elseType branches) \
              (typeBranchActions branches ∩ alphabet.actions),
            TypeOffers.offer_wait env alphabet elseType branches hConds,
            ?_⟩
          simp [PactType.replaceVar, hBranchesInert]


/-- Semantic transport supplied by the paper's recursion-substitution helper,
specialized to the forward current-offer direction. -/
def RecursionSubstitutionStepForward
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType) : Prop :=
  ∀ {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage},
    relationMembership (buildRelationSet body (compileType body))
      residual state →
    DecoratedTypeTransition env
      (residual.replaceVar name (.recur alphabet name body)) label
      { current := current, future := future } residual' →
    (∃ bodyTarget bodyFuture,
        DecoratedTypeTransition env residual label
          { current := current, future := bodyFuture } bodyTarget ∧
        residual' = bodyTarget.replaceVar name (.recur alphabet name body)) ∨
      (∃ varAlphabet markerEdge,
        residual = .var varAlphabet name ∧
        markerEdge ∈ (compileTypeFuel (typeCompilationFuel body) body).edges ∧
        markerEdge.source = state ∧
        markerEdge.environment = env ∧
        markerEdge.label = .variable name ∧
        label = TypeLabel.silent ∧
        current = ∅ ∧
        residual' = body.replaceVar name (.recur alphabet name body) ∧
        env.WellFormed alphabet ∧ env.clock = false)

/-- Semantic transport supplied by the paper's recursion-substitution helper,
specialized to the backward current-offer direction. -/
def RecursionSubstitutionStepBackward
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType) : Prop :=
  ∀ {residual bodyTarget : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage},
    relationMembership (buildRelationSet body (compileType body))
      residual state →
    DecoratedTypeTransition env residual label
      { current := current, future := future } bodyTarget →
    ∃ future',
      DecoratedTypeTransition env
        (residual.replaceVar name (.recur alphabet name body)) label
        { current := current, future := future' }
        (bodyTarget.replaceVar name (.recur alphabet name body))

/-- Paper recursion-substitution transport, forward direction, specialized to
current-offer correspondence.  The ordinary branch transports a body step
through substitution.  The variable branch is the semantic unfold matched by
the compiler's installed backedge. -/
theorem recursionSubstitutionStepForward_of_typeWF
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.recur alphabet name body)) :
    RecursionSubstitutionStepForward alphabet name body := by
  classical
  intro residual residual' state env label current future hRelated hStep
  -- the recursion's own conjuncts, read off `TypeWF_Γ`
  have hBoundRecur : PactType.AllVariablesBound bound
      (.recur alphabet name body) := hWF.2.1
  have hHygRecur : PactType.BinderHygienic bound (.recur alphabet name body) :=
    hWF.2.2.1
  have hTailClosedRecur : (PactType.recur alphabet name body).TailClosed :=
    hWF.2.2.2.1
  have hTailRecRecur : PactType.TailRecursive (.recur alphabet name body) :=
    hWF.2.2.2.2.2.1
  -- descend to the body: the binder joins the context
  have hBoundBody : PactType.AllVariablesBound (name :: bound) body := by
    simpa only [PactType.AllVariablesBound] using hBoundRecur
  have hHygBody : PactType.BinderHygienic (name :: bound) body := by
    have h := hHygRecur
    simp only [PactType.BinderHygienic] at h
    exact h.2
  have hFreshBody : PactType.BinderFreshFor (name :: bound) body :=
    PactType.binderHygienic_binderFreshFor body (name :: bound) hHygBody
  have hTailRecPair : PactType.TailOccurrences name True body ∧
      body.TailRecursive := by
    have h := hTailRecRecur
    simp only [PactType.TailRecursive] at h
    exact h
  have hTailRecBody : body.TailRecursive := hTailRecPair.2
  have hTailBody : body.TailOccurrences name True := hTailRecPair.1
  have hTailClosedBody : body.TailClosed := by
    intro other
    have h := hTailClosedRecur other
    simp only [PactType.TailOccurrences] at h
    by_cases hEq : name = other
    · exact hEq ▸ hTailBody
    · rw [if_neg (fun hOther : name = other => hEq hOther)] at h
      exact h
  -- transport each side condition to the residual `q` stands for
  have hResidualBound : PactType.AllVariablesBound (name :: bound) residual :=
    relationMembership_allVariablesBound body residual state (name :: bound)
      hBoundBody hRelated
  have hResidualFresh : PactType.BinderFreshFor (name :: bound) residual :=
    relationMembership_binderFreshFor body residual state (name :: bound)
      hFreshBody hRelated
  have hResidualTailPair := relationMembership_tailRecursive body residual state
    hTailRecBody hTailClosedBody hRelated
  have hResidualTail : residual.TailOccurrences name True :=
    relationMembership_tailOccurrences body residual state name True
      hTailRecBody hTailBody hRelated
  have hReplacementBound : PactType.AllVariablesBound (name :: bound)
      (.recur alphabet name body) :=
    PactType.allVariablesBound_mono
      (fun _ hMem => List.mem_cons_of_mem _ hMem) _ hBoundRecur
  rcases TypeOffers.replaceVar_tail_inv name (.recur alphabet name body)
      hReplacementBound hStep.2 hResidualTailPair.1 hResidualTail
      hResidualBound hResidualFresh with
    ⟨bodyTarget, bodyFuture, hBodyOffers, hTargetEq⟩ | ⟨varAlphabet, hVar⟩
  · exact Or.inl ⟨bodyTarget, bodyFuture,
      ⟨hBodyOffers.toTypeTransition, hBodyOffers⟩, hTargetEq⟩
  · -- `Body(ρ) = X`: the substituted residual is the recursion itself, and the
    -- step it takes is the unfolding matched by the installed backedge
    right
    subst hVar
    have hBodyAlphabetWF : body.AlphabetWellFormed :=
      (typeWellFormedIn_recur hWF).1
    have hBodyAlphabet : body.alphabet = alphabet := by
      have hAlpha : PactType.AlphabetWellFormed (.recur alphabet name body) :=
        hWF.1
      simp only [PactType.AlphabetWellFormed] at hAlpha
      exact hAlpha.2.1
    have hVarAlphabet : varAlphabet = alphabet := by
      have h := relationMembership_alphabet_eq_of_wellFormed body
        (.var varAlphabet name) state hBodyAlphabetWF hRelated
      rw [hBodyAlphabet] at h
      simpa [PactType.alphabet] using h
    have hSourceEq : (PactType.var varAlphabet name).replaceVar name
        (.recur alphabet name body) = .recur alphabet name body := by
      simp [PactType.replaceVar]
    obtain ⟨-, hOffers⟩ := hStep
    rw [hSourceEq] at hOffers
    cases hOffers with
    | recur _ _ _ _ hConds =>
        have hEnvMem : env ∈ varAlphabet.localEnvironments := by
          rw [hVarAlphabet]
          exact PactTypeAlphabet.mem_localEnvironments_of_wellFormed hConds.1
        obtain ⟨markerEdge, hMarkerEdge, hMarkerSource, hMarkerEnv,
          hMarkerLabel⟩ :=
          markerSourceFor_of_var_residual body name env varAlphabet hTailBody
            hEnvMem hConds.2 hRelated
        exact ⟨varAlphabet, markerEdge, rfl, hMarkerEdge, hMarkerSource,
          hMarkerEnv, hMarkerLabel, rfl, rfl, rfl, hConds.1, hConds.2⟩

/-- Paper recursion-substitution transport, backward direction, specialized to
current-offer correspondence.  A body step at a copied recursion state remains
a step after substituting the recursive type for its open call. -/
theorem recursionSubstitutionStepBackward_of_typeWF
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.recur alphabet name body)) :
    RecursionSubstitutionStepBackward alphabet name body := by
  classical
  intro residual bodyTarget state env label current future hRelated hStep
  -- the recursion's own conjuncts, read off `TypeWF_Γ`
  have hBoundRecur : PactType.AllVariablesBound bound
      (.recur alphabet name body) := hWF.2.1
  have hHygRecur : PactType.BinderHygienic bound (.recur alphabet name body) :=
    hWF.2.2.1
  have hTailClosedRecur : (PactType.recur alphabet name body).TailClosed :=
    hWF.2.2.2.1
  have hTailRecRecur : PactType.TailRecursive (.recur alphabet name body) :=
    hWF.2.2.2.2.2.1
  -- descend to the body: the binder joins the context
  have hBoundBody : PactType.AllVariablesBound (name :: bound) body := by
    simpa only [PactType.AllVariablesBound] using hBoundRecur
  have hHygBody : PactType.BinderHygienic (name :: bound) body := by
    have h := hHygRecur
    simp only [PactType.BinderHygienic] at h
    exact h.2
  have hFreshBody : PactType.BinderFreshFor (name :: bound) body :=
    PactType.binderHygienic_binderFreshFor body (name :: bound) hHygBody
  have hTailRecPair : PactType.TailOccurrences name True body ∧
      body.TailRecursive := by
    have h := hTailRecRecur
    simp only [PactType.TailRecursive] at h
    exact h
  have hTailRecBody : body.TailRecursive := hTailRecPair.2
  have hTailBody : body.TailOccurrences name True := hTailRecPair.1
  have hTailClosedBody : body.TailClosed := by
    intro other
    have h := hTailClosedRecur other
    simp only [PactType.TailOccurrences] at h
    by_cases hEq : name = other
    · exact hEq ▸ hTailBody
    · rw [if_neg (fun hOther : name = other => hEq hOther)] at h
      exact h
  -- transport each side condition to the residual `q` stands for
  have hResidualBound : PactType.AllVariablesBound (name :: bound) residual :=
    relationMembership_allVariablesBound body residual state (name :: bound)
      hBoundBody hRelated
  have hResidualFresh : PactType.BinderFreshFor (name :: bound) residual :=
    relationMembership_binderFreshFor body residual state (name :: bound)
      hFreshBody hRelated
  have hResidualTailPair := relationMembership_tailRecursive body residual state
    hTailRecBody hTailClosedBody hRelated
  have hResidualTail : residual.TailOccurrences name True :=
    relationMembership_tailOccurrences body residual state name True
      hTailRecBody hTailBody hRelated
  -- the replacement is the recursion itself, bound in the extended context
  have hReplacementBound : PactType.AllVariablesBound (name :: bound)
      (.recur alphabet name body) :=
    PactType.allVariablesBound_mono
      (fun _ hMem => List.mem_cons_of_mem _ hMem) _ hBoundRecur
  obtain ⟨future', hOffers'⟩ := TypeOffers.replaceVar_tail name
    (.recur alphabet name body) hReplacementBound hStep.2 hResidualTailPair.1
    hResidualTail hResidualBound hResidualFresh
  exact ⟨future', hOffers'.toTypeTransition, hOffers'⟩

/-- A tagged recursion-child edge is either an ordinary body edge, or the
installed backedge of a residual call to the binder. -/
theorem compileType_recur_child_edge_cases
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    (hBodyTail : body.TailOccurrences name True)
    (hBodyAlphabet : body.alphabet = alphabet)
    (hBodyLocal : EdgeLocalAt (typeCompilationFuel body) body)
    (hBodyClock :
      (compileTypeFuel (typeCompilationFuel body) body).ClockEdgesAreTock)
    {bodyResidual : PactType} {q state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hBodyRelated : relationMembership (buildRelationSet body (compileType body))
      bodyResidual q)
    (hEdge : (compileType (.recur alphabet name body)).HasEdge (.child 0 q) env label
      { current := current, future := future } state') :
    (∃ edge ∈ (compileTypeFuel (typeCompilationFuel body) body).edges,
      edge.source = q ∧ edge.environment = env ∧ edge.label = .visible label ∧
      edge.current = current ∧ state' = .child 0 edge.target ∧
      future = resolveFutureSpec
        (fun r => computeFutureOf (.recur alphabet name body) (.child 0 r)) edge.future) ∨
    (∃ varAlphabet,
      bodyResidual = .var varAlphabet name ∧
      state' = .child 0 (compileTypeFuel (typeCompilationFuel body) body).initial ∧
      label = TypeLabel.silent ∧
      current = ∅ ∧
      env.WellFormed alphabet ∧ env.clock = false ∧
      future = computeFutureOf (.recur alphabet name body)
        (.child 0 (compileTypeFuel (typeCompilationFuel body) body).initial)) := by
  classical
  obtain ⟨parentEdge, hParentEdge, hSource, hEnv, hLabel, hCurrent, hFuture, hTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge (.recur alphabet name body)
      (.child 0 q) state' env label { current := current, future := future }).mp hEdge
  change resolveFutureSpec (computeFutureOf (.recur alphabet name body)) parentEdge.future =
    future at hFuture
  rw [compileTypeFuel_recur_eq] at hParentEdge
  simp only [buildRecursionAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hParentEdge
  rcases hParentEdge with ⟨environment, hEnvironment, hEq⟩ |
      ⟨bodyEdge, hBodyEdge, hEq⟩
  · subst hEq
    simp at hSource
  · subst hEq
    by_cases hMarker : bodyEdge.label = AutomatonConstructionLabel.variable name
    · rw [if_pos hMarker] at hSource hEnv hLabel hCurrent hFuture hTarget
      right
      have hBodySource : bodyEdge.source = q := by
        simpa [childState] using hSource
      have hMarkerSource :
          MarkerSource (compileTypeFuel (typeCompilationFuel body) body) name q := by
        exact ⟨bodyEdge, hBodyEdge, hBodySource, hMarker⟩
      obtain ⟨varAlphabet, hVar⟩ :=
        (markerSource_iff_var_residual body name hBodyTail hBodyRelated).mp
          hMarkerSource
      refine ⟨varAlphabet, hVar, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [childState] using hTarget.symm
      · simpa using hLabel.symm
      · simpa using hCurrent.symm
      · have hEdgeEnv :
            bodyEdge.environment ∈ body.alphabet.localEnvironments :=
          (hBodyLocal bodyEdge hBodyEdge).1
        rw [hEnv, hBodyAlphabet] at hEdgeEnv
        exact PactTypeAlphabet.environment_wellFormed
          hEdgeEnv
      · have hNotClock : bodyEdge.environment.clock ≠ true := by
          intro hClocked
          have hTock := (hBodyClock bodyEdge hBodyEdge hClocked).1
          rw [hMarker] at hTock
          simp [AutomatonConstructionLabel.semantic, TypeLabel.silent] at hTock
        have hClockFalse : bodyEdge.environment.clock = false := by
          cases hClock : bodyEdge.environment.clock <;> simp [hClock] at hNotClock ⊢
        rwa [hEnv] at hClockFalse
      · simpa [resolveFutureSpec, childState] using hFuture.symm
    · rw [if_neg hMarker] at hSource hEnv hLabel hCurrent hFuture hTarget
      left
      refine ⟨bodyEdge, hBodyEdge, ?_, hEnv, hLabel, hCurrent, ?_, ?_⟩
      · simpa [childState] using hSource
      · simpa [childState] using hTarget.symm
      · calc
          future = resolveFutureSpec (computeFutureOf (.recur alphabet name body))
              (childFutureSpec 0 bodyEdge.future) := hFuture.symm
          _ = resolveFutureSpec
              (fun r => computeFutureOf (.recur alphabet name body) (.child 0 r))
              bodyEdge.future :=
            resolve_childFutureSpec 0 bodyEdge.future _ _ (fun _ _ => rfl)

/-- Current-offer correspondence for a recursion, assembled from the body IH,
the marker invariant, and substitution transport. -/
theorem currentOfferCorrespondence_recur
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.recur alphabet name body))
    (hBody : CurrentOfferCorrespondence body)
    (hForward : RecursionSubstitutionStepForward alphabet name body)
    (hBackward : RecursionSubstitutionStepBackward alphabet name body) :
    CurrentOfferCorrespondence (.recur alphabet name body) := by
  classical
  have hBodyWF := typeWellFormedIn_recur hWF
  obtain ⟨hParentAlphabet, -, -, -, -, hParentTailRecursive, -, -, -, -, -, -,
    -, -, -⟩ := hWF
  obtain ⟨hBodyAlphabetWF, -, -, -, -, -, -, -, -, -, -, -, hBodyScoped,
    hBodyAlphabetScoped, -⟩ := hBodyWF
  have hBodyTail : body.TailOccurrences name True := by
    have hTail := hParentTailRecursive
    simp only [PactType.TailRecursive] at hTail
    exact hTail.1
  have hBodyAlphabet : body.alphabet = alphabet := by
    have hAlpha := hParentAlphabet
    simp only [PactType.AlphabetWellFormed] at hAlpha
    exact hAlpha.2.1
  have hBodyLocal : EdgeLocalAt (typeCompilationFuel body) body :=
    edgeLocalAt_holds (typeCompilationFuel body) body le_rfl
      hBodyAlphabetWF hBodyScoped hBodyAlphabetScoped
  have hBodyClock :
      (compileTypeFuel (typeCompilationFuel body) body).ClockEdgesAreTock :=
    compileTypeFuel_clockEdgesAreTock (typeCompilationFuel body) body le_rfl
  constructor
  · intro residual residual' state env label current future hRelated hStep
    rcases relationMembership_recur_cases alphabet name body hRelated with
      hRoot | ⟨q, bodyResidual, hEntry, hBodyRelated⟩
    · rw [Prod.ext_iff] at hRoot
      obtain ⟨hResidual, hState⟩ := hRoot
      subst hResidual
      subst hState
      obtain ⟨hTrans, hOffers⟩ := hStep
      cases hTrans with
      | recur env alphabet name body hEnv hClock =>
          cases hOffers with
          | recur _ _ _ _ hOffersEnv =>
              refine ⟨.child 0 (compileTypeFuel (typeCompilationFuel body) body).initial,
                computeFutureOf (.recur alphabet name body)
                  (.child 0 (compileTypeFuel (typeCompilationFuel body) body).initial),
                compileType_recur_root_hasEdge alphabet name body hEnv hClock,
                ?_⟩
              exact relationMembership_recur_child alphabet name body body
                (buildRelationSet_initial body (compileType body))
    · rw [Prod.ext_iff] at hEntry
      obtain ⟨hResidual, hState⟩ := hEntry
      subst hResidual
      subst hState
      rcases hForward hBodyRelated hStep with
        ⟨bodyTarget, bodyFuture, hBodyStep, hTargetEq⟩ |
        ⟨varAlphabet, markerEdge, hVar, hMarkerEdge, hMarkerSource,
          hMarkerEnv, hMarkerLabel, hLabel, hCurrent, hTargetEq, hEnv,
          hClock⟩
      · obtain ⟨q', bodyEdgeFuture, hBodyEdge, hBodyTarget⟩ :=
          hBody.1 hBodyRelated hBodyStep
        obtain ⟨parentFuture, hParentEdge⟩ :=
          compileType_recur_child_edge_lift_current alphabet name body hBodyEdge
        exact ⟨.child 0 q', parentFuture, hParentEdge,
          hTargetEq ▸ relationMembership_recur_child alphabet name body bodyTarget
            hBodyTarget⟩
      · subst hVar
        subst hLabel
        subst hCurrent
        subst hTargetEq
        refine ⟨.child 0 (compileTypeFuel (typeCompilationFuel body) body).initial,
          computeFutureOf (.recur alphabet name body)
            (.child 0 (compileTypeFuel (typeCompilationFuel body) body).initial),
          ?_,
          relationMembership_recur_child alphabet name body body
            (buildRelationSet_initial body (compileType body))⟩
        rw [compileType_hasEdge_iff_hasResolvedEdge]
        refine ⟨
          { source := .child 0 markerEdge.source,
            environment := markerEdge.environment,
            label := .visible TypeLabel.silent,
            current := ∅,
            future := .at (.child 0 (compileTypeFuel (typeCompilationFuel body) body).initial) ∅,
            target := .child 0 (compileTypeFuel (typeCompilationFuel body) body).initial },
          ?_, ?_, hMarkerEnv, rfl, rfl, ?_, rfl⟩
        · rw [compileTypeFuel_recur_eq]
          simp only [buildRecursionAutomaton, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image]
          exact Or.inr ⟨markerEdge, hMarkerEdge, by
            rw [if_pos hMarkerLabel]
            rfl⟩
        · simp [hMarkerSource]
        · simp
  · intro residual state state' env label current future hRelated hEdge
    rcases relationMembership_recur_cases alphabet name body hRelated with
      hRoot | ⟨q, bodyResidual, hEntry, hBodyRelated⟩
    · rw [Prod.ext_iff] at hRoot
      obtain ⟨hResidual, hState⟩ := hRoot
      subst hResidual
      subst hState
      obtain ⟨pendingEdge, hPending, hSource, hEnv, hLabel, hCurrent, -, hTarget⟩ :=
        (compileType_hasEdge_iff_hasResolvedEdge (.recur alphabet name body)
          .root state' env label { current := current, future := future }).mp hEdge
      rw [compileTypeFuel_recur_eq] at hPending
      simp only [buildRecursionAutomaton, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hPending
      rcases hPending with ⟨environment, hEnvFilter, hEq⟩ | ⟨bodyEdge, -, hEq⟩
      · subst hEq
        simp only at hEnv hLabel hCurrent hTarget
        have hLabelEq : label = TypeLabel.silent := by simpa using hLabel.symm
        have hCurrentEq : current = ∅ := hCurrent.symm
        subst hLabelEq
        subst hCurrentEq
        subst hEnv
        refine ⟨body.replaceVar name (.recur alphabet name body),
          typeFutureOffers (body.replaceVar name (.recur alphabet name body)),
          ?_, ?_⟩
        · exact ⟨TypeTransition.recur environment alphabet name body
            (PactTypeAlphabet.environment_wellFormed hEnvFilter.1)
            hEnvFilter.2,
          TypeOffers.recur environment alphabet name body
            ⟨PactTypeAlphabet.environment_wellFormed hEnvFilter.1,
              hEnvFilter.2⟩⟩
        · rw [← hTarget]
          exact relationMembership_recur_child alphabet name body body
            (buildRelationSet_initial body (compileType body))
      · rw [← hEq] at hSource
        by_cases hMarker : bodyEdge.label = AutomatonConstructionLabel.variable name
        · rw [if_pos hMarker] at hSource
          simp [childState] at hSource
        · rw [if_neg hMarker] at hSource
          simp [childState] at hSource
    · rw [Prod.ext_iff] at hEntry
      obtain ⟨hResidual, hState⟩ := hEntry
      subst hResidual
      subst hState
      rcases compileType_recur_child_edge_cases alphabet name body
          hBodyTail hBodyAlphabet hBodyLocal hBodyClock hBodyRelated hEdge with
        ⟨bodyEdge, hBodyMem, hSource, hEnv, hLabel, hCurrent, hStateEq, _⟩ |
        ⟨varAlphabet, hVar, hStateEq, hLabel, hCurrent, hEnv, hClock, _⟩
      · have hBodyEdge : (compileType body).HasEdge q env label
            ⟨current, resolveFutureSpec (computeFutureOf body) bodyEdge.future⟩
            bodyEdge.target := by
          rw [compileType_hasEdge_iff_hasResolvedEdge]
          exact ⟨bodyEdge, hBodyMem, hSource, hEnv, hLabel, hCurrent, rfl, rfl⟩
        obtain ⟨bodyTarget, bodyStepFuture, hBodyStep, hBodyTarget⟩ :=
          hBody.2 hBodyRelated hBodyEdge
        obtain ⟨parentStepFuture, hParentStep⟩ :=
          hBackward hBodyRelated hBodyStep
        subst hStateEq
        exact ⟨bodyTarget.replaceVar name (.recur alphabet name body),
          parentStepFuture, hParentStep,
          relationMembership_recur_child alphabet name body bodyTarget
            hBodyTarget⟩
      · subst hVar
        subst hStateEq
        subst hLabel
        subst hCurrent
        refine ⟨body.replaceVar name (.recur alphabet name body),
          typeFutureOffers (body.replaceVar name (.recur alphabet name body)),
          ?_,
          relationMembership_recur_child alphabet name body body
            (buildRelationSet_initial body (compileType body))⟩
        simpa [PactType.replaceVar] using
          (⟨TypeTransition.recur env alphabet name body hEnv hClock,
            TypeOffers.recur env alphabet name body ⟨hEnv, hClock⟩⟩ :
            DecoratedTypeTransition env (.recur alphabet name body)
              TypeLabel.silent
              { current := ∅,
                future := typeFutureOffers
                  (body.replaceVar name (.recur alphabet name body)) }
              (body.replaceVar name (.recur alphabet name body)))

/-- Current-offer correspondence for recursion in the form used by the
simultaneous induction: the body IH is the only recursive input, and the
substitution transport is discharged from `TypeWF`. -/
theorem currentOfferCorrespondence_recur_of_typeWF
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.recur alphabet name body))
    (hBody : CurrentOfferCorrespondence body) :
    CurrentOfferCorrespondence (.recur alphabet name body) :=
  currentOfferCorrespondence_recur alphabet name body hWF hBody
    (recursionSubstitutionStepForward_of_typeWF alphabet name body hWF)
    (recursionSubstitutionStepBackward_of_typeWF alphabet name body hWF)

/-- The recursion header reads the menu of its unfolding target. -/
theorem compileType_recur_root_future
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    {env : TypeEnvironment} {label : TypeLabel} {current future : Finset BareMessage}
    {target : TypeAutomatonState}
    (hEdge : (compileType (.recur alphabet name body)).HasEdge .root env label
      ⟨current, future⟩ target) :
    future = computeFutureOf (.recur alphabet name body) target := by
  obtain ⟨edge, hMem, hSource, _, _, _, hFuture, hTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge _ _ _ _ _ _).mp hEdge
  change resolveFutureSpec (computeFutureOf (.recur alphabet name body)) edge.future =
    future at hFuture
  rw [compileTypeFuel_recur_eq] at hMem
  simp only [buildRecursionAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image] at hMem
  rcases hMem with ⟨env, _, rfl⟩ | ⟨child, _, rfl⟩
  · rw [← hTarget]
    simpa [resolveFutureSpec] using hFuture.symm
  · split at hSource <;> simp [childState] at hSource

/-- A represented call has no public body step; its installed edge is a backedge. -/
theorem compileType_recur_marker_future
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    (hBody : CurrentOfferCorrespondence body)
    {varAlphabet : PactTypeAlphabet} {q target : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {current future : Finset BareMessage}
    (hRelated : relationMembership (buildRelationSet body (compileType body))
      (.var varAlphabet name) q)
    (hEdge : (compileType (.recur alphabet name body)).HasEdge (.child 0 q) env label
      ⟨current, future⟩ target) :
    future = computeFutureOf (.recur alphabet name body) target := by
  obtain ⟨edge, hMem, hSource, hEnv, hLabel, hCurrent, hFuture, hTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge _ _ _ _ _ _).mp hEdge
  change resolveFutureSpec (computeFutureOf (.recur alphabet name body)) edge.future =
    future at hFuture
  rw [compileTypeFuel_recur_eq] at hMem
  simp only [buildRecursionAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image] at hMem
  rcases hMem with ⟨env, _, rfl⟩ | ⟨child, hChild, rfl⟩
  · simp at hSource
  · by_cases hMarker : child.label = .variable name
    · rw [if_pos hMarker] at hFuture hTarget
      rw [← hTarget]
      simpa [resolveFutureSpec] using hFuture.symm
    · rw [if_neg hMarker] at hSource hEnv hLabel hCurrent hTarget
      have hChildEdge : (compileType body).HasEdge q env label
          ⟨current, resolveFutureSpec (computeFutureOf body) child.future⟩ child.target := by
        rw [compileType_hasEdge_iff_hasResolvedEdge]
        exact ⟨child, hChild, by simpa [childState] using hSource,
          hEnv, hLabel, hCurrent, rfl, rfl⟩
      obtain ⟨rho, f, hStep, _⟩ := hBody.2 hRelated hChildEdge
      cases hStep.2

/-- The same-rank menu equation identifies the common header/backedge operand. -/
theorem recursion_entry_menu_eq
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    (hMenus : FutureOffersAgree (.recur alphabet name body)) :
    computeFutureOf (.recur alphabet name body)
        (.child 0 (compileTypeFuel (typeCompilationFuel body) body).initial) =
      typeFutureOffers (body.replaceVar name (.recur alphabet name body)) :=
  hMenus (relationMembership_recur_child alphabet name body body
    (buildRelationSet_initial body (compileType body)))

theorem offer_recur_root_forward
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    (hMenus : FutureOffersAgree (.recur alphabet name body))
    {env : TypeEnvironment} {label : TypeLabel} {current future : Finset BareMessage}
    {target : PactType}
    (hStep : DecoratedTypeTransition env (.recur alphabet name body) label
      ⟨current, future⟩ target) :
    ∃ q', (compileType (.recur alphabet name body)).HasEdge .root env label
        ⟨current, future⟩ q' ∧
      relationMembership (buildRelationSet (.recur alphabet name body)
        (compileType (.recur alphabet name body))) target q' := by
  cases hStep.2 with
  | recur _ _ _ _ hEnv =>
    refine ⟨_, ?_, relationMembership_recur_child alphabet name body body
      (buildRelationSet_initial body (compileType body))⟩
    simpa only [recursion_entry_menu_eq alphabet name body hMenus] using
      compileType_recur_root_hasEdge alphabet name body hEnv.1 hEnv.2

theorem offer_recur_backedge_forward
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    (hMenus : FutureOffersAgree (.recur alphabet name body))
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel (typeCompilationFuel body) body).edges)
    (hMarker : edge.label = .variable name)
    {label : TypeLabel} {current future : Finset BareMessage} {target : PactType}
    (hStep : DecoratedTypeTransition edge.environment (.recur alphabet name body) label
      ⟨current, future⟩ target) :
    ∃ q', (compileType (.recur alphabet name body)).HasEdge (.child 0 edge.source)
        edge.environment label ⟨current, future⟩ q' ∧
      relationMembership (buildRelationSet (.recur alphabet name body)
        (compileType (.recur alphabet name body))) target q' := by
  cases hStep.2 with
  | recur _ _ _ _ hEnv =>
    refine ⟨_, ?_, relationMembership_recur_child alphabet name body body
      (buildRelationSet_initial body (compileType body))⟩
    simpa only [recursion_entry_menu_eq alphabet name body hMenus] using
      compileType_recur_backedge_hasEdge alphabet name body edge hEdge hMarker

/-- An unfolding step exposes its target menu, already identified at this rank. -/
private theorem offer_recur_unfold_backward
    {alphabet : PactTypeAlphabet} {name : String} {body : PactType}
    (hCurrent : CurrentOfferCorrespondence (.recur alphabet name body))
    (hMenus : FutureOffersAgree (.recur alphabet name body))
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hRelated : relationMembership (buildRelationSet (.recur alphabet name body)
      (compileType (.recur alphabet name body))) (.recur alphabet name body) q)
    (hEdge : (compileType (.recur alphabet name body)).HasEdge q env label
      ⟨current, future⟩ q')
    (hFuture : future = computeFutureOf (.recur alphabet name body) q') :
    ∃ target, DecoratedTypeTransition env (.recur alphabet name body) label
        ⟨current, future⟩ target ∧
      relationMembership (buildRelationSet (.recur alphabet name body)
        (compileType (.recur alphabet name body))) target q' := by
  obtain ⟨target, stepFuture, hStep, hTarget⟩ := hCurrent.2 hRelated hEdge
  have hSemantic : stepFuture = typeFutureOffers target := by
    cases hStep.2
    rfl
  rw [hMenus hTarget] at hFuture
  exact ⟨target, (hSemantic.trans hFuture.symm) ▸ hStep, hTarget⟩

theorem offer_recur_root_backward
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    (hCurrent : CurrentOfferCorrespondence (.recur alphabet name body))
    (hMenus : FutureOffersAgree (.recur alphabet name body))
    {q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType (.recur alphabet name body)).HasEdge .root env label
      ⟨current, future⟩ q') :
    ∃ target, DecoratedTypeTransition env (.recur alphabet name body) label
        ⟨current, future⟩ target ∧
      relationMembership (buildRelationSet (.recur alphabet name body)
        (compileType (.recur alphabet name body))) target q' :=
  offer_recur_unfold_backward hCurrent hMenus
    (relationMembership_recur_root alphabet name body) hEdge
    (compileType_recur_root_future alphabet name body hEdge)

theorem offer_recur_backedge_backward
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    (hBody : CurrentOfferCorrespondence body)
    (hCurrent : CurrentOfferCorrespondence (.recur alphabet name body))
    (hMenus : FutureOffersAgree (.recur alphabet name body))
    {varAlphabet : PactTypeAlphabet} {q q' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {current future : Finset BareMessage}
    (hRelated : relationMembership (buildRelationSet body (compileType body))
      (.var varAlphabet name) q)
    (hEdge : (compileType (.recur alphabet name body)).HasEdge (.child 0 q) env label
      ⟨current, future⟩ q') :
    ∃ target, DecoratedTypeTransition env (.recur alphabet name body) label
        ⟨current, future⟩ target ∧
      relationMembership (buildRelationSet (.recur alphabet name body)
        (compileType (.recur alphabet name body))) target q' := by
  have hParentRelated := relationMembership_recur_child alphabet name body
    (.var varAlphabet name) hRelated
  simp only [PactType.replaceVar] at hParentRelated
  exact offer_recur_unfold_backward hCurrent hMenus hParentRelated hEdge
    (compileType_recur_marker_future alphabet name body hBody hRelated hEdge)

end

end Pact
