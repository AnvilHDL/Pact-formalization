import Anvilpp.PactTypes.Correspondence.CorrespondenceRecursionClosureSuperset

/-!
# recursionBodyCompletingClosure_iff and compilationCompletingCorrect_recursion_regular_leaf
-/

namespace Pact

noncomputable section


/-- Reverse (`⊇`) half of `recursionBodyCompletingClosure_iff`.

A state whose represented residual completes once `.var name` is scored as
`body.CanCompleteBeforeTock` lies in the backward completion closure of the
seed.  Unlike the forward half this is not an upper-bound argument: it must
*construct* a silent path from the state either into `bodyFragment.completing`
(when plain, unsubstituted completion already holds) or into a recursive-call
source (when the substituted value is what makes the residual complete, which
forces the residual to contain a reachable `.var name` in tail position, and
therefore forces the body entry to be completing so that the conditional seed
branch is the non-empty one).  The intended proof is a per-constructor closure
decomposition over `body`, using the existing outgoing-edge classifiers
`buildChoiceAutomaton_outgoing_left/right`,
`buildSequenceAutomaton_outgoing_right` and
`buildExclusiveOfferAutomaton_outgoing_*`. -/
private theorem recursionBodyCompletingClosure_superset
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hGuardedOccurrences : PactType.GuardedOccurrences name False body)
    (hTailOccurrences : PactType.TailOccurrences name True body)
    (hBodyGuarded : PactType.ClockGuarded body)
    (hBodyTail : PactType.TailRecursive body)
    (hBodyHygienic : PactType.BinderHygienic [name] body)
    (hBodySupports : signature.Supports body)
    (hChildrenVanilla : ∀ child : PactType, sizeOf child < sizeOf body →
      signature.Supports child → child.ClockGuarded → child.TailRecursive →
      child.BinderHygienic [] →
        CompilationCompletingCorrect signature child)
    (hVanilla : CompilationCompletingCorrect signature body)
    (state : TypeAutomatonState) (residual : PactType)
    (hRelated : TypeCompilationRelation body state residual)
    (hComplete : PactType.canCompleteBeforeTockSubst name
      body.CanCompleteBeforeTock residual = true) :
    state ∈ completingBackClosure
        (compileTypeFuel signature (typeCompilationFuel body) body)
        ((if (compileTypeFuel signature (typeCompilationFuel body) body).initial ∈
              (compileTypeFuel signature (typeCompilationFuel body)
                body).completing then
            ((compileTypeFuel signature (typeCompilationFuel body)
                body).edges.filter
              fun edge => edge.label = .variable name).image
                fun edge => edge.source
          else ∅) ∪
          (compileTypeFuel signature (typeCompilationFuel body)
            body).completing) := by
  sorry -- TODO(redevelopment): proof broken by upstream TypeCompilationRelation/EntryCanonical changes; .


theorem compiledBranch_zipIdx_cases
    (signature : TypeAlphabet) (fuel : Nat)
    (branches : List (BareMessage × PactType))
    (indexed : (BareMessage × AutomatonFragment) × Nat)
    (hIndexed : indexed ∈
      (branches.map fun branch =>
        (branch.1, compileTypeFuel signature fuel branch.2)).zipIdx) :
    ∃ action branchType,
      branches[indexed.2]? = some (action, branchType) ∧
        indexed.1 =
          (action, compileTypeFuel signature fuel branchType) := by
  have hFields := List.mem_zipIdx hIndexed
  simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hFields
  rcases hFields with ⟨hBound, hValue⟩
  have hAt :
      (branches.map fun branch =>
        (branch.1, compileTypeFuel signature fuel branch.2))[indexed.2]? =
          some indexed.1 := by
    rw [List.getElem?_eq_getElem hBound, hValue]
  rw [List.getElem?_map] at hAt
  cases hOriginal : branches[indexed.2]? with
  | none => simp [hOriginal] at hAt
  | some branch =>
      rcases branch with ⟨action, branchType⟩
      simp only [hOriginal, Option.map_some, Option.some.injEq] at hAt
      exact ⟨action, branchType, rfl, hAt.symm⟩

/-- The remaining graph content of the recursion completion leaf.

The backward completion closure of the compiled body — seeded by the body's
own `completing` states together with the recursive-call sources, the latter
only when the binder itself completes — is exactly the set of states whose
represented residual completes once a bare `.var name` is scored as
`body.CanCompleteBeforeTock` instead of `false`.

This is the one statement standing between the checked assembly below and a
closed `compilationCompletingCorrect_recursion_regular_leaf`.  Both directions
are graph/syntax correspondence, not bookkeeping:

* `⊆` follows from `completingBackClosure_subset_of_predecessor_closed` with
  ambient set `seed ∪ edges.image (·.source)` (deliberately not `states`, so
  no carrier invariant is needed) filtered by `∀ r, TypeCompilationRelation
  body q r → canCompleteBeforeTockSubst name _ r = true`; the `∀` avoids
  needing state-totality, and `TypeCompilationRelation.residual_unique`
  transfers the result to the given residual.  Seed inclusion uses `hVanilla`
  with `PactType.canCompleteBeforeTock_le_subst`, and — for the recursive-call
  sources — that under `hTailOccurrences` the source of a matching
  `.variable name` edge represents exactly `.var name`.
* `⊇` needs that substituted completion which is not plain completion forces a
  silent path to such a source, by per-constructor closure decomposition over
  `body` using the existing outgoing-edge classifiers. -/
private theorem recursionBodyCompletingClosure_iff
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hGuardedOccurrences : PactType.GuardedOccurrences name False body)
    (hTailOccurrences : PactType.TailOccurrences name True body)
    (hBodyGuarded : PactType.ClockGuarded body)
    (hBodyTail : PactType.TailRecursive body)
    (hBodyHygienic : PactType.BinderHygienic [name] body)
    (hBodySupports : signature.Supports body)
    (hChildrenVanilla : ∀ child : PactType, sizeOf child < sizeOf body →
      signature.Supports child → child.ClockGuarded → child.TailRecursive →
      child.BinderHygienic [] →
        CompilationCompletingCorrect signature child)
    (hVanilla : CompilationCompletingCorrect signature body)
    (state : TypeAutomatonState) (residual : PactType)
    (hRelated : TypeCompilationRelation body state residual) :
    (state ∈ completingBackClosure
        (compileTypeFuel signature (typeCompilationFuel body) body)
        ((if (compileTypeFuel signature (typeCompilationFuel body) body).initial ∈
              (compileTypeFuel signature (typeCompilationFuel body)
                body).completing then
            ((compileTypeFuel signature (typeCompilationFuel body)
                body).edges.filter
              fun edge => edge.label = .variable name).image
                fun edge => edge.source
          else ∅) ∪
          (compileTypeFuel signature (typeCompilationFuel body)
            body).completing) ↔
      PactType.canCompleteBeforeTockSubst name body.CanCompleteBeforeTock
        residual = true) :=
  ⟨fun hMem => recursionBodyCompletingClosure_subset signature name body
      hTailOccurrences hBodyTail hBodyHygienic hVanilla state residual hRelated
        hMem,
    fun hComplete => recursionBodyCompletingClosure_superset signature name body
      hGuardedOccurrences hTailOccurrences hBodyGuarded hBodyTail hBodyHygienic
        hBodySupports hChildrenVanilla hVanilla state residual hRelated
          hComplete⟩

/-- Completion metadata for a guarded binder.  The fresh root is completing
exactly when the body entry is, and a tagged body state is completing exactly
when the backward closure says so — which
`recursionBodyCompletingClosure_iff` identifies with the substituted syntax
predicate, and `PactType.replaceVar_canCompleteBeforeTock` identifies that
with the residual actually represented by `TypeCompilationRelation`. -/
theorem compilationCompletingCorrect_recursion_regular_leaf
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hSupports : signature.Supports (.recur name body))
    (hGuarded : PactType.ClockGuarded (.recur name body))
    (hTail : PactType.TailRecursive (.recur name body))
    (hHygienic : PactType.BinderHygienic [] (.recur name body)) :
    CompilationCompletingCorrect signature (.recur name body) := by
  sorry -- TODO(redevelopment): proof broken by upstream TypeCompilationRelation/EntryCanonical changes; .

end

end Pact
