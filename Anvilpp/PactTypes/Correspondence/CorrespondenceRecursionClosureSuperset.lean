import Anvilpp.PactTypes.Correspondence.CorrespondenceRecursionClosureLift

/-!
# recursionBodyCompletingClosure_superset_aux
-/

namespace Pact

noncomputable section


/-- Generic (not fixed to `body`) form of the reverse-closure argument,
quantified over an arbitrary subterm `processType` with its own compiled
fragment and own seed.  This is required because `TypeCompilationRelation`'s
constructors (e.g. `choice_left`) recurse through strictly smaller *type*
arguments, so a `body`-fixed motive cannot serve as an induction target: the
induction hypothesis needed at `choice_left` is a fact about `left`'s own
fragment, not `body`'s.

`hVanilla` is threaded as an explicit parameter (not re-derived via
`compilationCompletingCorrect_of_nestedRecursion`, which would need a forward
reference to `compilationCompletingCorrect_recursion_regular_leaf`, defined
later in this file, for its nested-recursion case): the CALLER supplies
`CompilationCompletingCorrect signature processType`, and at each recursive
step into a strictly smaller child (`left`/`right`/...), the child's own
`CompilationCompletingCorrect` fact is derived directly from the parent's via
the tagged-completing-set argument above, not re-derived from scratch.

Only the atomic and choice/fairChoice cases are proved here; the remaining
constructors are separate, precisely-scoped sorries (see the comment at each
site for exactly what remains). -/
theorem recursionBodyCompletingClosure_superset_aux
    (signature : TypeAlphabet) :
    ∀ (name : String) (value : Bool) (processType : PactType),
      PactType.TailOccurrences name True processType →
      signature.Supports processType →
      PactType.ClockGuarded processType →
      PactType.TailRecursive processType →
      PactType.BinderHygienic [name] processType →
      (∀ child : PactType, sizeOf child < sizeOf processType →
        signature.Supports child → child.ClockGuarded → child.TailRecursive →
          child.BinderHygienic [] →
            CompilationCompletingCorrect signature child) →
      CompilationCompletingCorrect signature processType →
      ∀ state residual,
        TypeCompilationRelation processType state residual →
        PactType.canCompleteBeforeTockSubst name value residual = true →
        state ∈ completingBackClosure
          (compileTypeFuel signature (typeCompilationFuel processType) processType)
          ((if value then
              ((compileTypeFuel signature (typeCompilationFuel processType)
                  processType).edges.filter
                fun edge => edge.label = .variable name).image
                  fun edge => edge.source
            else ∅) ∪
            (compileTypeFuel signature (typeCompilationFuel processType)
              processType).completing) := by
  sorry -- TODO(redevelopment): proof broken by upstream TypeCompilationRelation `sequence_left`/`parallel_fuse`/EntryCanonical changes; .
end

end Pact
