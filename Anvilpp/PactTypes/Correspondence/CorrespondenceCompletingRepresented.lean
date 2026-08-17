import Anvilpp.PactTypes.Correspondence.CorrespondenceMarkerSkipping

/-!
# compiledFragmentCompleting_represented (mutual induction)
-/

namespace Pact

noncomputable section

/- **Non-clock predecessor step for substituted completion.**

If the target of a non-clock edge of a compiled fragment represents a residual
that completes before the next tock — scoring a bare `.var name` as `value`
rather than `false` — then the edge's source also represents such a residual.
This is the graph obligation of the forward (`⊆`) half of
`recursionBodyCompletingClosure_iff`.

Two features of this statement were forced by counterexamples found while
assembling the forward half, and must not be weakened back:

* The conclusion is **existential** (`∃ sourceResidual, related ∧ complete`),
  not the seemingly more convenient universal form `∀ r, related → complete`.
  The universal form cannot be discharged, and a parallel product refutes it
  up to the existence of one synchronised edge.  Take
  `body = .par (.var "y") .skip ∅` inside a binder for `"x"`.  The product
  edge synchronising the left fragment's `.variable "y"` marker
  (`.root → .final`, silent) with the right fragment's silent self-loop is
  itself silent; its source `.pair .root .root` represents
  `.par (.var "y") .skip ∅`, whose substituted completion for `"x"` is
  `false`; and its target `.pair .final .root` represents *nothing at all*,
  since the `.var` fragment's `.final` is unrelated.  So the universal
  premise holds vacuously while the universal conclusion fails.  (This was
  not turned into a kernel-checked regression lemma: whether that product
  edge is actually emitted depends on `syncAutomatonEdges` at a concrete
  signature, and the point stands regardless — the universal form is not
  provable by this induction.)  Crucially, filtering the ambient set by the
  universal predicate does *not* rescue it either: `buildParallelAutomaton`
  emits a `.future` self-loop at *every* product state, so the unrepresented
  target is an edge source and therefore does lie in the ambient set.  The
  existential form is immune, because the vacuous premise becomes an
  unsatisfiable one.
* The hypothesis is `≠ TypeLabel.tock`, not `= TypeLabel.silent`.  Silent
  implies non-clock, so this is only a strengthening at the use site, but the
  induction *requires* it: `buildParallelAutomaton` can hide two visible
  message edges inside one silent product edge, and the induction hypothesis
  has to be applied to those non-silent components.  `≠ tock` survives that
  decomposition by `AutomatonConstructionLabel.component_nonclock_of_sync`,
  whereas `= silent` does not.  It is also exactly the right condition
  semantically: the only compiled edge that legitimately destroys completion
  is the clock edge of `.tock`.

Intended proof: induction on the compilation fuel, one case per constructor.
Atomic constructors are direct (the clock edge of `.tock` is excluded by the
hypothesis, every other atomic edge is a silent self-loop or lands in
`.skip`); the `.var` case is vacuous because its `.final` target represents
nothing.  Child edges of `.choice`/`.fairChoice`/`.seq`/`.xoffer`/`.offer`
transport through the matching relation constructor and the corresponding
`canCompleteBeforeTockSubst` clause.  Fresh administrative edges are handled
by `compileTypeFuel_initial_relation` (their targets are child entries).  The
`.seq` bridge edges additionally need that a `skipping` state represents
`.skip` — a further mechanical induction that does not exist yet.  The `.par`
case decomposes through `resolvedAutomatonEdges` and
`component_nonclock_of_sync`.  The `.recur` case relates the header edge and
the installed backedges to `PactType.replaceVar_canCompleteBeforeTock`. -/
mutual

theorem compiledFragmentNonClockPredecessor_eval
    (signature : TypeAlphabet) (active : List String)
    (valuation : String → Bool) (fuel : Nat) :
    ∀ (processType : PactType),
      (∀ name, name ∉ active → valuation name = false) →
      TypeCompilationFuelSufficient processType fuel →
      PactType.TailRecursive processType →
      PactType.BinderHygienic active processType →
      ∀ edge ∈ (compileTypeFuel signature fuel processType).edges,
        edge.label.semantic ≠ TypeLabel.tock →
        ∀ targetResidual,
          TypeCompilationRelation processType edge.target targetResidual →
          PactType.completionEval valuation targetResidual = true →
            ∃ sourceResidual,
              TypeCompilationRelation processType edge.source sourceResidual ∧
              PactType.completionEval valuation sourceResidual = true := by
  sorry -- TODO(redevelopment): proof broken by upstream TypeCompilationRelation `sequence_left`/`parallel_fuse` split; .

/-- Every compiler state marked as completing represents a semantic residual.
The proof carries the stronger fact that the witness itself completes; the
recursion case then closes the non-clock predecessor saturation using
`compiledFragmentNonClockPredecessor_subst`. -/
theorem compiledFragmentCompleting_represented
    (signature : TypeAlphabet) (bound : List String) (fuel : Nat) :
    ∀ (processType : PactType),
      TypeCompilationFuelSufficient processType fuel →
      PactType.TailRecursive processType →
      PactType.BinderHygienic bound processType →
      ∀ state ∈ (compileTypeFuel signature fuel processType).completing,
        ∃ residual, TypeCompilationRelation processType state residual ∧
          residual.CanCompleteBeforeTock = true := by
  sorry -- TODO(redevelopment): proof broken by upstream TypeCompilationRelation `sequence_left`/`parallel_fuse` split; .

end

end

end Pact
