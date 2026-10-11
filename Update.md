# Updates Since Submission

This note summarizes how the Lean artifact fills in the formal details of the
submitted paper. It clarifies and refines the semantics and makes the theorem
statements precise. The artifact proves inference and checking soundness,
type-automaton correspondence, compatibility soundness, and inferred-type
optimality for the definitions described below. [RESULTS.md](RESULTS.md) indexes
the statements and their proof chains.

## Explicit Message Alphabets

Processes and types now carry fixed finite alphabets of polarized message
actions, distinguishing `m!` from `m?`. Inference preserves the process's
alphabet. Admissible environments supply complementary actions from that
alphabet, and future-offer menus are restricted to the declared actions.

Parallel composition makes the alphabet discipline explicit: interface
messages have complementary polarities in the children and are hidden from
the parent. Outside the interface, both children carry the parent's alphabet.
When one child finishes, the survivor is reannotated with the parent alphabet,
including its nested components.

See [Alphabet.lean](Anvilpp/Alphabet.lean) and the
[type syntax](Anvilpp/PactTypes/Spec/Syntax/PactTypeSyntaxDefs.lean).

## Parallel Steps and Future Offers

The parallel rules make the local-environment premises precise: each child's
environment uses the current and future offers of the sibling's actual step.
This keeps the environment and offer witnesses consistent. The rules also
spell out synchronization, interface hiding, joint completion, and survivor
execution on both the process and type sides.

Future offers are conservative same-cycle menus, not necessarily the menu of
the selected target. Conditional and fair-choice steps retain the source's
menu; exclusive-offer resolution removes the branch heads from its source
menu. Sequence combines the stepping child's future offers with the right
continuation's menu when the left can optimistically complete before a clock.
That completion test does not depend on alphabet membership. These conventions
are shared by the process semantics, type semantics, and compiler.

See [PactSemantics.lean](Anvilpp/PactSemantics.lean) and
[type offers](Anvilpp/PactTypes/Spec/Syntax/PactTypeFutureOffersDefs.lean).

## Conformance and Refinement

Conformance builds on the paper's erased step matching with an explicit
readiness clause: at related states, if the type can step under the erased
environment, the process can step under the concrete environment. This
supplies the readiness guarantee used to transfer safety from types to
processes. The clause requires a process step to exist, rather than requiring
the process to realize every nondeterministic type target.

Refinement likewise includes availability as well as forward step matching.
It compares single decorated steps under the same environment, preserving
their labels and current/future offer pairs. Related residuals also agree on
whether they are `skip`, so completion behaves consistently in compositions.

See the [conformance and refinement definitions](Anvilpp/PactTypes/Spec/Syntax/TypeTransitionSystemDefs.lean).

## Constructive Automaton Correspondence

The submission describes a canonical automaton obtained from semantic
residuals. The artifact gives an explicit constructor-by-constructor compiler,
with a proof that its decorated steps correspond to the type semantics in both
directions. The proof establishes step correspondence and future-menu
agreement together.

Automaton menus are computed by finite saturation along non-clock execution
edges and explicit menu dependencies. Menu dependencies only contribute to
offer computation; they are not additional execution transitions.

See the [compiler](Anvilpp/PactTypes/Spec/Automata/CompileTypeDefs.lean) and
[correspondence proofs](Anvilpp/PactTypes/Proofs/Correspondence/README.md).

## Well-Formedness and Precise Theorem Statements

The artifact spells out the regularity requirements as explicit conditions
for binding, clock-guarded tail recursion, same-cycle message linearity,
interface scoping, and ownership in parallel and conjunctive branches. Offer
continuations, including the default, cannot re-advertise branch-head message
names in their same-cycle future menus.

Inference soundness requires a data-well-formed process with a well-formed
inferred type. Compatibility soundness additionally requires equal process
and type fair-choice and progress identifiers. Optimality compares
well-formed compositions with the same interfaces and required progress set;
each claimed component must match its process's alphabet and identifier sets.
The optimality claim remains relative to data-oblivious checking.

These premises appear in the public statements in
[PactSafety.lean](Anvilpp/PactSafety.lean), including `UserTypeDomain`.

## Evaluation Scope

The artifact focuses on semantic correctness, including compositional
checking soundness, regularity of the log objective, and equivalence between
game-based and semantic compatibility. The paper's complexity bounds and
algorithmic decidability claims are not formalized.

Use the commands in [README.md](README.md) to build the artifact and run
[ProofAudit.lean](ProofAudit.lean), which checks the axiom dependencies of the
main results.
