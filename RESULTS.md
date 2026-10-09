# Results and Proofs

Public results are in [PactSafety.lean](Anvilpp/PactSafety.lean), in namespace
`Pact`. This index states the main conclusions; the declarations give the
full quantified premises. Supporting module indexes cover the remaining lemmas.

## Inference and Checking

| Result | Statement |
|---|---|
| `decorated_step_lifting` | A reachable, data-well-formed process can realize an inferred-type step's current and future offers under the concrete environment. It need not realize that particular type target. |
| `readiness_abstraction` | Readiness of the inferred type implies readiness of the reachable process under the same erased environment. |
| `inferred_type_soundness` | Every `WFProc` process conforms to its inferred type. |
| `conformance_closed_under_refinement` | A process conforming to a precise type also conforms to a type it refines. |
| `type_checking_soundness` | A well-formed process conforms to every type accepted by data-oblivious checking. |
| `compositional_type_checking_soundness` | Componentwise checking gives conformance of the parallel composition, with matching component alphabets and well-formed process and claimed type compositions. |
| `strategy_transfer` | Honest type strategies enforcing value-oblivious objectives transfer to conforming processes. |

`WFProc` requires data well-formedness and a well-formed inferred type.
Conformance combines forward process-step matching with reflection of type
readiness. Step matching relates targets; readiness requires only a step to
exist. The lifting lemma does not claim that every abstract branch is selected
by the concrete guard.

[Inference](Anvilpp/ProofHelpers/Inference/README.md) proves erasure, menu
agreement, offer realization, and preservation of reachable-process invariants.
`ProcReachable.refl`, `ProcReachable.step`, `WFProc.conjunctRegular`,
`WFProc.sideConditions`, and `dataWFProc_step` supply the invariants used above.

## Automaton Correspondence

| Result | Statement |
|---|---|
| `type_automaton_correspondence` | An admissible type and its compiled automaton match decorated steps in both directions, including environments, labels, offer pairs, and related targets. |
| `process_automaton_correspondence` | A process conforming to an admissible type has matching erased automaton steps and equivalent readiness at related states. |
| `process_automaton_path` | Every finite process execution has a matching erased automaton path ending at a related state. |

The [simultaneous induction](Anvilpp/PactTypes/Proofs/Correspondence/Simultaneous/README.md)
proves decorated-step correspondence and future-menu agreement together, by
induction on compilation fuel. [Structural helpers](Anvilpp/PactTypes/Proofs/Correspondence/Helpers/README.md)
provide residual shapes, substitution transport, and survivor transport.
`correspondence_steps` instantiates the empty binder context; the public
theorem adds the initial relation pair. Process correspondence then composes
type correspondence with conformance. It is not a process/type bisimulation.

## Regularity and Compatibility

| Result | Statement |
|---|---|
| `log_objective_regular` | The honesty, clock, fairness, and progress objective has a finite Rabin recognizer over the finite boundary alphabet. |
| `game_reduction_correctness` | Game-based compatibility equals completed-log compatibility for well-formed types. |
| `type_compatibility_soundness` | Compatibility of a well-formed type transfers to a conforming process with equal fair-choice and progress IDs. |

[ObjectiveRegularity](Anvilpp/ProofHelpers/ObjectiveRegularity.lean) combines
finite honesty memory with round-robin monitors. Recurring completion flags
characterize recurring requests; unfairness pairs require one recurring outcome
and finitely many opposite outcomes.

[CompatibilityBridge](Anvilpp/ProofHelpers/CompatibilityBridge.lean) and
[StrategyExtension](Anvilpp/ProofHelpers/StrategyExtension.lean) transfer
strategies between executions and the monitored game.
[ConformanceTransfer](Anvilpp/ProofHelpers/ConformanceTransfer.lean) preserves
completed logs under erasure. A stuck process would produce an eventually silent
log, contradicting the winning objective's recurring clock requirement.

## Refinement and Optimality

| Result | Statement |
|---|---|
| `compatibility_monotone_under_refinement` | A compatible abstract tuple has a compatible componentwise refinement, when component alphabets and identifiers agree and both compositions are well formed. |
| `inferred_types_optimal` | A well-formed inferred composition is compatible exactly when some compatible claimed tuple in `UserTypeDomain` passes data-oblivious checking. |
| `inferred_failure_rules_out_data_oblivious_proofs` | Failure of inferred compatibility excludes every compatible checked tuple in that domain. |

`UserTypeDomain` requires matching component alphabets, fair-choice IDs, and
progress IDs, together with well-formed claimed compositions. All comparisons
use the same interfaces and required progress set.

[ResigningRefinement](Anvilpp/ProofHelpers/ResigningRefinement.lean) proves
common-restriction closure, parallel refinement, and composition refinement.
[RefinementLifting](Anvilpp/ProofHelpers/RefinementLifting.lean) lifts component
relations, matches completed logs, and transfers compatibility.
`Refines.refl` and `helper_h23_refinement_trans` establish reflexivity and
transitivity. Inference preserves the alphabets and identifier sets needed to
use the inferred tuple itself as the forward optimality witness.

## Supporting Proofs

| Index | Results |
|---|---|
| [Syntax](Anvilpp/PactTypes/Proofs/Syntax/README.md) | Substitution, reannotation, regularity, completion, menus, and offer environments |
| [Automata](Anvilpp/PactTypes/Proofs/Automata/README.md) | Fuel stability, edge shape, finite menu closure, and recursion markers |
| [Correspondence](Anvilpp/PactTypes/Proofs/Correspondence/README.md) | State/residual relations and constructor cases |
| [Safety helpers](Anvilpp/ProofHelpers/README.md) | Log erasure, monitors, strategy transfer, and refinement |

[ProofAudit.lean](ProofAudit.lean) checks the public theorem dependencies.
