# Type and Compiler Proofs

Proofs about the [type and automaton definitions](../Spec/README.md).

| Directory | Contents |
|---|---|
| [Syntax](Syntax/README.md) | Substitution, regularity, completion, and offer laws |
| [Automata](Automata/README.md) | Compiler structure, fuel stability, and edge properties |
| [Correspondence](Correspondence/README.md) | Decorated-step correspondence and menu agreement |

The correspondence proof combines syntax and compiler properties through
`correspondence_simultaneous`. Proof-specific predicates, including
`FutureOffersAgree`, `MarkerSourceFor`, and `EdgeLocalAt`, live beside
the proofs that use them.
