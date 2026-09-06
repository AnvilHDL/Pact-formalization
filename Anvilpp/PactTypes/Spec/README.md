# Anvilpp.PactTypes.Spec

The definitions Lemma 4.5 is about: the type language, its operational
semantics, and the constructor-automaton compiler.

| | Files | Lines | Defs |
|---|---:|---:|---:|
| [`Syntax/`](Syntax/README.md) | 13 | 2,604 | 153 |
| [`Automata/`](Automata/README.md) | 13 | 1,972 | 96 |

`Syntax/` defines the object being compiled and what it means to run it:
`PactType`, the step relation `TypeTransition`, its decorated form
`TypeOffers` carrying current and future offer sets, and the syntax-derived
menu `typeFutureOffers`.

`Automata/` defines the target: `AutomatonFragment`, one builder per type
constructor, `compileType`, and `computeFutureOf` — the reach-based closed
form of the paper's Φ least fixed point.

The correspondence relation (`buildRelationSet`, `relationMembership`) is in
`Proofs/Correspondence/TypeAutoRelCore.lean`, beside the induction that
establishes its properties.
