# Type and Automaton Definitions

| Directory | Definitions |
|---|---|
| [Syntax](Syntax/README.md) | Types, substitution, well-formedness, transitions, and offers |
| [Automata](Automata/README.md) | Finite constructor fragments, execution edges, and menu aggregation |

`TypeTransition` describes execution; `TypeOffers` also records current and
future offers. `compileType` resolves constructor fragments into a finite
automaton. The state/residual relation is defined separately in
[TypeAutoRelCore](../Proofs/Correspondence/TypeAutoRelCore.lean).
