# Anvilpp.PactTypes.Proofs

Everything proved about [`../Spec/`](../Spec/README.md), together with the
names introduced only to state a proof obligation —
`CurrentOfferCorrespondence`, `FutureOffersAgree`, `MarkerSourceFor`,
`RecursionSubstitutionStepForward`/`Backward`, `survivorLeftEdge`, `ShapeEq`,
`EdgeLocalAt`.

| | Files | Lines | Theorems |
|---|---:|---:|---:|
| [`Syntax/`](Syntax/README.md) | 14 | 5,857 | 115 |
| [`Automata/`](Automata/README.md) | 14 | 6,492 | 171 |
| [`Correspondence/`](Correspondence/README.md) | 42 | 37,314 | 656 |

The layers are used in that order. `Syntax/` proves facts about types alone —
substitution, regularity, menus. `Automata/` proves facts about compiled
fragments alone — fuel irrelevance, edge shape, marker absence.
`Correspondence/` is where the two meet, ending at
`correspondence_simultaneous`.

Most of the weight is in the parallel and recursion constructors:
`Correspondence/Helpers/Parallel.lean` (3,816 lines),
`Helpers/AlphabetPreservation.lean` (3,359),
`Simultaneous/Recursion.lean` (2,671).
