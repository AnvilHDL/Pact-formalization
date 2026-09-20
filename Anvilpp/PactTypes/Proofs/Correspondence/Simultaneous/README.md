# Simultaneous Correspondence

Constructor cases for decorated-step correspondence and menu agreement,
assembled by [Simultaneous.lean](../Simultaneous.lean) using strong induction on
`typeCompilationFuel`.

`TypeAutomatonStepCorrespondence` matches complete offer pairs in both
directions. `FutureOffersAgree` identifies a compiled state's menu with the
future offers of every related residual.

## Modules

| Module | Contents |
|---|---|
| `Base` | Offer predicates, base menus, edge locality, and state membership |
| `ChoiceAndSequence` | Base and choice cases; sequence infrastructure |
| `SequenceCurrent`, `Sequence` | Sequence steps and optimistic menus |
| `Offers` | Exclusive and conjunctive offer steps, root dependencies, and menus |
| `Parallel`, `ParallelMenus` | Product and survivor steps and menu equations |
| `Recursion` | Substitution transport and current-offer correspondence |
| `RecursionMenus`, `MarkerCorrespondence` | Recursion menu equations and marker reachability |
| `BasicMarkerPaths`, `SequenceMarkerPaths`, `RecursionMarkerPaths` | Marker paths through non-clock targets and menu dependencies |
| `RecursionTargetFields` | Target-menu fields under substitution |
| `RecursionStoredFields` | Stored fields under substitution |
| `RecursionFuture` | Full future-field transport and recursion correspondence |
| `EdgeFuture`, `CompletionFlag` | Future-field structure and completion flags |

## Recursion

Tagged body states represent substituted residuals. Step transport therefore
relates body transitions to transitions after substitution. Menu transport
handles source references, target references, stored fields, and sequence unions
separately.

Marker edges preserve their environments when converted to recursive backedges.
The marker invariant is environment-indexed so those edges match the semantic
unfolding steps under the same environment.
