# Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous

The constructor cases of helpers 16 and 17, which
[`../Simultaneous.lean`](../Simultaneous.lean) combines by strong induction on
`typeCompilationFuel`.

`Base.lean` states the two obligations:

```lean
def CurrentOfferCorrespondence (processType : PactType) : Prop   -- helper 16
def FutureOffersAgree         (processType : PactType) : Prop   -- helper 17
```

Helper 16 is a two-way step/edge correspondence carrying the current offer;
helper 17 is the menu equation `OF(q) = FutOff(ρ)`.

## Cases

| Constructor | Current offer | Menu |
|---|---|---|
| leaves, `choice`, `fairChoice` | `ChoiceAndSequence` | `ChoiceAndSequence` |
| `seq` | `SequenceCurrent` | `Sequence` |
| `xoffer`, `offer` | `Offers` | `Offers` |
| `par` | `Parallel` | `../Simultaneous.lean` |
| `recur` | `Recursion` | `RecursionMenus`, `MarkerCorrespondence` |

## Modules

| Module | Lines | Contents |
|---|---:|---|
| `Base` | 2,068 | the two obligations, base-fragment guards, `EdgeLocalAt`, `relationMembership_state_mem` |
| `Recursion` | 2,609 | helper 12 both directions (`TypeOffers.replaceVar_tail`, `..._tail_inv`), the environment-indexed `markerSourceFor_of_var_residual`, `currentOfferCorrespondence_recur_of_typeWF` |
| `Offers` | 2,518 | exclusive and conjunctive offer graphs; `edgeLocal_xoffer`, `edgeLocal_offer` |
| `Parallel` | 1,293 | product step inversion, `localEnvironment_iff`, `sync_of_local`, `skip_step_offers` |
| `ChoiceAndSequence` | 1,053 | `currentOfferCorrespondence_choice`, `_seq`, `futureOffersAgree_choice` |
| `BasicMarkerPaths`, `SequenceMarkerPaths`, `RecursionMarkerPaths` | 1,292 | when a compiled state reaches an `X`-marker through non-clock edges and menu dependencies |
| `MarkerCorrespondence` | 143 | `markerReachable_iff_menuReachesVar_recur`, tying those paths to the syntactic test |
| `RecursionMenus` | 279 | `computeFutureOf_recur_child_split`, `compiledMenuGraph_recur` |
| `EdgeFuture`, `CompletionFlag` | 408 | `FutureRemoval` and the backward completion flag |

## Note on recursion

Helper 12 transports a step through `ρ[X↦S]` by case analysis on `ρ`, without
induction: `TailOccurrences` makes every non-tail child inert, and
`preserves_tailOccurrences` makes the step's target inert with it.

The marker invariant must be environment-indexed here, because
`buildRecursionAutomaton` copies a marker edge's environment onto the backedge
it installs, so the semantic step's own `E` has to be matched.
