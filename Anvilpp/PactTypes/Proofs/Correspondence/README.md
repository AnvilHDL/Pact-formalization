# Anvilpp.PactTypes.Proofs.Correspondence

Lemma 4.5.

| Module | Contents |
|---|---|
| `TypeAutoRelCore` | the correspondence relation: `buildRelationSet`, `relationMembership`, `buildRelationSet_initial` (the seed pair `(τ, i_τ)`), and `TypeAutomatonStepCorrespondence` |
| `Simultaneous` | `correspondence_simultaneous` — helpers 16 and 17, by strong induction on `typeCompilationFuel`; also the parallel menu clause |
| `CasesTop` | `correspondence_steps`, instantiating the above at `Γ = ∅` |
| `CompileWFHelpers` | edge and menu equations for the atomic constructors |

| Subdirectory | Files | Lines | Role |
|---|---:|---:|---|
| [`Helpers/`](Helpers/README.md) | 23 | 21,576 | helpers 1–15 |
| [`Simultaneous/`](Simultaneous/README.md) | 14 | 11,927 | constructor cases of helpers 16–17 |
| [`Cases/`](Cases/README.md) | 1 | 591 | atomic step equivalences |

## Assembly

```lean
theorem correspondence_steps_of_helpers (processType : PactType)
    (hCurrent : CurrentOfferCorrespondence processType)
    (hMenus   : FutureOffersAgree processType) :
    TypeAutomatonStepCorrespondence processType
```

Both directions come from the same two hypotheses.
`hCurrent.forward_with_future hMenus` takes a semantic step to a matching edge:
helper 16 supplies the edge and its current offer, helper 17 identifies the
future offer at the target. `hCurrent.backward_with_future hMenus` recovers the
semantic offer pair from an edge the same way.
