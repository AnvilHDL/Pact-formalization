# Anvilpp.PactTypes

Lemma 4.5, the type–automaton correspondence: an operational type and its
compiled automaton take exactly the same decorated steps.

```lean
theorem type_automaton_correspondence {processType : PactType}
    (hAdmissible : AdmissibleType processType) :
    Nonempty (TypeAutomatonCorrespondence processType (compileType processType))
```

The statement is in `Anvilpp/PactSafety.lean`; everything here supports it.

## Layout

```text
Spec/     Syntax/     type language, semantics, regularity predicates
          Automata/   automaton representation, constructor compiler
Proofs/   Syntax/     laws of the type language
          Automata/   laws of the compiler
          Correspondence/  Lemma 4.5
                      Helpers/       helpers 1–15
                      Simultaneous/  helpers 16–17, one file per constructor
                      Cases/         atomic step equivalences
```

`Spec/` holds the definitions the paper gives. Names introduced only to state
a proof obligation live with their proofs.

## The proof

```text
type_automaton_correspondence      PactSafety.lean
  correspondence_steps             Proofs/Correspondence/CasesTop.lean
    correspondence_simultaneous    Proofs/Correspondence/Simultaneous.lean
```

`correspondence_simultaneous` proves helpers 16 and 17 together, by strong
induction on `typeCompilationFuel`:

```lean
theorem correspondence_simultaneous :
    ∀ (bound : List String) (processType : PactType),
      TypeWellFormedIn bound processType →
      CurrentOfferCorrespondence processType ∧ FutureOffersAgree processType
```

`correspondence_steps` instantiates it at `Γ = ∅`. Both directions of the
correspondence follow from those two helpers alone: helper 16 matches a step
with an edge carrying the same *current* offer, and helper 17 identifies the
*future* offer at the target. The uniform offer law
(`TypeOffers.future_eq_sdiff_of_label_ne_tock`) lets the future offer be
recomputed at the target rather than transported, which is why no third helper
is needed.

## Paper helpers in Lean

| # | Paper | Lean |
|---|---|---|
| 1 | `type-step-alphabet-preservation` | `TypeOffers.preserves_alphabet` |
| 5 | `dead-declarations-inert` | `liveEq_preserves_futOff` |
| 6 | `represented-alphabet` | `relationMembership_alphabet_eq` |
| 7 | `survivor-entry` | `survivorTransport_all` |
| 9 | `compiled-state-shape` | `relationMembership_*_cases` |
| 10 | `final-states-completion` | `final_states_completion` |
| 11 | `uniform-offer-law` | `TypeOffers.future_eq_sdiff_of_label_ne_tock` |
| 12 | `recursion-substitution-transport` | `TypeOffers.replaceVar_tail`, `..._tail_inv` |
| 15 | `recursion-marker-invariant` | `markerSourceFor_of_var_residual` |
| 16 | `current-offer-correspondence` | `correspondence_simultaneous`, first component |
| 17 | `future-offers-agree` | `correspondence_simultaneous`, second component |

Helpers 13 and 18 are deferred in the paper and are not mechanised.

## Size

| | Files | Lines | Defs | Theorems |
|---|---:|---:|---:|---:|
| `Spec/Syntax` | 13 | 2,586 | 153 | 8 |
| `Spec/Automata` | 13 | 1,977 | 96 | 1 |
| `Proofs/Syntax` | 14 | 5,897 | 0 | 117 |
| `Proofs/Automata` | 14 | 6,479 | 11 | 171 |
| `Proofs/Correspondence` | 42 | 37,084 | 44 | 651 |

## Verification

```bash
lake build
```

```lean
#print axioms Pact.type_automaton_correspondence
-- [propext, Classical.choice, Quot.sound]
```
