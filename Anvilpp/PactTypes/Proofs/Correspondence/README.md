# Type-Automaton Correspondence

Related type residuals and compiled states have matching decorated steps and menus.

| Module | Contents |
|---|---|
| `TypeAutoRelCore` | State/residual relation and `TypeAutomatonStepCorrespondence` |
| `Simultaneous` | Constructor induction for full step correspondence and menu agreement |
| `CasesTop` | Instantiation at the empty binder context |
| `CompileWFHelpers` | Atomic edge and menu equations |
| [Helpers](Helpers/README.md) | Structural invariants, substitution, and survivor transport |
| [Simultaneous](Simultaneous/README.md) | Constructor cases and future-field transport |
| [Cases](Cases/README.md) | Atomic step equivalences |

## Assembly

`correspondence_simultaneous` establishes:

```lean
TypeAutomatonStepCorrespondence processType ∧ FutureOffersAgree processType
```

The first component already matches both current and future offers. The second
identifies compiled menus with semantic future offers and supports the
constructor induction. Source-reading and stored future fields are handled
directly; a target-only offer law is not assumed.

`correspondence_steps` applies this result to an admissible type in the empty
binder context. `type_automaton_correspondence` adds the initial pair and its
state membership to produce the public correspondence witness.
