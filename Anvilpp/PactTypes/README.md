# Pact Types

Type semantics, finite constructor automata, and their decorated-step correspondence.

## Layout

| Directory | Contents |
|---|---|
| [Spec/Syntax](Spec/Syntax/README.md) | Types, substitution, regularity, and operational semantics |
| [Spec/Automata](Spec/Automata/README.md) | Automaton representation and constructor compiler |
| [Proofs/Syntax](Proofs/Syntax/README.md) | Substitution, regularity, and offer laws |
| [Proofs/Automata](Proofs/Automata/README.md) | Compiler structure, fuel stability, and edge properties |
| [Proofs/Correspondence](Proofs/Correspondence/README.md) | Relations between type residuals and compiled states |

## Correspondence

The public result in [PactSafety.lean](../PactSafety.lean) is:

```lean
theorem type_automaton_correspondence {processType : PactType}
    (hAdmissible : AdmissibleType processType) :
    Nonempty (TypeAutomatonCorrespondence processType (compileType processType))
```

Its assembly is:

```text
type_automaton_correspondence
  correspondence_steps
    correspondence_simultaneous
```

The simultaneous induction proves full decorated-step correspondence together
with menu agreement:

```lean
theorem correspondence_simultaneous :
    ∀ (bound : List String) (processType : PactType),
      TypeWellFormedIn bound processType →
      TypeAutomatonStepCorrespondence processType ∧
        FutureOffersAgree processType
```

Both directions match the environment, label, current offers, future offers,
and related target. Menu agreement identifies each represented state's menu
with its type residual's future offers. The induction is on
`typeCompilationFuel`; `correspondence_steps` instantiates the empty binder context.

Future fields may contain stored offers, source or target menu references,
or sequence unions. The proof transports these fields according to the
constructor; it does not assume that every future is a target menu.

Menu saturation follows non-clock execution targets and explicit menu
dependencies. The dependencies retain optimistic continuation menus without
adding execution states or transitions.

## Verification

```bash
lake build Anvilpp.PactSafety
```

```lean
import Anvilpp.PactSafety
#print axioms Pact.type_automaton_correspondence
```

The theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
