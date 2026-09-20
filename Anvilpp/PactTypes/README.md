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

For an admissible type, `type_automaton_correspondence` matches semantic and
compiled decorated steps in both directions. Its assembly is:

```text
type_automaton_correspondence
  correspondence_steps
    correspondence_simultaneous
```

The simultaneous induction matches environments, labels, complete offer pairs,
and related targets while proving future-menu agreement. It uses
`typeCompilationFuel`; `correspondence_steps` fixes the empty binder context.

Menu saturation follows non-clock execution targets and separate optimistic
dependencies. Those dependencies add no execution states or transitions.
Future-field transport covers stored sets, source/target references, and
sequence unions.

The [results index](../../RESULTS.md) connects correspondence to process
conformance, compatibility, and optimality. Build and audit commands are in the
[repository README](../../README.md).
