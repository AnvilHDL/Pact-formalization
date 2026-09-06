# Anvilpp.PactTypes.Proofs.Correspondence.Cases

Step equivalences for the atomic constructors, each an `↔` between a
`DecoratedTypeTransition` and a `compileType … |>.HasEdge`.

| Theorem | Statement |
|---|---|
| `correspondence_skip_stepIff` | `skip`'s only step is its idle self-loop, matching its single compiled edge |
| `correspondence_message_stepIff` | a declared message either fires or waits, each matching its edge family; an undeclared message has neither |
| `correspondence_tock_stepIff` | the clock steps to `skip` on a clock environment and idles otherwise |
| `correspondence_progress_stepIff` | `progress pid` fires to `skip` |
| `correspondence_var_stepIff` | an open variable has no semantic step, and its only edge is the recursion marker, which is not public |

Used by the base cases of
[`../Simultaneous/Base.lean`](../Simultaneous/Base.lean), paired with the
corresponding `BaseGuard`. For compound constructors the same content is
supplied by helper 16.
