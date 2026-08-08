import Anvilpp.PactTypes.CorrespondenceCombinators

/-!
# Paper-aligned Pact types

Compatibility façade for the Pact type development. The implementation is
split by dependency layer:

* `Anvilpp.PactTypes.Syntax`: syntax, erasure, and operational type semantics;
* `Anvilpp.PactTypes.Automata`: finite constructor automata and compilation;
* `Anvilpp.PactTypes.CorrespondenceCore`: relation invariants and atomic cases;
* `Anvilpp.PactTypes.CorrespondenceCombinators`: choice, fair choice,
  sequencing, parallel futures, recursion, and closing correspondence lemmas.

Importing `Anvilpp.PactTypes` preserves the original public API.
-/
