import Anvilpp.PactTypes.Correspondence.CorrespondenceAssembly

/-!
# Paper-aligned Pact types

Compatibility façade for the Pact type development. The implementation is
split by dependency layer:

* `Anvilpp.PactTypes.PactType*` / `TypeErasure` / `TypeDynamicsCore` /
  `TypeCompletionFuel` / `TypeFutureOffersFuel` / `TypeTransitionSystem`:
  syntax, erasure, and operational type semantics (formerly one `Syntax.lean`,
  split by concern — see the README);
* `Anvilpp.PactTypes.Automata`: finite constructor automata and compilation;
* `Anvilpp.PactTypes.CorrespondenceCore`: relation invariants and atomic cases;
* `Anvilpp.PactTypes.Correspondence*`: choice, fair choice, sequencing,
  parallel futures, recursion, and closing correspondence lemmas, split by
  concern across many files — see `Anvilpp/PactTypes/README.md` for the
  layout and the dependency chain between them.

Importing `Anvilpp.PactTypes` preserves the original public API.
-/
