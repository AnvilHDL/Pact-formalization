import Anvilpp.ProofHelpers.Regularity

namespace Pact

noncomputable section

open Classical

/-! ## Section 7 helper-lemma scaffold

These are the named helper lemmas from `pact.pdf`, Section 7, stated against
the current Lean scaffold.  The substantial proof content is intentionally
left as redevelopment work. -/

/-- Helper Lemma H1: erasure preserves offers. -/
lemma helper_h1_erasure_preserves_offers
    {env : Environment} {process target : Proc} {label : Label}
    {current : Finset Offer} {future : Finset BareMessage}
    (hOffers : Offers env process label target current future) :
    TypeOffers (eraseEnvironment env) (inferProcess process) (eraseLabel label)
      (inferProcess target) (current.image Offer.bare) future := by
  sorry -- TODO(section7): prove by induction on `hOffers`.

/-- Helper Lemma H1: erasure preserves sibling-local environments. -/
lemma helper_h1_erasure_preserves_local_environment
    {outer siblingEnv localEnv : Environment} {interface : Interface}
    {localProc sibling : Proc} {label : Label}
    {current : Finset Offer} {future : Finset BareMessage}
    (hLocal :
      LocalEnvironment outer interface siblingEnv sibling label localEnv) :
    LocalTypeOfferEnvironment (eraseEnvironment outer) interface
      (inferProcess localProc)
      (eraseEnvironment siblingEnv) (current.image Offer.bare) future
      (eraseEnvironment localEnv) := by
  sorry -- TODO(section7): combine local-env inversion with offer erasure.

/-- Helper Lemma H2: every well-formed erased environment has a concrete
representative preserving availability. -/
lemma helper_h2_concrete_representative_of_erased_environment
    (env : TypeEnvironment) (hWellFormed : env.WellFormed) :
    ∃ concrete : Environment,
      eraseEnvironment concrete = env ∧
      concrete.available = typeAvailable env ∧
      (env = TypeEnvironment.empty → concrete = Environment.empty) := by
  sorry -- TODO(section7): choose payload representatives for erased sends.

/-- Helper Lemma H3: type strategies can be matched by process strategies
along conformance. -/
lemma helper_h3_matching_finite_strategy_histories
    {process : Proc} {processType : PactType}
    (hConforms : Conforms process processType)
    (typeStrategy : TypeStrategy) :
    ∃ processStrategy : ProcessStrategy process, True := by
  sorry -- TODO(section7): build the concretizing process strategy.

/-- Helper Lemma H4: completed process logs erase to completed type logs. -/
lemma helper_h4_completed_process_logs_erase
    {process : Proc} {processType : PactType}
    (processStrategy : ProcessStrategy process) (typeStrategy : TypeStrategy)
    {processLog : ProcessLog}
    (hCompleted : CompletedProcessLog processStrategy processLog) :
    ∃ typeLog : TypeLog,
      CompletedTypeLog processType typeStrategy typeLog ∧
      eraseProcessLog processLog = typeLog := by
  sorry -- TODO(section7): use the history matching construction of H3.

/-- Helper Lemma H5: honesty is preserved by concretization. -/
lemma helper_h5_honesty_preserved_by_concretization
    {processLog : ProcessLog} {typeLog : TypeLog}
    (hErase : eraseProcessLog processLog = typeLog)
    (hHonest : HonestTypeLog typeLog) :
    HonestProcessLog processLog := by
  sorry -- TODO(section7): use H2's availability preservation at each index.

/-- Helper Lemma H6: abstraction ignores data substitution. -/
lemma helper_h6_abstraction_expr_substitution
    (process : Proc) (name : String) (value : Bool) :
    inferProcess (Semantics.procExprReplace process name value) =
      inferProcess process := by
  sorry -- TODO(section7): structural induction on processes.

/-- Helper Lemma H6: abstraction commutes with recursive process substitution. -/
lemma helper_h6_abstraction_process_substitution
    (process replacement : Proc) (name : String) :
    inferProcess (Semantics.procReplace process name replacement) =
      (inferProcess process).replaceVar name (inferProcess replacement) := by
  sorry -- TODO(section7): structural induction with branch cases.

/-- Helper Lemma H6: abstraction reflects literal `skip`. -/
lemma helper_h6_abstraction_skip_iff (process : Proc) :
    inferProcess process = .skip (processAlphabet process) ↔ process = .skip := by
  sorry -- TODO(section7): inspect the abstraction clauses.


/-- Helper Lemma H6: abstraction preserves the selected conjunctive-offer
transformation from the process semantics.  This is the Lean counterpart of
the paper's `abs(C^P_{B,a_j}) = C^{absB(B)}_{Msg(a_j)}` obligation. -/
lemma helper_h6_abstraction_offer_transformation_preserved
    (selected : ChoiceBranch) (branches : List ChoiceBranch) :
    inferProcess
        (parallelProcessBranchesSelecting (inferBranch selected) branches) =
      parallelTypeBranchesSelecting (inferBranch selected)
        (branches.map inferBranch) := by
  sorry

-- Need to define the helper lemma h6 for offer transformation.
-- lemma helper_h6_abstraction_offer_transformation_preserved
-- For this we have to define or give name to offer transformation structure

/-- Helper Lemma H7: one process step abstracts to one type step. -/
lemma helper_h7_one_step_abstraction
    {env : Environment} {process target : Proc} {label : Label}
    (hStep : ProcessTransition env process label target) :
    TypeTransition (eraseEnvironment env) (inferProcess process)
      (eraseLabel label) (inferProcess target) := by
  sorry -- TODO(section7): induction on the process-step derivation.

/-- Helper Lemma H8: abstraction reflects readiness. -/
lemma helper_h8_abstraction_reflects_readiness
    {process : Proc} (hWF : WFProc process) {env : Environment} :
    TypeReady (eraseEnvironment env) (inferProcess process) →
      ProcessReady env process := by
  sorry -- TODO(section7): split on clock/non-clock environments.

/-- Helper Lemma H9: one-step conformance match. -/
lemma helper_h9_one_step_conformance_match
    {process process₀ process₁ : Proc} {processType type₀ : PactType}
    {env : Environment} {label : Label}
    (witness : ConformanceWitness process processType)
    (hRelated : witness.relation process₀ type₀)
    (hStep : ProcessTransition env process₀ label process₁) :
    ∃ type₁,
      TypeTransition (eraseEnvironment env) type₀ (eraseLabel label) type₁ ∧
      witness.relation process₁ type₁ := by
  exact witness.matchStep hRelated hStep

/-- Helper Lemma H10: refinement response coherence for undecorated steps. -/
lemma helper_h10_refinement_response_coherence
    {precise abstract type₀ type₀' type₁ : PactType}
    {env : TypeEnvironment} {label : TypeLabel}
    (witness : RefinementWitness precise abstract)
    (hRelated : witness.relation type₀ type₀')
    (hStep : TypeTransition env type₀ label type₁) :
    ∃ type₁',
      TypeTransition env type₀' label type₁' ∧
      witness.relation type₁ type₁' := by
  sorry -- TODO(section7): decorate the step using H17, then use response.

end

end Pact
