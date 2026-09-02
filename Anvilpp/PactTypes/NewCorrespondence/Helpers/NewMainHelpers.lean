import Anvilpp.PactTypes.Syntax.TypeOfferDeterminacy
import Anvilpp.PactTypes.Syntax.TypeOfferEnvironmentAgreementLemmas
import Anvilpp.PactTypes.NewCorrespondence.Helpers.EnvironmentAndAlphabet
import Anvilpp.PactTypes.NewCorrespondence.Helpers.Parallel
import Anvilpp.PactTypes.NewCorrespondence.Helpers.FutureClosure

/-!
Helper lemmas of the pen-and-paper proof of Lemma 4.5, under the names used
there.  Each entry either reuses an existing result or proves the missing one.
-/

namespace Pact

noncomputable section

/-! ### Uniform offer law -/

/-- Clock half of the uniform offer law: a clock step advertises nothing now. -/
theorem TypeOffers.current_eq_empty_of_label_tock
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future)
    (hLabel : label = TypeLabel.tock) :
    current = ∅ := by
  induction hOffers using TypeOffers.rec with
  | action => cases hLabel
  | action_wait => cases hLabel
  | choice_left => cases hLabel
  | choice_right => cases hLabel
  | fair_left => cases hLabel
  | fair_right => cases hLabel
  | cycle => rfl
  | cycle_wait => cases hLabel
  | skip => cases hLabel
  | progress => cases hLabel
  | recur => cases hLabel
  | seq _ _ _ _ _ _ _ _ _ _ hNotTock _ => exact absurd hLabel hNotTock
  | seq_tock => rfl
  | seq_fuse _ _ _ _ _ _ _ _ _ hNotTock _ => exact absurd hLabel hNotTock
  | seq_fuse_tock => rfl
  | xoffer_branch => cases hLabel
  | xoffer_else => cases hLabel
  | xoffer_wait => cases hLabel
  | offer_some => cases hLabel
  | offer_else => cases hLabel
  | offer_wait => cases hLabel
  | par outer leftEnv rightEnv interface left left' right right' leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture _ _ _ _ _ _ _
      _ ihLeft ihRight =>
      obtain ⟨hLeftTock, hRightTock⟩ :=
        (TypeLabel.combine_eq_tock_iff interface leftLabel rightLabel).mp hLabel
      rw [ihLeft hLeftTock, ihRight hRightTock]
      simp [hideTypeOffers]
  | par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNotTock _ _ =>
      exact absurd hLabel hNotTock
  | par_fuse_tock => rfl
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNotTock _ =>
      exact absurd hLabel hNotTock
  | left_complete_tock => rfl
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNotTock _ =>
      exact absurd hLabel hNotTock
  | right_complete_tock => rfl

/-- Non-clock half of the uniform offer law, in the form the case analysis
uses: a step's future is contained in the menu at its own target. -/
theorem uniform_offer_law_future_subset
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future) :
    future ⊆ typeFutureOffers target ∪ current :=
  typeOffers_future_subset_target_union_current hOffers

/-- Clock rules publish the empty pair on both components. -/
theorem uniform_offer_law_clock
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future)
    (hLabel : label = TypeLabel.tock) :
    current = ∅ ∧ future = ∅ :=
  ⟨hOffers.current_eq_empty_of_label_tock hLabel,
    hOffers.future_eq_empty_of_label_tock hLabel⟩

/-! ### Offer determinacy -/

/-- A derivable step exposes exactly one offer pair. -/
theorem offer_determinacy
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {c₁ f₁ c₂ f₂ : Finset BareMessage}
    (h₁ : TypeOffers env source label target c₁ f₁)
    (hWF : source.AlphabetWellFormed)
    (hLin : source.SameCycleMessageLinear)
    (hMsg : source.ParallelMessageOwnership)
    (hProg : source.ParallelProgressOwnership)
    (hFair : source.ParallelFairChoiceOwnership)
    (hScop : source.InterfaceScoped)
    (h₂ : TypeOffers env source label target c₂ f₂) :
    c₁ = c₂ ∧ f₁ = f₂ :=
  typeOffers_unique h₁ hWF hLin hMsg hProg hFair hScop h₂ rfl rfl rfl rfl

/-! ### Synchronization premises agree -/

/-- A component's local environment is fixed by the sibling offers it is given. -/
theorem sync_premises_determine_local_env
    {outer : TypeEnvironment} {interface : Interface} {localType : PactType}
    {sib₁ sib₂ localEnv₁ localEnv₂ : TypeEnvironment}
    {c f : Finset BareMessage}
    (h₁ : LocalTypeOfferEnvironment outer interface localType sib₁ c f localEnv₁)
    (h₂ : LocalTypeOfferEnvironment outer interface localType sib₂ c f localEnv₂) :
    localEnv₁ = localEnv₂ :=
  localTypeOfferEnvironment_unique h₁ h₂

/-- Whatever the sibling offers, a component's local environment is determined
outside the interface. -/
theorem sync_premises_agree_outside_interface
    {outer : TypeEnvironment} {interface : Interface} {localType : PactType}
    {sib₁ sib₂ localEnv₁ localEnv₂ : TypeEnvironment}
    {c₁ f₁ c₂ f₂ : Finset BareMessage}
    (h₁ : LocalTypeOfferEnvironment outer interface localType sib₁ c₁ f₁ localEnv₁)
    (h₂ : LocalTypeOfferEnvironment outer interface localType sib₂ c₂ f₂ localEnv₂) :
    hideTypeOffers interface localEnv₁.immediate =
        hideTypeOffers interface localEnv₂.immediate ∧
      hideTypeOffers interface localEnv₁.future =
        hideTypeOffers interface localEnv₂.future :=
  localTypeOfferEnvironment_agree_outside_interface h₁ h₂


/-! ### Final states represent completion -/

/-- Forward half: an accepting state represents a completed residual. -/
theorem final_state_represents_skip
    (processType : PactType) {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType processType)) residual state)
    (hAccept : state ∈ (compileType processType).accepting) :
    ∃ skipAlphabet, residual = .skip skipAlphabet := by
  obtain ⟨skipAlphabet, hSkip⟩ :=
    relationMembership_of_accepting processType hAccept
  exact ⟨skipAlphabet,
    relationMembership_functional processType (compileType processType)
      hRelated hSkip⟩


/-! ### Re-signing invariance -/

/-- Re-signing renames no state, moves no entry point and accepts the same
states.  The compilation budget is unchanged, so the same fuel suffices. -/
theorem resign_invariance
    (fuel : Nat) (processType : PactType)
    (hDisjoint : processType.OfferBranchesDisjoint)
    (alphabet : PactTypeAlphabet) :
    typeCompilationFuel (processType.reannotate alphabet) =
        typeCompilationFuel processType ∧
      (compileTypeFuel fuel (processType.reannotate alphabet)).states =
        (compileTypeFuel fuel processType).states ∧
      (compileTypeFuel fuel (processType.reannotate alphabet)).accepting =
        (compileTypeFuel fuel processType).accepting :=
  ⟨typeCompilationFuel_reannotate alphabet processType,
    (CompiledShape.compileTypeFuel_shapeEq_reannotate fuel processType hDisjoint
      alphabet).1,
    (CompiledShape.compileTypeFuel_shapeEq_reannotate fuel processType hDisjoint
      alphabet).2.2⟩

/-- Shape factorization, in the form the proof uses it: two types whose bodies
differ only in annotations compile to the same carrier and accepting set. -/
theorem shape_factorization
    (fuel : Nat) (processType : PactType)
    (hDisjoint : processType.OfferBranchesDisjoint)
    (alphabet : PactTypeAlphabet) :
    (compileTypeFuel fuel (processType.reannotate alphabet)).states =
        (compileTypeFuel fuel processType).states ∧
      (compileTypeFuel fuel (processType.reannotate alphabet)).accepting =
        (compileTypeFuel fuel processType).accepting :=
  ⟨(resign_invariance fuel processType hDisjoint alphabet).2.1,
    (resign_invariance fuel processType hDisjoint alphabet).2.2⟩


/-- Non-clock half of the uniform offer law: a non-clock step's future offer is
the menu at its own target, less what it already offers now. -/
theorem TypeOffers.future_eq_sdiff_of_label_ne_tock
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future)
    (hLabel : label ≠ TypeLabel.tock) :
    future = typeFutureOffers target \ current := by
  induction hOffers using TypeOffers.rec with
  | action => simp [typeFutureOffers, typeFutureOffersFuel]
  | action_wait => rfl
  | choice_left => simp
  | choice_right => simp
  | fair_left => simp
  | fair_right => simp
  | cycle => exact absurd rfl hLabel
  | cycle_wait => simp
  | skip => simp
  | progress => simp
  | recur => simp
  | seq => rfl
  | seq_tock => exact absurd rfl hLabel
  | seq_fuse => rfl
  | seq_fuse_tock => exact absurd rfl hLabel
  | xoffer_branch => rfl
  | xoffer_else => simp
  | xoffer_wait => rfl
  | offer_some => simp
  | offer_else => rfl
  | offer_wait => rfl
  | par _ _ _ interface _ _ _ _ leftLabel rightLabel _ _ _ _ _ _ _ _ _ _ _ _ =>
      simp only [if_neg hLabel]
  | par_fuse _ _ _ _ _ _ _ _ _ _ _ _ hLeft hRight _ _ _ _ _ _ =>
      rw [hLeft.future_eq_empty_of_target_skip rfl,
        hRight.future_eq_empty_of_target_skip rfl]
      simp [hideTypeOffers, typeFutureOffers, typeFutureOffersFuel]
  | par_fuse_tock => simp_all
  | left_complete => rfl
  | left_complete_tock => exact absurd (by assumption) hLabel
  | right_complete => rfl
  | right_complete_tock => exact absurd (by assumption) hLabel

end

end Pact
