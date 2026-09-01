import Anvilpp.PactTypes.Syntax.PactTypeFutureOffers

/-!
Boundary (outside-the-interface) algebra for `hideTypeOffers`, and the
replacement for Lemma 1: a component's local environment is determined by the
outer environment *outside the interface*, whatever the sibling offers are.
-/

namespace Pact

set_option maxHeartbeats 1000000

@[simp] theorem hideTypeOffers_union (interface : Interface)
    (left right : Finset BareMessage) :
    hideTypeOffers interface (left ∪ right) =
      hideTypeOffers interface left ∪ hideTypeOffers interface right := by
  simp [hideTypeOffers, Finset.filter_union]

@[simp] theorem hideTypeOffers_sdiff (interface : Interface)
    (left right : Finset BareMessage) :
    hideTypeOffers interface (left \ right) =
      hideTypeOffers interface left \ hideTypeOffers interface right := by
  ext action
  simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_sdiff]
  tauto

@[simp] theorem hideTypeOffers_restrictTypeOffers (interface : Interface)
    (offers : Finset BareMessage) :
    hideTypeOffers interface (restrictTypeOffers interface offers) = ∅ := by
  ext action
  simp only [hideTypeOffers, restrictTypeOffers, Finset.mem_filter,
    Finset.notMem_empty, iff_false]
  tauto

/-- Replacement for Lemma 1.  The sibling only ever contributes actions inside
the interface, so outside the interface the local environment is a function of
the outer environment alone. -/
theorem localTypeOfferEnvironment_agree_outside_interface
    {outer : TypeEnvironment} {interface : Interface} {localType : PactType}
    {sib₁ sib₂ localEnv₁ localEnv₂ : TypeEnvironment}
    {c₁ f₁ c₂ f₂ : Finset BareMessage}
    (h₁ : LocalTypeOfferEnvironment outer interface localType sib₁ c₁ f₁ localEnv₁)
    (h₂ : LocalTypeOfferEnvironment outer interface localType sib₂ c₂ f₂ localEnv₂) :
    hideTypeOffers interface localEnv₁.immediate =
        hideTypeOffers interface localEnv₂.immediate ∧
      hideTypeOffers interface localEnv₁.future =
        hideTypeOffers interface localEnv₂.future := by
  cases h₁ with
  | clock _ _ _ _ hClock₁ =>
      cases h₂ with
      | clock => exact ⟨rfl, rfl⟩
      | ordinary _ _ _ _ _ _ hClock₂ => simp_all
  | ordinary _ _ _ _ _ _ hClock₁ _ _ hImm₁ hFut₁ =>
      cases h₂ with
      | clock _ _ _ _ hClock₂ => simp_all
      | ordinary _ _ _ _ _ _ _ _ _ hImm₂ hFut₂ =>
          rw [hFut₁, hFut₂, hImm₁, hImm₂]
          simp

/-! ### Hiding a union of interfaces, and commuting with projection -/

theorem hideTypeOffers_union_interface (H interface : Interface)
    (offers : Finset BareMessage) :
    hideTypeOffers (H ∪ interface) offers =
      hideTypeOffers interface (hideTypeOffers H offers) := by
  ext action
  simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union]
  tauto

theorem hideTypeOffers_restrict_union (H interface : Interface)
    (offers : Finset BareMessage) :
    hideTypeOffers (H ∪ interface) (restrictTypeOffers interface offers) = ∅ := by
  ext action
  simp only [hideTypeOffers, restrictTypeOffers, Finset.mem_filter,
    Finset.notMem_empty, iff_false, Finset.mem_union]
  tauto

theorem hideTypeOffers_project (H : Interface) (alphabet : PactTypeAlphabet)
    (offers : Finset BareMessage) :
    hideTypeOffers H (projectTypeEnvironmentOffers alphabet offers) =
      projectTypeEnvironmentOffers alphabet (hideTypeOffers H offers) := by
  ext action
  simp only [hideTypeOffers, projectTypeEnvironmentOffers, Finset.mem_filter]
  tauto

@[simp] theorem hideTypeOffers_empty_interface (offers : Finset BareMessage) :
    hideTypeOffers ∅ offers = offers := by
  ext action
  simp [hideTypeOffers]

theorem hideTypeOffers_hide_union (H interface : Interface)
    (offers : Finset BareMessage) :
    hideTypeOffers H (hideTypeOffers interface offers) =
      hideTypeOffers (H ∪ interface) offers := by
  ext action
  simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union]
  tauto

/-! ### Environments agreeing away from a hidden set -/

/-- Two environments agree away from the hidden set `H`. -/
structure EnvAgreeOutside (H : Interface) (env₁ env₂ : TypeEnvironment) : Prop where
  immediate : hideTypeOffers H env₁.immediate = hideTypeOffers H env₂.immediate
  future : hideTypeOffers H env₁.future = hideTypeOffers H env₂.future
  clock : env₁.clock = env₂.clock

theorem EnvAgreeOutside.refl (H : Interface) (env : TypeEnvironment) :
    EnvAgreeOutside H env env := ⟨rfl, rfl, rfl⟩

/-- The waiting menu is read off the future menu at the branch actions, and
`typeNeed` preserves message ids, so it agrees wherever the futures agree. -/
theorem typeWaitingOffers_agree_outside {H : Interface}
    {env₁ env₂ : TypeEnvironment}
    (hFuture : hideTypeOffers H env₁.future = hideTypeOffers H env₂.future)
    (branches : List (BareMessage × PactType)) :
    hideTypeOffers H (typeWaitingOffers env₁ branches) =
      hideTypeOffers H (typeWaitingOffers env₂ branches) := by
  have hMem : ∀ (env : TypeEnvironment) (action : BareMessage),
      action.1 ∉ H →
      (action ∈ typeWaitingOffers env branches ↔
        typeNeed action ∈ hideTypeOffers H env.future ∧
          action ∈ typeBranchActions branches) := by
    intro env action hOut
    simp only [typeWaitingOffers, Finset.mem_inter, Finset.mem_image,
      hideTypeOffers, Finset.mem_filter, typeNeed]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hAct⟩
      refine ⟨⟨?_, ?_⟩, hAct⟩
      · rcases x with ⟨msg, dir⟩
        cases dir <;> simpa [typeNeed, MessageDir.invert] using hx
      · rcases x with ⟨msg, dir⟩
        cases dir <;> simpa [typeNeed, MessageDir.invert] using hOut
    · rintro ⟨⟨hNeed, -⟩, hAct⟩
      refine ⟨⟨(action.1, action.2.invert), hNeed, ?_⟩, hAct⟩
      rcases action with ⟨msg, dir⟩
      cases dir <;> rfl
  ext action
  simp only [hideTypeOffers, Finset.mem_filter]
  constructor
  · rintro ⟨hIn, hOut⟩
    exact ⟨((hMem env₂ action hOut).mpr
      (by rw [← hFuture]; exact (hMem env₁ action hOut).mp hIn)), hOut⟩
  · rintro ⟨hIn, hOut⟩
    exact ⟨((hMem env₁ action hOut).mpr
      (by rw [hFuture]; exact (hMem env₂ action hOut).mp hIn)), hOut⟩

/-- Replacement for Lemma 1, generalised to two outer environments that agree
only away from `H`: the component environments then agree away from
`H ∪ interface`. -/
theorem localTypeOfferEnvironment_agree_of_outer_agree
    {H : Interface} {outer₁ outer₂ : TypeEnvironment} {interface : Interface}
    {localType : PactType} {sib₁ sib₂ localEnv₁ localEnv₂ : TypeEnvironment}
    {c₁ f₁ c₂ f₂ : Finset BareMessage}
    (hOuter : EnvAgreeOutside H outer₁ outer₂)
    (h₁ : LocalTypeOfferEnvironment outer₁ interface localType sib₁ c₁ f₁ localEnv₁)
    (h₂ : LocalTypeOfferEnvironment outer₂ interface localType sib₂ c₂ f₂ localEnv₂) :
    EnvAgreeOutside (H ∪ interface) localEnv₁ localEnv₂ := by
  cases h₁ with
  | clock _ _ _ _ hClock₁ =>
      cases h₂ with
      | clock => exact ⟨rfl, rfl, rfl⟩
      | ordinary _ _ _ _ _ _ hClock₂ =>
          rw [hOuter.clock, hClock₂] at hClock₁
          exact absurd hClock₁ (by simp)
  | ordinary _ _ _ _ _ _ hClock₁ _ hLocalClock₁ hImm₁ hFut₁ =>
      cases h₂ with
      | clock _ _ _ _ hClock₂ =>
          rw [hOuter.clock] at hClock₁
          rw [hClock₂] at hClock₁
          exact absurd hClock₁ (by simp)
      | ordinary _ _ _ _ _ _ _ _ hLocalClock₂ hImm₂ hFut₂ =>
          have hStep : ∀ S₁ S₂ x₁ x₂ : Finset BareMessage,
              hideTypeOffers H S₁ = hideTypeOffers H S₂ →
              hideTypeOffers (H ∪ interface)
                  (projectTypeEnvironmentOffers localType.alphabet S₁ ∪
                    restrictTypeOffers interface x₁) =
                hideTypeOffers (H ∪ interface)
                  (projectTypeEnvironmentOffers localType.alphabet S₂ ∪
                    restrictTypeOffers interface x₂) := by
            intro S₁ S₂ x₁ x₂ hEq
            simp only [hideTypeOffers_union, hideTypeOffers_restrict_union,
              hideTypeOffers_project, Finset.union_empty]
            rw [hideTypeOffers_union_interface, hideTypeOffers_union_interface,
              hEq]
          have hImmAgree :
              hideTypeOffers (H ∪ interface) localEnv₁.immediate =
                hideTypeOffers (H ∪ interface) localEnv₂.immediate := by
            rw [hImm₁, hImm₂]
            exact hStep _ _ _ _ hOuter.immediate
          refine ⟨hImmAgree, ?_, by rw [hLocalClock₁, hLocalClock₂]⟩
          rw [hFut₁, hFut₂, hideTypeOffers_sdiff, hideTypeOffers_sdiff,
            hImmAgree, hStep _ _ _ _ hOuter.future]

end Pact
