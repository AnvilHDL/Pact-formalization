import Anvilpp.PactTypes.Syntax.PactTypeFutureOffersDefs

/-!
# Offers versus declared alphabets

Two alphabet facts about decorated type steps.

`typeOffers_current_subset_alphabet` says the current offers of a decorated step
are declared by the source's own alphabet.  Every rule with a nonempty current
offer carries the membership as a premise, inherits it from the left of a
sequence, or hides the union of the two children's offers at a parallel node,
whose alphabet is `PactTypeAlphabet.mergeHidden` of the children's.

`complement_declared_of_offered` says an interface action declared by one side of
a parallel node has its complement declared by the other side.  The Lean
`PactTypeAlphabet.ComplementaryOn` records the paper's interface complementarity
as a per-message disjunction rather than as an equation between the restricted
alphabets, so the polarity is pinned by `PactTypeAlphabet.WellFormed` on the side
that declares the action.  Only that side's well-formedness is consumed; the
`left.WellFormed` argument is kept in the signature for symmetry and is named
`_hOne` so it is not reported as unused.
-/

namespace Pact

set_option maxHeartbeats 1000000

/-- Branch heads of an offer are declared by the offer's alphabet. -/
private theorem typeBranchActions_subset_declared
    {alphabet : PactTypeAlphabet} {branches : List (BareMessage × PactType)}
    (hActions : ∀ b ∈ branches, b.1 ∈ alphabet.actions) :
    typeBranchActions branches ⊆ alphabet.actions := by
  intro action hAction
  simp only [typeBranchActions, List.mem_toFinset, List.mem_map] at hAction
  obtain ⟨branch, hBranch, rfl⟩ := hAction
  exact hActions branch hBranch

/-- Waiting offers are branch heads, hence declared by the offer's alphabet. -/
private theorem typeWaitingOffers_subset_declared
    {alphabet : PactTypeAlphabet} {env : TypeEnvironment}
    {branches : List (BareMessage × PactType)}
    (hActions : ∀ b ∈ branches, b.1 ∈ alphabet.actions) :
    typeWaitingOffers env branches ⊆ alphabet.actions := by
  intro action hAction
  simp only [typeWaitingOffers, Finset.mem_inter] at hAction
  exact typeBranchActions_subset_declared hActions hAction.2

/-- A non-interface action declared by either child is declared by the merged
parallel alphabet. -/
private theorem mem_mergeHidden_actions
    {left right : PactTypeAlphabet} {interface : Interface}
    {action : BareMessage}
    (hMem : action ∈ left.actions ∨ action ∈ right.actions)
    (hHidden : action.1 ∉ interface) :
    action ∈ (PactTypeAlphabet.mergeHidden left right interface).actions := by
  simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter, Finset.mem_union]
  exact ⟨hMem, hHidden⟩

/-- The current offers of a decorated step are declared by the source's fixed
alphabet. -/
theorem typeOffers_current_subset_alphabet
    {env : TypeEnvironment} {rho : PactType} {label : TypeLabel}
    {rho' : PactType} {current future : Finset BareMessage}
    (hWF : rho.AlphabetWellFormed)
    (h : TypeOffers env rho label rho' current future) :
    current ⊆ rho.alphabet.actions := by
  induction h with
  | action _ alphabet msg dir _ hMem =>
      simp only [PactType.alphabet]
      exact Finset.singleton_subset_iff.mpr hMem
  | action_wait _ alphabet msg dir _ hMem =>
      simp only [PactType.alphabet]
      exact Finset.singleton_subset_iff.mpr hMem
  | choice_left => exact Finset.empty_subset _
  | choice_right => exact Finset.empty_subset _
  | fair_left => exact Finset.empty_subset _
  | fair_right => exact Finset.empty_subset _
  | cycle => exact Finset.empty_subset _
  | cycle_wait => exact Finset.empty_subset _
  | skip => exact Finset.empty_subset _
  | progress => exact Finset.empty_subset _
  | recur => exact Finset.empty_subset _
  | seq _ alphabet left left' right lbl cur childFuture _ _ _ ih =>
      simp only [PactType.AlphabetWellFormed] at hWF
      have hSub := ih hWF.2.2.2.1
      rw [hWF.2.1] at hSub
      simpa [PactType.alphabet] using hSub
  | seq_tock => exact Finset.empty_subset _
  | seq_fuse _ alphabet skipAlphabet left right lbl cur childFuture _ _ ih =>
      simp only [PactType.AlphabetWellFormed] at hWF
      have hSub := ih hWF.2.2.2.1
      rw [hWF.2.1] at hSub
      simpa [PactType.alphabet] using hSub
  | seq_fuse_tock => exact Finset.empty_subset _
  | xoffer_branch _ alphabet elseType branches action processType conds hActions =>
      simp only [PactType.alphabet]
      exact Finset.singleton_subset_iff.mpr
        (hActions (action, processType) conds.2.1)
  | xoffer_else => exact Finset.empty_subset _
  | xoffer_wait _ alphabet elseType branches _ hActions =>
      simp only [PactType.alphabet]
      exact typeWaitingOffers_subset_declared hActions
  | offer_some => exact Finset.empty_subset _
  | offer_else _ alphabet elseType branches _ hActions =>
      simp only [PactType.alphabet]
      exact typeBranchActions_subset_declared hActions
  | offer_wait _ alphabet elseType branches _ hActions =>
      simp only [PactType.alphabet]
      exact typeBranchActions_subset_declared hActions
  | par outer leftEnv rightEnv interface alphabet left left' right right' leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture _ _ _ _ _ _ _ _
      ihLeft ihRight =>
      simp only [PactType.AlphabetWellFormed] at hWF
      have hL := ihLeft hWF.2.2.1
      have hR := ihRight hWF.2.2.2
      intro a ha
      simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union] at ha
      simp only [PactType.alphabet]
      exact mem_mergeHidden_actions (ha.1.imp (fun hx => hL hx) (fun hx => hR hx))
        ha.2
  | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture _ _ _ _ _ _ ihLeft ihRight =>
      simp only [PactType.AlphabetWellFormed] at hWF
      have hL := ihLeft hWF.2.2.1
      have hR := ihRight hWF.2.2.2
      intro a ha
      simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union] at ha
      simp only [PactType.alphabet]
      exact mem_mergeHidden_actions (ha.1.imp (fun hx => hL hx) (fun hx => hR hx))
        ha.2
  | par_fuse_tock => exact Finset.empty_subset _
  | left_complete outer rightEnv interface alphabet left right right' rightLabel
      rightCurrent rightFuture _ _ _ _ _ _ _ _ _ ih =>
      simp only [PactType.AlphabetWellFormed] at hWF
      have hR := ih hWF.2.2.2
      intro a ha
      simp only [hideTypeOffers, Finset.mem_filter] at ha
      simp only [PactType.alphabet]
      exact mem_mergeHidden_actions (Or.inr (hR ha.1)) ha.2
  | left_complete_tock => exact Finset.empty_subset _
  | right_complete outer leftEnv interface alphabet left left' right leftLabel
      leftCurrent leftFuture _ _ _ _ _ _ _ _ _ ih =>
      simp only [PactType.AlphabetWellFormed] at hWF
      have hL := ih hWF.2.2.1
      intro a ha
      simp only [hideTypeOffers, Finset.mem_filter] at ha
      simp only [PactType.alphabet]
      exact mem_mergeHidden_actions (Or.inl (hL ha.1)) ha.2
  | right_complete_tock => exact Finset.empty_subset _

/-- An interface action declared by one side of a parallel node has its
complement declared by the other side. -/
theorem complement_declared_of_offered
    {left right : PactTypeAlphabet} {interface : Interface}
    {action : BareMessage}
    (hComp : PactTypeAlphabet.ComplementaryOn left right interface)
    (_hOne : left.WellFormed) (hOneR : right.WellFormed)
    (hMem : action ∈ right.actions) (hIface : action.1 ∈ interface) :
    typeNeed action ∈ left.actions := by
  obtain ⟨msg, dir⟩ := action
  have hPolarity : right.OnePolarity := hOneR
  rcases hComp msg hIface with ⟨hLeftSend, hRightRecv⟩ | ⟨hLeftRecv, hRightSend⟩
  · cases dir with
    | send => exact absurd ⟨hMem, hRightRecv⟩ (hPolarity msg)
    | recv => exact hLeftSend
  · cases dir with
    | send => exact hLeftRecv
    | recv => exact absurd ⟨hRightSend, hMem⟩ (hPolarity msg)

end Pact
