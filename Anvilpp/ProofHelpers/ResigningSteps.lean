import Anvilpp.ProofHelpers.Resigning

namespace Pact

noncomputable section

open Classical

/-! ## Structural side conditions carried along the re-signing induction

The properties the source of a re-signed step must have: `AlphaWF`,
`IfaceScoped` with its alphabet companion, `TailRec`, and distinct
conjunctive heads.  Re-signing and a step both preserve them. -/

structure ResignRegular (processType : PactType) : Prop where
  alphabetWellFormed : processType.AlphabetWellFormed
  interfaceScoped : processType.InterfaceScoped
  interfaceAlphabetScoped : processType.InterfaceAlphabetScoped
  tailRecursive : processType.TailRecursive
  tailClosed : processType.TailClosed
  conjunctive : processType.ConjunctiveMessageOwnership

namespace ResignRegular

lemma choice_left {alphabet : PactTypeAlphabet} {left right : PactType}
    (h : ResignRegular (.choice alphabet left right)) : ResignRegular left := by
  obtain ⟨hA, hS, hAS, hT, hTC, hC⟩ := h
  simp only [PactType.AlphabetWellFormed, PactType.InterfaceScoped,
    PactType.InterfaceAlphabetScoped, PactType.TailRecursive,
    PactType.ConjunctiveMessageOwnership] at hA hS hAS hT hC
  exact ⟨hA.2.2.2.1, hS.1, hAS.2.1, hT.1, fun other => by
    have := hTC other; simp only [PactType.TailOccurrences] at this; exact this.1,
    hC.1⟩

lemma choice_right {alphabet : PactTypeAlphabet} {left right : PactType}
    (h : ResignRegular (.choice alphabet left right)) : ResignRegular right := by
  obtain ⟨hA, hS, hAS, hT, hTC, hC⟩ := h
  simp only [PactType.AlphabetWellFormed, PactType.InterfaceScoped,
    PactType.InterfaceAlphabetScoped, PactType.TailRecursive,
    PactType.ConjunctiveMessageOwnership] at hA hS hAS hT hC
  exact ⟨hA.2.2.2.2, hS.2, hAS.2.2, hT.2, fun other => by
    have := hTC other; simp only [PactType.TailOccurrences] at this; exact this.2,
    hC.2⟩

lemma fair_left {alphabet : PactTypeAlphabet} {bid : BranchId}
    {left right : PactType}
    (h : ResignRegular (.fairChoice alphabet bid left right)) :
    ResignRegular left := by
  obtain ⟨hA, hS, hAS, hT, hTC, hC⟩ := h
  simp only [PactType.AlphabetWellFormed, PactType.InterfaceScoped,
    PactType.InterfaceAlphabetScoped, PactType.TailRecursive,
    PactType.ConjunctiveMessageOwnership] at hA hS hAS hT hC
  exact ⟨hA.2.2.2.1, hS.1, hAS.2.1, hT.1, fun other => by
    have := hTC other; simp only [PactType.TailOccurrences] at this; exact this.1,
    hC.1⟩

lemma fair_right {alphabet : PactTypeAlphabet} {bid : BranchId}
    {left right : PactType}
    (h : ResignRegular (.fairChoice alphabet bid left right)) :
    ResignRegular right := by
  obtain ⟨hA, hS, hAS, hT, hTC, hC⟩ := h
  simp only [PactType.AlphabetWellFormed, PactType.InterfaceScoped,
    PactType.InterfaceAlphabetScoped, PactType.TailRecursive,
    PactType.ConjunctiveMessageOwnership] at hA hS hAS hT hC
  exact ⟨hA.2.2.2.2, hS.2, hAS.2.2, hT.2, fun other => by
    have := hTC other; simp only [PactType.TailOccurrences] at this; exact this.2,
    hC.2⟩

lemma seq_left {alphabet : PactTypeAlphabet} {left right : PactType}
    (h : ResignRegular (.seq alphabet left right)) : ResignRegular left := by
  obtain ⟨hA, hS, hAS, hT, hTC, hC⟩ := h
  simp only [PactType.AlphabetWellFormed, PactType.InterfaceScoped,
    PactType.InterfaceAlphabetScoped, PactType.TailRecursive,
    PactType.ConjunctiveMessageOwnership] at hA hS hAS hT hC
  exact ⟨hA.2.2.2.1, hS.1, hAS.2.1, hT.1, fun other => by
    have := hTC other
    simp only [PactType.TailOccurrences] at this
    exact PactType.tailOccurrences_mono other False.elim left this.1, hC.1⟩

lemma seq_right {alphabet : PactTypeAlphabet} {left right : PactType}
    (h : ResignRegular (.seq alphabet left right)) : ResignRegular right := by
  obtain ⟨hA, hS, hAS, hT, hTC, hC⟩ := h
  simp only [PactType.AlphabetWellFormed, PactType.InterfaceScoped,
    PactType.InterfaceAlphabetScoped, PactType.TailRecursive,
    PactType.ConjunctiveMessageOwnership] at hA hS hAS hT hC
  exact ⟨hA.2.2.2.2, hS.2, hAS.2.2, hT.2, fun other => by
    have := hTC other; simp only [PactType.TailOccurrences] at this; exact this.2,
    hC.2⟩

lemma par_left {alphabet : PactTypeAlphabet} {left right : PactType}
    {interface : Interface}
    (h : ResignRegular (.par alphabet left right interface)) :
    ResignRegular left := by
  obtain ⟨hA, hS, hAS, hT, hTC, hC⟩ := h
  simp only [PactType.AlphabetWellFormed, PactType.InterfaceScoped,
    PactType.InterfaceAlphabetScoped, PactType.TailRecursive,
    PactType.ConjunctiveMessageOwnership] at hA hS hAS hT hC
  exact ⟨hA.2.2.1, hS.2.1, hAS.2.1, hT.1, fun other => by
    have := hTC other
    simp only [PactType.TailOccurrences] at this
    exact PactType.tailOccurrences_mono other False.elim left this.1, hC.1⟩

lemma par_right {alphabet : PactTypeAlphabet} {left right : PactType}
    {interface : Interface}
    (h : ResignRegular (.par alphabet left right interface)) :
    ResignRegular right := by
  obtain ⟨hA, hS, hAS, hT, hTC, hC⟩ := h
  simp only [PactType.AlphabetWellFormed, PactType.InterfaceScoped,
    PactType.InterfaceAlphabetScoped, PactType.TailRecursive,
    PactType.ConjunctiveMessageOwnership] at hA hS hAS hT hC
  exact ⟨hA.2.2.2, hS.2.2, hAS.2.2, hT.2, fun other => by
    have := hTC other
    simp only [PactType.TailOccurrences] at this
    exact PactType.tailOccurrences_mono other False.elim right this.2, hC.2⟩

lemma recur_body {alphabet : PactTypeAlphabet} {name : String} {body : PactType}
    (h : ResignRegular (.recur alphabet name body)) : ResignRegular body := by
  obtain ⟨hA, hS, hAS, hT, hTC, hC⟩ := h
  simp only [PactType.AlphabetWellFormed, PactType.InterfaceScoped,
    PactType.InterfaceAlphabetScoped, PactType.TailRecursive,
    PactType.ConjunctiveMessageOwnership] at hA hS hAS hT hC
  refine ⟨hA.2.2, hS, hAS.2, hT.2, fun other => ?_, hC⟩
  by_cases hName : name = other
  · subst hName; exact hT.1
  · have := hTC other
    simp only [PactType.TailOccurrences, if_neg hName] at this
    exact this

lemma xoffer_else {alphabet : PactTypeAlphabet} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    (h : ResignRegular (.xoffer alphabet elseType branches)) :
    ResignRegular elseType := by
  obtain ⟨hA, hS, hAS, hT, hTC, hC⟩ := h
  simp only [PactType.AlphabetWellFormed, PactType.InterfaceScoped,
    PactType.InterfaceAlphabetScoped, PactType.TailRecursive,
    PactType.ConjunctiveMessageOwnership] at hA hS hAS hT hC
  exact ⟨hA.2.2.1, hS.1, hAS.2.1, hT.1, fun other => by
    have := hTC other; simp only [PactType.TailOccurrences] at this; exact this.1,
    hC.1⟩

lemma offer_else {alphabet : PactTypeAlphabet} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    (h : ResignRegular (.offer alphabet elseType branches)) :
    ResignRegular elseType := by
  obtain ⟨hA, hS, hAS, hT, hTC, hC⟩ := h
  simp only [PactType.AlphabetWellFormed, PactType.InterfaceScoped,
    PactType.InterfaceAlphabetScoped, PactType.TailRecursive,
    PactType.ConjunctiveMessageOwnership] at hA hS hAS hT hC
  exact ⟨hA.2.2.1, hS.1, hAS.2.1, hT.1, fun other => by
    have := hTC other; simp only [PactType.TailOccurrences] at this; exact this.1,
    hC.1⟩

end ResignRegular

/-! ### Branch lists -/

lemma interfaceAlphabetScoped_of_mem_branches
    {branches : List (BareMessage × PactType)}
    (h : PactType.InterfaceAlphabetScopedBranches branches) :
    ∀ b ∈ branches, b.2.InterfaceAlphabetScoped := by
  induction branches with
  | nil => intro b hb; cases hb
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      simp only [PactType.InterfaceAlphabetScopedBranches] at h
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hTail
      · exact h.1
      · exact ih h.2 b hTail

lemma tailOccurrences_of_mem_branches {name : String} {tail : Prop}
    {branches : List (BareMessage × PactType)}
    (h : PactType.TailBranchOccurrences name tail branches) :
    ∀ branch ∈ branches, branch.2.TailOccurrences name tail := by
  induction branches with
  | nil => intro branch hMem; cases hMem
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      simp only [PactType.TailBranchOccurrences] at h
      intro branch hMem
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact h.1
      · exact ih h.2 branch hRest

lemma conjunctive_of_mem_bodies {branches : List (BareMessage × PactType)}
    (h : PactType.ConjunctiveMessageOwnershipBodies branches) :
    ∀ b ∈ branches, b.2.ConjunctiveMessageOwnership := by
  induction branches with
  | nil => intro b hb; cases hb
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      simp only [PactType.ConjunctiveMessageOwnershipBodies] at h
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hTail
      · exact h.1
      · exact ih h.2 b hTail

lemma conjunctive_of_mem_branches {branches : List (BareMessage × PactType)}
    (h : PactType.ConjunctiveMessageOwnershipBranches branches) :
    ∀ b ∈ branches, b.2.ConjunctiveMessageOwnership := by
  induction branches with
  | nil => intro b hb; cases hb
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      simp only [PactType.ConjunctiveMessageOwnershipBranches] at h
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hTail
      · exact h.1
      · exact ih h.2.2 b hTail

namespace ResignRegular

lemma xoffer_branch {alphabet : PactTypeAlphabet} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    (h : ResignRegular (.xoffer alphabet elseType branches))
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    ResignRegular branch.2 ∧ branch.2.alphabet = alphabet := by
  obtain ⟨hA, hS, hAS, hT, hTC, hC⟩ := h
  simp only [PactType.AlphabetWellFormed, PactType.InterfaceScoped,
    PactType.InterfaceAlphabetScoped, PactType.TailRecursive,
    PactType.ConjunctiveMessageOwnership] at hA hS hAS hT hC
  obtain ⟨hAlpha, hWF⟩ := branchesAlphabetWellFormed_mem hA.2.2.2 branch hMem
  refine ⟨⟨hWF, interfaceScoped_of_mem_branches hS.2 branch hMem,
    interfaceAlphabetScoped_of_mem_branches hAS.2.2 branch hMem,
    tailRecursive_of_mem_branches hT.2 hMem, fun other => ?_,
    conjunctive_of_mem_bodies hC.2 branch hMem⟩, hAlpha⟩
  have := hTC other
  simp only [PactType.TailOccurrences] at this
  exact tailOccurrences_of_mem_branches this.2 branch hMem

lemma offer_branch {alphabet : PactTypeAlphabet} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    (h : ResignRegular (.offer alphabet elseType branches))
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    ResignRegular branch.2 ∧ branch.2.alphabet = alphabet := by
  obtain ⟨hA, hS, hAS, hT, hTC, hC⟩ := h
  simp only [PactType.AlphabetWellFormed, PactType.InterfaceScoped,
    PactType.InterfaceAlphabetScoped, PactType.TailRecursive,
    PactType.ConjunctiveMessageOwnership] at hA hS hAS hT hC
  obtain ⟨hAlpha, hWF⟩ := offerBranchesWellFormed_mem hA.2.2.2 branch hMem
  refine ⟨⟨hWF, interfaceScoped_of_mem_branches hS.2 branch hMem,
    interfaceAlphabetScoped_of_mem_branches hAS.2.2 branch hMem,
    tailRecursive_of_mem_branches hT.2 hMem, fun other => ?_,
    conjunctive_of_mem_branches hC.2 branch hMem⟩, hAlpha⟩
  have := hTC other
  simp only [PactType.TailOccurrences] at this
  exact PactType.tailOccurrences_mono other False.elim branch.2
    (tailOccurrences_of_mem_branches this.2 branch hMem)

/-- Distinct conjunctive heads, as the committed product needs them. -/
lemma offer_heads_pairwise {alphabet : PactTypeAlphabet} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    (h : ResignRegular (.offer alphabet elseType branches)) :
    List.Pairwise (fun x y => x.1 ≠ y.1) branches := by
  have hC := h.conjunctive
  simp only [PactType.ConjunctiveMessageOwnership] at hC
  exact branchHeadsPairwise_of_conjunctive hC.2

/-! ### Re-signing preserves the side conditions -/

lemma alphabet_wellFormed {processType : PactType} (h : ResignRegular processType) :
    processType.alphabet.WellFormed :=
  h.alphabetWellFormed.alphabet_wellFormed

/-- A subalphabet of a one-polarity alphabet is one-polarity. -/
lemma _root_.Pact.PactTypeAlphabet.wellFormed_of_subset
    {small large : PactTypeAlphabet} (hLarge : large.WellFormed)
    (hSub : small.actions ⊆ large.actions) : small.WellFormed :=
  fun msg hBoth => hLarge msg ⟨hSub hBoth.1, hSub hBoth.2⟩

lemma reannotate {processType : PactType} (h : ResignRegular processType)
    {target : PactTypeAlphabet}
    (hSub : target.actions ⊆ processType.alphabet.actions) :
    ResignRegular (processType.reannotate target) := by
  have hAvoid : ∀ action ∈ target.actions,
      action.1 ∉ PactType.ParallelInterfaces processType := fun action hAction =>
    h.interfaceAlphabetScoped.avoids action (hSub hAction)
  have hTargetWF : target.WellFormed :=
    PactTypeAlphabet.wellFormed_of_subset h.alphabet_wellFormed hSub
  exact ⟨PactType.reannotate_alphabetWellFormed_avoiding processType target
      h.alphabetWellFormed hTargetWF h.interfaceScoped hAvoid,
    PactType.reannotate_interfaceScoped processType target h.interfaceScoped,
    PactType.reannotate_interfaceAlphabetScoped processType target
      h.interfaceAlphabetScoped hAvoid,
    PactType.reannotate_tailRecursive processType target h.tailRecursive,
    fun other => PactType.reannotate_tailOccurrences other processType target True
      (h.tailClosed other),
    (PactType.reannotate_conjunctiveMessageOwnership processType target).2
      h.conjunctive⟩

end ResignRegular

/-! ## Environments and the alphabet they range over -/

/-- Environment well-formedness only shrinks the menus, so it survives enlarging
the alphabet. -/
lemma TypeEnvironment.wellFormed_mono {env : TypeEnvironment}
    {small large : PactTypeAlphabet} (h : env.WellFormed small)
    (hSub : small.actions ⊆ large.actions) : env.WellFormed large := by
  have hImage : small.actions.image typeNeed ⊆ large.actions.image typeNeed :=
    Finset.image_subset_image hSub
  exact ⟨h.1, h.2.1, h.2.2.1.trans hImage, h.2.2.2.trans hImage⟩

/-- An action the environment supplies the complement of is declared. -/
lemma mem_actions_of_hasNeed {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {action : BareMessage} (hWF : env.WellFormed alphabet)
    (hNeed : env.hasNeed action) : action ∈ alphabet.actions := by
  have hMem : typeNeed action ∈ env.immediate := hNeed
  have := typeNeed_image_subset_actions hWF.2.2.1
    (Finset.mem_image.mpr ⟨typeNeed action, hMem, rfl⟩)
  simpa [typeNeed] using this

/-- The complements of the future menu are declared actions. -/
lemma future_image_subset {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    (hWF : env.WellFormed alphabet) :
    env.future.image typeNeed ⊆ alphabet.actions :=
  typeNeed_image_subset_actions hWF.2.2.2

/-! ## Offers lie in the alphabet of their source

The paper's "all component offers lie in their component alphabets, by
induction on their offer derivations". -/

/-- Hiding an interface maps the two child alphabets onto the parent. -/
lemma hideTypeOffers_union_subset {parent left right : PactTypeAlphabet}
    {interface : Interface}
    (hCompat : PactTypeAlphabet.ParallelCompatible parent left right interface)
    {leftOffers rightOffers : Finset BareMessage}
    (hLeft : leftOffers ⊆ left.actions) (hRight : rightOffers ⊆ right.actions) :
    hideTypeOffers interface (leftOffers ∪ rightOffers) ⊆ parent.actions := by
  intro action hAction
  rw [hideTypeOffers, Finset.mem_filter, Finset.mem_union] at hAction
  rcases hAction.1 with hInLeft | hInRight
  · rw [← hCompat.parent_eq_left]
    exact Finset.mem_filter.mpr ⟨hLeft hInLeft, hAction.2⟩
  · rw [← hCompat.parent_eq_right]
    exact Finset.mem_filter.mpr ⟨hRight hInRight, hAction.2⟩

theorem TypeOffers.offers_subset_alphabet
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future) :
    ResignRegular source →
      current ⊆ source.alphabet.actions ∧ future ⊆ source.alphabet.actions := by
  induction hOffers with
  | action env alphabet msg dir hPrem =>
      intro _
      simp [PactType.alphabet, typeFutureOffers, typeFutureOffersFuel]
  | action_wait env alphabet msg dir hPrem =>
      intro hRegular
      refine ⟨Finset.inter_subset_right, (Finset.sdiff_subset).trans ?_⟩
      exact typeFutureOffers_subset_alphabet _ hRegular.alphabetWellFormed
  | choice_left env alphabet left right hPrem
  | choice_right env alphabet left right hPrem =>
      intro hRegular
      exact ⟨Finset.empty_subset _,
        typeFutureOffers_subset_alphabet _ hRegular.alphabetWellFormed⟩
  | fair_left env alphabet bid left right hPrem
  | fair_right env alphabet bid left right hPrem =>
      intro hRegular
      exact ⟨Finset.empty_subset _,
        typeFutureOffers_subset_alphabet _ hRegular.alphabetWellFormed⟩
  | cycle env alphabet hPrem =>
      intro _; exact ⟨Finset.empty_subset _, Finset.empty_subset _⟩
  | cycle_wait env alphabet hPrem =>
      intro hRegular
      exact ⟨Finset.empty_subset _,
        typeFutureOffers_subset_alphabet _ hRegular.alphabetWellFormed⟩
  | skip env alphabet hPrem =>
      intro _
      simp [PactType.alphabet, typeFutureOffers, typeFutureOffersFuel]
  | progress env alphabet pid hPrem =>
      intro _
      simp [PactType.alphabet, typeFutureOffers, typeFutureOffersFuel]
  | recur env alphabet name body hPrem =>
      intro hRegular
      have hA := hRegular.alphabetWellFormed
      have hT := hRegular.tailRecursive
      simp only [PactType.AlphabetWellFormed] at hA
      simp only [PactType.TailRecursive] at hT
      have hUnfoldWF : (body.replaceVar name (.recur alphabet name body)).AlphabetWellFormed :=
        PactType.replaceVar_alphabetWellFormed name hRegular.alphabetWellFormed body
          hA.2.2 (by rw [PactType.alphabet]; exact hA.2.1.symm) hT.1
      have hAlpha : (body.replaceVar name (.recur alphabet name body)).alphabet =
          alphabet := by
        rw [PactType.replaceVar_alphabet_eq_of_replacement body name
          (by rw [PactType.alphabet]; exact hA.2.1.symm)]
        exact hA.2.1
      refine ⟨Finset.empty_subset _, ?_⟩
      have := typeFutureOffers_subset_alphabet _ hUnfoldWF
      rw [hAlpha] at this
      simpa [PactType.alphabet] using this
  | seq env alphabet left left' right label current childFuture hChild hNotSkip
      hNotTock ih
  | seq_fuse env alphabet skipAlphabet left right label current childFuture
      hChild hNotTock ih =>
      intro hRegular
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      obtain ⟨hCurrent, hFuture⟩ := ih hRegular.seq_left
      rw [hA.2.1] at hCurrent hFuture
      refine ⟨by simpa [PactType.alphabet] using hCurrent, ?_⟩
      have hRight : sequenceRightMenu left right ⊆ alphabet.actions := by
        rw [sequenceRightMenu]
        split
        · have := typeFutureOffers_subset_alphabet right hA.2.2.2.2
          rwa [hA.2.2.1] at this
        · exact Finset.empty_subset _
      simp only [PactType.alphabet]
      exact (Finset.sdiff_subset).trans (Finset.union_subset hFuture hRight)
  | seq_tock env alphabet left left' right current childFuture hChild hNotSkip ih
  | seq_fuse_tock env alphabet skipAlphabet left right current childFuture
      hChild ih =>
      intro _; exact ⟨Finset.empty_subset _, Finset.empty_subset _⟩
  | xoffer_branch env alphabet elseType branches action processType hPrem =>
      intro hRegular
      refine ⟨?_, (Finset.sdiff_subset).trans
        (typeFutureOffers_subset_alphabet _ hRegular.alphabetWellFormed)⟩
      intro a ha
      rw [Finset.mem_singleton] at ha
      subst ha
      exact mem_actions_of_hasNeed hPrem.1 hPrem.2.2.1
  | xoffer_else env alphabet elseType branches hPrem =>
      intro hRegular
      exact ⟨Finset.empty_subset _, (Finset.sdiff_subset).trans
        (typeFutureOffers_subset_alphabet _ hRegular.alphabetWellFormed)⟩
  | xoffer_wait env alphabet elseType branches hPrem =>
      intro hRegular
      refine ⟨?_, (Finset.sdiff_subset).trans
        (typeFutureOffers_subset_alphabet _ hRegular.alphabetWellFormed)⟩
      exact (Finset.inter_subset_left).trans (future_image_subset hPrem.1)
  | offer_some env alphabet elseType branches enabled hPrem =>
      intro hRegular
      refine ⟨Finset.empty_subset _, ?_⟩
      rw [typeFutureOffers_parallelTypeBranchesSelecting alphabet enabled branches
        (fun b hb => (hRegular.offer_branch hb).2)
        (fun b hb => (hRegular.offer_branch hb).1.alphabetWellFormed)]
      exact Finset.inter_subset_right
  | offer_else env alphabet elseType branches hPrem =>
      intro hRegular
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      refine ⟨Finset.inter_subset_right, (Finset.sdiff_subset).trans ?_⟩
      have := typeFutureOffers_subset_alphabet elseType hA.2.2.1
      rwa [hA.2.1] at this
  | offer_wait env alphabet elseType branches hPrem =>
      intro hRegular
      exact ⟨Finset.inter_subset_right, (Finset.sdiff_subset).trans
        (typeFutureOffers_subset_alphabet _ hRegular.alphabetWellFormed)⟩
  | par outer leftEnv rightEnv interface alphabet left left' right right'
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      hLeftNotSkip hRightNotSkip hLeft hRight hNotBothSkip hLocalLeft hLocalRight
      hPrem ihLeft ihRight =>
      intro hRegular
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      obtain ⟨hLC, hLF⟩ := ihLeft hRegular.par_left
      obtain ⟨hRC, hRF⟩ := ihRight hRegular.par_right
      refine ⟨hideTypeOffers_union_subset hA.2.1 hLC hRC, ?_⟩
      split
      · exact Finset.empty_subset _
      · exact hideTypeOffers_union_subset hA.2.1 hLF hRF
  | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeft hRight
      hLocalLeft hLocalRight hPrem hNotTock ihLeft ihRight =>
      intro hRegular
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      obtain ⟨hLC, hLF⟩ := ihLeft hRegular.par_left
      obtain ⟨hRC, hRF⟩ := ihRight hRegular.par_right
      exact ⟨hideTypeOffers_union_subset hA.2.1 hLC hRC,
        hideTypeOffers_union_subset hA.2.1 hLF hRF⟩
  | par_fuse_tock outer leftEnv rightEnv interface alphabet left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeft hRight
      hLocalLeft hLocalRight hPrem hTock ihLeft ihRight =>
      intro _; exact ⟨Finset.empty_subset _, Finset.empty_subset _⟩
  | left_complete outer leftEnv rightEnv interface alphabet left right right'
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftSkip
      hRightNotSkip hLeft hRight hTargetNotSkip hLocalLeft hLocalRight hEnv hSync
      ihLeft ihRight =>
      intro hRegular
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      obtain ⟨hRC, hRF⟩ := ihRight hRegular.par_right
      have hC := hideTypeOffers_union_subset hA.2.1
        (Finset.empty_subset left.alphabet.actions) hRC
      have hF := hideTypeOffers_union_subset hA.2.1
        (Finset.empty_subset left.alphabet.actions) hRF
      rw [Finset.empty_union] at hC hF
      exact ⟨hC, hF⟩
  | right_complete outer leftEnv rightEnv interface alphabet left left' right
      leftLabel leftCurrent leftFuture rightCurrent rightFuture hRightSkip
      hLeftNotSkip hRight hLeft hTargetNotSkip hLocalLeft hLocalRight hEnv hSync
      ihRight ihLeft =>
      intro hRegular
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      obtain ⟨hLC, hLF⟩ := ihLeft hRegular.par_left
      have hC := hideTypeOffers_union_subset hA.2.1 hLC
        (Finset.empty_subset right.alphabet.actions)
      have hF := hideTypeOffers_union_subset hA.2.1 hLF
        (Finset.empty_subset right.alphabet.actions)
      rw [Finset.union_empty] at hC hF
      exact ⟨hC, hF⟩

/-! ## The step equation

`D_E(ρ[A]) = {(α, O_C ∩ A, O_F ∩ A, η[A]) | (α,O_C,O_F,η) ∈ D_E(ρ)}`, proved
as its two inclusions.  This is the forward one. -/

/-- Re-signing keeps the `skip` test, since it keeps every constructor. -/
lemma reannotate_eq_skip_iff (processType : PactType) (target : PactTypeAlphabet) :
    processType.reannotate target = .skip target ↔
      processType = .skip processType.alphabet := by
  cases processType <;> simp [PactType.reannotate, PactType.alphabet]

/-- Re-signing a `skip` type at its own alphabet. -/
lemma reannotate_skip (alphabet target : PactTypeAlphabet) :
    (PactType.skip alphabet).reannotate target = .skip target := by
  rw [PactType.reannotate]

/-- Restricting to a subalphabet absorbs the wider one. -/
lemma inter_inter_of_subset {offers : Finset BareMessage}
    {wide restrict : PactTypeAlphabet} (hSub : restrict.actions ⊆ wide.actions) :
    offers ∩ wide.actions ∩ restrict.actions = offers ∩ restrict.actions := by
  ext action
  simp only [Finset.mem_inter]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hSub h.2⟩, h.2⟩⟩

/-- Restriction distributes over the difference in the future clause. -/
lemma sdiff_inter (left right restrict : Finset BareMessage) :
    (left \ right) ∩ restrict = (left ∩ restrict) \ (right ∩ restrict) := by
  ext action
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- A menu already inside the wider alphabet is unchanged by intersecting it. -/
lemma sdiff_inter_of_subset {left right : Finset BareMessage}
    {wide restrict : PactTypeAlphabet} (hSub : restrict.actions ⊆ wide.actions) :
    (left \ (right ∩ wide.actions)) ∩ restrict.actions =
      (left ∩ restrict.actions) \ (right ∩ restrict.actions) := by
  ext action
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  have := @hSub action
  tauto

/-- Interface offers of a child survive the projection to its restricted
alphabet, so the local environment equations are unchanged. -/
lemma restrictTypeOffers_inter_projectParallel {child parent : PactTypeAlphabet}
    {interface : Interface} {offers : Finset BareMessage}
    (hOffers : offers ⊆ child.actions) :
    restrictTypeOffers interface
        (offers ∩ (PactTypeAlphabet.projectParallel parent child interface).actions) =
      restrictTypeOffers interface offers := by
  ext action
  simp only [restrictTypeOffers, Finset.mem_filter, Finset.mem_inter,
    PactTypeAlphabet.projectParallel, Finset.mem_union]
  constructor
  · rintro ⟨⟨hOffer, -⟩, hIface⟩
    exact ⟨hOffer, hIface⟩
  · rintro ⟨hOffer, hIface⟩
    exact ⟨⟨hOffer, Or.inl ⟨hOffers hOffer, hIface⟩⟩, hIface⟩

/-- Away from the interface the projected child alphabets agree with the new
boundary alphabet, so hiding publishes the restricted union. -/
lemma hideTypeOffers_inter_projectParallel {parent left right : PactTypeAlphabet}
    {interface : Interface} (leftOffers rightOffers : Finset BareMessage) :
    hideTypeOffers interface
        ((leftOffers ∩
            (PactTypeAlphabet.projectParallel parent left interface).actions) ∪
          (rightOffers ∩
            (PactTypeAlphabet.projectParallel parent right interface).actions)) =
      hideTypeOffers interface (leftOffers ∪ rightOffers) ∩ parent.actions := by
  ext action
  by_cases hIface : action.1 ∈ interface
  · simp [hideTypeOffers, Finset.mem_filter, hIface]
  · simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_inter,
      Finset.mem_union, hIface, not_false_eq_true, and_true,
      mem_projectParallel_of_not_interface hIface]
    tauto

/-! ### The local environments of a parallel node

Their boundary part lies in the restricted alphabet and their interface part is
retained by the child projection, so they remain admissible after restriction. -/

/-- Complementary interface actions of the sibling are declared by the child. -/
lemma restrictTypeOffers_subset_image
    {localAlphabet siblingAlphabet restrict : PactTypeAlphabet}
    {interface : Interface} {offers : Finset BareMessage}
    (hComplementary :
      PactTypeAlphabet.ComplementaryOn localAlphabet siblingAlphabet interface)
    (hSiblingWF : siblingAlphabet.WellFormed)
    (hOffers : offers ⊆ siblingAlphabet.actions) :
    restrictTypeOffers interface offers ⊆
      (PactTypeAlphabet.projectParallel restrict localAlphabet
        interface).actions.image typeNeed := by
  intro action hAction
  rw [restrictTypeOffers, Finset.mem_filter] at hAction
  obtain ⟨hOffer, hIface⟩ := hAction
  have hSibling : action ∈ siblingAlphabet.actions := hOffers hOffer
  have hLocal : typeNeed action ∈ localAlphabet.actions := by
    rcases hComplementary action.1 hIface with ⟨hSend, hRecv⟩ | ⟨hRecv, hSend⟩
    · cases hDir : action.2 with
      | send =>
          exact absurd ⟨by rw [← hDir]; exact hSibling, hRecv⟩ (hSiblingWF action.1)
      | recv => rw [typeNeed, hDir]; exact hSend
    · cases hDir : action.2 with
      | send => rw [typeNeed, hDir]; exact hRecv
      | recv =>
          exact absurd ⟨hSend, by rw [← hDir]; exact hSibling⟩ (hSiblingWF action.1)
  refine Finset.mem_image.mpr ⟨typeNeed action, ?_, by simp [typeNeed]⟩
  exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hLocal, hIface⟩)

lemma typeEnvironment_tock_wellFormed (alphabet : PactTypeAlphabet) :
    TypeEnvironment.tock.WellFormed alphabet := by
  refine ⟨fun _ => ⟨rfl, rfl⟩, ?_, ?_, ?_⟩ <;> simp [TypeEnvironment.tock]

lemma localTypeOfferEnvironment_wellFormed
    {outer siblingEnv localEnv : TypeEnvironment} {interface : Interface}
    {localType : PactType} {siblingCurrent siblingFuture : Finset BareMessage}
    {restrict localAlphabet siblingAlphabet : PactTypeAlphabet}
    (hLocal : LocalTypeOfferEnvironment outer interface localType siblingEnv
      siblingCurrent siblingFuture localEnv)
    (hOuter : outer.WellFormed restrict)
    (hComplementary :
      PactTypeAlphabet.ComplementaryOn localAlphabet siblingAlphabet interface)
    (hSiblingWF : siblingAlphabet.WellFormed)
    (hCurrent : siblingCurrent ⊆ siblingAlphabet.actions)
    (hFuture : siblingFuture ⊆ siblingAlphabet.actions) :
    localEnv.WellFormed
      (PactTypeAlphabet.projectParallel restrict localAlphabet interface) := by
  have hRestrict : restrict.actions ⊆
      (PactTypeAlphabet.projectParallel restrict localAlphabet interface).actions :=
    fun action hAction => Finset.mem_union_right _ hAction
  cases hLocal with
  | clock _ _ _ _ _ =>
      exact typeEnvironment_tock_wellFormed _
  | ordinary _ _ _ _ _ _ hOuterClock hSiblingClock hLocalClock hImmediate
      hFutureEq =>
      refine ⟨fun h => absurd h (by rw [hLocalClock]; simp), fun _ => ?_, ?_, ?_⟩
      · rw [hFutureEq]
        exact Finset.inter_sdiff_self _ _
      · rw [hImmediate]
        exact Finset.union_subset
          (hOuter.2.2.1.trans (Finset.image_subset_image hRestrict))
          (restrictTypeOffers_subset_image hComplementary hSiblingWF hCurrent)
      · rw [hFutureEq]
        exact (Finset.sdiff_subset).trans (Finset.union_subset
          (hOuter.2.2.2.trans (Finset.image_subset_image hRestrict))
          (restrictTypeOffers_subset_image hComplementary hSiblingWF hFuture))

/-! ## A step preserves interface scoping

The part of "type steps preserve alphabet well-formedness" that the survivor
rules need: the target is still scoped and introduces no new interface. -/

theorem TypeOffers.preserves_scoping
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future) :
    source.InterfaceScoped → source.TailRecursive →
      target.InterfaceScoped ∧
        PactType.ParallelInterfaces target ⊆
          PactType.ParallelInterfaces source := by
  induction hOffers with
  | action env alphabet msg dir hPrem
  | cycle env alphabet hPrem
  | progress env alphabet pid hPrem =>
      intro _ _
      simp [PactType.InterfaceScoped, PactType.ParallelInterfaces]
  | action_wait env alphabet msg dir hPrem
  | cycle_wait env alphabet hPrem
  | skip env alphabet hPrem
  | xoffer_wait env alphabet elseType branches hPrem
  | offer_wait env alphabet elseType branches hPrem =>
      intro hScoped _
      exact ⟨hScoped, Finset.Subset.refl _⟩
  | choice_left env alphabet left right hPrem
  | fair_left env alphabet bid left right hPrem =>
      intro hScoped _
      simp only [PactType.InterfaceScoped] at hScoped
      exact ⟨hScoped.1, by
        rw [PactType.ParallelInterfaces]
        exact Finset.subset_union_left⟩
  | choice_right env alphabet left right hPrem
  | fair_right env alphabet bid left right hPrem =>
      intro hScoped _
      simp only [PactType.InterfaceScoped] at hScoped
      exact ⟨hScoped.2, by
        rw [PactType.ParallelInterfaces]
        exact Finset.subset_union_right⟩
  | recur env alphabet name body hPrem =>
      intro hScoped hTail
      simp only [PactType.InterfaceScoped] at hScoped
      simp only [PactType.TailRecursive] at hTail
      refine ⟨PactType.replaceVar_interfaceScoped name (.recur alphabet name body)
        body hScoped hTail.1 (by simp only [PactType.InterfaceScoped]; exact hScoped), ?_⟩
      have hSub := (replaceVar_ownership_subset name (.recur alphabet name body)
        body).2.2.2.2
      simp only [PactType.ParallelInterfaces, Finset.union_self] at hSub ⊢
      exact hSub
  | seq env alphabet left left' right label current childFuture hChild hNotSkip
      hNotTock ih
  | seq_tock env alphabet left left' right current childFuture hChild hNotSkip
      ih =>
      intro hScoped hTail
      simp only [PactType.InterfaceScoped] at hScoped
      simp only [PactType.TailRecursive] at hTail
      obtain ⟨hLeftScoped, hLeftInterfaces⟩ := ih hScoped.1 hTail.1
      refine ⟨by
        simp only [PactType.InterfaceScoped]
        exact ⟨hLeftScoped, hScoped.2⟩, ?_⟩
      simp only [PactType.ParallelInterfaces]
      exact Finset.union_subset_union hLeftInterfaces (Finset.Subset.refl _)
  | seq_fuse env alphabet skipAlphabet left right label current childFuture
      hChild hNotTock ih
  | seq_fuse_tock env alphabet skipAlphabet left right current childFuture
      hChild ih =>
      intro hScoped _
      simp only [PactType.InterfaceScoped] at hScoped
      exact ⟨hScoped.2, by
        rw [PactType.ParallelInterfaces]
        exact Finset.subset_union_right⟩
  | xoffer_branch env alphabet elseType branches action processType hPrem =>
      intro hScoped _
      simp only [PactType.InterfaceScoped] at hScoped
      refine ⟨interfaceScoped_of_mem_branches hScoped.2 (action, processType)
        hPrem.2.1, ?_⟩
      rw [PactType.ParallelInterfaces]
      exact (parallelInterfaces_subset_branches branches (action, processType)
        hPrem.2.1).trans Finset.subset_union_right
  | xoffer_else env alphabet elseType branches hPrem
  | offer_else env alphabet elseType branches hPrem =>
      intro hScoped _
      simp only [PactType.InterfaceScoped] at hScoped
      exact ⟨hScoped.1, by
        rw [PactType.ParallelInterfaces]
        exact Finset.subset_union_left⟩
  | offer_some env alphabet elseType branches enabled hPrem =>
      intro hScoped _
      simp only [PactType.InterfaceScoped] at hScoped
      refine ⟨parallelTypeBranchesSelecting_interfaceScoped alphabet enabled
        branches hScoped.2, ?_⟩
      cases branches with
      | nil => cases hPrem.2.1
      | cons head tail =>
          rw [parallelTypeBranchesSelecting,
            parallelTypeBranchesSelectingWithin_parallelInterfaces,
            PactType.ParallelInterfaces]
          exact Finset.subset_union_right
  | par outer leftEnv rightEnv interface alphabet left left' right right'
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      hLeftNotSkip hRightNotSkip hLeft hRight hNotBothSkip hLocalLeft hLocalRight
      hPrem ihLeft ihRight =>
      intro hScoped hTail
      simp only [PactType.InterfaceScoped] at hScoped
      simp only [PactType.TailRecursive] at hTail
      obtain ⟨hLeftScoped, hLeftInterfaces⟩ := ihLeft hScoped.2.1 hTail.1
      obtain ⟨hRightScoped, hRightInterfaces⟩ := ihRight hScoped.2.2 hTail.2
      have hUnion : PactType.ParallelInterfaces left' ∪
          PactType.ParallelInterfaces right' ⊆
            PactType.ParallelInterfaces left ∪ PactType.ParallelInterfaces right :=
        Finset.union_subset_union hLeftInterfaces hRightInterfaces
      refine ⟨by
        simp only [PactType.InterfaceScoped]
        exact ⟨Finset.disjoint_of_subset_right hUnion hScoped.1, hLeftScoped,
          hRightScoped⟩, ?_⟩
      simp only [PactType.ParallelInterfaces]
      exact Finset.union_subset_union
        (Finset.union_subset_union (Finset.Subset.refl _) hLeftInterfaces)
        hRightInterfaces
  | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeft hRight
      hLocalLeft hLocalRight hPrem hNotTock ihLeft ihRight
  | par_fuse_tock outer leftEnv rightEnv interface alphabet left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeft hRight
      hLocalLeft hLocalRight hPrem hTock ihLeft ihRight =>
      intro _ _
      simp [PactType.InterfaceScoped, PactType.ParallelInterfaces]
  | left_complete outer leftEnv rightEnv interface alphabet left right right'
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftSkip
      hRightNotSkip hLeft hRight hTargetNotSkip hLocalLeft hLocalRight hEnv hSync
      ihLeft ihRight =>
      intro hScoped hTail
      simp only [PactType.InterfaceScoped] at hScoped
      simp only [PactType.TailRecursive] at hTail
      obtain ⟨hRightScoped, hRightInterfaces⟩ := ihRight hScoped.2.2 hTail.2
      refine ⟨PactType.reannotate_interfaceScoped right' alphabet hRightScoped, ?_⟩
      rw [PactType.reannotate_parallelInterfaces, PactType.ParallelInterfaces]
      exact hRightInterfaces.trans Finset.subset_union_right
  | right_complete outer leftEnv rightEnv interface alphabet left left' right
      leftLabel leftCurrent leftFuture rightCurrent rightFuture hRightSkip
      hLeftNotSkip hRight hLeft hTargetNotSkip hLocalLeft hLocalRight hEnv hSync
      ihRight ihLeft =>
      intro hScoped hTail
      simp only [PactType.InterfaceScoped] at hScoped
      simp only [PactType.TailRecursive] at hTail
      obtain ⟨hLeftScoped, hLeftInterfaces⟩ := ihLeft hScoped.2.1 hTail.1
      refine ⟨PactType.reannotate_interfaceScoped left' alphabet hLeftScoped, ?_⟩
      rw [PactType.reannotate_parallelInterfaces, PactType.ParallelInterfaces]
      exact hLeftInterfaces.trans
        (Finset.subset_union_right.trans Finset.subset_union_left)

/-! ## Re-signing through an intermediate alphabet

The survivor rules re-sign their target twice.  When the intermediate alphabet
declares none of the interfaces below the type, the first re-signing is
forgotten. -/

set_option maxHeartbeats 1000000 in
theorem reannotate_reannotate_of_avoiding :
    ∀ (processType : PactType) (source target : PactTypeAlphabet),
      processType.InterfaceScoped →
      (∀ action ∈ source.actions,
        action.1 ∉ PactType.ParallelInterfaces processType) →
      (processType.reannotate source).reannotate target =
        processType.reannotate target := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ source target : PactTypeAlphabet,
          PactType.InterfaceScopedBranches branches →
          (∀ action ∈ source.actions,
            action.1 ∉ PactType.ParallelBranchInterfaces branches) →
          branches.map (fun branch =>
              (branch.1, (branch.2.reannotate source).reannotate target)) =
            branches.map fun branch => (branch.1, branch.2.reannotate target) := by
        intro branches
        induction branches with
        | nil => intro _ _ _ _ _; rfl
        | cons head tail restIH =>
            intro hSizeCons source target hScoped hAvoid
            rcases head with ⟨action, body⟩
            simp only [PactType.InterfaceScopedBranches] at hScoped
            rw [PactType.ParallelBranchInterfaces] at hAvoid
            have hBodySize : sizeOf body < n := by
              have h1 : sizeOf body < sizeOf (action, body) := by simp_wf; omega
              have h2 : sizeOf (action, body) < sizeOf ((action, body) :: tail) := by
                simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have : sizeOf tail < sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            simp only [List.map_cons]
            rw [ih (sizeOf body) hBodySize body rfl source target hScoped.1
                (fun a ha hIn => hAvoid a ha (Finset.mem_union_left _ hIn)),
              restIH hTailSize source target hScoped.2
                (fun a ha hIn => hAvoid a ha (Finset.mem_union_right _ hIn))]
      intro source target hScoped hAvoid
      subst hSize
      cases processType with
      | message a m d | progress a p | tock a | skip a | var a v =>
          rw [PactType.reannotate, PactType.reannotate, PactType.reannotate]
      | recur a name body =>
          simp only [PactType.InterfaceScoped] at hScoped
          rw [PactType.ParallelInterfaces] at hAvoid
          rw [PactType.reannotate, PactType.reannotate, PactType.reannotate,
            ih (sizeOf body) (by simp_wf; omega) body rfl source target hScoped
              hAvoid]
      | choice a l r | seq a l r =>
          simp only [PactType.InterfaceScoped] at hScoped
          rw [PactType.ParallelInterfaces] at hAvoid
          rw [PactType.reannotate, PactType.reannotate, PactType.reannotate,
            ih (sizeOf l) (by simp_wf; omega) l rfl source target hScoped.1
              (fun a ha hIn => hAvoid a ha (Finset.mem_union_left _ hIn)),
            ih (sizeOf r) (by simp_wf; omega) r rfl source target hScoped.2
              (fun a ha hIn => hAvoid a ha (Finset.mem_union_right _ hIn))]
      | fairChoice a bid l r =>
          simp only [PactType.InterfaceScoped] at hScoped
          rw [PactType.ParallelInterfaces] at hAvoid
          rw [PactType.reannotate, PactType.reannotate, PactType.reannotate,
            ih (sizeOf l) (by simp_wf; omega) l rfl source target hScoped.1
              (fun a ha hIn => hAvoid a ha (Finset.mem_union_left _ hIn)),
            ih (sizeOf r) (by simp_wf; omega) r rfl source target hScoped.2
              (fun a ha hIn => hAvoid a ha (Finset.mem_union_right _ hIn))]
      | par a l r interface =>
          simp only [PactType.InterfaceScoped] at hScoped
          rw [PactType.ParallelInterfaces] at hAvoid
          have hSourceHidden : ∀ action ∈ source.actions, action.1 ∉ interface :=
            fun action hAction =>
              fun hIn => hAvoid action hAction
                (Finset.mem_union_left _ (Finset.mem_union_left _ hIn))
          have hLeftAvoid : ∀ action ∈
              (PactTypeAlphabet.projectParallel source l.alphabet interface).actions,
              action.1 ∉ PactType.ParallelInterfaces l := by
            intro action hAction
            rcases Finset.mem_union.mp hAction with hIface | hSource
            · exact fun hIn => Finset.disjoint_left.mp hScoped.1
                (Finset.mem_filter.mp hIface).2 (Finset.mem_union_left _ hIn)
            · exact fun hIn => hAvoid action hSource
                (Finset.mem_union_left _ (Finset.mem_union_right _ hIn))
          have hRightAvoid : ∀ action ∈
              (PactTypeAlphabet.projectParallel source r.alphabet interface).actions,
              action.1 ∉ PactType.ParallelInterfaces r := by
            intro action hAction
            rcases Finset.mem_union.mp hAction with hIface | hSource
            · exact fun hIn => Finset.disjoint_left.mp hScoped.1
                (Finset.mem_filter.mp hIface).2 (Finset.mem_union_right _ hIn)
            · exact fun hIn => hAvoid action hSource (Finset.mem_union_right _ hIn)
          rw [PactType.reannotate, PactType.reannotate, PactType.reannotate]
          simp only [PactType.reannotate_alphabet]
          rw [ih (sizeOf l) (by simp_wf; omega) l rfl _ _ hScoped.2.1 hLeftAvoid,
            ih (sizeOf r) (by simp_wf; omega) r rfl _ _ hScoped.2.2 hRightAvoid,
            PactTypeAlphabet.projectParallel_reannotate hSourceHidden,
            PactTypeAlphabet.projectParallel_reannotate hSourceHidden]
      | xoffer a elseType branches =>
          simp only [PactType.InterfaceScoped] at hScoped
          rw [PactType.ParallelInterfaces] at hAvoid
          rw [PactType.reannotate, PactType.reannotate, PactType.reannotate]
          simp only [PactType.reannotateBranches_map, List.map_map,
            Function.comp_def]
          rw [ih (sizeOf elseType) (by simp_wf; omega) elseType rfl source target
              hScoped.1 (fun a ha hIn => hAvoid a ha (Finset.mem_union_left _ hIn)),
            hBranches branches (by simp_wf; omega) source target hScoped.2
              (fun a ha hIn => hAvoid a ha (Finset.mem_union_right _ hIn))]
      | offer a elseType branches =>
          simp only [PactType.InterfaceScoped] at hScoped
          rw [PactType.ParallelInterfaces] at hAvoid
          rw [PactType.reannotate, PactType.reannotate, PactType.reannotate]
          simp only [PactType.reannotateOfferBranches_map, List.map_map,
            Function.comp_def]
          rw [ih (sizeOf elseType) (by simp_wf; omega) elseType rfl source target
              hScoped.1 (fun a ha hIn => hAvoid a ha (Finset.mem_union_left _ hIn)),
            hBranches branches (by simp_wf; omega) source target hScoped.2
              (fun a ha hIn => hAvoid a ha (Finset.mem_union_right _ hIn))]

/-! ## Menus under re-signing -/

/-- The optimistic completion test does not read the alphabet. -/
lemma canCompleteDeclared_reannotate (processType : PactType)
    (target : PactTypeAlphabet) :
    (processType.reannotate target).CanCompleteDeclared =
      processType.CanCompleteDeclared := by
  let fuel := max (sizeOf (processType.reannotate target)) (sizeOf processType) + 1
  rw [← typeCanCompleteThisCycleFuel_eq_canCompleteDeclared fuel _
      (by dsimp [fuel]; omega),
    ← typeCanCompleteThisCycleFuel_eq_canCompleteDeclared fuel processType
      (by dsimp [fuel]; omega),
    typeCanCompleteThisCycleFuel_reannotate]

lemma futureOffers_restrict {processType : PactType} {restrict : PactTypeAlphabet}
    (hWF : processType.AlphabetWellFormed)
    (hSub : restrict.actions ⊆ processType.alphabet.actions) :
    typeFutureOffers processType ∩ restrict.actions =
      typeFutureOffers (processType.reannotate restrict) :=
  (typeFutureOffers_reannotate processType restrict hWF hSub).symm

/-- The sequence clause's right menu is projected with everything else. -/
lemma sequenceRightMenu_reannotate {left right : PactType}
    {restrict : PactTypeAlphabet} (hWF : right.AlphabetWellFormed)
    (hSub : restrict.actions ⊆ right.alphabet.actions) :
    sequenceRightMenu (left.reannotate restrict) (right.reannotate restrict) =
      sequenceRightMenu left right ∩ restrict.actions := by
  simp only [sequenceRightMenu, canCompleteDeclared_reannotate]
  split
  · exact (futureOffers_restrict hWF hSub).symm
  · exact (Finset.empty_inter _).symm

lemma sdiff_inter_right (left right restrict : Finset BareMessage) :
    (left \ right) ∩ restrict = (left ∩ restrict) \ right := by
  ext action
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto

lemma union_sdiff_inter (childFuture rightMenu current restrict : Finset BareMessage) :
    ((childFuture ∪ rightMenu) \ current) ∩ restrict =
      ((childFuture ∩ restrict) ∪ (rightMenu ∩ restrict)) \ (current ∩ restrict) := by
  ext action
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union]
  tauto

/-- Re-signing rewrites branch bodies only, so the written heads are unchanged. -/
lemma typeBranchActions_map (restrict : PactTypeAlphabet)
    (branches : List (BareMessage × PactType)) :
    typeBranchActions
        (branches.map fun branch => (branch.1, branch.2.reannotate restrict)) =
      typeBranchActions branches := by
  simp [typeBranchActions, List.map_map, Function.comp_def]

lemma typeBranchNeeds_map (restrict : PactTypeAlphabet)
    (branches : List (BareMessage × PactType)) :
    typeBranchNeeds
        (branches.map fun branch => (branch.1, branch.2.reannotate restrict)) =
      typeBranchNeeds branches := by
  simp [typeBranchNeeds, List.map_map, Function.comp_def]

/-- Intersection distributes over the offer menu fold. -/
lemma foldl_menu_restrict (restrict : PactTypeAlphabet) :
    ∀ (branches : List (BareMessage × PactType))
      (seedResigned seed : Finset BareMessage),
      (∀ branch ∈ branches,
        typeFutureOffers (branch.2.reannotate restrict) =
          typeFutureOffers branch.2 ∩ restrict.actions) →
      seedResigned ∩ restrict.actions = seed ∩ restrict.actions →
      ((branches.map fun branch => (branch.1, branch.2.reannotate restrict)).foldl
          (fun offers branch => offers ∪ {branch.1} ∪ typeFutureOffers branch.2)
          seedResigned) ∩ restrict.actions =
        (branches.foldl
          (fun offers branch => offers ∪ {branch.1} ∪ typeFutureOffers branch.2)
          seed) ∩ restrict.actions := by
  intro branches
  induction branches with
  | nil => intro seedResigned seed _ hSeed; simpa using hSeed
  | cons branch rest ih =>
      intro seedResigned seed hAll hSeed
      simp only [List.map_cons, List.foldl_cons]
      refine ih _ _ (fun b hb => hAll b (List.mem_cons_of_mem _ hb)) ?_
      have hBranch := hAll branch (List.mem_cons_self ..)
      have hSeedPt := Finset.ext_iff.mp hSeed
      simp only [Finset.mem_inter] at hSeedPt
      rw [hBranch]
      ext action
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
      have := hSeedPt action
      tauto

lemma _root_.Pact.PactTypeAlphabet.ComplementaryOn.symm
    {left right : PactTypeAlphabet} {interface : Interface}
    (h : PactTypeAlphabet.ComplementaryOn left right interface) :
    PactTypeAlphabet.ComplementaryOn right left interface := by
  intro msg hMsg
  rcases h msg hMsg with ⟨hSend, hRecv⟩ | ⟨hRecv, hSend⟩
  · exact Or.inr ⟨hRecv, hSend⟩
  · exact Or.inl ⟨hSend, hRecv⟩

lemma reannotate_ne_skip {processType : PactType} {restrict : PactTypeAlphabet}
    (h : processType ≠ .skip processType.alphabet) :
    processType.reannotate restrict ≠
      .skip (processType.reannotate restrict).alphabet := by
  rw [PactType.reannotate_alphabet]
  exact fun hEq => h ((reannotate_eq_skip_iff processType restrict).mp hEq)

lemma reannotate_eq_skip {processType : PactType} {restrict : PactTypeAlphabet}
    (h : processType = .skip processType.alphabet) :
    processType.reannotate restrict =
      .skip (processType.reannotate restrict).alphabet := by
  rw [PactType.reannotate_alphabet]
  exact (reannotate_eq_skip_iff processType restrict).mpr h

/-- The restricted child alphabet still sits inside the child's own. -/
lemma projectParallel_subset_left {parent left right restrict : PactTypeAlphabet}
    {interface : Interface}
    (hCompat : PactTypeAlphabet.ParallelCompatible parent left right interface)
    (hSub : restrict.actions ⊆ parent.actions) :
    (PactTypeAlphabet.projectParallel restrict left interface).actions ⊆
      left.actions := by
  intro action hAction
  rcases Finset.mem_union.mp hAction with h | h
  · exact (Finset.mem_filter.mp h).1
  · exact parent_actions_subset_left hCompat (hSub h)

lemma projectParallel_subset_right {parent left right restrict : PactTypeAlphabet}
    {interface : Interface}
    (hCompat : PactTypeAlphabet.ParallelCompatible parent left right interface)
    (hSub : restrict.actions ⊆ parent.actions) :
    (PactTypeAlphabet.projectParallel restrict right interface).actions ⊆
      right.actions := by
  intro action hAction
  rcases Finset.mem_union.mp hAction with h | h
  · exact (Finset.mem_filter.mp h).1
  · exact parent_actions_subset_right hCompat (hSub h)

/-- Restricting the sibling's offers leaves the local environment equations
untouched, so the same environments serve before and after restriction. -/
lemma localTypeOfferEnvironment_restrict {outer siblingEnv localEnv : TypeEnvironment}
    {interface : Interface} {localType localType' : PactType}
    {siblingCurrent siblingFuture : Finset BareMessage}
    {sibling restrict : PactTypeAlphabet}
    (hLocal : LocalTypeOfferEnvironment outer interface localType siblingEnv
      siblingCurrent siblingFuture localEnv)
    (hCurrent : siblingCurrent ⊆ sibling.actions)
    (hFuture : siblingFuture ⊆ sibling.actions) :
    LocalTypeOfferEnvironment outer interface localType' siblingEnv
      (siblingCurrent ∩
        (PactTypeAlphabet.projectParallel restrict sibling interface).actions)
      (siblingFuture ∩
        (PactTypeAlphabet.projectParallel restrict sibling interface).actions)
      localEnv := by
  cases hLocal with
  | clock _ _ _ _ hClock => exact .clock _ _ _ _ _ hClock
  | ordinary _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
      refine .ordinary _ _ _ _ _ _ _ h1 h2 h3 ?_ ?_
      · rw [restrictTypeOffers_inter_projectParallel hCurrent]; exact h4
      · rw [restrictTypeOffers_inter_projectParallel hFuture]; exact h5

/-! ## Helper Lemma 21, second bullet: the step equation, forward inclusion -/

set_option maxHeartbeats 2000000 in
theorem typeOffers_reannotate_forward
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future) :
    ∀ restrict : PactTypeAlphabet,
      ResignRegular source →
      restrict.actions ⊆ source.alphabet.actions →
      env.WellFormed restrict →
      TypeOffers env (source.reannotate restrict) label
        (target.reannotate restrict)
        (current ∩ restrict.actions) (future ∩ restrict.actions) := by
  induction hOffers with
  | action env alphabet msg dir hPrem =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      rw [inter_inter_of_subset hSubA, typeFutureOffers_skip, Finset.empty_inter,
        ← typeFutureOffers_skip restrict]
      simp only [PactType.reannotate]
      exact TypeOffers.action env restrict msg dir ⟨hEnv, hPrem.2⟩
  | action_wait env alphabet msg dir hPrem =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      rw [inter_inter_of_subset hSubA, sdiff_inter_of_subset hSubA,
        futureOffers_restrict hRegular.alphabetWellFormed hSub]
      simp only [PactType.reannotate]
      exact TypeOffers.action_wait env restrict msg dir ⟨hEnv, hPrem.2.1, hPrem.2.2⟩
  | choice_left env alphabet left right hPrem =>
      intro restrict hRegular hSub hEnv
      rw [Finset.empty_inter,
        futureOffers_restrict hRegular.alphabetWellFormed hSub]
      simp only [PactType.reannotate]
      exact TypeOffers.choice_left env restrict _ _ ⟨hEnv, hPrem.2⟩
  | choice_right env alphabet left right hPrem =>
      intro restrict hRegular hSub hEnv
      rw [Finset.empty_inter,
        futureOffers_restrict hRegular.alphabetWellFormed hSub]
      simp only [PactType.reannotate]
      exact TypeOffers.choice_right env restrict _ _ ⟨hEnv, hPrem.2⟩
  | fair_left env alphabet bid left right hPrem =>
      intro restrict hRegular hSub hEnv
      rw [Finset.empty_inter,
        futureOffers_restrict hRegular.alphabetWellFormed hSub]
      simp only [PactType.reannotate]
      exact TypeOffers.fair_left env restrict bid _ _ ⟨hEnv, hPrem.2⟩
  | fair_right env alphabet bid left right hPrem =>
      intro restrict hRegular hSub hEnv
      rw [Finset.empty_inter,
        futureOffers_restrict hRegular.alphabetWellFormed hSub]
      simp only [PactType.reannotate]
      exact TypeOffers.fair_right env restrict bid _ _ ⟨hEnv, hPrem.2⟩
  | cycle env alphabet hPrem =>
      intro restrict hRegular hSub hEnv
      rw [Finset.empty_inter]
      simp only [PactType.reannotate]
      exact TypeOffers.cycle env restrict ⟨hEnv, hPrem.2⟩
  | cycle_wait env alphabet hPrem =>
      intro restrict hRegular hSub hEnv
      rw [Finset.empty_inter,
        futureOffers_restrict hRegular.alphabetWellFormed hSub]
      simp only [PactType.reannotate]
      exact TypeOffers.cycle_wait env restrict ⟨hEnv, hPrem.2⟩
  | skip env alphabet hPrem =>
      intro restrict hRegular hSub hEnv
      rw [Finset.empty_inter,
        futureOffers_restrict hRegular.alphabetWellFormed hSub]
      simp only [PactType.reannotate]
      exact TypeOffers.skip env restrict ⟨hEnv, hPrem.2⟩
  | progress env alphabet pid hPrem =>
      intro restrict hRegular hSub hEnv
      rw [Finset.empty_inter, typeFutureOffers_skip, Finset.empty_inter,
        ← typeFutureOffers_skip restrict]
      simp only [PactType.reannotate]
      exact TypeOffers.progress env restrict pid ⟨hEnv, hPrem.2⟩
  | recur env alphabet name body hPrem =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      have hA := hRegular.alphabetWellFormed
      have hT := hRegular.tailRecursive
      simp only [PactType.AlphabetWellFormed] at hA
      simp only [PactType.TailRecursive] at hT
      have hReplAlpha : (PactType.recur alphabet name body).alphabet =
          body.alphabet := by rw [PactType.alphabet]; exact hA.2.1.symm
      have hUnfoldWF := PactType.replaceVar_alphabetWellFormed name
        hRegular.alphabetWellFormed body hA.2.2 hReplAlpha hT.1
      have hUnfoldAlpha :
          (body.replaceVar name (.recur alphabet name body)).alphabet = alphabet := by
        rw [PactType.replaceVar_alphabet_eq_of_replacement body name hReplAlpha]
        exact hA.2.1
      have hSubU : restrict.actions ⊆
          (body.replaceVar name (.recur alphabet name body)).alphabet.actions := by
        rw [hUnfoldAlpha]; exact hSubA
      rw [Finset.empty_inter, futureOffers_restrict hUnfoldWF hSubU,
        PactType.reannotate_replaceVar name body restrict
          (.recur alphabet name body) hA.2.2 hReplAlpha hT.1]
      simp only [PactType.reannotate]
      exact TypeOffers.recur env restrict name (body.reannotate restrict)
        ⟨hEnv, hPrem.2⟩
  | seq env alphabet left left' right label current childFuture hChild hNotSkip
      hNotTock ih =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      have hSubL : restrict.actions ⊆ left.alphabet.actions := by
        rw [hA.2.1]; exact hSubA
      have hSubR : restrict.actions ⊆ right.alphabet.actions := by
        rw [hA.2.2.1]; exact hSubA
      rw [union_sdiff_inter,
        ← sequenceRightMenu_reannotate (left := left) hA.2.2.2.2 hSubR]
      simp only [PactType.reannotate]
      exact TypeOffers.seq env restrict _ _ _ label _ _
        (ih restrict hRegular.seq_left hSubL hEnv) (reannotate_ne_skip hNotSkip)
        hNotTock
  | seq_tock env alphabet left left' right current childFuture hChild hNotSkip
      ih =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      have hSubL : restrict.actions ⊆ left.alphabet.actions := by
        rw [hA.2.1]; exact hSubA
      rw [Finset.empty_inter]
      simp only [PactType.reannotate]
      exact TypeOffers.seq_tock env restrict _ _ _ _ _
        (ih restrict hRegular.seq_left hSubL hEnv) (reannotate_ne_skip hNotSkip)
  | seq_fuse env alphabet skipAlphabet left right label current childFuture
      hChild hNotTock ih =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      have hSubL : restrict.actions ⊆ left.alphabet.actions := by
        rw [hA.2.1]; exact hSubA
      have hSubR : restrict.actions ⊆ right.alphabet.actions := by
        rw [hA.2.2.1]; exact hSubA
      have hChild' := ih restrict hRegular.seq_left hSubL hEnv
      rw [PactType.reannotate] at hChild'
      rw [union_sdiff_inter,
        ← sequenceRightMenu_reannotate (left := left) hA.2.2.2.2 hSubR]
      simp only [PactType.reannotate]
      exact TypeOffers.seq_fuse env restrict restrict _ _ label _ _ hChild' hNotTock
  | seq_fuse_tock env alphabet skipAlphabet left right current childFuture
      hChild ih =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      have hSubL : restrict.actions ⊆ left.alphabet.actions := by
        rw [hA.2.1]; exact hSubA
      have hChild' := ih restrict hRegular.seq_left hSubL hEnv
      rw [PactType.reannotate] at hChild'
      rw [Finset.empty_inter]
      simp only [PactType.reannotate]
      exact TypeOffers.seq_fuse_tock env restrict restrict _ _ _ _ hChild'
  | xoffer_branch env alphabet elseType branches action processType hPrem =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      have hAction : action ∈ restrict.actions :=
        mem_actions_of_hasNeed hEnv hPrem.2.2.1
      have hRule := TypeOffers.xoffer_branch env restrict
        (elseType.reannotate restrict)
        (branches.map fun branch => (branch.1, branch.2.reannotate restrict))
        action (processType.reannotate restrict)
        ⟨hEnv, List.mem_map_of_mem hPrem.2.1, hPrem.2.2.1, by
          simp only [TypeResolved, typeBranchNeeds_map]; exact hPrem.2.2.2⟩
      rw [typeBranchActions_map] at hRule
      rw [sdiff_inter_right, futureOffers_restrict hRegular.alphabetWellFormed hSub,
        Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hAction),
        PactType.reannotate, PactType.reannotateBranches_map]
      exact hRule
  | xoffer_else env alphabet elseType branches hPrem =>
      intro restrict hRegular hSub hEnv
      have hRule := TypeOffers.xoffer_else env restrict
        (elseType.reannotate restrict)
        (branches.map fun branch => (branch.1, branch.2.reannotate restrict))
        ⟨hEnv, hPrem.2.1, by
            simp only [TypeNoImmediateBranch, typeBranchNeeds_map]
            exact hPrem.2.2.1, by
            simp only [TypeResolved, typeBranchNeeds_map]; exact hPrem.2.2.2⟩
      rw [typeBranchActions_map] at hRule
      rw [Finset.empty_inter, sdiff_inter_right,
        futureOffers_restrict hRegular.alphabetWellFormed hSub,
        PactType.reannotate, PactType.reannotateBranches_map]
      exact hRule
  | xoffer_wait env alphabet elseType branches hPrem =>
      intro restrict hRegular hSub hEnv
      have hWaiting : typeWaitingOffers env branches ⊆ restrict.actions :=
        (Finset.inter_subset_left).trans (future_image_subset hEnv)
      have hRule := TypeOffers.xoffer_wait env restrict
        (elseType.reannotate restrict)
        (branches.map fun branch => (branch.1, branch.2.reannotate restrict))
        ⟨hEnv, by
            simp only [TypeResolved, typeBranchNeeds_map]; exact hPrem.2.1,
          hPrem.2.2⟩
      simp only [typeWaitingOffers, typeBranchActions_map] at hRule
      rw [Finset.inter_eq_left.mpr hWaiting, sdiff_inter_right,
        futureOffers_restrict hRegular.alphabetWellFormed hSub,
        PactType.reannotate, PactType.reannotateBranches_map]
      exact hRule
  | offer_else env alphabet elseType branches hPrem =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      have hSubE : restrict.actions ⊆ elseType.alphabet.actions := by
        rw [hA.2.1]; exact hSubA
      have hRule := TypeOffers.offer_else env restrict
        (elseType.reannotate restrict)
        (branches.map fun branch => (branch.1, branch.2.reannotate restrict))
        ⟨hEnv, hPrem.2.1, by
            simp only [TypeNoImmediateBranch, typeBranchNeeds_map]
            exact hPrem.2.2.1, by
            simp only [TypeResolved, typeBranchNeeds_map]; exact hPrem.2.2.2⟩
      rw [typeBranchActions_map] at hRule
      rw [inter_inter_of_subset hSubA, sdiff_inter_of_subset hSubA,
        futureOffers_restrict hA.2.2.1 hSubE,
        PactType.reannotate, PactType.reannotateOfferBranches_map]
      exact hRule
  | offer_wait env alphabet elseType branches hPrem =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      have hRule := TypeOffers.offer_wait env restrict
        (elseType.reannotate restrict)
        (branches.map fun branch => (branch.1, branch.2.reannotate restrict))
        ⟨hEnv, hPrem.2.1, by
            simp only [TypeNoImmediateBranch, typeBranchNeeds_map]
            exact hPrem.2.2.1, by
            simp only [TypeResolved, typeBranchNeeds_map]; exact hPrem.2.2.2⟩
      rw [typeBranchActions_map] at hRule
      rw [inter_inter_of_subset hSubA, sdiff_inter_of_subset hSubA,
        futureOffers_restrict hRegular.alphabetWellFormed hSub,
        PactType.reannotate, PactType.reannotateOfferBranches_map]
      exact hRule
  | offer_some env alphabet elseType branches enabled hPrem =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      have hAlphaEq : ∀ b ∈ branches, b.2.alphabet = alphabet :=
        fun b hb => (hRegular.offer_branch hb).2
      have hWF : ∀ b ∈ branches, b.2.AlphabetWellFormed :=
        fun b hb => (hRegular.offer_branch hb).1.alphabetWellFormed
      have hSubBranch : ∀ b ∈ branches, restrict.actions ⊆ b.2.alphabet.actions :=
        fun b hb => by rw [hAlphaEq b hb]; exact hSubA
      have hWFRestrict : ∀ b ∈ branches, (b.2.reannotate restrict).AlphabetWellFormed :=
        fun b hb => ((hRegular.offer_branch hb).1.reannotate
          (hSubBranch b hb)).alphabetWellFormed
      have hWFAlpha : ∀ b ∈ branches, (b.2.reannotate alphabet).AlphabetWellFormed :=
        fun b hb => ((hRegular.offer_branch hb).1.reannotate
          (by rw [hAlphaEq b hb])).alphabetWellFormed
      have hMenu : ∀ b ∈ branches,
          typeFutureOffers (b.2.reannotate restrict) =
            typeFutureOffers b.2 ∩ restrict.actions :=
        fun b hb => typeFutureOffers_reannotate b.2 restrict (hWF b hb)
          (hSubBranch b hb)
      cases branches with
      | nil => cases hPrem.2.1
      | cons head tail =>
          have hMapped : ∀ b ∈ ((head :: tail).map fun branch =>
              (branch.1, branch.2.reannotate restrict)), b.2.alphabet = restrict := by
            intro b hb
            obtain ⟨source, -, rfl⟩ := List.mem_map.mp hb
            exact PactType.reannotate_alphabet restrict source.2
          have hMappedWF : ∀ b ∈ ((head :: tail).map fun branch =>
              (branch.1, branch.2.reannotate restrict)), b.2.AlphabetWellFormed := by
            intro b hb
            obtain ⟨source, hSource, rfl⟩ := List.mem_map.mp hb
            exact hWFRestrict source hSource
          have hTargetEq :
              (parallelTypeBranchesSelecting alphabet enabled
                  (head :: tail)).reannotate restrict =
                parallelTypeBranchesSelecting restrict
                  (enabled.1, enabled.2.reannotate restrict)
                  ((head :: tail).map fun branch =>
                    (branch.1, branch.2.reannotate restrict)) := by
            rw [reannotate_parallelTypeBranchesSelecting alphabet restrict enabled
              head tail hWF hWFAlpha]
            have hMapEq := parallelTypeBranchesSelectingWithin_map_reannotate
              restrict restrict enabled (head :: tail) hWF hWFRestrict
              hRegular.offer_heads_pairwise hPrem.2.1
            simp only [List.map_cons] at hMapEq
            simp only [List.map_cons, parallelTypeBranchesSelecting]
            exact hMapEq.symm
          have hRule := TypeOffers.offer_some env restrict
            (elseType.reannotate restrict)
            ((head :: tail).map fun branch => (branch.1, branch.2.reannotate restrict))
            (enabled.1, enabled.2.reannotate restrict)
            ⟨hEnv, List.mem_map_of_mem hPrem.2.1, hPrem.2.2⟩
          rw [typeFutureOffers_parallelTypeBranchesSelecting restrict _ _ hMapped
            hMappedWF] at hRule
          rw [Finset.empty_inter, hTargetEq,
            typeFutureOffers_parallelTypeBranchesSelecting alphabet enabled
              (head :: tail) hAlphaEq hWF,
            inter_inter_of_subset hSubA,
            ← foldl_menu_restrict restrict (head :: tail) ∅ ∅ hMenu rfl,
            PactType.reannotate, PactType.reannotateOfferBranches_map]
          exact hRule
  | par outer leftEnv rightEnv interface alphabet left left' right right'
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      hLeftNotSkip hRightNotSkip hLeft hRight hNotBothSkip hLocalLeft hLocalRight
      hPrem ihLeft ihRight =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      have hCompat := hA.2.1
      obtain ⟨hLC, hLF⟩ := hLeft.offers_subset_alphabet hRegular.par_left
      obtain ⟨hRC, hRF⟩ := hRight.offers_subset_alphabet hRegular.par_right
      have hLeft' := ihLeft
        (PactTypeAlphabet.projectParallel restrict left.alphabet interface)
        hRegular.par_left (projectParallel_subset_left hCompat hSubA)
        (localTypeOfferEnvironment_wellFormed hLocalLeft hEnv hCompat.complementary
          hRegular.par_right.alphabet_wellFormed hRC hRF)
      have hRight' := ihRight
        (PactTypeAlphabet.projectParallel restrict right.alphabet interface)
        hRegular.par_right (projectParallel_subset_right hCompat hSubA)
        (localTypeOfferEnvironment_wellFormed hLocalRight hEnv
          hCompat.complementary.symm hRegular.par_left.alphabet_wellFormed hLC hLF)
      have hNotBothSkip' : ¬ (left'.reannotate
            (PactTypeAlphabet.projectParallel restrict left.alphabet interface) =
          .skip (left'.reannotate (PactTypeAlphabet.projectParallel restrict
            left.alphabet interface)).alphabet ∧
        right'.reannotate
            (PactTypeAlphabet.projectParallel restrict right.alphabet interface) =
          .skip (right'.reannotate (PactTypeAlphabet.projectParallel restrict
            right.alphabet interface)).alphabet) := by
        rintro ⟨hL, hR⟩
        rw [PactType.reannotate_alphabet] at hL hR
        exact hNotBothSkip ⟨(reannotate_eq_skip_iff _ _).mp hL,
          (reannotate_eq_skip_iff _ _).mp hR⟩
      have hRule := TypeOffers.par outer leftEnv rightEnv interface restrict
        (left.reannotate (PactTypeAlphabet.projectParallel restrict left.alphabet
          interface))
        (left'.reannotate (PactTypeAlphabet.projectParallel restrict left.alphabet
          interface))
        (right.reannotate (PactTypeAlphabet.projectParallel restrict right.alphabet
          interface))
        (right'.reannotate (PactTypeAlphabet.projectParallel restrict right.alphabet
          interface))
        leftLabel rightLabel _ _ _ _
        (reannotate_ne_skip hLeftNotSkip) (reannotate_ne_skip hRightNotSkip)
        hLeft' hRight' hNotBothSkip'
        (localTypeOfferEnvironment_restrict hLocalLeft hRC hRF)
        (localTypeOfferEnvironment_restrict hLocalRight hLC hLF)
        ⟨hEnv, hPrem.2⟩
      have hAlphaL : left'.alphabet = left.alphabet :=
        hLeft.preserves_alphabet hRegular.par_left.alphabetWellFormed
      have hAlphaR : right'.alphabet = right.alphabet :=
        hRight.preserves_alphabet hRegular.par_right.alphabetWellFormed
      simp only [PactType.reannotate, hAlphaL, hAlphaR]
      rw [← hideTypeOffers_inter_projectParallel (parent := restrict)
        (left := left.alphabet) (right := right.alphabet) (interface := interface)
        leftCurrent rightCurrent]
      by_cases hTock : TypeLabel.combine interface leftLabel rightLabel =
          TypeLabel.tock
      · rw [if_pos hTock] at hRule ⊢
        rw [Finset.empty_inter]
        exact hRule
      · rw [if_neg hTock] at hRule ⊢
        rw [← hideTypeOffers_inter_projectParallel (parent := restrict)
          (left := left.alphabet) (right := right.alphabet)
          (interface := interface) leftFuture rightFuture]
        exact hRule
  | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeft hRight
      hLocalLeft hLocalRight hPrem hNotTock ihLeft ihRight =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      have hCompat := hA.2.1
      obtain ⟨hLC, hLF⟩ := hLeft.offers_subset_alphabet hRegular.par_left
      obtain ⟨hRC, hRF⟩ := hRight.offers_subset_alphabet hRegular.par_right
      have hLeft' : TypeOffers leftEnv
          (left.reannotate (PactTypeAlphabet.projectParallel restrict left.alphabet
            interface)) leftLabel
          (.skip (left.reannotate (PactTypeAlphabet.projectParallel restrict
            left.alphabet interface)).alphabet)
          (leftCurrent ∩ (PactTypeAlphabet.projectParallel restrict left.alphabet
            interface).actions)
          (leftFuture ∩ (PactTypeAlphabet.projectParallel restrict left.alphabet
            interface).actions) := by
        rw [PactType.reannotate_alphabet]
        have h := ihLeft
          (PactTypeAlphabet.projectParallel restrict left.alphabet interface)
          hRegular.par_left (projectParallel_subset_left hCompat hSubA)
          (localTypeOfferEnvironment_wellFormed hLocalLeft hEnv
            hCompat.complementary hRegular.par_right.alphabet_wellFormed hRC hRF)
        rwa [PactType.reannotate] at h
      have hRight' : TypeOffers rightEnv
          (right.reannotate (PactTypeAlphabet.projectParallel restrict
            right.alphabet interface)) rightLabel
          (.skip (right.reannotate (PactTypeAlphabet.projectParallel restrict
            right.alphabet interface)).alphabet)
          (rightCurrent ∩ (PactTypeAlphabet.projectParallel restrict right.alphabet
            interface).actions)
          (rightFuture ∩ (PactTypeAlphabet.projectParallel restrict right.alphabet
            interface).actions) := by
        rw [PactType.reannotate_alphabet]
        have h := ihRight
          (PactTypeAlphabet.projectParallel restrict right.alphabet interface)
          hRegular.par_right (projectParallel_subset_right hCompat hSubA)
          (localTypeOfferEnvironment_wellFormed hLocalRight hEnv
            hCompat.complementary.symm hRegular.par_left.alphabet_wellFormed hLC hLF)
        rwa [PactType.reannotate] at h
      have hRule := TypeOffers.par_fuse outer leftEnv rightEnv interface restrict
        _ _ leftLabel rightLabel _ _ _ _ hLeft' hRight'
        (localTypeOfferEnvironment_restrict hLocalLeft hRC hRF)
        (localTypeOfferEnvironment_restrict hLocalRight hLC hLF)
        ⟨hEnv, hPrem.2⟩ hNotTock
      rw [hideTypeOffers_inter_projectParallel,
        hideTypeOffers_inter_projectParallel] at hRule
      simp only [PactType.reannotate]
      exact hRule
  | par_fuse_tock outer leftEnv rightEnv interface alphabet left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeft hRight
      hLocalLeft hLocalRight hPrem hTock ihLeft ihRight =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      have hCompat := hA.2.1
      obtain ⟨hLC, hLF⟩ := hLeft.offers_subset_alphabet hRegular.par_left
      obtain ⟨hRC, hRF⟩ := hRight.offers_subset_alphabet hRegular.par_right
      have hLeft' : TypeOffers leftEnv
          (left.reannotate (PactTypeAlphabet.projectParallel restrict left.alphabet
            interface)) leftLabel
          (.skip (left.reannotate (PactTypeAlphabet.projectParallel restrict
            left.alphabet interface)).alphabet)
          (leftCurrent ∩ (PactTypeAlphabet.projectParallel restrict left.alphabet
            interface).actions)
          (leftFuture ∩ (PactTypeAlphabet.projectParallel restrict left.alphabet
            interface).actions) := by
        rw [PactType.reannotate_alphabet]
        have h := ihLeft
          (PactTypeAlphabet.projectParallel restrict left.alphabet interface)
          hRegular.par_left (projectParallel_subset_left hCompat hSubA)
          (localTypeOfferEnvironment_wellFormed hLocalLeft hEnv
            hCompat.complementary hRegular.par_right.alphabet_wellFormed hRC hRF)
        rwa [PactType.reannotate] at h
      have hRight' : TypeOffers rightEnv
          (right.reannotate (PactTypeAlphabet.projectParallel restrict
            right.alphabet interface)) rightLabel
          (.skip (right.reannotate (PactTypeAlphabet.projectParallel restrict
            right.alphabet interface)).alphabet)
          (rightCurrent ∩ (PactTypeAlphabet.projectParallel restrict right.alphabet
            interface).actions)
          (rightFuture ∩ (PactTypeAlphabet.projectParallel restrict right.alphabet
            interface).actions) := by
        rw [PactType.reannotate_alphabet]
        have h := ihRight
          (PactTypeAlphabet.projectParallel restrict right.alphabet interface)
          hRegular.par_right (projectParallel_subset_right hCompat hSubA)
          (localTypeOfferEnvironment_wellFormed hLocalRight hEnv
            hCompat.complementary.symm hRegular.par_left.alphabet_wellFormed hLC hLF)
        rwa [PactType.reannotate] at h
      have hRule := TypeOffers.par_fuse_tock outer leftEnv rightEnv interface
        restrict _ _ leftLabel rightLabel _ _ _ _ hLeft' hRight'
        (localTypeOfferEnvironment_restrict hLocalLeft hRC hRF)
        (localTypeOfferEnvironment_restrict hLocalRight hLC hLF)
        ⟨hEnv, hPrem.2⟩ hTock
      rw [Finset.empty_inter]
      simp only [PactType.reannotate]
      exact hRule
  | left_complete outer leftEnv rightEnv interface alphabet left right right'
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftSkip
      hRightNotSkip hLeft hRight hTargetNotSkip hLocalLeft hLocalRight hEnvAlpha
      hSync ihLeft ihRight =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      have hCompat := hA.2.1
      obtain ⟨hLC, hLF⟩ := hLeft.offers_subset_alphabet hRegular.par_left
      obtain ⟨hRC, hRF⟩ := hRight.offers_subset_alphabet hRegular.par_right
      have hLeft' := ihLeft
        (PactTypeAlphabet.projectParallel restrict left.alphabet interface)
        hRegular.par_left (projectParallel_subset_left hCompat hSubA)
        (localTypeOfferEnvironment_wellFormed hLocalLeft hEnv hCompat.complementary
          hRegular.par_right.alphabet_wellFormed hRC hRF)
      have hRight' := ihRight
        (PactTypeAlphabet.projectParallel restrict right.alphabet interface)
        hRegular.par_right (projectParallel_subset_right hCompat hSubA)
        (localTypeOfferEnvironment_wellFormed hLocalRight hEnv
          hCompat.complementary.symm hRegular.par_left.alphabet_wellFormed hLC hLF)
      obtain ⟨hScoped', hInterfaces'⟩ := hRight.preserves_scoping
        hRegular.par_right.interfaceScoped hRegular.par_right.tailRecursive
      have hIS := hRegular.interfaceScoped
      have hIAS := hRegular.interfaceAlphabetScoped
      simp only [PactType.InterfaceScoped] at hIS
      simp only [PactType.InterfaceAlphabetScoped] at hIAS
      have hAvoidAlpha : ∀ action ∈ alphabet.actions,
          action.1 ∉ PactType.ParallelInterfaces right' := by
        intro action hAction hIn
        exact Finset.disjoint_left.mp hIAS.1
          (Finset.mem_image.mpr ⟨action, hAction, rfl⟩)
          (Finset.mem_union_right _ (hInterfaces' hIn))
      have hAvoidChild : ∀ action ∈ (PactTypeAlphabet.projectParallel restrict
          right.alphabet interface).actions,
          action.1 ∉ PactType.ParallelInterfaces right' := by
        intro action hAction hIn
        rcases Finset.mem_union.mp hAction with h | h
        · exact Finset.disjoint_left.mp hIS.1 (Finset.mem_filter.mp h).2
            (Finset.mem_union_right _ (hInterfaces' hIn))
        · exact hAvoidAlpha action (hSubA h) hIn
      have hTargetEq : (right'.reannotate (PactTypeAlphabet.projectParallel restrict
            right.alphabet interface)).reannotate restrict =
          (right'.reannotate alphabet).reannotate restrict := by
        rw [reannotate_reannotate_of_avoiding right' _ restrict hScoped' hAvoidChild,
          reannotate_reannotate_of_avoiding right' alphabet restrict hScoped'
            hAvoidAlpha]
      have hHide : ∀ offers : Finset BareMessage, offers ⊆ right.alphabet.actions →
          hideTypeOffers interface (offers ∩
              (PactTypeAlphabet.projectParallel restrict right.alphabet
                interface).actions) =
            hideTypeOffers interface offers ∩ restrict.actions := by
        intro offers _
        have h := hideTypeOffers_inter_projectParallel (parent := restrict)
          (left := left.alphabet) (right := right.alphabet) (interface := interface)
          ∅ offers
        rw [Finset.empty_inter, Finset.empty_union, Finset.empty_union] at h
        exact h
      have hRule := TypeOffers.left_complete outer leftEnv rightEnv interface
        restrict _ _
        (right'.reannotate (PactTypeAlphabet.projectParallel restrict right.alphabet
          interface))
        rightLabel _ _ _ _ (reannotate_eq_skip hLeftSkip)
        (reannotate_ne_skip hRightNotSkip) hLeft' hRight'
        (reannotate_ne_skip hTargetNotSkip)
        (localTypeOfferEnvironment_restrict hLocalLeft hRC hRF)
        (localTypeOfferEnvironment_restrict hLocalRight hLC hLF) hEnv hSync
      rw [hTargetEq, hHide rightCurrent hRC, hHide rightFuture hRF] at hRule
      simp only [PactType.reannotate]
      exact hRule
  | right_complete outer leftEnv rightEnv interface alphabet left left' right
      leftLabel leftCurrent leftFuture rightCurrent rightFuture hRightSkip
      hLeftNotSkip hRight hLeft hTargetNotSkip hLocalLeft hLocalRight hEnvAlpha
      hSync ihRight ihLeft =>
      intro restrict hRegular hSub hEnv
      have hSubA : restrict.actions ⊆ alphabet.actions := hSub
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      have hCompat := hA.2.1
      obtain ⟨hLC, hLF⟩ := hLeft.offers_subset_alphabet hRegular.par_left
      obtain ⟨hRC, hRF⟩ := hRight.offers_subset_alphabet hRegular.par_right
      have hLeft' := ihLeft
        (PactTypeAlphabet.projectParallel restrict left.alphabet interface)
        hRegular.par_left (projectParallel_subset_left hCompat hSubA)
        (localTypeOfferEnvironment_wellFormed hLocalLeft hEnv hCompat.complementary
          hRegular.par_right.alphabet_wellFormed hRC hRF)
      have hRight' := ihRight
        (PactTypeAlphabet.projectParallel restrict right.alphabet interface)
        hRegular.par_right (projectParallel_subset_right hCompat hSubA)
        (localTypeOfferEnvironment_wellFormed hLocalRight hEnv
          hCompat.complementary.symm hRegular.par_left.alphabet_wellFormed hLC hLF)
      obtain ⟨hScoped', hInterfaces'⟩ := hLeft.preserves_scoping
        hRegular.par_left.interfaceScoped hRegular.par_left.tailRecursive
      have hIS := hRegular.interfaceScoped
      have hIAS := hRegular.interfaceAlphabetScoped
      simp only [PactType.InterfaceScoped] at hIS
      simp only [PactType.InterfaceAlphabetScoped] at hIAS
      have hAvoidAlpha : ∀ action ∈ alphabet.actions,
          action.1 ∉ PactType.ParallelInterfaces left' := by
        intro action hAction hIn
        exact Finset.disjoint_left.mp hIAS.1
          (Finset.mem_image.mpr ⟨action, hAction, rfl⟩)
          (Finset.mem_union_left _ (Finset.mem_union_right _ (hInterfaces' hIn)))
      have hAvoidChild : ∀ action ∈ (PactTypeAlphabet.projectParallel restrict
          left.alphabet interface).actions,
          action.1 ∉ PactType.ParallelInterfaces left' := by
        intro action hAction hIn
        rcases Finset.mem_union.mp hAction with h | h
        · exact Finset.disjoint_left.mp hIS.1 (Finset.mem_filter.mp h).2
            (Finset.mem_union_left _ (hInterfaces' hIn))
        · exact hAvoidAlpha action (hSubA h) hIn
      have hTargetEq : (left'.reannotate (PactTypeAlphabet.projectParallel restrict
            left.alphabet interface)).reannotate restrict =
          (left'.reannotate alphabet).reannotate restrict := by
        rw [reannotate_reannotate_of_avoiding left' _ restrict hScoped' hAvoidChild,
          reannotate_reannotate_of_avoiding left' alphabet restrict hScoped'
            hAvoidAlpha]
      have hHide : ∀ offers : Finset BareMessage, offers ⊆ left.alphabet.actions →
          hideTypeOffers interface (offers ∩
              (PactTypeAlphabet.projectParallel restrict left.alphabet
                interface).actions) =
            hideTypeOffers interface offers ∩ restrict.actions := by
        intro offers _
        have h := hideTypeOffers_inter_projectParallel (parent := restrict)
          (left := left.alphabet) (right := right.alphabet) (interface := interface)
          offers ∅
        rw [Finset.empty_inter, Finset.union_empty, Finset.union_empty] at h
        exact h
      have hRule := TypeOffers.right_complete outer leftEnv rightEnv interface
        restrict _
        (left'.reannotate (PactTypeAlphabet.projectParallel restrict left.alphabet
          interface))
        _ leftLabel _ _ _ _ (reannotate_eq_skip hRightSkip)
        (reannotate_ne_skip hLeftNotSkip) hRight' hLeft'
        (reannotate_ne_skip hTargetNotSkip)
        (localTypeOfferEnvironment_restrict hLocalLeft hRC hRF)
        (localTypeOfferEnvironment_restrict hLocalRight hLC hLF) hEnv hSync
      rw [hTargetEq, hHide leftCurrent hLC, hHide leftFuture hLF] at hRule
      simp only [PactType.reannotate]
      exact hRule

/-- The sibling type is a phantom parameter of the local-environment relation. -/
lemma LocalTypeOfferEnvironment.congr_localType {outer siblingEnv localEnv : TypeEnvironment}
    {interface : Interface} {localType localType' : PactType}
    {current future : Finset BareMessage}
    (h : LocalTypeOfferEnvironment outer interface localType siblingEnv current
      future localEnv) :
    LocalTypeOfferEnvironment outer interface localType' siblingEnv current future
      localEnv := by
  cases h with
  | clock _ _ _ _ hClock => exact .clock _ _ _ _ _ hClock
  | ordinary _ _ _ _ _ _ h1 h2 h3 h4 h5 => exact .ordinary _ _ _ _ _ _ _ h1 h2 h3 h4 h5

lemma localTypeOfferEnvironment_unrestrict {outer siblingEnv localEnv : TypeEnvironment}
    {interface : Interface} {localType localType' : PactType}
    {siblingCurrent siblingFuture : Finset BareMessage}
    {sibling restrict : PactTypeAlphabet}
    (hLocal : LocalTypeOfferEnvironment outer interface localType siblingEnv
      (siblingCurrent ∩
        (PactTypeAlphabet.projectParallel restrict sibling interface).actions)
      (siblingFuture ∩
        (PactTypeAlphabet.projectParallel restrict sibling interface).actions)
      localEnv)
    (hCurrent : siblingCurrent ⊆ sibling.actions)
    (hFuture : siblingFuture ⊆ sibling.actions) :
    LocalTypeOfferEnvironment outer interface localType' siblingEnv siblingCurrent
      siblingFuture localEnv := by
  cases hLocal with
  | clock _ _ _ _ hClock => exact .clock _ _ _ _ _ hClock
  | ordinary _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
      rw [restrictTypeOffers_inter_projectParallel hCurrent] at h4
      rw [restrictTypeOffers_inter_projectParallel hFuture] at h5
      exact .ordinary _ _ _ _ _ _ _ h1 h2 h3 h4 h5

/-! ## Helper Lemma 21, second bullet: the step equation, backward inclusion -/

set_option maxHeartbeats 4000000 in
theorem typeOffers_reannotate_backward :
    ∀ (source : PactType) (restrict : PactTypeAlphabet) (env : TypeEnvironment)
      (label : TypeLabel) (resigned : PactType)
      (resignedCurrent resignedFuture : Finset BareMessage),
      TypeOffers env (source.reannotate restrict) label resigned resignedCurrent
        resignedFuture →
      ResignRegular source →
      restrict.actions ⊆ source.alphabet.actions →
      env.WellFormed restrict →
      ∃ target current future,
        TypeOffers env source label target current future ∧
        resigned = target.reannotate restrict ∧
        resignedCurrent = current ∩ restrict.actions ∧
        resignedFuture = future ∩ restrict.actions := by
  intro source
  induction hSize : sizeOf source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
      intro restrict env label resigned resignedCurrent resignedFuture hOffers
        hRegular hSub hEnv
      subst hSize
      cases source with
      | var alphabet name =>
          rw [PactType.reannotate] at hOffers
          cases hOffers
      | message alphabet msg dir =>
          have hSubA : restrict.actions ⊆ alphabet.actions := hSub
          have hEnvA : env.WellFormed alphabet :=
            TypeEnvironment.wellFormed_mono hEnv hSubA
          rw [PactType.reannotate] at hOffers
          cases hOffers with
          | action _ _ _ _ hPrem =>
              refine ⟨.skip alphabet, {(msg, dir)} ∩ alphabet.actions,
                typeFutureOffers (.skip alphabet),
                TypeOffers.action env alphabet msg dir ⟨hEnvA, hPrem.2⟩, ?_, ?_, ?_⟩
              · rw [PactType.reannotate]
              · rw [inter_inter_of_subset hSubA]
              · rw [typeFutureOffers_skip, typeFutureOffers_skip, Finset.empty_inter]
          | action_wait _ _ _ _ hPrem =>
              refine ⟨.message alphabet msg dir, {(msg, dir)} ∩ alphabet.actions,
                typeFutureOffers (.message alphabet msg dir) \
                  ({(msg, dir)} ∩ alphabet.actions),
                TypeOffers.action_wait env alphabet msg dir
                  ⟨hEnvA, hPrem.2.1, hPrem.2.2⟩, ?_, ?_, ?_⟩
              · rw [PactType.reannotate]
              · rw [inter_inter_of_subset hSubA]
              · rw [sdiff_inter_of_subset hSubA,
                  futureOffers_restrict hRegular.alphabetWellFormed hSub,
                  PactType.reannotate]
      | progress alphabet pid =>
          have hSubA : restrict.actions ⊆ alphabet.actions := hSub
          have hEnvA : env.WellFormed alphabet :=
            TypeEnvironment.wellFormed_mono hEnv hSubA
          rw [PactType.reannotate] at hOffers
          cases hOffers with
          | progress _ _ _ hPrem =>
              refine ⟨.skip alphabet, ∅, typeFutureOffers (.skip alphabet),
                TypeOffers.progress env alphabet pid ⟨hEnvA, hPrem.2⟩, ?_, ?_, ?_⟩
              · rw [PactType.reannotate]
              · rw [Finset.empty_inter]
              · rw [typeFutureOffers_skip, typeFutureOffers_skip, Finset.empty_inter]
      | tock alphabet =>
          have hSubA : restrict.actions ⊆ alphabet.actions := hSub
          have hEnvA : env.WellFormed alphabet :=
            TypeEnvironment.wellFormed_mono hEnv hSubA
          rw [PactType.reannotate] at hOffers
          cases hOffers with
          | cycle _ _ hPrem =>
              refine ⟨.skip alphabet, ∅, ∅,
                TypeOffers.cycle env alphabet ⟨hEnvA, hPrem.2⟩, ?_, ?_, ?_⟩
              · rw [PactType.reannotate]
              · rw [Finset.empty_inter]
              · rw [Finset.empty_inter]
          | cycle_wait _ _ hPrem =>
              refine ⟨.tock alphabet, ∅, typeFutureOffers (.tock alphabet),
                TypeOffers.cycle_wait env alphabet ⟨hEnvA, hPrem.2⟩, ?_, ?_, ?_⟩
              · rw [PactType.reannotate]
              · rw [Finset.empty_inter]
              · rw [futureOffers_restrict hRegular.alphabetWellFormed hSub,
                  PactType.reannotate]
      | skip alphabet =>
          have hSubA : restrict.actions ⊆ alphabet.actions := hSub
          have hEnvA : env.WellFormed alphabet :=
            TypeEnvironment.wellFormed_mono hEnv hSubA
          rw [PactType.reannotate] at hOffers
          cases hOffers with
          | skip _ _ hPrem =>
              refine ⟨.skip alphabet, ∅, typeFutureOffers (.skip alphabet),
                TypeOffers.skip env alphabet ⟨hEnvA, hPrem.2⟩, ?_, ?_, ?_⟩
              · rw [PactType.reannotate]
              · rw [Finset.empty_inter]
              · rw [typeFutureOffers_skip, typeFutureOffers_skip, Finset.empty_inter]
      | choice alphabet left right =>
          have hSubA : restrict.actions ⊆ alphabet.actions := hSub
          have hEnvA : env.WellFormed alphabet :=
            TypeEnvironment.wellFormed_mono hEnv hSubA
          rw [PactType.reannotate] at hOffers
          cases hOffers with
          | choice_left _ _ _ _ hPrem =>
              refine ⟨left, ∅, typeFutureOffers (.choice alphabet left right),
                TypeOffers.choice_left env alphabet left right ⟨hEnvA, hPrem.2⟩,
                rfl, ?_, ?_⟩
              · rw [Finset.empty_inter]
              · rw [futureOffers_restrict hRegular.alphabetWellFormed hSub,
                  PactType.reannotate]
          | choice_right _ _ _ _ hPrem =>
              refine ⟨right, ∅, typeFutureOffers (.choice alphabet left right),
                TypeOffers.choice_right env alphabet left right ⟨hEnvA, hPrem.2⟩,
                rfl, ?_, ?_⟩
              · rw [Finset.empty_inter]
              · rw [futureOffers_restrict hRegular.alphabetWellFormed hSub,
                  PactType.reannotate]
      | fairChoice alphabet bid left right =>
          have hSubA : restrict.actions ⊆ alphabet.actions := hSub
          have hEnvA : env.WellFormed alphabet :=
            TypeEnvironment.wellFormed_mono hEnv hSubA
          rw [PactType.reannotate] at hOffers
          cases hOffers with
          | fair_left _ _ _ _ _ hPrem =>
              refine ⟨left, ∅,
                typeFutureOffers (.fairChoice alphabet bid left right),
                TypeOffers.fair_left env alphabet bid left right
                  ⟨hEnvA, hPrem.2⟩, rfl, ?_, ?_⟩
              · rw [Finset.empty_inter]
              · rw [futureOffers_restrict hRegular.alphabetWellFormed hSub,
                  PactType.reannotate]
          | fair_right _ _ _ _ _ hPrem =>
              refine ⟨right, ∅,
                typeFutureOffers (.fairChoice alphabet bid left right),
                TypeOffers.fair_right env alphabet bid left right
                  ⟨hEnvA, hPrem.2⟩, rfl, ?_, ?_⟩
              · rw [Finset.empty_inter]
              · rw [futureOffers_restrict hRegular.alphabetWellFormed hSub,
                  PactType.reannotate]
      | recur alphabet name body =>
          have hSubA : restrict.actions ⊆ alphabet.actions := hSub
          have hEnvA : env.WellFormed alphabet :=
            TypeEnvironment.wellFormed_mono hEnv hSubA
          have hA := hRegular.alphabetWellFormed
          have hT := hRegular.tailRecursive
          simp only [PactType.AlphabetWellFormed] at hA
          simp only [PactType.TailRecursive] at hT
          have hReplAlpha : (PactType.recur alphabet name body).alphabet =
              body.alphabet := by rw [PactType.alphabet]; exact hA.2.1.symm
          have hUnfoldWF := PactType.replaceVar_alphabetWellFormed name
            hRegular.alphabetWellFormed body hA.2.2 hReplAlpha hT.1
          have hUnfoldAlpha :
              (body.replaceVar name (.recur alphabet name body)).alphabet =
                alphabet := by
            rw [PactType.replaceVar_alphabet_eq_of_replacement body name hReplAlpha]
            exact hA.2.1
          have hSubU : restrict.actions ⊆
              (body.replaceVar name (.recur alphabet name body)).alphabet.actions := by
            rw [hUnfoldAlpha]; exact hSubA
          rw [PactType.reannotate] at hOffers
          cases hOffers with
          | recur _ _ _ _ hPrem =>
              refine ⟨body.replaceVar name (.recur alphabet name body), ∅,
                typeFutureOffers (body.replaceVar name (.recur alphabet name body)),
                TypeOffers.recur env alphabet name body ⟨hEnvA, hPrem.2⟩, ?_, ?_, ?_⟩
              · rw [PactType.reannotate_replaceVar name body restrict
                  (.recur alphabet name body) hA.2.2 hReplAlpha hT.1,
                  PactType.reannotate]
              · rw [Finset.empty_inter]
              · rw [futureOffers_restrict hUnfoldWF hSubU,
                  PactType.reannotate_replaceVar name body restrict
                    (.recur alphabet name body) hA.2.2 hReplAlpha hT.1,
                  PactType.reannotate]
      | seq alphabet left right =>
          have hSubA : restrict.actions ⊆ alphabet.actions := hSub
          have hA := hRegular.alphabetWellFormed
          simp only [PactType.AlphabetWellFormed] at hA
          have hSubL : restrict.actions ⊆ left.alphabet.actions := by
            rw [hA.2.1]; exact hSubA
          have hSubR : restrict.actions ⊆ right.alphabet.actions := by
            rw [hA.2.2.1]; exact hSubA
          have hLeftSize : sizeOf left < sizeOf (PactType.seq alphabet left right) := by
            simp_wf; omega
          rw [PactType.reannotate] at hOffers
          cases hOffers with
          | seq _ _ _ leftResigned _ _ _ childFuture hChild hNotSkip hNotTock =>
              obtain ⟨leftTarget, current, future, hChildStep, hTargetEq, hCurrentEq,
                hFutureEq⟩ := ih _ hLeftSize left rfl restrict env label
                  leftResigned resignedCurrent childFuture hChild hRegular.seq_left
                  hSubL hEnv
              subst hTargetEq; subst hCurrentEq; subst hFutureEq
              refine ⟨.seq alphabet leftTarget right, current,
                (future ∪ sequenceRightMenu left right) \ current,
                TypeOffers.seq env alphabet left leftTarget right label current
                  future hChildStep (fun h => hNotSkip (reannotate_eq_skip h))
                  hNotTock, ?_, rfl, ?_⟩
              · rw [PactType.reannotate]
              · rw [sequenceRightMenu_reannotate hA.2.2.2.2 hSubR, union_sdiff_inter]
          | seq_tock _ _ _ leftResigned _ childCurrent childFuture hChild hNotSkip =>
              obtain ⟨leftTarget, current, future, hChildStep, hTargetEq, hCurrentEq,
                hFutureEq⟩ := ih _ hLeftSize left rfl restrict env TypeLabel.tock
                  leftResigned childCurrent childFuture hChild hRegular.seq_left
                  hSubL hEnv
              subst hTargetEq
              refine ⟨.seq alphabet leftTarget right, ∅, ∅,
                TypeOffers.seq_tock env alphabet left leftTarget right current future
                  hChildStep (fun h => hNotSkip (reannotate_eq_skip h)), ?_, ?_, ?_⟩
              · rw [PactType.reannotate]
              · rw [Finset.empty_inter]
              · rw [Finset.empty_inter]
          | seq_fuse _ _ skipAlphabet _ _ _ _ childFuture hChild hNotTock =>
              obtain ⟨leftTarget, current, future, hChildStep, hTargetEq, hCurrentEq,
                hFutureEq⟩ := ih _ hLeftSize left rfl restrict env label
                  (.skip skipAlphabet) resignedCurrent childFuture hChild
                  hRegular.seq_left hSubL hEnv
              have hAlphaEq : skipAlphabet = restrict := by
                have := congrArg PactType.alphabet hTargetEq
                rw [PactType.alphabet, PactType.reannotate_alphabet] at this
                exact this
              subst hAlphaEq
              have hSkip : leftTarget = .skip leftTarget.alphabet :=
                (reannotate_eq_skip_iff leftTarget skipAlphabet).mp hTargetEq.symm
              subst hCurrentEq; subst hFutureEq
              refine ⟨right, current, (future ∪ sequenceRightMenu left right) \ current,
                TypeOffers.seq_fuse env alphabet leftTarget.alphabet left right
                  label current future (hSkip ▸ hChildStep) hNotTock, rfl, rfl, ?_⟩
              rw [sequenceRightMenu_reannotate hA.2.2.2.2 hSubR, union_sdiff_inter]
          | seq_fuse_tock _ _ skipAlphabet _ _ childCurrent childFuture hChild =>
              obtain ⟨leftTarget, current, future, hChildStep, hTargetEq, hCurrentEq,
                hFutureEq⟩ := ih _ hLeftSize left rfl restrict env TypeLabel.tock
                  (.skip skipAlphabet) childCurrent childFuture hChild
                  hRegular.seq_left hSubL hEnv
              have hAlphaEq : skipAlphabet = restrict := by
                have := congrArg PactType.alphabet hTargetEq
                rw [PactType.alphabet, PactType.reannotate_alphabet] at this
                exact this
              subst hAlphaEq
              have hSkip : leftTarget = .skip leftTarget.alphabet :=
                (reannotate_eq_skip_iff leftTarget skipAlphabet).mp hTargetEq.symm
              refine ⟨right, ∅, ∅,
                TypeOffers.seq_fuse_tock env alphabet leftTarget.alphabet left right
                  current future (hSkip ▸ hChildStep), rfl, ?_, ?_⟩
              · rw [Finset.empty_inter]
              · rw [Finset.empty_inter]
      | xoffer alphabet elseType branches =>
          have hSubA : restrict.actions ⊆ alphabet.actions := hSub
          have hEnvA : env.WellFormed alphabet :=
            TypeEnvironment.wellFormed_mono hEnv hSubA
          rw [PactType.reannotate, PactType.reannotateBranches_map] at hOffers
          cases hOffers with
          | xoffer_branch _ _ _ _ action _ hPrem =>
              obtain ⟨branch, hMem, hEq⟩ := List.mem_map.mp hPrem.2.1
              have hHead : branch.1 = action := congrArg Prod.fst hEq
              have hBody : resigned = branch.2.reannotate restrict :=
                (congrArg Prod.snd hEq).symm
              have hEnabled : TypeBranchEnabled env branch := by
                show typeNeed branch.1 ∈ env.immediate
                rw [hHead]; exact hPrem.2.2.1
              refine ⟨branch.2, {branch.1},
                typeFutureOffers (.xoffer alphabet elseType branches) \
                  typeBranchActions branches,
                hHead ▸ TypeOffers.xoffer_branch env alphabet elseType branches
                  branch.1 branch.2 ⟨hEnvA, by rw [Prod.mk.eta]; exact hMem,
                    by rw [Prod.mk.eta]; exact hEnabled, by
                      simp only [TypeResolved, typeBranchNeeds_map] at hPrem
                      exact hPrem.2.2.2⟩,
                hBody, ?_, ?_⟩
              · rw [hHead, Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr
                  (mem_actions_of_hasNeed hEnv hPrem.2.2.1))]
              · rw [sdiff_inter_right,
                  futureOffers_restrict hRegular.alphabetWellFormed hSub,
                  PactType.reannotate, PactType.reannotateBranches_map,
                  typeBranchActions_map]
          | xoffer_else _ _ _ _ hPrem =>
              refine ⟨elseType, ∅,
                typeFutureOffers (.xoffer alphabet elseType branches) \
                  typeBranchActions branches,
                TypeOffers.xoffer_else env alphabet elseType branches
                  ⟨hEnvA, hPrem.2.1, by
                      simp only [TypeNoImmediateBranch, typeBranchNeeds_map] at hPrem
                      exact hPrem.2.2.1, by
                      simp only [TypeResolved, typeBranchNeeds_map] at hPrem
                      exact hPrem.2.2.2⟩,
                rfl, ?_, ?_⟩
              · rw [Finset.empty_inter]
              · rw [sdiff_inter_right,
                  futureOffers_restrict hRegular.alphabetWellFormed hSub,
                  PactType.reannotate, PactType.reannotateBranches_map,
                  typeBranchActions_map]
          | xoffer_wait _ _ _ _ hPrem =>
              have hWaiting : typeWaitingOffers env branches ⊆ restrict.actions :=
                (Finset.inter_subset_left).trans (future_image_subset hEnv)
              refine ⟨.xoffer alphabet elseType branches,
                typeWaitingOffers env branches,
                typeFutureOffers (.xoffer alphabet elseType branches) \
                  typeWaitingOffers env branches,
                TypeOffers.xoffer_wait env alphabet elseType branches
                  ⟨hEnvA, by
                      simp only [TypeResolved, typeBranchNeeds_map] at hPrem
                      exact hPrem.2.1, hPrem.2.2⟩, ?_, ?_, ?_⟩
              · rw [PactType.reannotate, PactType.reannotateBranches_map]
              · have hEq : typeWaitingOffers env (branches.map fun branch =>
                    (branch.1, branch.2.reannotate restrict)) =
                      typeWaitingOffers env branches := by
                  simp only [typeWaitingOffers, typeBranchActions_map]
                rw [hEq, Finset.inter_eq_left.mpr hWaiting]
              · have hEq : typeWaitingOffers env (branches.map fun branch =>
                    (branch.1, branch.2.reannotate restrict)) =
                      typeWaitingOffers env branches := by
                  simp only [typeWaitingOffers, typeBranchActions_map]
                rw [hEq, sdiff_inter_right,
                  futureOffers_restrict hRegular.alphabetWellFormed hSub,
                  PactType.reannotate, PactType.reannotateBranches_map]
      | offer alphabet elseType branches =>
          have hSubA : restrict.actions ⊆ alphabet.actions := hSub
          have hEnvA : env.WellFormed alphabet :=
            TypeEnvironment.wellFormed_mono hEnv hSubA
          have hA := hRegular.alphabetWellFormed
          simp only [PactType.AlphabetWellFormed] at hA
          have hSubE : restrict.actions ⊆ elseType.alphabet.actions := by
            rw [hA.2.1]; exact hSubA
          rw [PactType.reannotate, PactType.reannotateOfferBranches_map] at hOffers
          cases hOffers with
          | offer_some _ _ _ _ enabled hPrem =>
              obtain ⟨branch, hMem, hEq⟩ := List.mem_map.mp hPrem.2.1
              have hNonempty : branches ≠ [] := by
                intro h; rw [h] at hMem; cases hMem
              obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil hNonempty
              have hAlphaEq : ∀ b ∈ head :: tail, b.2.alphabet = alphabet :=
                fun b hb => (hRegular.offer_branch hb).2
              have hWF : ∀ b ∈ head :: tail, b.2.AlphabetWellFormed :=
                fun b hb => (hRegular.offer_branch hb).1.alphabetWellFormed
              have hSubBranch : ∀ b ∈ head :: tail,
                  restrict.actions ⊆ b.2.alphabet.actions :=
                fun b hb => by rw [hAlphaEq b hb]; exact hSubA
              have hWFRestrict : ∀ b ∈ head :: tail,
                  (b.2.reannotate restrict).AlphabetWellFormed :=
                fun b hb => ((hRegular.offer_branch hb).1.reannotate
                  (hSubBranch b hb)).alphabetWellFormed
              have hWFAlpha : ∀ b ∈ head :: tail,
                  (b.2.reannotate alphabet).AlphabetWellFormed :=
                fun b hb => ((hRegular.offer_branch hb).1.reannotate
                  (by rw [hAlphaEq b hb])).alphabetWellFormed
              have hMenu : ∀ b ∈ head :: tail,
                  typeFutureOffers (b.2.reannotate restrict) =
                    typeFutureOffers b.2 ∩ restrict.actions :=
                fun b hb => typeFutureOffers_reannotate b.2 restrict (hWF b hb)
                  (hSubBranch b hb)
              have hMapped : ∀ b ∈ ((head :: tail).map fun branch =>
                  (branch.1, branch.2.reannotate restrict)),
                  b.2.alphabet = restrict := by
                intro b hb
                obtain ⟨source, -, rfl⟩ := List.mem_map.mp hb
                exact PactType.reannotate_alphabet restrict source.2
              have hMappedWF : ∀ b ∈ ((head :: tail).map fun branch =>
                  (branch.1, branch.2.reannotate restrict)),
                  b.2.AlphabetWellFormed := by
                intro b hb
                obtain ⟨source, hSource, rfl⟩ := List.mem_map.mp hb
                exact hWFRestrict source hSource
              have hTargetEq :
                  (parallelTypeBranchesSelecting alphabet branch
                      (head :: tail)).reannotate restrict =
                    parallelTypeBranchesSelecting restrict
                      (branch.1, branch.2.reannotate restrict)
                      ((head :: tail).map fun b =>
                        (b.1, b.2.reannotate restrict)) := by
                rw [reannotate_parallelTypeBranchesSelecting alphabet restrict branch
                  head tail hWF hWFAlpha]
                have hMapEq := parallelTypeBranchesSelectingWithin_map_reannotate
                  restrict restrict branch (head :: tail) hWF hWFRestrict
                  hRegular.offer_heads_pairwise hMem
                simp only [List.map_cons] at hMapEq
                simp only [List.map_cons, parallelTypeBranchesSelecting]
                exact hMapEq.symm
              refine ⟨parallelTypeBranchesSelecting alphabet branch (head :: tail), ∅,
                typeFutureOffers (parallelTypeBranchesSelecting alphabet branch
                  (head :: tail)),
                TypeOffers.offer_some env alphabet elseType (head :: tail) branch
                  ⟨hEnvA, hMem, by
                      show typeNeed branch.1 ∈ env.immediate
                      rw [congrArg Prod.fst hEq]; exact hPrem.2.2⟩, ?_, ?_, ?_⟩
              · rw [hTargetEq, ← hEq]
              · rw [Finset.empty_inter]
              · rw [hEq] at hTargetEq
                rw [typeFutureOffers_parallelTypeBranchesSelecting restrict _ _
                    hMapped hMappedWF,
                  typeFutureOffers_parallelTypeBranchesSelecting alphabet branch
                    (head :: tail) hAlphaEq hWF,
                  inter_inter_of_subset hSubA,
                  ← foldl_menu_restrict restrict (head :: tail) ∅ ∅ hMenu rfl]
          | offer_else _ _ _ _ hPrem =>
              refine ⟨elseType, typeBranchActions branches ∩ alphabet.actions,
                typeFutureOffers elseType \
                  (typeBranchActions branches ∩ alphabet.actions),
                TypeOffers.offer_else env alphabet elseType branches
                  ⟨hEnvA, hPrem.2.1, by
                      simp only [TypeNoImmediateBranch, typeBranchNeeds_map] at hPrem
                      exact hPrem.2.2.1, by
                      simp only [TypeResolved, typeBranchNeeds_map] at hPrem
                      exact hPrem.2.2.2⟩,
                rfl, ?_, ?_⟩
              · rw [typeBranchActions_map, inter_inter_of_subset hSubA]
              · rw [typeBranchActions_map, sdiff_inter_of_subset hSubA,
                  futureOffers_restrict hA.2.2.1 hSubE]
          | offer_wait _ _ _ _ hPrem =>
              refine ⟨.offer alphabet elseType branches,
                typeBranchActions branches ∩ alphabet.actions,
                typeFutureOffers (.offer alphabet elseType branches) \
                  (typeBranchActions branches ∩ alphabet.actions),
                TypeOffers.offer_wait env alphabet elseType branches
                  ⟨hEnvA, hPrem.2.1, by
                      simp only [TypeNoImmediateBranch, typeBranchNeeds_map] at hPrem
                      exact hPrem.2.2.1, by
                      simp only [TypeResolved, typeBranchNeeds_map] at hPrem
                      exact hPrem.2.2.2⟩, ?_, ?_, ?_⟩
              · rw [PactType.reannotate, PactType.reannotateOfferBranches_map]
              · rw [typeBranchActions_map, inter_inter_of_subset hSubA]
              · rw [typeBranchActions_map, sdiff_inter_of_subset hSubA,
                  futureOffers_restrict hRegular.alphabetWellFormed hSub,
                  PactType.reannotate, PactType.reannotateOfferBranches_map]
      | par alphabet left right interface =>
          have hSubA : restrict.actions ⊆ alphabet.actions := hSub
          have hEnvA : env.WellFormed alphabet :=
            TypeEnvironment.wellFormed_mono hEnv hSubA
          have hA := hRegular.alphabetWellFormed
          simp only [PactType.AlphabetWellFormed] at hA
          have hCompat := hA.2.1
          have hSubLeft := projectParallel_subset_left hCompat hSubA
          have hSubRight := projectParallel_subset_right hCompat hSubA
          have hLeftWF := (hRegular.par_left.reannotate hSubLeft).alphabetWellFormed
          have hRightWF := (hRegular.par_right.reannotate hSubRight).alphabetWellFormed
          have hLeftSize : sizeOf left <
              sizeOf (PactType.par alphabet left right interface) := by
            simp_wf; omega
          have hRightSize : sizeOf right <
              sizeOf (PactType.par alphabet left right interface) := by
            simp_wf; omega
          rw [PactType.reannotate] at hOffers
          cases hOffers with
          | par _ leftEnv rightEnv _ _ _ leftResigned _ rightResigned leftLabel
              rightLabel leftCurrent' leftFuture' rightCurrent' rightFuture'
              hLeftNotSkip hRightNotSkip hLeftStep hRightStep hNotBothSkip
              hLocalLeft hLocalRight hPrem =>
              have hEnvL : leftEnv.WellFormed
                  (PactTypeAlphabet.projectParallel restrict left.alphabet
                    interface) := by
                have := PactType.typeOffers_env_wellFormed hLeftStep hLeftWF
                rwa [PactType.reannotate_alphabet] at this
              have hEnvR : rightEnv.WellFormed
                  (PactTypeAlphabet.projectParallel restrict right.alphabet
                    interface) := by
                have := PactType.typeOffers_env_wellFormed hRightStep hRightWF
                rwa [PactType.reannotate_alphabet] at this
              obtain ⟨leftTarget, leftCurrent, leftFuture, hLeft, hLT, hLC, hLF⟩ :=
                ih _ hLeftSize left rfl _ leftEnv leftLabel leftResigned
                  leftCurrent' leftFuture' hLeftStep hRegular.par_left hSubLeft hEnvL
              obtain ⟨rightTarget, rightCurrent, rightFuture, hRight, hRT, hRC,
                hRF⟩ := ih _ hRightSize right rfl _ rightEnv rightLabel
                  rightResigned rightCurrent' rightFuture' hRightStep
                  hRegular.par_right hSubRight hEnvR
              subst hLT; subst hLC; subst hLF; subst hRT; subst hRC; subst hRF
              obtain ⟨hLCsub, hLFsub⟩ :=
                hLeft.offers_subset_alphabet hRegular.par_left
              obtain ⟨hRCsub, hRFsub⟩ :=
                hRight.offers_subset_alphabet hRegular.par_right
              have hAlphaL : leftTarget.alphabet = left.alphabet :=
                hLeft.preserves_alphabet hRegular.par_left.alphabetWellFormed
              have hAlphaR : rightTarget.alphabet = right.alphabet :=
                hRight.preserves_alphabet hRegular.par_right.alphabetWellFormed
              refine ⟨.par alphabet leftTarget rightTarget interface,
                hideTypeOffers interface (leftCurrent ∪ rightCurrent),
                (if TypeLabel.combine interface leftLabel rightLabel =
                    TypeLabel.tock then ∅
                  else hideTypeOffers interface (leftFuture ∪ rightFuture)),
                TypeOffers.par env leftEnv rightEnv interface alphabet left
                  leftTarget right rightTarget leftLabel rightLabel leftCurrent
                  leftFuture rightCurrent rightFuture
                  (fun h => hLeftNotSkip (reannotate_eq_skip h))
                  (fun h => hRightNotSkip (reannotate_eq_skip h)) hLeft hRight
                  (fun h => hNotBothSkip ⟨reannotate_eq_skip h.1,
                    reannotate_eq_skip h.2⟩)
                  (localTypeOfferEnvironment_unrestrict hLocalLeft hRCsub hRFsub)
                  (localTypeOfferEnvironment_unrestrict hLocalRight hLCsub hLFsub)
                  ⟨hEnvA, hPrem.2⟩, ?_, ?_, ?_⟩
              · rw [PactType.reannotate, hAlphaL, hAlphaR]
              · rw [hideTypeOffers_inter_projectParallel]
              · by_cases hTock : TypeLabel.combine interface leftLabel rightLabel =
                    TypeLabel.tock
                · rw [if_pos hTock, if_pos hTock, Finset.empty_inter]
                · rw [if_neg hTock, if_neg hTock,
                    hideTypeOffers_inter_projectParallel]
          | par_fuse _ leftEnv rightEnv _ _ _ _ leftLabel rightLabel leftCurrent'
              leftFuture' rightCurrent' rightFuture' hLeftStep hRightStep
              hLocalLeft hLocalRight hPrem hNotTock =>
              have hEnvL : leftEnv.WellFormed
                  (PactTypeAlphabet.projectParallel restrict left.alphabet
                    interface) := by
                have := PactType.typeOffers_env_wellFormed hLeftStep hLeftWF
                rwa [PactType.reannotate_alphabet] at this
              have hEnvR : rightEnv.WellFormed
                  (PactTypeAlphabet.projectParallel restrict right.alphabet
                    interface) := by
                have := PactType.typeOffers_env_wellFormed hRightStep hRightWF
                rwa [PactType.reannotate_alphabet] at this
              obtain ⟨leftTarget, leftCurrent, leftFuture, hLeft, hLT, hLC, hLF⟩ :=
                ih _ hLeftSize left rfl _ leftEnv leftLabel _ leftCurrent'
                  leftFuture' hLeftStep hRegular.par_left hSubLeft hEnvL
              obtain ⟨rightTarget, rightCurrent, rightFuture, hRight, hRT, hRC,
                hRF⟩ := ih _ hRightSize right rfl _ rightEnv rightLabel _
                  rightCurrent' rightFuture' hRightStep hRegular.par_right
                  hSubRight hEnvR
              subst hLC; subst hLF; subst hRC; subst hRF
              obtain ⟨hLCsub, hLFsub⟩ :=
                hLeft.offers_subset_alphabet hRegular.par_left
              obtain ⟨hRCsub, hRFsub⟩ :=
                hRight.offers_subset_alphabet hRegular.par_right
              have hAlphaL : leftTarget.alphabet = left.alphabet :=
                hLeft.preserves_alphabet hRegular.par_left.alphabetWellFormed
              have hAlphaR : rightTarget.alphabet = right.alphabet :=
                hRight.preserves_alphabet hRegular.par_right.alphabetWellFormed
              have hSkipL : leftTarget = .skip left.alphabet := by
                rw [PactType.reannotate_alphabet] at hLT
                rw [← hAlphaL]
                exact (reannotate_eq_skip_iff leftTarget _).mp hLT.symm
              have hSkipR : rightTarget = .skip right.alphabet := by
                rw [PactType.reannotate_alphabet] at hRT
                rw [← hAlphaR]
                exact (reannotate_eq_skip_iff rightTarget _).mp hRT.symm
              refine ⟨.skip alphabet,
                hideTypeOffers interface (leftCurrent ∪ rightCurrent),
                hideTypeOffers interface (leftFuture ∪ rightFuture),
                TypeOffers.par_fuse env leftEnv rightEnv interface alphabet left
                  right leftLabel rightLabel leftCurrent leftFuture rightCurrent
                  rightFuture (hSkipL ▸ hLeft) (hSkipR ▸ hRight)
                  (localTypeOfferEnvironment_unrestrict hLocalLeft hRCsub hRFsub)
                  (localTypeOfferEnvironment_unrestrict hLocalRight hLCsub hLFsub)
                  ⟨hEnvA, hPrem.2⟩ hNotTock, ?_, ?_, ?_⟩
              · rw [PactType.reannotate]
              · rw [hideTypeOffers_inter_projectParallel]
              · rw [hideTypeOffers_inter_projectParallel]
          | par_fuse_tock _ leftEnv rightEnv _ _ _ _ leftLabel rightLabel
              leftCurrent' leftFuture' rightCurrent' rightFuture' hLeftStep
              hRightStep hLocalLeft hLocalRight hPrem hTock =>
              have hEnvL : leftEnv.WellFormed
                  (PactTypeAlphabet.projectParallel restrict left.alphabet
                    interface) := by
                have := PactType.typeOffers_env_wellFormed hLeftStep hLeftWF
                rwa [PactType.reannotate_alphabet] at this
              have hEnvR : rightEnv.WellFormed
                  (PactTypeAlphabet.projectParallel restrict right.alphabet
                    interface) := by
                have := PactType.typeOffers_env_wellFormed hRightStep hRightWF
                rwa [PactType.reannotate_alphabet] at this
              obtain ⟨leftTarget, leftCurrent, leftFuture, hLeft, hLT, hLC, hLF⟩ :=
                ih _ hLeftSize left rfl _ leftEnv leftLabel _ leftCurrent'
                  leftFuture' hLeftStep hRegular.par_left hSubLeft hEnvL
              obtain ⟨rightTarget, rightCurrent, rightFuture, hRight, hRT, hRC,
                hRF⟩ := ih _ hRightSize right rfl _ rightEnv rightLabel _
                  rightCurrent' rightFuture' hRightStep hRegular.par_right
                  hSubRight hEnvR
              obtain ⟨hLCsub, hLFsub⟩ :=
                hLeft.offers_subset_alphabet hRegular.par_left
              obtain ⟨hRCsub, hRFsub⟩ :=
                hRight.offers_subset_alphabet hRegular.par_right
              have hAlphaL : leftTarget.alphabet = left.alphabet :=
                hLeft.preserves_alphabet hRegular.par_left.alphabetWellFormed
              have hAlphaR : rightTarget.alphabet = right.alphabet :=
                hRight.preserves_alphabet hRegular.par_right.alphabetWellFormed
              have hSkipL : leftTarget = .skip left.alphabet := by
                rw [PactType.reannotate_alphabet] at hLT
                rw [← hAlphaL]
                exact (reannotate_eq_skip_iff leftTarget _).mp hLT.symm
              have hSkipR : rightTarget = .skip right.alphabet := by
                rw [PactType.reannotate_alphabet] at hRT
                rw [← hAlphaR]
                exact (reannotate_eq_skip_iff rightTarget _).mp hRT.symm
              subst hLC; subst hLF; subst hRC; subst hRF
              refine ⟨.skip alphabet, ∅, ∅,
                TypeOffers.par_fuse_tock env leftEnv rightEnv interface alphabet left
                  right leftLabel rightLabel leftCurrent leftFuture rightCurrent
                  rightFuture (hSkipL ▸ hLeft) (hSkipR ▸ hRight)
                  (localTypeOfferEnvironment_unrestrict hLocalLeft hRCsub hRFsub)
                  (localTypeOfferEnvironment_unrestrict hLocalRight hLCsub hLFsub)
                  ⟨hEnvA, hPrem.2⟩ hTock, ?_, ?_, ?_⟩
              · rw [PactType.reannotate]
              · rw [Finset.empty_inter]
              · rw [Finset.empty_inter]
          | left_complete _ leftEnv rightEnv _ _ _ _ rightResigned _ leftCurrent'
              leftFuture' rightCurrent' rightFuture' hLeftSkip hRightNotSkip
              hLeftStep hRightStep hTargetNotSkip hLocalLeft hLocalRight
              hEnvAlpha hSync =>
              rw [PactType.reannotate_alphabet] at hLeftSkip
              have hLeftSkip' : left = .skip left.alphabet :=
                (reannotate_eq_skip_iff left _).mp hLeftSkip
              rw [hLeftSkip] at hLeftStep
              have hEnvR : rightEnv.WellFormed
                  (PactTypeAlphabet.projectParallel restrict right.alphabet
                    interface) := by
                have := PactType.typeOffers_env_wellFormed hRightStep hRightWF
                rwa [PactType.reannotate_alphabet] at this
              obtain ⟨rightTarget, rightCurrent, rightFuture, hRight, hRT, hRC,
                hRF⟩ := ih _ hRightSize right rfl _ rightEnv label rightResigned
                  rightCurrent' rightFuture' hRightStep hRegular.par_right
                  hSubRight hEnvR
              subst hRC; subst hRF
              obtain ⟨hRCsub, hRFsub⟩ :=
                hRight.offers_subset_alphabet hRegular.par_right
              obtain ⟨hScoped', hInterfaces'⟩ := hRight.preserves_scoping
                hRegular.par_right.interfaceScoped hRegular.par_right.tailRecursive
              have hIS := hRegular.interfaceScoped
              have hIAS := hRegular.interfaceAlphabetScoped
              simp only [PactType.InterfaceScoped] at hIS
              simp only [PactType.InterfaceAlphabetScoped] at hIAS
              have hAvoidAlpha : ∀ action ∈ alphabet.actions,
                  action.1 ∉ PactType.ParallelInterfaces rightTarget := by
                intro action hAction hIn
                exact Finset.disjoint_left.mp hIAS.1
                  (Finset.mem_image.mpr ⟨action, hAction, rfl⟩)
                  (Finset.mem_union_right _ (hInterfaces' hIn))
              have hAvoidChild : ∀ action ∈ (PactTypeAlphabet.projectParallel
                  restrict right.alphabet interface).actions,
                  action.1 ∉ PactType.ParallelInterfaces rightTarget := by
                intro action hAction hIn
                rcases Finset.mem_union.mp hAction with h | h
                · exact Finset.disjoint_left.mp hIS.1 (Finset.mem_filter.mp h).2
                    (Finset.mem_union_right _ (hInterfaces' hIn))
                · exact hAvoidAlpha action (hSubA h) hIn
              have hHide : ∀ offers : Finset BareMessage,
                  offers ⊆ right.alphabet.actions →
                  hideTypeOffers interface (offers ∩
                      (PactTypeAlphabet.projectParallel restrict right.alphabet
                        interface).actions) =
                    hideTypeOffers interface offers ∩ restrict.actions := by
                intro offers _
                have h := hideTypeOffers_inter_projectParallel (parent := restrict)
                  (left := left.alphabet) (right := right.alphabet)
                  (interface := interface) ∅ offers
                rw [Finset.empty_inter, Finset.empty_union, Finset.empty_union] at h
                exact h
              cases hLeftStep with
              | skip _ _ hPremL =>
                  have hEnvLA : leftEnv.WellFormed left.alphabet :=
                    TypeEnvironment.wellFormed_mono hPremL.1 hSubLeft
                  have hLeftStepU : TypeOffers leftEnv left TypeLabel.silent left ∅
                      (typeFutureOffers (.skip left.alphabet)) := by
                    rw [hLeftSkip']
                    exact TypeOffers.skip leftEnv left.alphabet ⟨hEnvLA, hPremL.2⟩
                  rw [typeFutureOffers_skip] at hLocalRight
                  refine ⟨rightTarget.reannotate alphabet,
                    hideTypeOffers interface rightCurrent,
                    hideTypeOffers interface rightFuture,
                    TypeOffers.left_complete env leftEnv rightEnv interface alphabet
                      left right rightTarget label ∅
                      (typeFutureOffers (.skip left.alphabet)) rightCurrent
                      rightFuture hLeftSkip'
                      (fun h => hRightNotSkip (reannotate_eq_skip h)) hLeftStepU
                      hRight (fun h => hTargetNotSkip (hRT ▸ reannotate_eq_skip h))
                      (localTypeOfferEnvironment_unrestrict hLocalLeft hRCsub hRFsub)
                      (by
                        rw [typeFutureOffers_skip]
                        exact hLocalRight.congr_localType)
                      hEnvA hSync, ?_, ?_, ?_⟩
                  · rw [hRT, reannotate_reannotate_of_avoiding rightTarget _ restrict
                      hScoped' hAvoidChild,
                      reannotate_reannotate_of_avoiding rightTarget alphabet restrict
                        hScoped' hAvoidAlpha]
                  · rw [hHide rightCurrent hRCsub]
                  · rw [hHide rightFuture hRFsub]
          | right_complete _ leftEnv rightEnv _ _ _ leftResigned _ _ leftCurrent'
              leftFuture' rightCurrent' rightFuture' hRightSkip hLeftNotSkip
              hRightStep hLeftStep hTargetNotSkip hLocalLeft hLocalRight
              hEnvAlpha hSync =>
              rw [PactType.reannotate_alphabet] at hRightSkip
              have hRightSkip' : right = .skip right.alphabet :=
                (reannotate_eq_skip_iff right _).mp hRightSkip
              rw [hRightSkip] at hRightStep
              have hEnvL : leftEnv.WellFormed
                  (PactTypeAlphabet.projectParallel restrict left.alphabet
                    interface) := by
                have := PactType.typeOffers_env_wellFormed hLeftStep hLeftWF
                rwa [PactType.reannotate_alphabet] at this
              obtain ⟨leftTarget, leftCurrent, leftFuture, hLeft, hLT, hLC, hLF⟩ :=
                ih _ hLeftSize left rfl _ leftEnv label leftResigned leftCurrent'
                  leftFuture' hLeftStep hRegular.par_left hSubLeft hEnvL
              subst hLC; subst hLF
              obtain ⟨hLCsub, hLFsub⟩ :=
                hLeft.offers_subset_alphabet hRegular.par_left
              obtain ⟨hScoped', hInterfaces'⟩ := hLeft.preserves_scoping
                hRegular.par_left.interfaceScoped hRegular.par_left.tailRecursive
              have hIS := hRegular.interfaceScoped
              have hIAS := hRegular.interfaceAlphabetScoped
              simp only [PactType.InterfaceScoped] at hIS
              simp only [PactType.InterfaceAlphabetScoped] at hIAS
              have hAvoidAlpha : ∀ action ∈ alphabet.actions,
                  action.1 ∉ PactType.ParallelInterfaces leftTarget := by
                intro action hAction hIn
                exact Finset.disjoint_left.mp hIAS.1
                  (Finset.mem_image.mpr ⟨action, hAction, rfl⟩)
                  (Finset.mem_union_left _
                    (Finset.mem_union_right _ (hInterfaces' hIn)))
              have hAvoidChild : ∀ action ∈ (PactTypeAlphabet.projectParallel
                  restrict left.alphabet interface).actions,
                  action.1 ∉ PactType.ParallelInterfaces leftTarget := by
                intro action hAction hIn
                rcases Finset.mem_union.mp hAction with h | h
                · exact Finset.disjoint_left.mp hIS.1 (Finset.mem_filter.mp h).2
                    (Finset.mem_union_left _ (hInterfaces' hIn))
                · exact hAvoidAlpha action (hSubA h) hIn
              have hHide : ∀ offers : Finset BareMessage,
                  offers ⊆ left.alphabet.actions →
                  hideTypeOffers interface (offers ∩
                      (PactTypeAlphabet.projectParallel restrict left.alphabet
                        interface).actions) =
                    hideTypeOffers interface offers ∩ restrict.actions := by
                intro offers _
                have h := hideTypeOffers_inter_projectParallel (parent := restrict)
                  (left := left.alphabet) (right := right.alphabet)
                  (interface := interface) offers ∅
                rw [Finset.empty_inter, Finset.union_empty, Finset.union_empty] at h
                exact h
              cases hRightStep with
              | skip _ _ hPremR =>
                  have hEnvRA : rightEnv.WellFormed right.alphabet :=
                    TypeEnvironment.wellFormed_mono hPremR.1 hSubRight
                  have hRightStepU : TypeOffers rightEnv right TypeLabel.silent right
                      ∅ (typeFutureOffers (.skip right.alphabet)) := by
                    rw [hRightSkip']
                    exact TypeOffers.skip rightEnv right.alphabet ⟨hEnvRA, hPremR.2⟩
                  rw [typeFutureOffers_skip] at hLocalLeft
                  refine ⟨leftTarget.reannotate alphabet,
                    hideTypeOffers interface leftCurrent,
                    hideTypeOffers interface leftFuture,
                    TypeOffers.right_complete env leftEnv rightEnv interface alphabet
                      left leftTarget right label leftCurrent leftFuture ∅
                      (typeFutureOffers (.skip right.alphabet)) hRightSkip'
                      (fun h => hLeftNotSkip (reannotate_eq_skip h)) hRightStepU
                      hLeft (fun h => hTargetNotSkip (hLT ▸ reannotate_eq_skip h))
                      (by
                        rw [typeFutureOffers_skip]
                        exact hLocalLeft.congr_localType)
                      (localTypeOfferEnvironment_unrestrict hLocalRight hLCsub hLFsub)
                      hEnvA hSync, ?_, ?_, ?_⟩
                  · rw [hLT, reannotate_reannotate_of_avoiding leftTarget _ restrict
                      hScoped' hAvoidChild,
                      reannotate_reannotate_of_avoiding leftTarget alphabet restrict
                        hScoped' hAvoidAlpha]
                  · rw [hHide leftCurrent hLCsub]
                  · rw [hHide leftFuture hLFsub]

/-! ## Unfolding preserves the remaining structural side conditions

`TailRec` keeps the recursion variable out of parallel components and
conjunctive branches, so substitution leaves those subterms alone. -/

theorem PactType.replaceVar_conjunctiveMessageOwnership (name : String)
    (replacement : PactType) :
    ∀ processType : PactType,
      processType.ConjunctiveMessageOwnership →
      processType.TailOccurrences name True →
      replacement.ConjunctiveMessageOwnership →
      (processType.replaceVar name replacement).ConjunctiveMessageOwnership := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.ConjunctiveMessageOwnershipBodies branches →
          PactType.TailBranchOccurrences name True branches →
          replacement.ConjunctiveMessageOwnership →
          PactType.ConjunctiveMessageOwnershipBodies
            (PactType.replaceBranches branches name replacement) := by
        intro branches hBranchesSize hOwn hTail hReplacement
        induction branches with
        | nil => simp [PactType.replaceBranches,
            PactType.ConjunctiveMessageOwnershipBodies]
        | cons head rest restIH =>
            rcases head with ⟨action, body⟩
            simp only [PactType.ConjunctiveMessageOwnershipBodies] at hOwn
            simp only [PactType.TailBranchOccurrences] at hTail
            have hBodySize : sizeOf body < n := by
              have h1 : sizeOf body < sizeOf (action, body) := by simp_wf; omega
              have h2 : sizeOf (action, body) <
                  sizeOf ((action, body) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have : sizeOf rest < sizeOf ((action, body) :: rest) := by
                simp_wf; omega
              omega
            simp only [PactType.replaceBranches,
              PactType.ConjunctiveMessageOwnershipBodies]
            exact ⟨ih (sizeOf body) hBodySize body rfl hOwn.1 hTail.1 hReplacement,
              restIH hRestSize hOwn.2 hTail.2⟩
      intro hOwn hTail hReplacement
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ =>
          simp [PactType.replaceVar, PactType.ConjunctiveMessageOwnership]
      | var alphabet current =>
          by_cases hName : name = current
          · simpa [PactType.replaceVar, hName] using hReplacement
          · simp [PactType.replaceVar, hName, PactType.ConjunctiveMessageOwnership]
      | recur alphabet current body =>
          by_cases hName : name = current
          · simpa [PactType.replaceVar, hName] using hOwn
          · have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            simp only [PactType.ConjunctiveMessageOwnership] at hOwn
            simp only [PactType.TailOccurrences,
              if_neg (fun h : current = name => hName h.symm)] at hTail
            simp only [PactType.replaceVar, if_neg hName,
              PactType.ConjunctiveMessageOwnership]
            exact ih (sizeOf body) hBodySize body rfl hOwn hTail hReplacement
      | choice alphabet left right | fairChoice alphabet _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ConjunctiveMessageOwnership] at hOwn
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.ConjunctiveMessageOwnership]
          exact ⟨ih (sizeOf left) hLeftSize left rfl hOwn.1 hTail.1 hReplacement,
            ih (sizeOf right) hRightSize right rfl hOwn.2 hTail.2 hReplacement⟩
      | seq alphabet left right =>
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ConjunctiveMessageOwnership] at hOwn
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.ConjunctiveMessageOwnership]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
            replacement left hTail.1]
          exact ⟨hOwn.1, ih (sizeOf right) hRightSize right rfl hOwn.2 hTail.2
            hReplacement⟩
      | par alphabet left right interface =>
          simp only [PactType.ConjunctiveMessageOwnership] at hOwn
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.ConjunctiveMessageOwnership]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement left hTail.1,
            PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement right hTail.2]
          exact hOwn
      | xoffer alphabet elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.ConjunctiveMessageOwnership] at hOwn
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.ConjunctiveMessageOwnership]
          exact ⟨ih (sizeOf elseType) hElseSize elseType rfl hOwn.1 hTail.1
              hReplacement,
            hBranches branches hBranchesSize hOwn.2 hTail.2 hReplacement⟩
      | offer alphabet elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ConjunctiveMessageOwnership] at hOwn
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.ConjunctiveMessageOwnership]
          rw [PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false
            name replacement branches hTail.2]
          exact ⟨ih (sizeOf elseType) hElseSize elseType rfl hOwn.1 hTail.1
            hReplacement, hOwn.2⟩

lemma parallelBranchInterfaces_replaceBranches (name : String)
    (replacement : PactType) :
    ∀ branches : List (BareMessage × PactType),
      PactType.ParallelBranchInterfaces
          (PactType.replaceBranches branches name replacement) ⊆
        PactType.ParallelBranchInterfaces branches ∪
          PactType.ParallelInterfaces replacement := by
  intro branches
  induction branches with
  | nil => simp [PactType.replaceBranches, PactType.ParallelBranchInterfaces]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      simp only [PactType.replaceBranches, PactType.ParallelBranchInterfaces]
      refine Finset.union_subset ?_ ?_
      · exact ((replaceVar_ownership_subset name replacement body).2.2.2.2).trans
          (Finset.union_subset_union_left Finset.subset_union_left)
      · exact ih.trans (Finset.union_subset_union_left Finset.subset_union_right)

theorem PactType.replaceVar_interfaceAlphabetScoped (name : String)
    (replacement : PactType) :
    ∀ processType : PactType,
      processType.AlphabetWellFormed →
      processType.InterfaceAlphabetScoped →
      processType.TailOccurrences name True →
      replacement.InterfaceAlphabetScoped →
      (∀ action ∈ processType.alphabet.actions,
        action.1 ∉ PactType.ParallelInterfaces replacement) →
      (processType.replaceVar name replacement).InterfaceAlphabetScoped := by
  have hDisjointOf : ∀ alphabet : PactTypeAlphabet,
      (∀ action ∈ alphabet.actions,
        action.1 ∉ PactType.ParallelInterfaces replacement) →
      Disjoint (PactTypeAlphabet.messageIds alphabet)
        (PactType.ParallelInterfaces replacement) := by
    intro alphabet hAvoid
    refine Finset.disjoint_left.mpr ?_
    intro msg hMsg hIn
    obtain ⟨action, hAction, rfl⟩ := Finset.mem_image.mp hMsg
    exact hAvoid action hAction hIn
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (alphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.BranchesAlphabetWellFormed alphabet branches →
          PactType.InterfaceAlphabetScopedBranches branches →
          PactType.TailBranchOccurrences name True branches →
          replacement.InterfaceAlphabetScoped →
          (∀ action ∈ alphabet.actions,
            action.1 ∉ PactType.ParallelInterfaces replacement) →
          PactType.InterfaceAlphabetScopedBranches
            (PactType.replaceBranches branches name replacement) := by
        intro branches alphabet hBranchesSize hWF hScoped hTail hReplacement hAvoid
        induction branches with
        | nil => simp [PactType.replaceBranches,
            PactType.InterfaceAlphabetScopedBranches]
        | cons head rest restIH =>
            rcases head with ⟨action, body⟩
            simp only [PactType.BranchesAlphabetWellFormed] at hWF
            simp only [PactType.InterfaceAlphabetScopedBranches] at hScoped
            simp only [PactType.TailBranchOccurrences] at hTail
            have hBodySize : sizeOf body < n := by
              have h1 : sizeOf body < sizeOf (action, body) := by simp_wf; omega
              have h2 : sizeOf (action, body) <
                  sizeOf ((action, body) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have : sizeOf rest < sizeOf ((action, body) :: rest) := by
                simp_wf; omega
              omega
            simp only [PactType.replaceBranches,
              PactType.InterfaceAlphabetScopedBranches]
            exact ⟨ih (sizeOf body) hBodySize body rfl hWF.2.1 hScoped.1 hTail.1
                hReplacement (by rw [hWF.1]; exact hAvoid),
              restIH hRestSize hWF.2.2 hScoped.2 hTail.2⟩
      intro hWF hScoped hTail hReplacement hAvoid
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ =>
          rw [PactType.replaceVar]
          simp only [PactType.InterfaceAlphabetScoped]
      | var alphabet current =>
          by_cases hName : name = current
          · simpa [PactType.replaceVar, hName] using hReplacement
          · simp [PactType.replaceVar, hName, PactType.InterfaceAlphabetScoped]
      | recur alphabet current body =>
          by_cases hName : name = current
          · simpa [PactType.replaceVar, hName] using hScoped
          · have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            simp only [PactType.AlphabetWellFormed] at hWF
            simp only [PactType.InterfaceAlphabetScoped] at hScoped
            simp only [PactType.TailOccurrences,
              if_neg (fun h : current = name => hName h.symm)] at hTail
            simp only [PactType.alphabet] at hAvoid
            simp only [PactType.replaceVar, if_neg hName,
              PactType.InterfaceAlphabetScoped]
            refine ⟨Finset.disjoint_union_right.mpr ?_ |>.mono_right
                ((replaceVar_ownership_subset name replacement body).2.2.2.2),
              ih (sizeOf body) hBodySize body rfl hWF.2.2 hScoped.2 hTail
                hReplacement (by rw [hWF.2.1]; exact hAvoid)⟩
            exact ⟨hScoped.1, hDisjointOf alphabet hAvoid⟩
      | choice alphabet left right | fairChoice alphabet _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceAlphabetScoped] at hScoped
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.alphabet] at hAvoid
          simp only [PactType.replaceVar, PactType.InterfaceAlphabetScoped]
          refine ⟨?_, ih (sizeOf left) hLeftSize left rfl hWF.2.2.2.1 hScoped.2.1
              hTail.1 hReplacement (by rw [hWF.2.1]; exact hAvoid),
            ih (sizeOf right) hRightSize right rfl hWF.2.2.2.2 hScoped.2.2 hTail.2
              hReplacement (by rw [hWF.2.2.1]; exact hAvoid)⟩
          refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
          · exact (Finset.disjoint_union_right.mpr
              ⟨hScoped.1.mono_right Finset.subset_union_left,
                hDisjointOf alphabet hAvoid⟩).mono_right
              ((replaceVar_ownership_subset name replacement left).2.2.2.2)
          · exact (Finset.disjoint_union_right.mpr
              ⟨hScoped.1.mono_right Finset.subset_union_right,
                hDisjointOf alphabet hAvoid⟩).mono_right
              ((replaceVar_ownership_subset name replacement right).2.2.2.2)
      | seq alphabet left right =>
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceAlphabetScoped] at hScoped
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.alphabet] at hAvoid
          simp only [PactType.replaceVar, PactType.InterfaceAlphabetScoped]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
            replacement left hTail.1]
          refine ⟨?_, hScoped.2.1,
            ih (sizeOf right) hRightSize right rfl hWF.2.2.2.2 hScoped.2.2 hTail.2
              hReplacement (by rw [hWF.2.2.1]; exact hAvoid)⟩
          refine Finset.disjoint_union_right.mpr
            ⟨hScoped.1.mono_right Finset.subset_union_left, ?_⟩
          exact (Finset.disjoint_union_right.mpr
            ⟨hScoped.1.mono_right Finset.subset_union_right,
              hDisjointOf alphabet hAvoid⟩).mono_right
            ((replaceVar_ownership_subset name replacement right).2.2.2.2)
      | par alphabet left right interface =>
          simp only [PactType.InterfaceAlphabetScoped] at hScoped
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.InterfaceAlphabetScoped]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement left hTail.1,
            PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement right hTail.2]
          exact hScoped
      | xoffer alphabet elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceAlphabetScoped] at hScoped
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.alphabet] at hAvoid
          simp only [PactType.replaceVar, PactType.InterfaceAlphabetScoped]
          refine ⟨?_, ih (sizeOf elseType) hElseSize elseType rfl hWF.2.2.1
              hScoped.2.1 hTail.1 hReplacement (by rw [hWF.2.1]; exact hAvoid),
            hBranches branches alphabet hBranchesSize hWF.2.2.2 hScoped.2.2 hTail.2
              hReplacement hAvoid⟩
          refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
          · exact (Finset.disjoint_union_right.mpr
              ⟨hScoped.1.mono_right Finset.subset_union_left,
                hDisjointOf alphabet hAvoid⟩).mono_right
              ((replaceVar_ownership_subset name replacement elseType).2.2.2.2)
          · exact (Finset.disjoint_union_right.mpr
              ⟨hScoped.1.mono_right Finset.subset_union_right,
                hDisjointOf alphabet hAvoid⟩).mono_right
              (parallelBranchInterfaces_replaceBranches name replacement branches)
      | offer alphabet elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceAlphabetScoped] at hScoped
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.alphabet] at hAvoid
          simp only [PactType.replaceVar, PactType.InterfaceAlphabetScoped]
          rw [PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false
            name replacement branches hTail.2]
          refine ⟨?_, ih (sizeOf elseType) hElseSize elseType rfl hWF.2.2.1
              hScoped.2.1 hTail.1 hReplacement (by rw [hWF.2.1]; exact hAvoid),
            hScoped.2.2⟩
          refine Finset.disjoint_union_right.mpr ⟨?_,
            hScoped.1.mono_right Finset.subset_union_right⟩
          exact (Finset.disjoint_union_right.mpr
            ⟨hScoped.1.mono_right Finset.subset_union_left,
              hDisjointOf alphabet hAvoid⟩).mono_right
            ((replaceVar_ownership_subset name replacement elseType).2.2.2.2)

/-! ## A step preserves the side conditions

The paper's "type steps preserve alphabet well-formedness", together with the
two clauses the Lean formulation also carries. -/

set_option maxHeartbeats 1000000 in
theorem TypeOffers.preserves_regularity
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future) :
    ResignRegular source →
      target.AlphabetWellFormed ∧ target.InterfaceAlphabetScoped ∧
        target.TailRecursive ∧ target.ConjunctiveMessageOwnership := by
  induction hOffers with
  | action env alphabet msg dir hPrem
  | cycle env alphabet hPrem
  | progress env alphabet pid hPrem =>
      intro hRegular
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA ⊢
      simp only [PactType.InterfaceAlphabetScoped, PactType.TailRecursive,
        PactType.ConjunctiveMessageOwnership]
      exact ⟨hA, trivial, trivial, trivial⟩
  | action_wait env alphabet msg dir hPrem
  | cycle_wait env alphabet hPrem
  | skip env alphabet hPrem
  | xoffer_wait env alphabet elseType branches hPrem
  | offer_wait env alphabet elseType branches hPrem =>
      intro hRegular
      exact ⟨hRegular.alphabetWellFormed, hRegular.interfaceAlphabetScoped,
        hRegular.tailRecursive, hRegular.conjunctive⟩
  | choice_left env alphabet left right hPrem =>
      intro hRegular
      exact ⟨hRegular.choice_left.alphabetWellFormed,
        hRegular.choice_left.interfaceAlphabetScoped,
        hRegular.choice_left.tailRecursive, hRegular.choice_left.conjunctive⟩
  | choice_right env alphabet left right hPrem =>
      intro hRegular
      exact ⟨hRegular.choice_right.alphabetWellFormed,
        hRegular.choice_right.interfaceAlphabetScoped,
        hRegular.choice_right.tailRecursive, hRegular.choice_right.conjunctive⟩
  | fair_left env alphabet bid left right hPrem =>
      intro hRegular
      exact ⟨hRegular.fair_left.alphabetWellFormed,
        hRegular.fair_left.interfaceAlphabetScoped,
        hRegular.fair_left.tailRecursive, hRegular.fair_left.conjunctive⟩
  | fair_right env alphabet bid left right hPrem =>
      intro hRegular
      exact ⟨hRegular.fair_right.alphabetWellFormed,
        hRegular.fair_right.interfaceAlphabetScoped,
        hRegular.fair_right.tailRecursive, hRegular.fair_right.conjunctive⟩
  | recur env alphabet name body hPrem =>
      intro hRegular
      have hA := hRegular.alphabetWellFormed
      have hAS := hRegular.interfaceAlphabetScoped
      have hT := hRegular.tailRecursive
      have hC := hRegular.conjunctive
      simp only [PactType.AlphabetWellFormed] at hA
      simp only [PactType.InterfaceAlphabetScoped] at hAS
      simp only [PactType.TailRecursive] at hT
      simp only [PactType.ConjunctiveMessageOwnership] at hC
      have hReplAlpha : (PactType.recur alphabet name body).alphabet =
          body.alphabet := by rw [PactType.alphabet]; exact hA.2.1.symm
      have hAvoid : ∀ action ∈ body.alphabet.actions,
          action.1 ∉ PactType.ParallelInterfaces (.recur alphabet name body) := by
        intro action hAction hIn
        rw [PactType.ParallelInterfaces] at hIn
        rw [hA.2.1] at hAction
        exact Finset.disjoint_left.mp hAS.1
          (Finset.mem_image.mpr ⟨action, hAction, rfl⟩) hIn
      refine ⟨PactType.replaceVar_alphabetWellFormed name
          hRegular.alphabetWellFormed body hA.2.2 hReplAlpha hT.1, ?_, ?_, ?_⟩
      · exact PactType.replaceVar_interfaceAlphabetScoped name
          (.recur alphabet name body) body hA.2.2 hAS.2 hT.1
          hRegular.interfaceAlphabetScoped hAvoid
      · exact PactType.tailRecursive_replaceVar name hRegular.tailRecursive
          hRegular.tailClosed body hT.2 hT.1
      · exact PactType.replaceVar_conjunctiveMessageOwnership name
          (.recur alphabet name body) body hC hT.1 hRegular.conjunctive
  | seq env alphabet left left' right label current childFuture hChild hNotSkip
      hNotTock ih
  | seq_tock env alphabet left left' right current childFuture hChild hNotSkip
      ih =>
      intro hRegular
      have hA := hRegular.alphabetWellFormed
      have hAS := hRegular.interfaceAlphabetScoped
      have hT := hRegular.tailRecursive
      have hC := hRegular.conjunctive
      simp only [PactType.AlphabetWellFormed] at hA
      simp only [PactType.InterfaceAlphabetScoped] at hAS
      simp only [PactType.TailRecursive] at hT
      simp only [PactType.ConjunctiveMessageOwnership] at hC
      obtain ⟨hAWF', hIAS', hTR', hCMO'⟩ := ih hRegular.seq_left
      have hAlpha : left'.alphabet = left.alphabet :=
        hChild.preserves_alphabet hRegular.seq_left.alphabetWellFormed
      obtain ⟨-, hPI⟩ := hChild.preserves_scoping
        hRegular.seq_left.interfaceScoped hRegular.seq_left.tailRecursive
      simp only [PactType.AlphabetWellFormed, PactType.InterfaceAlphabetScoped,
        PactType.TailRecursive, PactType.ConjunctiveMessageOwnership]
      exact ⟨⟨hA.1, by rw [hAlpha]; exact hA.2.1, hA.2.2.1, hAWF', hA.2.2.2.2⟩,
        ⟨hAS.1.mono_right (Finset.union_subset_union hPI (Finset.Subset.refl _)),
          hIAS', hAS.2.2⟩,
        ⟨hTR', hT.2⟩, ⟨hCMO', hC.2⟩⟩
  | seq_fuse env alphabet skipAlphabet left right label current childFuture
      hChild hNotTock ih
  | seq_fuse_tock env alphabet skipAlphabet left right current childFuture
      hChild ih =>
      intro hRegular
      exact ⟨hRegular.seq_right.alphabetWellFormed,
        hRegular.seq_right.interfaceAlphabetScoped,
        hRegular.seq_right.tailRecursive, hRegular.seq_right.conjunctive⟩
  | xoffer_branch env alphabet elseType branches action processType hPrem =>
      intro hRegular
      have hBranch := (hRegular.xoffer_branch hPrem.2.1).1
      exact ⟨hBranch.alphabetWellFormed, hBranch.interfaceAlphabetScoped,
        hBranch.tailRecursive, hBranch.conjunctive⟩
  | xoffer_else env alphabet elseType branches hPrem =>
      intro hRegular
      exact ⟨hRegular.xoffer_else.alphabetWellFormed,
        hRegular.xoffer_else.interfaceAlphabetScoped,
        hRegular.xoffer_else.tailRecursive, hRegular.xoffer_else.conjunctive⟩
  | offer_else env alphabet elseType branches hPrem =>
      intro hRegular
      exact ⟨hRegular.offer_else.alphabetWellFormed,
        hRegular.offer_else.interfaceAlphabetScoped,
        hRegular.offer_else.tailRecursive, hRegular.offer_else.conjunctive⟩
  | offer_some env alphabet elseType branches enabled hPrem =>
      intro hRegular
      have hAS := hRegular.interfaceAlphabetScoped
      have hT := hRegular.tailRecursive
      have hC := hRegular.conjunctive
      simp only [PactType.InterfaceAlphabetScoped] at hAS
      simp only [PactType.TailRecursive] at hT
      simp only [PactType.ConjunctiveMessageOwnership] at hC
      have hAvoid : ∀ action ∈ alphabet.actions,
          action.1 ∉ PactType.ParallelBranchInterfaces branches := by
        intro action hAction hIn
        exact Finset.disjoint_left.mp hAS.1
          (Finset.mem_image.mpr ⟨action, hAction, rfl⟩)
          (Finset.mem_union_right _ hIn)
      have hBranchTR : ∀ branch ∈ branches, branch.2.TailRecursive :=
        fun branch hb => tailRecursive_of_mem_branches hT.2 hb
      exact ⟨committedOffer_alphabetWellFormed alphabet elseType branches enabled
          hRegular.alphabetWellFormed hRegular.interfaceScoped
          hRegular.interfaceAlphabetScoped hPrem.2.1,
        parallelTypeBranchesSelecting_interfaceAlphabetScoped alphabet enabled
          branches hAS.2.2 hAvoid,
        parallelTypeBranchesSelecting_tailRecursive alphabet enabled branches
          hBranchTR (hBranchTR enabled hPrem.2.1),
        parallelTypeBranchesSelecting_conjunctiveMessageOwnership alphabet enabled
          branches hC.2⟩
  | par outer leftEnv rightEnv interface alphabet left left' right right'
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      hLeftNotSkip hRightNotSkip hLeft hRight hNotBothSkip hLocalLeft hLocalRight
      hPrem ihLeft ihRight =>
      intro hRegular
      have hA := hRegular.alphabetWellFormed
      have hAS := hRegular.interfaceAlphabetScoped
      simp only [PactType.AlphabetWellFormed] at hA
      simp only [PactType.InterfaceAlphabetScoped] at hAS
      obtain ⟨hAWFL, hIASL, hTRL, hCMOL⟩ := ihLeft hRegular.par_left
      obtain ⟨hAWFR, hIASR, hTRR, hCMOR⟩ := ihRight hRegular.par_right
      have hAlphaL : left'.alphabet = left.alphabet :=
        hLeft.preserves_alphabet hRegular.par_left.alphabetWellFormed
      have hAlphaR : right'.alphabet = right.alphabet :=
        hRight.preserves_alphabet hRegular.par_right.alphabetWellFormed
      obtain ⟨-, hPIL⟩ := hLeft.preserves_scoping
        hRegular.par_left.interfaceScoped hRegular.par_left.tailRecursive
      obtain ⟨-, hPIR⟩ := hRight.preserves_scoping
        hRegular.par_right.interfaceScoped hRegular.par_right.tailRecursive
      simp only [PactType.AlphabetWellFormed, PactType.InterfaceAlphabetScoped,
        PactType.TailRecursive, PactType.ConjunctiveMessageOwnership]
      exact ⟨⟨hA.1, by rw [hAlphaL, hAlphaR]; exact hA.2.1, hAWFL, hAWFR⟩,
        ⟨hAS.1.mono_right (Finset.union_subset_union
          (Finset.union_subset_union (Finset.Subset.refl _) hPIL) hPIR),
          hIASL, hIASR⟩,
        ⟨hTRL, hTRR⟩, ⟨hCMOL, hCMOR⟩⟩
  | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeft hRight
      hLocalLeft hLocalRight hPrem hNotTock ihLeft ihRight
  | par_fuse_tock outer leftEnv rightEnv interface alphabet left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeft hRight
      hLocalLeft hLocalRight hPrem hTock ihLeft ihRight =>
      intro hRegular
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA ⊢
      simp only [PactType.InterfaceAlphabetScoped, PactType.TailRecursive,
        PactType.ConjunctiveMessageOwnership]
      exact ⟨hA.1, trivial, trivial, trivial⟩
  | left_complete outer leftEnv rightEnv interface alphabet left right right'
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftSkip
      hRightNotSkip hLeft hRight hTargetNotSkip hLocalLeft hLocalRight hEnv hSync
      ihLeft ihRight =>
      intro hRegular
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      obtain ⟨hAWFR, hIASR, hTRR, hCMOR⟩ := ihRight hRegular.par_right
      obtain ⟨hISR, -⟩ := hRight.preserves_scoping
        hRegular.par_right.interfaceScoped hRegular.par_right.tailRecursive
      have hTCR : right'.TailClosed := fun other =>
        hRight.preserves_tailOccurrences other True
          hRegular.par_right.tailRecursive (hRegular.par_right.tailClosed other)
      have hAlphaR : right'.alphabet = right.alphabet :=
        hRight.preserves_alphabet hRegular.par_right.alphabetWellFormed
      have hSubR : alphabet.actions ⊆ right'.alphabet.actions := by
        rw [hAlphaR]; exact parent_actions_subset_right hA.2.1
      have hTargetRegular : ResignRegular right' :=
        ⟨hAWFR, hISR, hIASR, hTRR, hTCR, hCMOR⟩
      have := hTargetRegular.reannotate hSubR
      exact ⟨this.alphabetWellFormed, this.interfaceAlphabetScoped,
        this.tailRecursive, this.conjunctive⟩
  | right_complete outer leftEnv rightEnv interface alphabet left left' right
      leftLabel leftCurrent leftFuture rightCurrent rightFuture hRightSkip
      hLeftNotSkip hRight hLeft hTargetNotSkip hLocalLeft hLocalRight hEnv hSync
      ihRight ihLeft =>
      intro hRegular
      have hA := hRegular.alphabetWellFormed
      simp only [PactType.AlphabetWellFormed] at hA
      obtain ⟨hAWFL, hIASL, hTRL, hCMOL⟩ := ihLeft hRegular.par_left
      obtain ⟨hISL, -⟩ := hLeft.preserves_scoping
        hRegular.par_left.interfaceScoped hRegular.par_left.tailRecursive
      have hTCL : left'.TailClosed := fun other =>
        hLeft.preserves_tailOccurrences other True
          hRegular.par_left.tailRecursive (hRegular.par_left.tailClosed other)
      have hAlphaL : left'.alphabet = left.alphabet :=
        hLeft.preserves_alphabet hRegular.par_left.alphabetWellFormed
      have hSubL : alphabet.actions ⊆ left'.alphabet.actions := by
        rw [hAlphaL]; exact parent_actions_subset_left hA.2.1
      have hTargetRegular : ResignRegular left' :=
        ⟨hAWFL, hISL, hIASL, hTRL, hTCL, hCMOL⟩
      have := hTargetRegular.reannotate hSubL
      exact ⟨this.alphabetWellFormed, this.interfaceAlphabetScoped,
        this.tailRecursive, this.conjunctive⟩

/-- Every residual of a regular type is regular. -/
theorem TypeOffers.preserves_resignRegular
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future)
    (hRegular : ResignRegular source) : ResignRegular target := by
  obtain ⟨hAWF, hIAS, hTR, hCMO⟩ := hOffers.preserves_regularity hRegular
  exact ⟨hAWF, (hOffers.preserves_scoping hRegular.interfaceScoped
      hRegular.tailRecursive).1, hIAS, hTR,
    fun other => hOffers.preserves_tailOccurrences other True
      hRegular.tailRecursive (hRegular.tailClosed other), hCMO⟩

end

end Pact



