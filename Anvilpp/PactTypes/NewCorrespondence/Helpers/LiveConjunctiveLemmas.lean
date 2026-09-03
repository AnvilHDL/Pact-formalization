import Anvilpp.PactTypes.Syntax.LiveEquivalenceLemmas
import Anvilpp.PactTypes.NewCorrespondence.Helpers.AlphabetPreservation

/-!
The conjunctive-offer expansion respects live equivalence.

`parallelTypeBranchesSelecting` is the paper's `C_{B,a_j}`.  Its alphabets are
computed from the node alphabet, `PactType.branchAlphabetActions` and the
branches' own actions, and its bodies are re-signed by `PactType.reannotate`,
so the main theorem rests on `liveEqBody_reannotate`: re-signing preserves
`PactType.LiveEqBody` whenever the two target alphabets agree on the actions
the re-signed term still uses.

Two departures from the wording of the goal statement.

First, the two products are built at two alphabets rather than one, related by
`PactTypeAlphabet.AgreeOn` on the branch actions.  That is what an offer node
supplies: `PactType.LiveEqBody` equates the annotations of two `.offer` nodes
only on the actions they still use, and the recursion hands each tail product a
different alphabet.  Taking a single shared alphabet is the special case.

Second, `PactType.LiveEqBranches` alone is not enough, and the two extra
premises are the ones a well-formed conjunctive offer already carries.

* `PactType.branchAlphabetActions` and the left factor of each product read the
  branch bodies' own alphabet annotations, which live equivalence does not
  equate.  `BranchAlphabetsAgreeOn` records the agreement needed, and
  `branchAlphabetsAgreeOn_of_offerBranchesWellFormed` derives it from
  `PactType.OfferBranchesWellFormed` — the paper's `ConjunctCompatible` — on
  both lists, which pins every branch alphabet to the offer alphabet minus the
  siblings' declarations.
* `parallelTypeBranchesSelectingWithin` picks the committed branch with the
  syntactic test `branch = selected`, comparing annotations as well, so two
  branches differing only in annotations would move the selected position.
  `selectionTest_of_nodup` reduces that test to the head action under distinct
  branch heads, and `nodup_heads_of_branchDeclarationsDisjoint` derives those
  from `List.Pairwise BranchDeclarationsDisjoint` — the paper's `ParaMsgOwn`
  ownership condition on conjunctive branches, carried by
  `PactType.OfferBranchesDisjoint`.

`liveEqBody_parallelTypeBranchesSelecting_of_wellFormed` packages both, and
`liveEqBody_parallelTypeBranchesSelecting_of_ownership` packages them for a
caller holding `PactType.ParallelMessageOwnership` at the offer node instead:
its branch clause already keeps each head out of its siblings' actions, which
is all the selection test needs.  No hypothesis on the committed branches'
bodies is needed: `selected` only steers the test, and the product is built
from the branches themselves.

`branchDeclarationsDisjoint_of_ownership` needs all three ownership predicates,
not just the message one: `BranchDeclarationsDisjoint` also asks for disjoint
progress and fair-choice identifiers, which the message clause does not
mention.  The packaged theorem does not go through it.

`liveEqBody_alphabet_agreeOn` duplicates `liveEqBody_agreeOn` in
`Helpers/LiveStepLemmas.lean`; collapse the two once that file settles.
-/

namespace Pact

noncomputable section

open PactType

/-- The annotations at a node agree on the actions that node still uses.
Duplicates `liveEqBody_agreeOn` in `Helpers/LiveStepLemmas.lean`; to be
collapsed. -/
theorem liveEqBody_alphabet_agreeOn {x y : PactType} (h : LiveEqBody x y) :
    PactTypeAlphabet.AgreeOn x.alphabet y.alphabet (MessageActions x) := by
  cases x <;> cases y <;>
    first
      | (simp only [LiveEqBody] at h; done)
      | (intro action hAction; simp [MessageActions] at hAction; done)
      | (simp only [LiveEqBody] at h
         obtain ⟨rfl, rfl, hA⟩ := h
         simpa only [MessageActions, PactType.alphabet] using hA)
      | (simp only [LiveEqBody] at h
         simpa only [PactType.alphabet] using h.1)
      | (simp only [LiveEqBody] at h
         simpa only [PactType.alphabet] using h.2.1)
      | (simp only [LiveEqBody] at h
         simpa only [PactType.alphabet, MessageActions] using h.2.1)

/-- Projecting agreeing alphabets to a parallel child keeps them agreeing. -/
theorem agreeOn_projectParallelChild
    {parent parent' child child' : PactTypeAlphabet} {interface : Interface}
    {used : Finset BareMessage}
    (hParent : PactTypeAlphabet.AgreeOn parent parent' used)
    (hChild : PactTypeAlphabet.AgreeOn child child' used) :
    PactTypeAlphabet.AgreeOn
      (PactTypeAlphabet.projectParallelChild parent child interface)
      (PactTypeAlphabet.projectParallelChild parent' child' interface) used := by
  intro action hAction
  simp only [PactTypeAlphabet.projectParallelChild, Finset.mem_filter]
  rw [hChild action hAction, hParent action hAction]

/-- The left projection additionally subtracts the sibling's actions, which
live equivalence already equates. -/
theorem agreeOn_projectParallelLeft
    {parent parent' left left' : PactTypeAlphabet}
    {rightType rightType' : PactType} {interface : Interface}
    {used : Finset BareMessage}
    (hParent : PactTypeAlphabet.AgreeOn parent parent' used)
    (hLeft : PactTypeAlphabet.AgreeOn left left' used)
    (hRight : MessageActions rightType = MessageActions rightType') :
    PactTypeAlphabet.AgreeOn
      (PactTypeAlphabet.projectParallelLeft parent left rightType interface)
      (PactTypeAlphabet.projectParallelLeft parent' left' rightType' interface)
      used := by
  intro action hAction
  simp only [PactTypeAlphabet.projectParallelLeft,
    PactTypeAlphabet.projectParallelChild, Finset.mem_union, Finset.mem_filter,
    Finset.mem_sdiff, hRight]
  rw [hLeft action hAction, hParent action hAction]

/-- Mirror of `agreeOn_projectParallelLeft`. -/
theorem agreeOn_projectParallelRight
    {parent parent' right right' : PactTypeAlphabet}
    {leftType leftType' : PactType} {interface : Interface}
    {used : Finset BareMessage}
    (hParent : PactTypeAlphabet.AgreeOn parent parent' used)
    (hRight : PactTypeAlphabet.AgreeOn right right' used)
    (hLeft : MessageActions leftType = MessageActions leftType') :
    PactTypeAlphabet.AgreeOn
      (PactTypeAlphabet.projectParallelRight parent right leftType interface)
      (PactTypeAlphabet.projectParallelRight parent' right' leftType' interface)
      used := by
  intro action hAction
  simp only [PactTypeAlphabet.projectParallelRight,
    PactTypeAlphabet.projectParallelChild, Finset.mem_union, Finset.mem_filter,
    Finset.mem_sdiff, hLeft]
  rw [hRight action hAction, hParent action hAction]

/-- Re-signing an exclusive-offer branch list leaves its actions alone. -/
theorem branchMessageActions_reannotateBranches (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      BranchMessageActions (reannotateBranches alphabet branches) =
        BranchMessageActions branches
  | [] => by rw [PactType.reannotateBranches_nil]
  | (action, body) :: rest => by
      rw [PactType.reannotateBranches_cons]
      simp only [BranchMessageActions, PactType.messageActions_reannotate,
        branchMessageActions_reannotateBranches alphabet rest]

/-- A branch body's actions are among those its list records. -/
theorem messageActions_subset_branchMessageActions
    (action : BareMessage) (body : PactType)
    (rest : List (BareMessage × PactType)) :
    MessageActions body ⊆ BranchMessageActions ((action, body) :: rest) := by
  rw [BranchMessageActions]
  exact fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)

/-- A branch tail's actions are among those the whole list records. -/
theorem branchMessageActions_tail_subset
    (action : BareMessage) (body : PactType)
    (rest : List (BareMessage × PactType)) :
    BranchMessageActions rest ⊆ BranchMessageActions ((action, body) :: rest) := by
  rw [BranchMessageActions]
  exact fun x hx => Finset.mem_union_right _ hx

/-- Re-signing preserves live equivalence whenever the two target alphabets
agree on the actions the re-signed term still uses. -/
theorem liveEqBody_reannotate_fuel : ∀ (n : Nat) (t t' : PactType)
    (a a' : PactTypeAlphabet), sizeOf t ≤ n →
    PactTypeAlphabet.AgreeOn a a' (MessageActions t) → LiveEqBody t t' →
    LiveEqBody (t.reannotate a) (t'.reannotate a') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hBranches : ∀ (bs bs' : List (BareMessage × PactType))
        (a a' : PactTypeAlphabet), sizeOf bs < n →
        PactTypeAlphabet.AgreeOn a a' (BranchMessageActions bs) →
        LiveEqBranches bs bs' →
        LiveEqBranches (reannotateBranches a bs)
          (reannotateBranches a' bs') := by
      intro bs
      induction bs with
      | nil =>
          intro bs' a a' _ _ h
          cases bs' with
          | nil =>
              simp only [PactType.reannotateBranches_nil, LiveEqBranches]
          | cons _ _ => simp only [LiveEqBranches] at h
      | cons head rest ihRest =>
          intro bs' a a' hSize hAgree h
          cases bs' with
          | nil => simp only [LiveEqBranches] at h
          | cons head' rest' =>
              obtain ⟨action, body⟩ := head
              obtain ⟨action', body'⟩ := head'
              simp only [LiveEqBranches] at h
              obtain ⟨rfl, hBody, hRest⟩ := h
              have hBodySize : sizeOf body < n := by
                simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hSize
                omega
              have hRestSize : sizeOf rest < n := by
                simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hSize
                omega
              simp only [PactType.reannotateBranches_cons, LiveEqBranches]
              refine ⟨trivial, ?_, ?_⟩
              · exact ih _ hBodySize body body' a a' le_rfl
                  (hAgree.mono
                    (messageActions_subset_branchMessageActions action body rest))
                  hBody
              · exact ihRest rest' a a' hRestSize
                  (hAgree.mono
                    (branchMessageActions_tail_subset action body rest)) hRest
    have hOfferBranches : ∀ (bs bs' : List (BareMessage × PactType))
        (a a' : PactTypeAlphabet) (seen : Finset BareMessage), sizeOf bs < n →
        PactTypeAlphabet.AgreeOn a a' (BranchMessageActions bs) →
        LiveEqBranches bs bs' →
        LiveEqBranches (reannotateOfferBranches a seen bs)
          (reannotateOfferBranches a' seen bs') := by
      intro bs
      induction bs with
      | nil =>
          intro bs' a a' seen _ _ h
          cases bs' with
          | nil =>
              simp only [PactType.reannotateOfferBranches_nil, LiveEqBranches]
          | cons _ _ => simp only [LiveEqBranches] at h
      | cons head rest ihRest =>
          intro bs' a a' seen hSize hAgree h
          cases bs' with
          | nil => simp only [LiveEqBranches] at h
          | cons head' rest' =>
              obtain ⟨action, body⟩ := head
              obtain ⟨action', body'⟩ := head'
              simp only [LiveEqBranches] at h
              obtain ⟨rfl, hBody, hRest⟩ := h
              have hBodySize : sizeOf body < n := by
                simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hSize
                omega
              have hRestSize : sizeOf rest < n := by
                simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hSize
                omega
              have hRestActions : BranchMessageActions rest =
                  BranchMessageActions rest' := liveEqBranches_messageActions' hRest
              have hBodyActions : MessageActions body = MessageActions body' :=
                liveEqBody_messageActions' hBody
              simp only [PactType.reannotateOfferBranches_cons, ← hRestActions,
                ← hBodyActions, LiveEqBranches]
              refine ⟨trivial, ?_, ?_⟩
              · refine ih _ hBodySize body body' _ _ le_rfl ?_ hBody
                intro x hx
                simp only [Finset.mem_sdiff]
                rw [hAgree x
                  (messageActions_subset_branchMessageActions action body rest hx)]
              · exact ihRest rest' a a' _ hRestSize
                  (hAgree.mono
                    (branchMessageActions_tail_subset action body rest)) hRest
    intro t t' a a' hSize hAgree hLive
    cases t <;> cases t' <;>
      first
        | (simp only [LiveEqBody] at hLive; done)
        | skip
    case message.message _ m d _ m' d' =>
        simp only [MessageActions] at hAgree
        simp only [LiveEqBody] at hLive
        simp only [PactType.reannotate, LiveEqBody]
        exact ⟨hLive.1, hLive.2.1, hAgree⟩
    case progress.progress _ _ _ _ =>
        simp only [LiveEqBody] at hLive
        simp only [PactType.reannotate, LiveEqBody]
        exact hLive
    case tock.tock _ _ => simp only [PactType.reannotate, LiveEqBody]
    case skip.skip _ _ => simp only [PactType.reannotate, LiveEqBody]
    case var.var _ _ _ _ =>
        simp only [LiveEqBody] at hLive
        simp only [PactType.reannotate, LiveEqBody]
        exact hLive
    case choice.choice _ l r _ l' r' =>
        simp only [MessageActions] at hAgree
        simp only [LiveEqBody] at hLive
        simp only [PactType.choice.sizeOf_spec] at hSize
        simp only [PactType.reannotate, LiveEqBody, MessageActions,
          PactType.messageActions_reannotate]
        refine ⟨hAgree, ?_, ?_⟩
        · exact ih _ (by omega) l l' a a' le_rfl
            (hAgree.mono Finset.subset_union_left) hLive.2.1
        · exact ih _ (by omega) r r' a a' le_rfl
            (hAgree.mono Finset.subset_union_right) hLive.2.2
    case seq.seq _ l r _ l' r' =>
        simp only [MessageActions] at hAgree
        simp only [LiveEqBody] at hLive
        simp only [PactType.seq.sizeOf_spec] at hSize
        simp only [PactType.reannotate, LiveEqBody, MessageActions,
          PactType.messageActions_reannotate]
        refine ⟨hAgree, ?_, ?_⟩
        · exact ih _ (by omega) l l' a a' le_rfl
            (hAgree.mono Finset.subset_union_left) hLive.2.1
        · exact ih _ (by omega) r r' a a' le_rfl
            (hAgree.mono Finset.subset_union_right) hLive.2.2
    case fairChoice.fairChoice _ bid l r _ bid' l' r' =>
        simp only [MessageActions] at hAgree
        simp only [LiveEqBody] at hLive
        simp only [PactType.fairChoice.sizeOf_spec] at hSize
        simp only [PactType.reannotate, LiveEqBody, MessageActions,
          PactType.messageActions_reannotate]
        refine ⟨hLive.1, hAgree, ?_, ?_⟩
        · exact ih _ (by omega) l l' a a' le_rfl
            (hAgree.mono Finset.subset_union_left) hLive.2.2.1
        · exact ih _ (by omega) r r' a a' le_rfl
            (hAgree.mono Finset.subset_union_right) hLive.2.2.2
    case recur.recur _ name body _ name' body' =>
        simp only [MessageActions] at hAgree
        simp only [LiveEqBody] at hLive
        simp only [PactType.recur.sizeOf_spec] at hSize
        simp only [PactType.reannotate, LiveEqBody,
          PactType.messageActions_reannotate]
        exact ⟨hLive.1, hAgree, ih _ (by omega) body body' a a' le_rfl hAgree
          hLive.2.2⟩
    case par.par _ l r i _ l' r' i' =>
        simp only [MessageActions] at hAgree
        simp only [LiveEqBody] at hLive
        obtain ⟨rfl, hNode, hLeft, hRight⟩ := hLive
        simp only [PactType.par.sizeOf_spec] at hSize
        have hRightActions : MessageActions r = MessageActions r' :=
          liveEqBody_messageActions' hRight
        have hLeftActions : MessageActions l = MessageActions l' :=
          liveEqBody_messageActions' hLeft
        simp only [PactType.reannotate, LiveEqBody, MessageActions,
          PactType.messageActions_reannotate]
        refine ⟨trivial, hAgree, ?_, ?_⟩
        · refine ih _ (by omega) l l' _ _ le_rfl ?_ hLeft
          exact agreeOn_projectParallelLeft
            (hAgree.mono Finset.subset_union_left)
            ((liveEqBody_alphabet_agreeOn hLeft)) hRightActions
        · refine ih _ (by omega) r r' _ _ le_rfl ?_ hRight
          exact agreeOn_projectParallelRight
            (hAgree.mono Finset.subset_union_right)
            (liveEqBody_alphabet_agreeOn hRight) hLeftActions
    case xoffer.xoffer _ e bs _ e' bs' =>
        simp only [MessageActions] at hAgree
        simp only [LiveEqBody] at hLive
        simp only [PactType.xoffer.sizeOf_spec] at hSize
        simp only [PactType.reannotate, LiveEqBody, MessageActions,
          PactType.messageActions_reannotate,
          branchMessageActions_reannotateBranches]
        refine ⟨hAgree, ?_, ?_⟩
        · exact ih _ (by omega) e e' a a' le_rfl
            (hAgree.mono Finset.subset_union_left) hLive.2.1
        · exact hBranches bs bs' a a' (by omega)
            (hAgree.mono Finset.subset_union_right) hLive.2.2
    case offer.offer _ e bs _ e' bs' =>
        simp only [MessageActions] at hAgree
        simp only [LiveEqBody] at hLive
        simp only [PactType.offer.sizeOf_spec] at hSize
        simp only [PactType.reannotate, LiveEqBody, MessageActions,
          PactType.messageActions_reannotate,
          PactType.branchMessageActions_reannotateOfferBranches]
        refine ⟨hAgree, ?_, ?_⟩
        · exact ih _ (by omega) e e' a a' le_rfl
            (hAgree.mono Finset.subset_union_left) hLive.2.1
        · exact hOfferBranches bs bs' a a' ∅ (by omega)
            (hAgree.mono Finset.subset_union_right) hLive.2.2

/-- Fuel-free form of `liveEqBody_reannotate_fuel`. -/
theorem liveEqBody_reannotate {t t' : PactType} {a a' : PactTypeAlphabet}
    (hAgree : PactTypeAlphabet.AgreeOn a a' (MessageActions t))
    (hLive : LiveEqBody t t') :
    LiveEqBody (t.reannotate a) (t'.reannotate a') :=
  liveEqBody_reannotate_fuel (sizeOf t) t t' a a' le_rfl hAgree hLive

/-- Corresponding branch bodies carry alphabets agreeing on `used`. -/
abbrev BranchAlphabetsAgreeOn (used : Finset BareMessage)
    (branches branches' : List (BareMessage × PactType)) : Prop :=
  List.Forall₂ (fun branch branch' =>
    PactTypeAlphabet.AgreeOn branch.2.alphabet branch'.2.alphabet used)
    branches branches'

/-- Branch alphabets that agree pointwise also agree once unioned. -/
theorem agreeOn_branchAlphabetActions :
    ∀ {branches branches' : List (BareMessage × PactType)}
      {used : Finset BareMessage},
      BranchAlphabetsAgreeOn used branches branches' →
      PactTypeAlphabet.AgreeOn { actions := branchAlphabetActions branches }
        { actions := branchAlphabetActions branches' } used := by
  intro branches
  induction branches with
  | nil =>
      intro branches' used h
      cases h
      intro action _
      simp only [PactType.branchAlphabetActions]
  | cons head rest ih =>
      intro branches' used h
      cases branches' with
      | nil => cases h
      | cons head' rest' =>
          obtain ⟨action, body⟩ := head
          obtain ⟨action', body'⟩ := head'
          obtain ⟨hHead, hTail⟩ := List.forall₂_cons.mp h
          intro x hx
          simp only [PactType.branchAlphabetActions, Finset.mem_union]
          rw [hHead x hx, (ih hTail) x hx]

/-- The generated singleton exclusive offer respects live equivalence. -/
theorem liveEqBody_singletonTypeXOfferAt {a a' : PactTypeAlphabet}
    {action : BareMessage} {body body' : PactType} (hBody : LiveEqBody body body')
    (hAgree : PactTypeAlphabet.AgreeOn a a' ({action} ∪ MessageActions body)) :
    LiveEqBody (singletonTypeXOfferAt a (action, body))
      (singletonTypeXOfferAt a' (action, body')) := by
  simp only [singletonTypeXOfferAt]
  rw [LiveEqBody]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [MessageActions, BranchMessageActions,
      PactType.messageActions_reannotate, Finset.empty_union,
      Finset.union_empty] using hAgree
  · rw [LiveEqBody]
    trivial
  · rw [LiveEqBranches]
    refine ⟨rfl, ?_, ?_⟩
    · exact liveEqBody_reannotate
        (hAgree.mono Finset.subset_union_right) hBody
    · rw [LiveEqBranches]
      trivial

/-- The committed branch respects live equivalence. -/
theorem liveEqBody_selectedTypeBranchAt {a a' : PactTypeAlphabet}
    {action : BareMessage} {body body' : PactType} (hBody : LiveEqBody body body')
    (hAgree : PactTypeAlphabet.AgreeOn a a' ({action} ∪ MessageActions body)) :
    LiveEqBody (selectedTypeBranchAt a (action, body))
      (selectedTypeBranchAt a' (action, body')) := by
  simp only [selectedTypeBranchAt]
  rw [LiveEqBody]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [MessageActions, PactType.messageActions_reannotate] using hAgree
  · rw [LiveEqBody]
    refine ⟨rfl, rfl, ?_⟩
    exact hAgree.mono (by simp)
  · exact liveEqBody_reannotate (hAgree.mono Finset.subset_union_right) hBody

theorem parallelTypeBranchesWithin_nil (a : PactTypeAlphabet) :
    parallelTypeBranchesWithin a [] = .skip a := by
  rw [parallelTypeBranchesWithin]

theorem parallelTypeBranchesWithin_singleton (a : PactTypeAlphabet)
    (branch : BareMessage × PactType) :
    parallelTypeBranchesWithin a [branch] = singletonTypeXOfferAt a branch := by
  rw [parallelTypeBranchesWithin]

theorem parallelTypeBranchesWithin_cons_cons (a : PactTypeAlphabet)
    (branch next : BareMessage × PactType)
    (tail : List (BareMessage × PactType)) :
    parallelTypeBranchesWithin a (branch :: next :: tail) =
      .par a (singletonTypeXOfferAt branch.2.alphabet branch)
        (parallelTypeBranchesWithin
          { actions := branchAlphabetActions (next :: tail) } (next :: tail))
        ∅ := by
  rw [parallelTypeBranchesWithin]
  simp

theorem parallelTypeBranchesSelectingWithin_nil (a : PactTypeAlphabet)
    (selected : BareMessage × PactType) :
    parallelTypeBranchesSelectingWithin a selected [] = .skip a := by
  rw [parallelTypeBranchesSelectingWithin]

theorem parallelTypeBranchesSelectingWithin_singleton (a : PactTypeAlphabet)
    (selected branch : BareMessage × PactType) :
    parallelTypeBranchesSelectingWithin a selected [branch] =
      if branch = selected then selectedTypeBranchAt a branch
      else singletonTypeXOfferAt a branch := by
  rw [parallelTypeBranchesSelectingWithin]

theorem parallelTypeBranchesSelectingWithin_cons_cons (a : PactTypeAlphabet)
    (selected branch next : BareMessage × PactType)
    (tail : List (BareMessage × PactType)) :
    parallelTypeBranchesSelectingWithin a selected (branch :: next :: tail) =
      if branch = selected then
        .par a (selectedTypeBranchAt branch.2.alphabet branch)
          (parallelTypeBranchesWithin
            { actions := branchAlphabetActions (next :: tail) } (next :: tail))
          ∅
      else
        .par a (singletonTypeXOfferAt branch.2.alphabet branch)
          (parallelTypeBranchesSelectingWithin
            { actions := branchAlphabetActions (next :: tail) } selected
            (next :: tail))
          ∅ := by
  rw [parallelTypeBranchesSelectingWithin]
  simp

/-- The uncommitted branch product respects live equivalence. -/
theorem liveEqBody_parallelTypeBranchesWithin :
    ∀ (branches branches' : List (BareMessage × PactType))
      (a a' : PactTypeAlphabet) (used : Finset BareMessage),
      LiveEqBranches branches branches' →
      BranchAlphabetsAgreeOn used branches branches' →
      PactTypeAlphabet.AgreeOn a a' used →
      BranchMessageActions branches ⊆ used →
      LiveEqBody (parallelTypeBranchesWithin a branches)
        (parallelTypeBranchesWithin a' branches') := by
  intro branches
  induction branches with
  | nil =>
      intro branches' a a' used hLive _ _ _
      cases branches' with
      | nil =>
          rw [parallelTypeBranchesWithin_nil, parallelTypeBranchesWithin_nil,
            LiveEqBody]
          trivial
      | cons _ _ => simp only [LiveEqBranches] at hLive
  | cons head rest ih =>
      intro branches' a a' used hLive hAlpha hAgree hSub
      cases branches' with
      | nil => simp only [LiveEqBranches] at hLive
      | cons head' rest' =>
          obtain ⟨action, body⟩ := head
          obtain ⟨action', body'⟩ := head'
          simp only [LiveEqBranches] at hLive
          obtain ⟨rfl, hBody, hRest⟩ := hLive
          obtain ⟨hAlphaHead, hAlphaTail⟩ := List.forall₂_cons.mp hAlpha
          have hHeadSub : ({action} ∪ MessageActions body) ⊆ used := by
            refine subset_trans ?_ hSub
            rw [BranchMessageActions]
            exact Finset.subset_union_left
          have hTailSub : BranchMessageActions rest ⊆ used := by
            refine subset_trans ?_ hSub
            rw [BranchMessageActions]
            exact Finset.subset_union_right
          cases rest with
          | nil =>
              cases rest' with
              | nil =>
                  rw [parallelTypeBranchesWithin_singleton,
                    parallelTypeBranchesWithin_singleton]
                  exact liveEqBody_singletonTypeXOfferAt hBody
                    (hAgree.mono hHeadSub)
              | cons _ _ => simp only [LiveEqBranches] at hRest
          | cons next tail =>
              cases rest' with
              | nil => simp only [LiveEqBranches] at hRest
              | cons next' tail' =>
                  have hNodeAgree : PactTypeAlphabet.AgreeOn a a'
                      (MessageActions (parallelTypeBranchesWithin a
                        ((action, body) :: next :: tail))) := by
                    rw [parallelTypeBranchesWithin_messageActions]
                    exact hAgree.mono hSub
                  rw [parallelTypeBranchesWithin_cons_cons] at hNodeAgree
                  rw [parallelTypeBranchesWithin_cons_cons,
                    parallelTypeBranchesWithin_cons_cons, LiveEqBody]
                  refine ⟨rfl, hNodeAgree, ?_, ?_⟩
                  · exact liveEqBody_singletonTypeXOfferAt hBody
                      (hAlphaHead.mono hHeadSub)
                  · exact ih _ _ _ used hRest hAlphaTail
                      (agreeOn_branchAlphabetActions hAlphaTail) hTailSub

/-- The committed branch product respects live equivalence.  The two selection
tests agree because each list picks its committed branch by head action. -/
theorem liveEqBody_parallelTypeBranchesSelectingWithin :
    ∀ (branches branches' : List (BareMessage × PactType))
      (a a' : PactTypeAlphabet) (used : Finset BareMessage)
      (selected selected' : BareMessage × PactType),
      LiveEqBranches branches branches' →
      BranchAlphabetsAgreeOn used branches branches' →
      PactTypeAlphabet.AgreeOn a a' used →
      BranchMessageActions branches ⊆ used →
      selected.1 = selected'.1 →
      (∀ branch ∈ branches, (branch = selected ↔ branch.1 = selected.1)) →
      (∀ branch ∈ branches', (branch = selected' ↔ branch.1 = selected'.1)) →
      LiveEqBody (parallelTypeBranchesSelectingWithin a selected branches)
        (parallelTypeBranchesSelectingWithin a' selected' branches') := by
  intro branches
  induction branches with
  | nil =>
      intro branches' a a' used selected selected' hLive _ _ _ _ _ _
      cases branches' with
      | nil =>
          rw [parallelTypeBranchesSelectingWithin_nil,
            parallelTypeBranchesSelectingWithin_nil, LiveEqBody]
          trivial
      | cons _ _ => simp only [LiveEqBranches] at hLive
  | cons head rest ih =>
      intro branches' a a' used selected selected' hLive hAlpha hAgree hSub
        hSelected hTest hTest'
      cases branches' with
      | nil => simp only [LiveEqBranches] at hLive
      | cons head' rest' =>
          obtain ⟨action, body⟩ := head
          obtain ⟨action', body'⟩ := head'
          simp only [LiveEqBranches] at hLive
          obtain ⟨rfl, hBody, hRest⟩ := hLive
          obtain ⟨hAlphaHead, hAlphaTail⟩ := List.forall₂_cons.mp hAlpha
          have hHeadSub : ({action} ∪ MessageActions body) ⊆ used := by
            refine subset_trans ?_ hSub
            rw [BranchMessageActions]
            exact Finset.subset_union_left
          have hTailSub : BranchMessageActions rest ⊆ used := by
            refine subset_trans ?_ hSub
            rw [BranchMessageActions]
            exact Finset.subset_union_right
          have hSame : ((action, body) = selected) ↔
              ((action, body') = selected') := by
            rw [hTest _ (List.mem_cons_self ..),
              hTest' _ (List.mem_cons_self ..), hSelected]
          cases rest with
          | nil =>
              cases rest' with
              | nil =>
                  rw [parallelTypeBranchesSelectingWithin_singleton,
                    parallelTypeBranchesSelectingWithin_singleton]
                  by_cases hc : (action, body) = selected
                  · rw [if_pos hc, if_pos (hSame.mp hc)]
                    exact liveEqBody_selectedTypeBranchAt hBody
                      (hAgree.mono hHeadSub)
                  · rw [if_neg hc, if_neg (fun h => hc (hSame.mpr h))]
                    exact liveEqBody_singletonTypeXOfferAt hBody
                      (hAgree.mono hHeadSub)
              | cons _ _ => simp only [LiveEqBranches] at hRest
          | cons next tail =>
              cases rest' with
              | nil => simp only [LiveEqBranches] at hRest
              | cons next' tail' =>
                  have hNodeAgree : PactTypeAlphabet.AgreeOn a a'
                      (MessageActions
                        (parallelTypeBranchesSelectingWithin a selected
                          ((action, body) :: next :: tail))) := by
                    rw [(parallelTypeBranchesSelectingWithin_ownershipData a
                      selected ((action, body) :: next :: tail)).2.1]
                    exact hAgree.mono hSub
                  rw [parallelTypeBranchesSelectingWithin_cons_cons]
                    at hNodeAgree
                  rw [parallelTypeBranchesSelectingWithin_cons_cons,
                    parallelTypeBranchesSelectingWithin_cons_cons]
                  by_cases hc : (action, body) = selected
                  · rw [if_pos hc] at hNodeAgree
                    rw [if_pos hc, if_pos (hSame.mp hc), LiveEqBody]
                    refine ⟨rfl, hNodeAgree, ?_, ?_⟩
                    · exact liveEqBody_selectedTypeBranchAt hBody
                        (hAlphaHead.mono hHeadSub)
                    · exact liveEqBody_parallelTypeBranchesWithin _ _ _ _ used
                        hRest hAlphaTail (agreeOn_branchAlphabetActions hAlphaTail)
                        hTailSub
                  · rw [if_neg hc] at hNodeAgree
                    rw [if_neg hc, if_neg (fun h => hc (hSame.mpr h)),
                      LiveEqBody]
                    refine ⟨rfl, hNodeAgree, ?_, ?_⟩
                    · exact liveEqBody_singletonTypeXOfferAt hBody
                        (hAlphaHead.mono hHeadSub)
                    · refine ih _ _ _ used selected selected' hRest hAlphaTail
                        (agreeOn_branchAlphabetActions hAlphaTail) hTailSub
                        hSelected
                        (fun b hb => hTest b (List.mem_cons_of_mem _ hb))
                        (fun b hb => hTest' b (List.mem_cons_of_mem _ hb))

/-- The conjunctive-offer expansion respects live equivalence. -/
theorem liveEqBody_parallelTypeBranchesSelecting {a a' : PactTypeAlphabet}
    {selected selected' : BareMessage × PactType}
    {branches branches' : List (BareMessage × PactType)}
    (hLive : LiveEqBranches branches branches')
    (hAlpha : BranchAlphabetsAgreeOn (BranchMessageActions branches) branches
      branches')
    (hAgree : PactTypeAlphabet.AgreeOn a a' (BranchMessageActions branches))
    (hSelected : selected.1 = selected'.1)
    (hTest : ∀ branch ∈ branches, (branch = selected ↔ branch.1 = selected.1))
    (hTest' : ∀ branch ∈ branches',
      (branch = selected' ↔ branch.1 = selected'.1)) :
    LiveEqBody (parallelTypeBranchesSelecting a selected branches)
      (parallelTypeBranchesSelecting a' selected' branches') := by
  cases branches with
  | nil =>
      cases branches' with
      | nil =>
          rw [parallelTypeBranchesSelecting, parallelTypeBranchesSelecting,
            LiveEqBody]
          trivial
      | cons _ _ => simp only [LiveEqBranches] at hLive
  | cons head rest =>
      cases branches' with
      | nil => simp only [LiveEqBranches] at hLive
      | cons head' rest' =>
          rw [parallelTypeBranchesSelecting, parallelTypeBranchesSelecting]
          exact liveEqBody_parallelTypeBranchesSelectingWithin _ _ _ _ _ _ _
            hLive hAlpha hAgree (Finset.Subset.refl _) hSelected hTest hTest'

/-- Distinct branch heads reduce the syntactic selection test to its head. -/
theorem selectionTest_of_nodup {branches : List (BareMessage × PactType)}
    {selected : BareMessage × PactType}
    (hNodup : (branches.map Prod.fst).Nodup) (hMem : selected ∈ branches) :
    ∀ branch ∈ branches, (branch = selected ↔ branch.1 = selected.1) := by
  intro branch hBranch
  constructor
  · intro h
    rw [h]
  · intro h
    exact List.inj_on_of_nodup_map hNodup hBranch hMem h

/-- Branches owning disjoint declarations have distinct head actions. -/
theorem nodup_heads_of_branchDeclarationsDisjoint
    {branches : List (BareMessage × PactType)}
    (hDisjoint : List.Pairwise BranchDeclarationsDisjoint branches) :
    (branches.map Prod.fst).Nodup := by
  refine List.pairwise_map.mpr (hDisjoint.imp ?_)
  intro b1 b2 hd hEq
  have hLeft : b1.1 ∈ ({b1.1} ∪ MessageActions b1.2) :=
    Finset.mem_union_left _ (Finset.mem_singleton_self _)
  have hRight : b1.1 ∈ ({b2.1} ∪ MessageActions b2.2) := by
    rw [hEq]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
  exact Finset.disjoint_left.mp hd.1 hLeft hRight

/-- Conjunct compatibility fixes each branch alphabet as the offer alphabet
minus its siblings' declarations, so live-equivalent branch lists carry branch
alphabets that agree wherever their offer alphabets do. -/
theorem branchAlphabetsAgreeOn_of_offerBranchesWellFormed :
    ∀ (branches branches' : List (BareMessage × PactType))
      (a a' : PactTypeAlphabet) (seen used : Finset BareMessage),
      LiveEqBranches branches branches' →
      OfferBranchesWellFormed a seen branches →
      OfferBranchesWellFormed a' seen branches' →
      PactTypeAlphabet.AgreeOn a a' used →
      BranchAlphabetsAgreeOn used branches branches' := by
  intro branches
  induction branches with
  | nil =>
      intro branches' a a' seen used hLive _ _ _
      cases branches' with
      | nil => exact List.Forall₂.nil
      | cons _ _ => simp only [LiveEqBranches] at hLive
  | cons head rest ih =>
      intro branches' a a' seen used hLive hWF hWF' hAgree
      cases branches' with
      | nil => simp only [LiveEqBranches] at hLive
      | cons head' rest' =>
          obtain ⟨action, body⟩ := head
          obtain ⟨action', body'⟩ := head'
          simp only [LiveEqBranches] at hLive
          obtain ⟨rfl, hBody, hRest⟩ := hLive
          simp only [OfferBranchesWellFormed] at hWF hWF'
          have hRestActions : BranchMessageActions rest =
            BranchMessageActions rest' := liveEqBranches_messageActions' hRest
          have hBodyActions : MessageActions body = MessageActions body' :=
            liveEqBody_messageActions' hBody
          refine List.Forall₂.cons ?_ ?_
          · intro x hx
            show x ∈ body.alphabet.actions ↔ x ∈ body'.alphabet.actions
            rw [Finset.ext_iff.mp hWF.1 x, Finset.ext_iff.mp hWF'.1 x,
              Finset.mem_sdiff, Finset.mem_sdiff, ← hRestActions,
              hAgree x hx]
          · refine ih rest' a a' _ used hRest hWF.2.2 ?_ hAgree
            rw [hBodyActions]
            exact hWF'.2.2

/-- The conjunctive-offer expansion respects live equivalence, with the
premises a well-formed conjunctive offer supplies: conjunct compatibility for
the branch alphabets, disjoint branch declarations for the selection test, and
the agreement of the two offer alphabets. -/
theorem liveEqBody_parallelTypeBranchesSelecting_of_wellFormed
    {a a' : PactTypeAlphabet} {selected selected' : BareMessage × PactType}
    {branches branches' : List (BareMessage × PactType)}
    (hLive : LiveEqBranches branches branches')
    (hAgree : PactTypeAlphabet.AgreeOn a a' (BranchMessageActions branches))
    (hWF : OfferBranchesWellFormed a ∅ branches)
    (hWF' : OfferBranchesWellFormed a' ∅ branches')
    (hDisjoint : List.Pairwise BranchDeclarationsDisjoint branches)
    (hDisjoint' : List.Pairwise BranchDeclarationsDisjoint branches')
    (hMem : selected ∈ branches) (hMem' : selected' ∈ branches')
    (hSelected : selected.1 = selected'.1) :
    LiveEqBody (parallelTypeBranchesSelecting a selected branches)
      (parallelTypeBranchesSelecting a' selected' branches') :=
  liveEqBody_parallelTypeBranchesSelecting hLive
    (branchAlphabetsAgreeOn_of_offerBranchesWellFormed branches branches' a a' ∅
      (BranchMessageActions branches) hLive hWF hWF' hAgree)
    hAgree hSelected
    (selectionTest_of_nodup
      (nodup_heads_of_branchDeclarationsDisjoint hDisjoint) hMem)
    (selectionTest_of_nodup
      (nodup_heads_of_branchDeclarationsDisjoint hDisjoint') hMem')

/-- A branch's declarations are among those its list records. -/
theorem branchDeclarations_subset_branchMessageActions :
    ∀ {branches : List (BareMessage × PactType)}
      {branch : BareMessage × PactType}, branch ∈ branches →
      ({branch.1} ∪ MessageActions branch.2) ⊆
        BranchMessageActions branches := by
  intro branches
  induction branches with
  | nil => intro branch hMem; cases hMem
  | cons head rest ih =>
      intro branch hMem
      obtain ⟨action, body⟩ := head
      rw [BranchMessageActions]
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact Finset.subset_union_left
      · exact subset_trans (ih hRest) Finset.subset_union_right

/-- A branch's progress identifiers are among those its list records. -/
theorem progressIds_subset_branchProgressIds :
    ∀ {branches : List (BareMessage × PactType)}
      {branch : BareMessage × PactType}, branch ∈ branches →
      ProgressIds branch.2 ⊆ BranchProgressIds branches := by
  intro branches
  induction branches with
  | nil => intro branch hMem; cases hMem
  | cons head rest ih =>
      intro branch hMem
      obtain ⟨action, body⟩ := head
      rw [BranchProgressIds]
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact Finset.subset_union_left
      · exact subset_trans (ih hRest) Finset.subset_union_right

/-- A branch's fair-choice identifiers are among those its list records. -/
theorem fairChoiceIds_subset_branchFairChoiceIds :
    ∀ {branches : List (BareMessage × PactType)}
      {branch : BareMessage × PactType}, branch ∈ branches →
      FairChoiceIds branch.2 ⊆ BranchFairChoiceIds branches := by
  intro branches
  induction branches with
  | nil => intro branch hMem; cases hMem
  | cons head rest ih =>
      intro branch hMem
      obtain ⟨action, body⟩ := head
      rw [BranchFairChoiceIds]
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact Finset.subset_union_left
      · exact subset_trans (ih hRest) Finset.subset_union_right

/-- Sibling ownership at a conjunctive offer gives pairwise disjoint branch
declarations.  All three ownership predicates are needed: `BranchDeclarationsDisjoint`
also asks for disjoint progress and fair-choice identifiers, which the message
clause does not mention. -/
theorem branchDeclarationsDisjoint_of_ownership :
    ∀ {branches : List (BareMessage × PactType)},
      PactType.ParallelMessageOwnershipBranches branches →
      PactType.ParallelProgressOwnershipBranches branches →
      PactType.ParallelFairChoiceOwnershipBranches branches →
      List.Pairwise BranchDeclarationsDisjoint branches := by
  intro branches
  induction branches with
  | nil => intro _ _ _; exact List.Pairwise.nil
  | cons head rest ih =>
      intro hMessages hProgress hFair
      obtain ⟨action, body⟩ := head
      simp only [PactType.ParallelMessageOwnershipBranches] at hMessages
      simp only [PactType.ParallelProgressOwnershipBranches] at hProgress
      simp only [PactType.ParallelFairChoiceOwnershipBranches] at hFair
      refine List.Pairwise.cons ?_
        (ih hMessages.2.2.2 hProgress.2.2 hFair.2.2)
      intro branch hBranch
      refine ⟨?_, ?_, ?_⟩
      · exact Finset.disjoint_of_subset_right
          (branchDeclarations_subset_branchMessageActions hBranch)
          hMessages.2.2.1
      · exact Finset.disjoint_of_subset_right
          (progressIds_subset_branchProgressIds hBranch) hProgress.2.1
      · exact Finset.disjoint_of_subset_right
          (fairChoiceIds_subset_branchFairChoiceIds hBranch) hFair.2.1

/-- Branch heads are distinct.  The message-ownership clause keeps each head
out of its siblings' actions, which is all the selection test needs. -/
theorem nodup_heads_of_parallelMessageOwnershipBranches :
    ∀ {branches : List (BareMessage × PactType)},
      PactType.ParallelMessageOwnershipBranches branches →
      (branches.map Prod.fst).Nodup := by
  intro branches
  induction branches with
  | nil => intro _; simp
  | cons head rest ih =>
      intro hOwnership
      obtain ⟨action, body⟩ := head
      simp only [PactType.ParallelMessageOwnershipBranches] at hOwnership
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih hOwnership.2.2.2⟩
      intro hMem
      obtain ⟨branch, hBranch, hEq⟩ := List.mem_map.mp hMem
      have hHead : branch.1 = action := hEq
      have hAction : action ∈ BranchMessageActions rest := by
        rw [← hHead]
        exact branchDeclarations_subset_branchMessageActions hBranch
          (Finset.mem_union_left _ (Finset.mem_singleton_self branch.1))
      exact Finset.disjoint_left.mp hOwnership.2.2.1
        (Finset.mem_union_left _ (Finset.mem_singleton_self action)) hAction

/-- The conjunctive-offer expansion respects live equivalence, for a caller
holding `PactType.ParallelMessageOwnership` at the offer node: its branch
clause supplies the selection test directly. -/
theorem liveEqBody_parallelTypeBranchesSelecting_of_ownership
    {a a' : PactTypeAlphabet} {selected selected' : BareMessage × PactType}
    {branches branches' : List (BareMessage × PactType)}
    (hLive : LiveEqBranches branches branches')
    (hAgree : PactTypeAlphabet.AgreeOn a a' (BranchMessageActions branches))
    (hWF : OfferBranchesWellFormed a ∅ branches)
    (hWF' : OfferBranchesWellFormed a' ∅ branches')
    (hOwnership : PactType.ParallelMessageOwnershipBranches branches)
    (hOwnership' : PactType.ParallelMessageOwnershipBranches branches')
    (hMem : selected ∈ branches) (hMem' : selected' ∈ branches')
    (hSelected : selected.1 = selected'.1) :
    LiveEqBody (parallelTypeBranchesSelecting a selected branches)
      (parallelTypeBranchesSelecting a' selected' branches') :=
  liveEqBody_parallelTypeBranchesSelecting hLive
    (branchAlphabetsAgreeOn_of_offerBranchesWellFormed branches branches' a a' ∅
      (BranchMessageActions branches) hLive hWF hWF' hAgree)
    hAgree hSelected
    (selectionTest_of_nodup
      (nodup_heads_of_parallelMessageOwnershipBranches hOwnership) hMem)
    (selectionTest_of_nodup
      (nodup_heads_of_parallelMessageOwnershipBranches hOwnership') hMem')

end

end Pact
