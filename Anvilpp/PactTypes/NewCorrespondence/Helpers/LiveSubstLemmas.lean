import Anvilpp.PactTypes.Syntax.LiveEquivalenceLemmas
import Anvilpp.PactTypes.Syntax.PactTypeSubstitutionLemmas
import Anvilpp.PactTypes.Syntax.PactTypeRegularityLemmas

/-!
Substitution of a body for a tail-confined recursion variable preserves live
equivalence.  Unfolding a binder rebuilds the same control skeleton and grows a
node's actions only by the replacement's, so every per-node agreement obligation
survives.

Premises used, and why:

* The induction runs on `LiveEqBody`, not on `LiveEq`.  `LiveEq` also demands
  equal outer alphabets, and the two children of a parallel node only have
  agreeing alphabets, so the stronger relation is unavailable at every node.

* Agreement of the two node alphabets on the replacement's actions, not equality
  of those alphabets.  `AlphabetWellFormed` pins every non-parallel child's
  alphabet to its node's on each side separately, so along the whole path from
  the root to an occurrence the pair of annotations stays the root pair, and one
  agreement on `MessageActions R` covers every node on that path.

* `TailOccurrences n True b` keeps occurrences out of parallel operands and
  conjunctive-offer branches, the two places where a child's alphabet is not
  pinned to its node's; there substitution is inert instead.

* `R.alphabet` is unconstrained: an occurrence contributes the replacement's own
  agreement, never its annotation.

The induction also returns agreement on the substituted term's actions, which is
what a node needs of its children and what a variable occurrence supplies.
-/

namespace Pact

namespace PactTypeAlphabet

/-- Agreement on two sets is agreement on their union. -/
theorem AgreeOn.union {left right : PactTypeAlphabet}
    {s t : Finset BareMessage} (hs : AgreeOn left right s)
    (ht : AgreeOn left right t) : AgreeOn left right (s ∪ t) := by
  intro action hAction
  rcases Finset.mem_union.mp hAction with h | h
  · exact hs action h
  · exact ht action h

/-- Any two alphabets agree on no action at all. -/
theorem AgreeOn.empty (left right : PactTypeAlphabet) :
    AgreeOn left right ∅ := by
  intro action hAction
  simp at hAction

end PactTypeAlphabet

namespace PactType

/-- Live equivalence transports tail confinement: the relation fixes the control
skeleton and the variable names, which is all `TailOccurrences` reads. -/
theorem liveEqBody_tailOccurrences (name : String) :
    ∀ (fuel : Nat) (tail : Prop) (rho theta : PactType),
      sizeOf rho ≤ fuel → LiveEqBody rho theta →
      TailOccurrences name tail rho → TailOccurrences name tail theta := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    have branches : ∀ (tail : Prop) (bs bs' : List (BareMessage × PactType)),
        sizeOf bs < fuel → LiveEqBranches bs bs' →
        TailBranchOccurrences name tail bs →
        TailBranchOccurrences name tail bs' := by
      intro tail bs
      induction bs with
      | nil =>
          intro bs' _ hLive _
          cases bs' with
          | nil => simp [TailBranchOccurrences]
          | cons _ _ => simp only [LiveEqBranches] at hLive
      | cons head rest ihRest =>
          intro bs' hSize hLive hTail
          cases bs' with
          | nil => simp only [LiveEqBranches] at hLive
          | cons head' rest' =>
              obtain ⟨action, body⟩ := head
              obtain ⟨action', body'⟩ := head'
              simp only [LiveEqBranches] at hLive
              obtain ⟨rfl, hBody, hRest⟩ := hLive
              simp only [TailBranchOccurrences] at hTail ⊢
              simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hSize
              exact ⟨ih (sizeOf body) (by omega) tail body body' le_rfl hBody
                  hTail.1,
                ihRest rest' (by omega) hRest hTail.2⟩
    intro tail rho theta hSize hLive hTail
    cases rho <;> cases theta <;>
      first
        | (simp only [LiveEqBody] at hLive; done)
        | (simp only [TailOccurrences]; done)
        | skip
    case var.var a other a' other' =>
        simp only [LiveEqBody] at hLive
        subst hLive
        simp only [TailOccurrences] at hTail ⊢
        exact hTail
    case choice.choice a l r a' l' r' =>
        simp only [LiveEqBody] at hLive
        simp only [TailOccurrences] at hTail ⊢
        simp only [PactType.choice.sizeOf_spec] at hSize
        exact ⟨ih (sizeOf l) (by omega) tail l l' le_rfl hLive.2.1 hTail.1,
          ih (sizeOf r) (by omega) tail r r' le_rfl hLive.2.2 hTail.2⟩
    case seq.seq a l r a' l' r' =>
        simp only [LiveEqBody] at hLive
        simp only [TailOccurrences] at hTail ⊢
        simp only [PactType.seq.sizeOf_spec] at hSize
        exact ⟨ih (sizeOf l) (by omega) False l l' le_rfl hLive.2.1 hTail.1,
          ih (sizeOf r) (by omega) tail r r' le_rfl hLive.2.2 hTail.2⟩
    case fairChoice.fairChoice a bid l r a' bid' l' r' =>
        simp only [LiveEqBody] at hLive
        simp only [TailOccurrences] at hTail ⊢
        simp only [PactType.fairChoice.sizeOf_spec] at hSize
        exact ⟨ih (sizeOf l) (by omega) tail l l' le_rfl hLive.2.2.1 hTail.1,
          ih (sizeOf r) (by omega) tail r r' le_rfl hLive.2.2.2 hTail.2⟩
    case par.par a l r i a' l' r' i' =>
        simp only [LiveEqBody] at hLive
        simp only [TailOccurrences] at hTail ⊢
        simp only [PactType.par.sizeOf_spec] at hSize
        exact ⟨ih (sizeOf l) (by omega) False l l' le_rfl hLive.2.2.1 hTail.1,
          ih (sizeOf r) (by omega) False r r' le_rfl hLive.2.2.2 hTail.2⟩
    case recur.recur a other body a' other' body' =>
        have hOther : other = other' := by
          simp only [LiveEqBody] at hLive; exact hLive.1
        subst hOther
        simp only [LiveEqBody] at hLive
        simp only [TailOccurrences] at hTail ⊢
        simp only [PactType.recur.sizeOf_spec] at hSize
        by_cases hName : other = name
        · rw [if_pos hName]
          trivial
        · rw [if_neg hName] at hTail ⊢
          exact ih (sizeOf body) (by omega) tail body body' le_rfl hLive.2.2
            hTail
    case xoffer.xoffer a e bs a' e' bs' =>
        simp only [LiveEqBody] at hLive
        simp only [TailOccurrences] at hTail ⊢
        simp only [PactType.xoffer.sizeOf_spec] at hSize
        exact ⟨ih (sizeOf e) (by omega) tail e e' le_rfl hLive.2.1 hTail.1,
          branches tail bs bs' (by omega) hLive.2.2 hTail.2⟩
    case offer.offer a e bs a' e' bs' =>
        simp only [LiveEqBody] at hLive
        simp only [TailOccurrences] at hTail ⊢
        simp only [PactType.offer.sizeOf_spec] at hSize
        exact ⟨ih (sizeOf e) (by omega) tail e e' le_rfl hLive.2.1 hTail.1,
          branches False bs bs' (by omega) hLive.2.2 hTail.2⟩

/-- Fuel-free form of `liveEqBody_tailOccurrences`. -/
theorem liveEqBody_tailOccurrences' {name : String} {tail : Prop}
    {rho theta : PactType} (hLive : LiveEqBody rho theta)
    (hTail : TailOccurrences name tail rho) :
    TailOccurrences name tail theta :=
  liveEqBody_tailOccurrences name (sizeOf rho) tail rho theta le_rfl hLive hTail

/-- Branch-list form of `liveEqBody_tailOccurrences`. -/
theorem liveEqBranches_tailBranchOccurrences (name : String) (tail : Prop) :
    ∀ bs bs' : List (BareMessage × PactType), LiveEqBranches bs bs' →
      TailBranchOccurrences name tail bs →
        TailBranchOccurrences name tail bs' := by
  intro bs
  induction bs with
  | nil =>
      intro bs' hLive _
      cases bs' with
      | nil => simp [TailBranchOccurrences]
      | cons _ _ => simp only [LiveEqBranches] at hLive
  | cons head rest ihRest =>
      intro bs' hLive hTail
      cases bs' with
      | nil => simp only [LiveEqBranches] at hLive
      | cons head' rest' =>
          obtain ⟨action, body⟩ := head
          obtain ⟨action', body'⟩ := head'
          simp only [LiveEqBranches] at hLive
          obtain ⟨rfl, hBody, hRest⟩ := hLive
          simp only [TailBranchOccurrences] at hTail ⊢
          exact ⟨liveEqBody_tailOccurrences' hBody hTail.1,
            ihRest rest' hRest hTail.2⟩

/-- Substituting live-equivalent bodies for a tail-confined variable preserves
live equivalence, and the result's actions stay within the agreement.  Fuelled
form, with the two node alphabets pinned to the root pair. -/
theorem liveEqBody_replaceVar_fuel (name : String) {R R' : PactType}
    {alphaL alphaR : PactTypeAlphabet} (hRepl : LiveEqBody R R')
    (hAgreeR : PactTypeAlphabet.AgreeOn alphaL alphaR (MessageActions R)) :
    ∀ (fuel : Nat) (b b' : PactType),
      sizeOf b ≤ fuel → LiveEqBody b b' →
      b.AlphabetWellFormed → b'.AlphabetWellFormed →
      b.alphabet = alphaL → b'.alphabet = alphaR →
      TailOccurrences name True b →
      LiveEqBody (b.replaceVar name R) (b'.replaceVar name R') ∧
        PactTypeAlphabet.AgreeOn alphaL alphaR
          (MessageActions (b.replaceVar name R)) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    have branches : ∀ (bs bs' : List (BareMessage × PactType)),
        sizeOf bs < fuel → LiveEqBranches bs bs' →
        BranchesAlphabetWellFormed alphaL bs →
        BranchesAlphabetWellFormed alphaR bs' →
        PactTypeAlphabet.AgreeOn alphaL alphaR (BranchMessageActions bs) →
        TailBranchOccurrences name True bs →
        LiveEqBranches (replaceBranches bs name R)
            (replaceBranches bs' name R') ∧
          PactTypeAlphabet.AgreeOn alphaL alphaR
            (BranchMessageActions (replaceBranches bs name R)) := by
      intro bs
      induction bs with
      | nil =>
          intro bs' _ hLive _ _ _ _
          cases bs' with
          | nil =>
              simp only [replaceBranches, BranchMessageActions]
              exact ⟨by simp [LiveEqBranches],
                PactTypeAlphabet.AgreeOn.empty _ _⟩
          | cons _ _ => simp only [LiveEqBranches] at hLive
      | cons head rest ihRest =>
          intro bs' hSize hLive hWF hWF' hAgreeBs hTail
          cases bs' with
          | nil => simp only [LiveEqBranches] at hLive
          | cons head' rest' =>
              obtain ⟨action, body⟩ := head
              obtain ⟨action', body'⟩ := head'
              simp only [LiveEqBranches] at hLive
              obtain ⟨rfl, hBody, hRest⟩ := hLive
              simp only [BranchesAlphabetWellFormed] at hWF hWF'
              simp only [TailBranchOccurrences] at hTail
              simp only [BranchMessageActions] at hAgreeBs
              simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hSize
              have hSubHead : ({action} : Finset BareMessage) ⊆
                  {action} ∪ MessageActions body ∪
                    BranchMessageActions rest := by
                intro x hx
                simp only [Finset.mem_union]
                exact Or.inl (Or.inl hx)
              have hSubRest : BranchMessageActions rest ⊆
                  {action} ∪ MessageActions body ∪
                    BranchMessageActions rest := by
                intro x hx
                simp only [Finset.mem_union]
                exact Or.inr hx
              have hb := ih (sizeOf body) (by omega) body body' le_rfl hBody
                hWF.2.1 hWF'.2.1 hWF.1 hWF'.1 hTail.1
              have hrest := ihRest rest' (by omega) hRest hWF.2.2 hWF'.2.2
                (hAgreeBs.mono hSubRest) hTail.2
              simp only [replaceBranches, LiveEqBranches, BranchMessageActions]
              exact ⟨⟨trivial, hb.1, hrest.1⟩,
                ((hAgreeBs.mono hSubHead).union hb.2).union hrest.2⟩
    intro b b' hSize hLive hWF hWF' hAlphaL hAlphaR hTail
    cases b <;> cases b' <;>
      first
        | (simp only [LiveEqBody] at hLive; done)
        | skip
    case message.message a m d a' m' d' =>
        have hAgree : PactTypeAlphabet.AgreeOn alphaL alphaR {(m, d)} := by
          simp only [PactType.alphabet] at hAlphaL hAlphaR
          subst hAlphaL
          subst hAlphaR
          simp only [LiveEqBody] at hLive
          exact hLive.2.2
        simp only [replaceVar]
        refine ⟨hLive, ?_⟩
        simpa only [MessageActions] using hAgree
    case progress.progress a p a' p' =>
        simp only [replaceVar]
        refine ⟨hLive, ?_⟩
        simp only [MessageActions]
        exact PactTypeAlphabet.AgreeOn.empty _ _
    case tock.tock a a' =>
        simp only [replaceVar]
        refine ⟨hLive, ?_⟩
        simp only [MessageActions]
        exact PactTypeAlphabet.AgreeOn.empty _ _
    case skip.skip a a' =>
        simp only [replaceVar]
        refine ⟨hLive, ?_⟩
        simp only [MessageActions]
        exact PactTypeAlphabet.AgreeOn.empty _ _
    case var.var a other a' other' =>
        simp only [LiveEqBody] at hLive
        subst hLive
        simp only [replaceVar]
        by_cases hName : name = other
        · rw [if_pos hName, if_pos hName]
          exact ⟨hRepl, hAgreeR⟩
        · rw [if_neg hName, if_neg hName]
          refine ⟨by simp [LiveEqBody], ?_⟩
          simp only [MessageActions]
          exact PactTypeAlphabet.AgreeOn.empty _ _
    case choice.choice a l r a' l' r' =>
        simp only [PactType.alphabet] at hAlphaL hAlphaR
        subst hAlphaL
        subst hAlphaR
        simp only [LiveEqBody] at hLive
        simp only [AlphabetWellFormed] at hWF hWF'
        simp only [TailOccurrences] at hTail
        simp only [PactType.choice.sizeOf_spec] at hSize
        have hl := ih (sizeOf l) (by omega) l l' le_rfl hLive.2.1 hWF.2.2.2.1
          hWF'.2.2.2.1 hWF.2.1 hWF'.2.1 hTail.1
        have hr := ih (sizeOf r) (by omega) r r' le_rfl hLive.2.2 hWF.2.2.2.2
          hWF'.2.2.2.2 hWF.2.2.1 hWF'.2.2.1 hTail.2
        have hNode := hl.2.union hr.2
        simp only [replaceVar, LiveEqBody, MessageActions]
        exact ⟨⟨hNode, hl.1, hr.1⟩, hNode⟩
    case seq.seq a l r a' l' r' =>
        simp only [PactType.alphabet] at hAlphaL hAlphaR
        subst hAlphaL
        subst hAlphaR
        simp only [LiveEqBody] at hLive
        simp only [AlphabetWellFormed] at hWF hWF'
        simp only [TailOccurrences] at hTail
        simp only [PactType.seq.sizeOf_spec] at hSize
        have hl := ih (sizeOf l) (by omega) l l' le_rfl hLive.2.1 hWF.2.2.2.1
          hWF'.2.2.2.1 hWF.2.1 hWF'.2.1
          (tailOccurrences_mono name False.elim l hTail.1)
        have hr := ih (sizeOf r) (by omega) r r' le_rfl hLive.2.2 hWF.2.2.2.2
          hWF'.2.2.2.2 hWF.2.2.1 hWF'.2.2.1 hTail.2
        have hNode := hl.2.union hr.2
        simp only [replaceVar, LiveEqBody, MessageActions]
        exact ⟨⟨hNode, hl.1, hr.1⟩, hNode⟩
    case fairChoice.fairChoice a bid l r a' bid' l' r' =>
        simp only [PactType.alphabet] at hAlphaL hAlphaR
        subst hAlphaL
        subst hAlphaR
        simp only [LiveEqBody] at hLive
        simp only [AlphabetWellFormed] at hWF hWF'
        simp only [TailOccurrences] at hTail
        simp only [PactType.fairChoice.sizeOf_spec] at hSize
        have hl := ih (sizeOf l) (by omega) l l' le_rfl hLive.2.2.1 hWF.2.2.2.1
          hWF'.2.2.2.1 hWF.2.1 hWF'.2.1 hTail.1
        have hr := ih (sizeOf r) (by omega) r r' le_rfl hLive.2.2.2 hWF.2.2.2.2
          hWF'.2.2.2.2 hWF.2.2.1 hWF'.2.2.1 hTail.2
        have hNode := hl.2.union hr.2
        simp only [replaceVar, LiveEqBody, MessageActions]
        exact ⟨⟨hLive.1, hNode, hl.1, hr.1⟩, hNode⟩
    case par.par a l r i a' l' r' i' =>
        simp only [PactType.alphabet] at hAlphaL hAlphaR
        subst hAlphaL
        subst hAlphaR
        simp only [LiveEqBody] at hLive
        simp only [TailOccurrences] at hTail
        have hl' := liveEqBody_tailOccurrences' hLive.2.2.1 hTail.1
        have hr' := liveEqBody_tailOccurrences' hLive.2.2.2 hTail.2
        simp only [replaceVar]
        rw [replaceVar_eq_self_of_tailOccurrences_false name R l hTail.1,
          replaceVar_eq_self_of_tailOccurrences_false name R r hTail.2,
          replaceVar_eq_self_of_tailOccurrences_false name R' l' hl',
          replaceVar_eq_self_of_tailOccurrences_false name R' r' hr']
        refine ⟨?_, hLive.2.1⟩
        simp only [LiveEqBody]
        exact hLive
    case recur.recur a other body a' other' body' =>
        have hOther : other = other' := by
          simp only [LiveEqBody] at hLive; exact hLive.1
        subst hOther
        simp only [PactType.alphabet] at hAlphaL hAlphaR
        subst hAlphaL
        subst hAlphaR
        simp only [replaceVar]
        by_cases hName : other = name
        · rw [if_pos hName.symm, if_pos hName.symm]
          refine ⟨hLive, ?_⟩
          simp only [MessageActions]
          simp only [LiveEqBody] at hLive
          exact hLive.2.1
        · rw [if_neg (fun h : name = other => hName h.symm),
            if_neg (fun h : name = other => hName h.symm)]
          simp only [LiveEqBody] at hLive
          simp only [AlphabetWellFormed] at hWF hWF'
          simp only [TailOccurrences] at hTail
          rw [if_neg hName] at hTail
          simp only [PactType.recur.sizeOf_spec] at hSize
          have hb := ih (sizeOf body) (by omega) body body' le_rfl hLive.2.2
            hWF.2.2 hWF'.2.2 hWF.2.1 hWF'.2.1 hTail
          simp only [LiveEqBody, MessageActions]
          exact ⟨⟨trivial, hb.2, hb.1⟩, hb.2⟩
    case xoffer.xoffer a e bs a' e' bs' =>
        simp only [PactType.alphabet] at hAlphaL hAlphaR
        subst hAlphaL
        subst hAlphaR
        simp only [LiveEqBody] at hLive
        simp only [AlphabetWellFormed] at hWF hWF'
        simp only [TailOccurrences] at hTail
        simp only [PactType.xoffer.sizeOf_spec] at hSize
        have hHead := hLive.1
        simp only [MessageActions] at hHead
        have hAgreeBs := PactTypeAlphabet.AgreeOn.mono hHead
          Finset.subset_union_right
        have he := ih (sizeOf e) (by omega) e e' le_rfl hLive.2.1 hWF.2.2.1
          hWF'.2.2.1 hWF.2.1 hWF'.2.1 hTail.1
        have hbs := branches bs bs' (by omega) hLive.2.2 hWF.2.2.2 hWF'.2.2.2
          hAgreeBs hTail.2
        have hNode := he.2.union hbs.2
        simp only [replaceVar, LiveEqBody, MessageActions]
        exact ⟨⟨hNode, he.1, hbs.1⟩, hNode⟩
    case offer.offer a e bs a' e' bs' =>
        simp only [PactType.alphabet] at hAlphaL hAlphaR
        subst hAlphaL
        subst hAlphaR
        simp only [LiveEqBody] at hLive
        simp only [AlphabetWellFormed] at hWF hWF'
        simp only [TailOccurrences] at hTail
        simp only [PactType.offer.sizeOf_spec] at hSize
        have hBs' := liveEqBranches_tailBranchOccurrences name False bs bs'
          hLive.2.2 hTail.2
        have hHead := hLive.1
        simp only [MessageActions] at hHead
        have hAgreeBs := PactTypeAlphabet.AgreeOn.mono hHead
          Finset.subset_union_right
        have he := ih (sizeOf e) (by omega) e e' le_rfl hLive.2.1 hWF.2.2.1
          hWF'.2.2.1 hWF.2.1 hWF'.2.1 hTail.1
        have hNode := he.2.union hAgreeBs
        simp only [replaceVar]
        rw [replaceBranches_eq_self_of_tailBranchOccurrences_false name R bs
            hTail.2,
          replaceBranches_eq_self_of_tailBranchOccurrences_false name R' bs'
            hBs']
        simp only [LiveEqBody, MessageActions]
        exact ⟨⟨hNode, he.1, hLive.2.2⟩, hNode⟩

/-- Unfolding a binder preserves live equivalence.  The two node alphabets need
only agree on the replacement's own actions. -/
theorem liveEqBody_replaceVar_agree {b b' R R' : PactType} {n : String}
    (hBody : LiveEqBody b b') (hRepl : LiveEq R R')
    (hWF : b.AlphabetWellFormed) (hWFt : b'.AlphabetWellFormed)
    (hAgreeR : PactTypeAlphabet.AgreeOn b.alphabet b'.alphabet
      (MessageActions R))
    (hTail : TailOccurrences n True b) :
    LiveEqBody (b.replaceVar n R) (b'.replaceVar n R') :=
  (liveEqBody_replaceVar_fuel n hRepl.2 hAgreeR (sizeOf b) b b' le_rfl hBody hWF
    hWFt rfl rfl hTail).1

/-- Equal node alphabets are the special case where the agreement is
reflexivity. -/
theorem liveEqBody_replaceVar {b b' R R' : PactType} {n : String}
    (hBody : LiveEqBody b b') (hRepl : LiveEq R R')
    (hWF : b.AlphabetWellFormed) (hWFt : b'.AlphabetWellFormed)
    (hAlpha : b.alphabet = b'.alphabet)
    (hTail : TailOccurrences n True b) :
    LiveEqBody (b.replaceVar n R) (b'.replaceVar n R') :=
  liveEqBody_replaceVar_agree hBody hRepl hWF hWFt
    (by rw [hAlpha]; exact PactTypeAlphabet.AgreeOn.refl _ _) hTail

end PactType

end Pact
