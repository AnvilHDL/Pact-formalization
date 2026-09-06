import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.CompletionFlag
import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.SequenceCurrent
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.SequenceMenus

namespace Pact

noncomputable section

open Classical Pact.NewCorrespondence

/-- Sequence menus follow from the child hypotheses. Tail closure excludes
unbound markers in the left component. -/
theorem futureOffersAgree_seq
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = alphabet)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeftMenus : FutureOffersAgree left)
    (hRightMenus : FutureOffersAgree right)
    (hLeftCurrent : CurrentOfferCorrespondence left)
    {bound : List String} (hLeftWF : TypeWellFormedIn bound left)
    (hLeftTail : ∀ name, left.TailOccurrences name False) :
    FutureOffersAgree (.seq alphabet left right) := by
  intro residual state hRelated
  rcases relationMembership_seq_cases alphabet left right hRelated with hLeft | hRight
  · obtain ⟨q, residualLeft, hPair, hRelatedLeft, hRetained⟩ := hLeft
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hPair
    have hKeep : q ∉ sequenceDeleted
        (compileTypeFuel (typeCompilationFuel left) left) := by
      rcases hRetained with hNotFinal | hInitial
      · exact not_mem_sequenceDeleted_of_not_accepting hNotFinal
      · exact hInitial ▸ initial_not_mem_sequenceDeleted _
    -- The left equation has exactly the completion flag of its related residual.
    have hComplete := completionFlag_backward_of_menuReachable left hLeftWF hLeftDisjoint
      (fun name => compileTypeFuel_noMarkerFor name _ left (hLeftTail name))
      hLeftCurrent hRelatedLeft
    rw [computeFutureOf_sequence_left alphabet left right hLeftDisjoint hRightDisjoint
      hLeftAlphabet hRightAlphabet q
      (relationMembership_state_mem left residualLeft q hLeftDisjoint hRelatedLeft)
      hKeep hComplete]
    have hFlag : (∃ candidate, (candidate, q) ∈
          buildRelationSetCoreFuel (typeCompilationFuel left) left ∧
          typeCanCompleteThisCycleFuel (sizeOf candidate + 1) candidate = true) ↔
        typeCanCompleteThisCycleFuel (sizeOf residualLeft + 1) residualLeft = true := by
      constructor
      · rintro ⟨candidate, hCandidate, hComplete⟩
        have hEq := buildRelationSetCoreFuel_functional (typeCompilationFuel left)
          left hCandidate hRelatedLeft
        simpa only [hEq] using hComplete
      · intro hComplete
        exact ⟨residualLeft, hRelatedLeft, hComplete⟩
    rw [hFlag, hLeftMenus hRelatedLeft,
      hRightMenus (buildRelationSetCoreFuel_initial_mem _ right
        (typeCompilationFuel_sufficient right))]
    -- Apply the two child hypotheses to obtain the syntax's sequence clause.
    rw [typeFutureOffers_sequence,
      ← typeCanCompleteThisCycleFuel_eq_canCompleteDeclared
        (sizeOf residualLeft + 1) residualLeft (by omega)]
    split_ifs <;> simp
  · obtain ⟨q, hState, hRelatedRight⟩ := hRight
    change state = .child 1 q at hState
    subst state
    -- Right states use the unchanged copied-child menu equation.
    rw [computeFutureOf_sequence_right alphabet left right hRightDisjoint hRightAlphabet q
      (relationMembership_state_mem right residual q hRightDisjoint hRelatedRight)]
    exact hRightMenus hRelatedRight

/-- Sequence keeps the full left witness and adds the right-entry menu under
the represented source flag. Final targets only change the state injection. -/
theorem offerCorrespondence_seq (alphabet : PactTypeAlphabet) (left right : PactType)
    (hLeftResidualWF : ∀ {rho : PactType} {q : TypeAutomatonState},
      relationMembership (buildRelationSet left (compileType left)) rho q →
        rho.AlphabetWellFormed)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hRightAlphabet : right.alphabet = alphabet)
    (hRightMenus : FutureOffersAgree right)
    (hLeft : TypeAutomatonStepCorrespondence left)
    (hRight : TypeAutomatonStepCorrespondence right) :
    TypeAutomatonStepCorrespondence (.seq alphabet left right) := by
  let l := compileTypeFuel (typeCompilationFuel left) left
  let r := compileTypeFuel (typeCompilationFuel right) right
  let whole := PactType.seq alphabet left right
  let leftFuture := computeFutureOf left
  let leftCompletes := fun state => decide (∃ entry ∈ buildRelationSetCoreFuel
    (typeCompilationFuel left) left, entry.2 = state ∧
      typeCanCompleteThisCycleFuel (sizeOf entry.1 + 1) entry.1 = true)
  have hEntry := relationMembership_seq_right alphabet left right right
    (buildRelationSet_initial right (compileType right))
  have hLiftLeft : ∀ {source q q' env label current future},
      relationMembership (buildRelationSet left (compileType left)) source q →
      (q ∉ (compileType left).accepting ∨ q = (compileType left).initial) →
      (compileType left).HasEdge q env label ⟨current, future⟩ q' →
      (compileType whole).HasEdge (.child 0 q) env label
        ⟨current, if label = TypeLabel.tock then ∅ else
          (future ∪ sequenceRightMenu source right) \ current⟩
        (sequenceRedirect l r q') := by
    intro source q q' env label current future hRelated hKept hEdge
    obtain ⟨e, he, hs, henv, hl, hc, hf, ht⟩ :=
      (compileType_hasEdge_iff_hasResolvedEdge left q q' env label
        ⟨current, future⟩).mp hEdge
    change resolveFutureSpec (computeFutureOf left) e.future = future at hf
    have hSource : e.source ∉ sequenceDeleted l := by
      rw [hs]
      rcases hKept with hn | hi
      · exact fun h => hn (Finset.mem_sdiff.mp h).1
      · simp [sequenceDeleted, l, hi, compileType]
    have hField := sequenceLeftEdge_resolve_future alphabet left right source e
      hRightDisjoint hRightAlphabet hRightMenus (by simpa only [hs] using hRelated)
    apply (compileType_hasEdge_iff_hasResolvedEdge whole _ _ _ _ _).mpr
    rw [compileTypeFuel_sequence_eq_build]
    refine ⟨sequenceLeftEdge l r leftFuture leftCompletes e,
      sequenceLeftEdge_mem l r e he hSource, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using congrArg (childState 0) hs
    · simpa using henv
    · simpa using hl
    · simpa using hc
    · simpa only [hl, AutomatonConstructionLabel.semantic, hc, hf] using hField
    · simp [ht]
  have hLiftRight : ∀ {q q' env label current future},
      (compileType right).HasEdge q env label ⟨current, future⟩ q' →
      (compileType whole).HasEdge (.child 1 q) env label
        ⟨current, future⟩ (.child 1 q') := by
    intro q q' env label current future hEdge
    obtain ⟨e, he, hs, henv, hl, hc, hf, ht⟩ :=
      (compileType_hasEdge_iff_hasResolvedEdge right q q' env label
        ⟨current, future⟩).mp hEdge
    apply (compileType_hasEdge_iff_hasResolvedEdge whole _ _ _ _ _).mpr
    rw [compileTypeFuel_sequence_eq_build]
    refine ⟨childPendingEdge 1 e, ?_, ?_, henv, hl, hc, ?_, ?_⟩
    · change childPendingEdge 1 e ∈ (buildSequenceAutomaton l r leftFuture leftCompletes).edges
      simp only [buildSequenceAutomaton, finishAutomatonFragment, Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨e, he, rfl⟩))
    · simpa [childPendingEdge, childState] using hs
    · exact (sequenceChildFuture_resolve alphabet left right e he
        hRightDisjoint hRightAlphabet).trans hf
    · simpa [childPendingEdge, childState] using ht
  constructor
  · intro rho rho' q env label offers hRelated hStep
    rcases offers with ⟨current, future⟩
    rcases relationMembership_seq_cases alphabet left right hRelated with
      ⟨s, source, hPair, hSource, hKept⟩ | ⟨s, hState, hSource⟩
    · cases hPair
      have hRetain : ∀ {target cf}, target ≠ .skip target.alphabet →
          DecoratedTypeTransition env source label ⟨current, cf⟩ target →
          future = (if label = TypeLabel.tock then ∅ else
            (cf ∪ sequenceRightMenu source right) \ current) →
          ∃ q', (compileType whole).HasEdge (.child 0 s) env label
            ⟨current, future⟩ q' ∧
            relationMembership (buildRelationSet whole (compileType whole))
              (.seq alphabet target right) q' := by
        intro target cf hn hc hf
        obtain ⟨t, he, hr⟩ := hLeft.1 hSource hc
        have ha : t ∉ (compileType left).accepting := by
          intro ha
          obtain ⟨a, rfl⟩ := (final_states_completion left hr).mp ha
          exact hn rfl
        have he' := hLiftLeft hSource hKept he
        rw [← hf, sequenceRedirect_of_not_accepting ha] at he'
        exact ⟨_, he', relationMembership_seq_left alphabet left right target hr ha⟩
      have hFuse : ∀ {a cf},
          DecoratedTypeTransition env source label ⟨current, cf⟩ (.skip a) →
          future = (if label = TypeLabel.tock then ∅ else
            (cf ∪ sequenceRightMenu source right) \ current) →
          ∃ q', (compileType whole).HasEdge (.child 0 s) env label
            ⟨current, future⟩ q' ∧
            relationMembership (buildRelationSet whole (compileType whole)) right q' := by
        intro a cf hc hf
        obtain ⟨t, he, hr⟩ := hLeft.1 hSource hc
        have ha := (final_states_completion left hr).mpr ⟨a, rfl⟩
        have he' := hLiftLeft hSource hKept he
        rw [← hf, sequenceRedirect_of_accepting ha] at he'
        exact ⟨_, he', hEntry⟩
      rcases decoratedTypeTransition_seq_cases hStep with
        ⟨target, cf, ht, hn, hc, hNC, hf⟩ |
        ⟨target, cc, cf, ht, hn, hl, hc, hf⟩ |
        ⟨ta, oa, cf, ht, hT, hO, hNC, hf⟩ |
        ⟨ta, oa, cc, cf, ht, hl, hT, hO, hf⟩
      · subst ht
        exact hRetain hn hc (by simpa only [if_neg hNC] using hf)
      · subst hl; subst ht
        have hC : current = ∅ := hStep.2.current_eq_empty_of_label_tock rfl
        have hCC : cc = ∅ := hc.2.current_eq_empty_of_label_tock rfl
        subst current; subst cc
        exact hRetain hn hc (by simpa only [if_pos rfl] using hf)
      · have hA : oa = ta := (TypeOffers.preserves_alphabet
            (hLeftResidualWF hSource) hO).trans
            (TypeTransition.preserves_alphabet (hLeftResidualWF hSource) hT).symm
        subst hA; subst ht
        exact hFuse ⟨hT, hO⟩ (by simpa only [if_neg hNC] using hf)
      · subst hl; subst ht
        have hC : current = ∅ := hStep.2.current_eq_empty_of_label_tock rfl
        have hCC : cc = ∅ := hO.current_eq_empty_of_label_tock rfl
        have hA : oa = ta := (TypeOffers.preserves_alphabet
            (hLeftResidualWF hSource) hO).trans
            (TypeTransition.preserves_alphabet (hLeftResidualWF hSource) hT).symm
        subst hA; subst current; subst cc
        exact hFuse ⟨hT, hO⟩ (by simpa only [if_pos rfl] using hf)
    · subst hState
      obtain ⟨t, he, hr⟩ := hRight.1 hSource hStep
      exact ⟨_, hLiftRight he, relationMembership_seq_right alphabet left right rho' hr⟩
  · intro rho q q' env label offers hRelated hEdge
    rcases offers with ⟨current, future⟩
    obtain ⟨e, he, hs, henv, hl, hc, hf, ht⟩ :=
      (compileType_hasEdge_iff_hasResolvedEdge whole q q' env label
        ⟨current, future⟩).mp hEdge
    change resolveFutureSpec (computeFutureOf whole) e.future = future at hf
    rw [compileTypeFuel_sequence_eq_build] at he
    rcases relationMembership_seq_cases alphabet left right hRelated with
      ⟨s, source, hPair, hSource, _⟩ | ⟨s, hState, hSource⟩
    · cases hPair
      obtain ⟨ce, hce, hcs, rfl⟩ :=
        buildSequenceAutomaton_outgoing_left l r s e ⟨he, hs⟩
      simp only [sequenceLeftEdge_environment, sequenceLeftEdge_label,
        sequenceLeftEdge_current, sequenceLeftEdge_target] at henv hl hc ht
      let cf := resolveFutureSpec (computeFutureOf left) ce.future
      have hChild : (compileType left).HasEdge s env label ⟨current, cf⟩ ce.target :=
        (compileType_hasEdge_iff_hasResolvedEdge left _ _ _ _ _).mpr
          ⟨ce, hce, hcs, henv, hl, hc, rfl, rfl⟩
      obtain ⟨target, hStep, hTarget⟩ := hLeft.2 hSource hChild
      have hField := sequenceLeftEdge_resolve_future alphabet left right source ce
        hRightDisjoint hRightAlphabet hRightMenus (by simpa only [hcs] using hSource)
      have hFuture : future = (if label = TypeLabel.tock then ∅ else
          (cf ∪ sequenceRightMenu source right) \ current) := by
        rw [← hf]
        simpa only [hl, AutomatonConstructionLabel.semantic, hc] using hField
      by_cases ha : ce.target ∈ (compileType left).accepting
      · obtain ⟨a, rfl⟩ := (final_states_completion left hTarget).mp ha
        rw [sequenceRedirect_of_accepting ha] at ht
        subst q'
        by_cases hClock : label = .tock
        · subst label
          rw [hFuture, if_pos rfl]
          have hC : current = ∅ := hStep.2.current_eq_empty_of_label_tock rfl
          refine ⟨right, ⟨.seq_fuse _ _ _ _ _ _ hStep.1, ?_⟩, hEntry⟩
          exact hC ▸ TypeOffers.seq_fuse_tock env alphabet a source right
            current cf hStep.2
        · rw [hFuture, if_neg hClock]
          exact ⟨right, ⟨.seq_fuse _ _ _ _ _ _ hStep.1,
            .seq_fuse _ _ _ _ _ _ _ _ hStep.2 hClock⟩, hEntry⟩
      · have hn : target ≠ .skip target.alphabet := by
          intro h; exact ha ((final_states_completion left hTarget).mpr ⟨_, h⟩)
        rw [sequenceRedirect_of_not_accepting ha] at ht
        subst q'
        have hr := relationMembership_seq_left alphabet left right target hTarget ha
        by_cases hClock : label = .tock
        · subst label
          rw [hFuture, if_pos rfl]
          have hC : current = ∅ := hStep.2.current_eq_empty_of_label_tock rfl
          refine ⟨.seq alphabet target right,
            ⟨.seq _ _ _ _ _ _ hStep.1 hn, ?_⟩, hr⟩
          exact hC ▸ TypeOffers.seq_tock env alphabet source target right
            current cf hStep.2 hn
        · rw [hFuture, if_neg hClock]
          exact ⟨.seq alphabet target right,
            ⟨.seq _ _ _ _ _ _ hStep.1 hn,
              .seq _ _ _ _ _ _ _ _ hStep.2 hn hClock⟩, hr⟩
    · subst hState
      obtain ⟨ce, hce, hcs, rfl⟩ :=
        (buildSequenceAutomaton_outgoing_right l r s e).mp ⟨he, hs⟩
      have hChild : (compileType right).HasEdge s env label
          ⟨current, resolveFutureSpec (computeFutureOf right) ce.future⟩ ce.target :=
        (compileType_hasEdge_iff_hasResolvedEdge right _ _ _ _ _).mpr
          ⟨ce, hce, hcs, henv, hl, hc, rfl, rfl⟩
      obtain ⟨target, hStep, hTarget⟩ := hRight.2 hSource hChild
      have hFuture := (sequenceChildFuture_resolve alphabet left right ce hce
        hRightDisjoint hRightAlphabet).symm.trans hf
      subst q'
      exact ⟨target, hFuture ▸ hStep,
        relationMembership_seq_right alphabet left right target hTarget⟩

end

end Pact
