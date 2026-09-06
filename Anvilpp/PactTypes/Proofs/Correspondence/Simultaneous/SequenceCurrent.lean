import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.Base
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.SequenceMenus

namespace Pact

noncomputable section

open Classical Pact.NewCorrespondence

/-- Sequence copies current offers; only the target determines redirection. -/
theorem currentOfferCorrespondence_seq (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hLeftResidualWF : ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet left (compileType left)) residual state →
        residual.AlphabetWellFormed)
    (hLeft : CurrentOfferCorrespondence left)
    (hRight : CurrentOfferCorrespondence right) :
    CurrentOfferCorrespondence (.seq alphabet left right) := by
  classical
  let l := compileTypeFuel (typeCompilationFuel left) left
  let r := compileTypeFuel (typeCompilationFuel right) right
  let whole := PactType.seq alphabet left right
  have hEntry := relationMembership_seq_right alphabet left right right
    (buildRelationSet_initial right (compileType right))
  -- The paper's left injection retains the source and redirects final targets.
  have hLiftLeft : ∀ {q q' env label current future},
      (q ∉ (compileType left).accepting ∨ q = (compileType left).initial) →
      (compileType left).HasEdge q env label ⟨current, future⟩ q' →
      ∃ future', (compileType whole).HasEdge (.child 0 q) env label
        ⟨current, future'⟩ (sequenceRedirect l r q') := by
    intro q q' env label current future hKept hEdge
    obtain ⟨e, he, hs, henv, hl, hc, _, ht⟩ :=
      (compileType_hasEdge_iff_hasResolvedEdge left q q' env label
        ⟨current, future⟩).mp hEdge
    have hSource : e.source ∉ sequenceDeleted l := by
      rw [hs]
      rcases hKept with hn | hi
      · exact fun h => hn (Finset.mem_sdiff.mp h).1
      · simp [sequenceDeleted, l, hi, compileType]
    have hMem := sequenceLeftEdge_mem l r e he hSource
    refine ⟨match (sequenceLeftEdge l r e).future with
      | .explicit f => f
      | .at t removed => computeFutureOf whole t \ removed, ?_⟩
    apply (compileType_hasEdge_iff_hasResolvedEdge whole _ _ _ _ _).mpr
    rw [compileTypeFuel_sequence_eq_build]
    exact ⟨sequenceLeftEdge l r e, hMem, by simpa using congrArg (childState 0) hs,
      by simpa using henv, by simpa using hl, by simpa using hc, rfl,
      by simp [ht]⟩
  -- The right injection copies the entire edge family.
  have hLiftRight : ∀ {q q' env label current future},
      (compileType right).HasEdge q env label ⟨current, future⟩ q' →
      ∃ future', (compileType whole).HasEdge (.child 1 q) env label
        ⟨current, future'⟩ (.child 1 q') := by
    intro q q' env label current future hEdge
    obtain ⟨e, he, hs, henv, hl, hc, _, ht⟩ :=
      (compileType_hasEdge_iff_hasResolvedEdge right q q' env label
        ⟨current, future⟩).mp hEdge
    refine ⟨match (childPendingEdge 1 e).future with
      | .explicit f => f
      | .at t removed => computeFutureOf whole t \ removed, ?_⟩
    apply (compileType_hasEdge_iff_hasResolvedEdge whole _ _ _ _ _).mpr
    rw [compileTypeFuel_sequence_eq_build]
    refine ⟨childPendingEdge 1 e, ?_, ?_, henv, hl, hc, rfl, ?_⟩
    · change childPendingEdge 1 e ∈ (buildSequenceAutomaton l r).edges
      simp only [buildSequenceAutomaton, finishAutomatonFragment, Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨e, he, rfl⟩))
    · simpa [childPendingEdge, childState] using hs
    · simpa [childPendingEdge, childState] using ht
  constructor
  · intro rho rho' q env label current future hRelated hStep
    rcases relationMembership_seq_cases alphabet left right hRelated with
      ⟨s, source, hPair, hSource, hKept⟩ | ⟨s, hState, hSource⟩
    · cases hPair
      -- Apply the child hypothesis, then the paper's final-state lemma.
      have hRetain : ∀ {target cf}, target ≠ .skip target.alphabet →
          DecoratedTypeTransition env source label ⟨current, cf⟩ target →
          ∃ q' future', (compileType whole).HasEdge (.child 0 s) env label
            ⟨current, future'⟩ q' ∧
            relationMembership (buildRelationSet whole (compileType whole))
              (.seq alphabet target right) q' := by
        intro target cf hn hc
        obtain ⟨t, f, he, hr⟩ := hLeft.1 hSource hc
        have ha : t ∉ (compileType left).accepting := by
          intro ha
          obtain ⟨a, rfl⟩ := (final_states_completion left hr).mp ha
          exact hn rfl
        obtain ⟨f', he'⟩ := hLiftLeft hKept he
        rw [sequenceRedirect_of_not_accepting ha] at he'
        exact ⟨_, f', he', relationMembership_seq_left alphabet left right target hr ha⟩
      have hFuse : ∀ {a cf},
          DecoratedTypeTransition env source label ⟨current, cf⟩ (.skip a) →
          ∃ q' future', (compileType whole).HasEdge (.child 0 s) env label
            ⟨current, future'⟩ q' ∧
            relationMembership (buildRelationSet whole (compileType whole)) right q' := by
        intro a cf hc
        obtain ⟨t, f, he, hr⟩ := hLeft.1 hSource hc
        have ha := (final_states_completion left hr).mpr ⟨a, rfl⟩
        obtain ⟨f', he'⟩ := hLiftLeft hKept he
        rw [sequenceRedirect_of_accepting ha] at he'
        exact ⟨_, f', he', hEntry⟩
      rcases decoratedTypeTransition_seq_cases hStep with
        ⟨target, cf, ht, hn, hc, _, _⟩ |
        ⟨target, cc, cf, ht, hn, hl, hc, _⟩ |
        ⟨ta, oa, cf, ht, hT, hO, _, _⟩ |
        ⟨ta, oa, cc, cf, ht, hl, hT, hO, _⟩
      · subst ht; exact hRetain hn hc
      · subst hl; subst ht
        have hC : current = ∅ := hStep.2.current_eq_empty_of_label_tock rfl
        have hCC : cc = ∅ := hc.2.current_eq_empty_of_label_tock rfl
        subst current; subst cc
        exact hRetain hn hc
      · have hA : oa = ta := (TypeOffers.preserves_alphabet
            (hLeftResidualWF hSource) hO).trans
            (TypeTransition.preserves_alphabet (hLeftResidualWF hSource) hT).symm
        subst hA; subst ht; exact hFuse ⟨hT, hO⟩
      · subst hl; subst ht
        have hC : current = ∅ := hStep.2.current_eq_empty_of_label_tock rfl
        have hCC : cc = ∅ := hO.current_eq_empty_of_label_tock rfl
        have hA : oa = ta := (TypeOffers.preserves_alphabet
            (hLeftResidualWF hSource) hO).trans
            (TypeTransition.preserves_alphabet (hLeftResidualWF hSource) hT).symm
        subst hA
        subst current; subst cc
        exact hFuse ⟨hT, hO⟩
    · subst hState
      obtain ⟨t, f, he, hr⟩ := hRight.1 hSource hStep
      obtain ⟨f', he'⟩ := hLiftRight he
      exact ⟨_, f', he', relationMembership_seq_right alphabet left right rho' hr⟩
  · intro rho q q' env label current future hRelated hEdge
    obtain ⟨e, he, hs, henv, hl, hc, _, ht⟩ :=
      (compileType_hasEdge_iff_hasResolvedEdge whole q q' env label
        ⟨current, future⟩).mp hEdge
    rw [compileTypeFuel_sequence_eq_build] at he
    rcases relationMembership_seq_cases alphabet left right hRelated with
      ⟨s, source, hPair, hSource, _⟩ | ⟨s, hState, hSource⟩
    · cases hPair
      obtain ⟨ce, hce, hcs, rfl⟩ :=
        buildSequenceAutomaton_outgoing_left l r s e ⟨he, hs⟩
      simp only [sequenceLeftEdge_environment, sequenceLeftEdge_label,
        sequenceLeftEdge_current, sequenceLeftEdge_target] at henv hl hc ht
      have hChild : (compileType left).HasEdge s env label
          ⟨current, match ce.future with
            | .explicit f => f
            | .at t removed => computeFutureOf left t \ removed⟩ ce.target :=
        (compileType_hasEdge_iff_hasResolvedEdge left _ _ _ _ _).mpr
          ⟨ce, hce, hcs, henv, hl, hc, rfl, rfl⟩
      obtain ⟨target, cf, hStep, hTarget⟩ := hLeft.2 hSource hChild
      -- A final child target fuses; every other target stays in the left copy.
      by_cases ha : ce.target ∈ (compileType left).accepting
      · obtain ⟨a, rfl⟩ := (final_states_completion left hTarget).mp ha
        rw [sequenceRedirect_of_accepting ha] at ht
        subst q'
        by_cases hClock : label = .tock
        · subst label
          have hC : current = ∅ := hStep.2.current_eq_empty_of_label_tock rfl
          refine ⟨right, ∅, ⟨.seq_fuse _ _ _ _ _ _ hStep.1, ?_⟩, hEntry⟩
          exact hC ▸ TypeOffers.seq_fuse_tock env alphabet a source right
            current cf hStep.2
        · exact ⟨right, typeFutureOffers right \ current,
            ⟨.seq_fuse _ _ _ _ _ _ hStep.1,
            .seq_fuse _ _ _ _ _ _ _ _ hStep.2 hClock⟩, hEntry⟩
      · have hn : target ≠ .skip target.alphabet := by
          intro h; exact ha ((final_states_completion left hTarget).mpr ⟨_, h⟩)
        rw [sequenceRedirect_of_not_accepting ha] at ht
        subst q'
        have hr := relationMembership_seq_left alphabet left right target hTarget ha
        by_cases hClock : label = .tock
        · subst label
          have hC : current = ∅ := hStep.2.current_eq_empty_of_label_tock rfl
          refine ⟨.seq alphabet target right, ∅,
            ⟨.seq _ _ _ _ _ _ hStep.1 hn, ?_⟩, hr⟩
          exact hC ▸ TypeOffers.seq_tock env alphabet source target right
            current cf hStep.2 hn
        · exact ⟨.seq alphabet target right,
            typeFutureOffers (.seq alphabet target right) \ current,
            ⟨.seq _ _ _ _ _ _ hStep.1 hn,
              .seq _ _ _ _ _ _ _ _ hStep.2 hn hClock⟩, hr⟩
    · subst hState
      obtain ⟨ce, hce, hcs, rfl⟩ :=
        (buildSequenceAutomaton_outgoing_right l r s e).mp ⟨he, hs⟩
      have hChild : (compileType right).HasEdge s env label
          ⟨current, match ce.future with
            | .explicit f => f
            | .at t removed => computeFutureOf right t \ removed⟩ ce.target :=
        (compileType_hasEdge_iff_hasResolvedEdge right _ _ _ _ _).mpr
          ⟨ce, hce, hcs, henv, hl, hc, rfl, rfl⟩
      obtain ⟨target, cf, hStep, hTarget⟩ := hRight.2 hSource hChild
      subst q'
      exact ⟨target, cf, hStep,
        relationMembership_seq_right alphabet left right target hTarget⟩

end

end Pact
