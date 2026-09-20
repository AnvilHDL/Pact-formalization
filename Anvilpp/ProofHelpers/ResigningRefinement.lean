import Anvilpp.ProofHelpers.ResigningSteps

namespace Pact

noncomputable section

open Classical

/-! ## Refinement under a common restriction -/

/-- Re-signing keeps the `skip` test, in the existential form the refinement
witness uses. -/
lemma reannotate_skip_exists (processType : PactType) (restrict : PactTypeAlphabet) :
    (∃ alphabet, processType.reannotate restrict = .skip alphabet) ↔
      (∃ alphabet, processType = .skip alphabet) := by
  constructor
  · rintro ⟨alphabet, hEq⟩
    cases processType with
    | skip other => exact ⟨other, rfl⟩
    | message _ _ _ | progress _ _ | tock _ | var _ _ | choice _ _ _
    | seq _ _ _ | par _ _ _ _ | recur _ _ _ | fairChoice _ _ _ _
    | xoffer _ _ _ | offer _ _ _ =>
        rw [PactType.reannotate] at hEq
        exact absurd hEq (by simp)
  · rintro ⟨alphabet, rfl⟩
    exact ⟨restrict, by rw [PactType.reannotate]⟩

/-- Regular, equal-alphabet pairs from a relation, re-signed by a common subalphabet. -/
def restrictedRefinement (relation : PactType → PactType → Prop)
    (alphabet restrict : PactTypeAlphabet) : PactType → PactType → Prop :=
  fun precise abstract =>
    ∃ source target, relation source target ∧
      ResignRegular source ∧ ResignRegular target ∧
      source.alphabet = alphabet ∧ target.alphabet = alphabet ∧
      precise = source.reannotate restrict ∧
      abstract = target.reannotate restrict

theorem refines_reannotate {precise abstract : PactType}
    {restrict : PactTypeAlphabet} (hRefines : Refines precise abstract)
    (hPrecise : ResignRegular precise) (hAbstract : ResignRegular abstract)
    (hAlphabet : abstract.alphabet = precise.alphabet)
    (hSub : restrict.actions ⊆ precise.alphabet.actions) :
    Refines (precise.reannotate restrict) (abstract.reannotate restrict) := by
  obtain ⟨witness⟩ := hRefines
  refine ⟨{
    relation := restrictedRefinement witness.relation precise.alphabet restrict
    initial := ⟨precise, abstract, witness.initial, hPrecise, hAbstract, rfl,
      hAlphabet, rfl, rfl⟩
    skipIff := ?_
    availability := ?_
    response := ?_ }⟩
  · rintro _ _ ⟨source, target, hRelated, -, -, -, -, rfl, rfl⟩
    rw [reannotate_skip_exists, reannotate_skip_exists]
    exact witness.skipIff hRelated
  · rintro _ _ resigned env label offers
      ⟨source, target, hRelated, hSource, hTarget, hSourceAlpha, hTargetAlpha,
        rfl, rfl⟩ ⟨-, hOffers⟩
    have hSubTarget : restrict.actions ⊆ target.alphabet.actions := by
      rw [hTargetAlpha]; exact hSub
    have hSubSource : restrict.actions ⊆ source.alphabet.actions := by
      rw [hSourceAlpha]; exact hSub
    have hEnv : env.WellFormed restrict := by
      have := PactType.typeOffers_env_wellFormed hOffers
        (hTarget.reannotate hSubTarget).alphabetWellFormed
      rwa [PactType.reannotate_alphabet] at this
    obtain ⟨abstractTarget, abstractCurrent, abstractFuture, hAbstractStep,
      hTargetEq, hCurrentEq, hFutureEq⟩ :=
      typeOffers_reannotate_backward target restrict env label resigned
        offers.current offers.future hOffers hTarget hSubTarget hEnv
    obtain ⟨preciseTarget, hPreciseStep⟩ := witness.availability hRelated
      (offers := ⟨abstractCurrent, abstractFuture⟩)
      ⟨hAbstractStep.toTypeTransition, hAbstractStep⟩
    refine ⟨preciseTarget.reannotate restrict, ?_, ?_⟩
    · exact (typeOffers_reannotate_forward hPreciseStep.2 restrict hSource
        hSubSource hEnv).toTypeTransition
    · rw [hCurrentEq, hFutureEq]
      exact typeOffers_reannotate_forward hPreciseStep.2 restrict hSource
        hSubSource hEnv
  · rintro _ _ resigned env label offers
      ⟨source, target, hRelated, hSource, hTarget, hSourceAlpha, hTargetAlpha,
        rfl, rfl⟩ ⟨-, hOffers⟩
    have hSubTarget : restrict.actions ⊆ target.alphabet.actions := by
      rw [hTargetAlpha]; exact hSub
    have hSubSource : restrict.actions ⊆ source.alphabet.actions := by
      rw [hSourceAlpha]; exact hSub
    have hEnv : env.WellFormed restrict := by
      have := PactType.typeOffers_env_wellFormed hOffers
        (hSource.reannotate hSubSource).alphabetWellFormed
      rwa [PactType.reannotate_alphabet] at this
    obtain ⟨preciseTarget, preciseCurrent, preciseFuture, hPreciseStep,
      hTargetEq, hCurrentEq, hFutureEq⟩ :=
      typeOffers_reannotate_backward source restrict env label resigned
        offers.current offers.future hOffers hSource hSubSource hEnv
    obtain ⟨abstractTarget, hAbstractStep, hRelated'⟩ := witness.response hRelated
      (offers := ⟨preciseCurrent, preciseFuture⟩)
      ⟨hPreciseStep.toTypeTransition, hPreciseStep⟩
    refine ⟨abstractTarget.reannotate restrict, ⟨?_, ?_⟩, ?_⟩
    · exact (typeOffers_reannotate_forward hAbstractStep.2 restrict hTarget
        hSubTarget hEnv).toTypeTransition
    · rw [hCurrentEq, hFutureEq]
      exact typeOffers_reannotate_forward hAbstractStep.2 restrict hTarget
        hSubTarget hEnv
    · refine ⟨preciseTarget, abstractTarget, hRelated',
        hPreciseStep.preserves_resignRegular hSource,
        hAbstractStep.2.preserves_resignRegular hTarget, ?_, ?_, hTargetEq, rfl⟩
      · rw [hPreciseStep.preserves_alphabet hSource.alphabetWellFormed,
          hSourceAlpha]
      · rw [hAbstractStep.2.preserves_alphabet hTarget.alphabetWellFormed,
          hTargetAlpha]

/-! ## Refinement closure under transitions -/

lemma Refines.refl (processType : PactType) : Refines processType processType := by
  refine ⟨{ relation := fun left right => left = right
            initial := rfl
            skipIff := ?_
            availability := ?_
            response := ?_ }⟩
  · intro left right hEq; rw [hEq]
  · intro left right target env label offers hEq hStep
    subst hEq
    exact ⟨target, hStep⟩
  · intro left right target env label offers hEq hStep
    subst hEq
    exact ⟨target, hStep, rfl⟩

lemma Refines.skip_iff {precise abstract : PactType} (h : Refines precise abstract) :
    (∃ alphabet, precise = .skip alphabet) ↔
      (∃ alphabet, abstract = .skip alphabet) := by
  obtain ⟨witness⟩ := h
  exact witness.skipIff witness.initial

lemma Refines.step {precise abstract target : PactType} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary} (h : Refines precise abstract)
    (hStep : DecoratedTypeTransition env precise label offers target) :
    ∃ abstractTarget,
      DecoratedTypeTransition env abstract label offers abstractTarget ∧
        Refines target abstractTarget := by
  obtain ⟨witness⟩ := h
  obtain ⟨abstractTarget, hAbstractStep, hRelated⟩ :=
    witness.response witness.initial hStep
  exact ⟨abstractTarget, hAbstractStep,
    ⟨{ relation := witness.relation
       initial := hRelated
       skipIff := witness.skipIff
       availability := witness.availability
       response := witness.response }⟩⟩

lemma Refines.available {precise abstract abstractTarget : PactType}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (h : Refines precise abstract)
    (hStep : DecoratedTypeTransition env abstract label offers abstractTarget) :
    ∃ target, DecoratedTypeTransition env precise label offers target := by
  obtain ⟨witness⟩ := h
  exact witness.availability witness.initial hStep

/-- The two shapes of the `skip` test agree. -/
lemma ne_skip_iff (processType : PactType) :
    processType ≠ .skip processType.alphabet ↔
      ¬ ∃ alphabet, processType = .skip alphabet := by
  constructor
  · rintro hNe ⟨alphabet, hEq⟩
    exact hNe (by rw [hEq, PactType.alphabet])
  · exact fun hNone hEq => hNone ⟨processType.alphabet, hEq⟩

/-! ## Parallel step assembly -/

@[simp] lemma hideTypeOffers_empty (interface : Interface) :
    hideTypeOffers interface ∅ = ∅ := by
  simp [hideTypeOffers]

/-- A `skip` source has exactly one step: the silent one back to itself. -/
lemma skip_step_shape {env : TypeEnvironment} {source target : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hSkip : source = .skip source.alphabet)
    (hOffers : TypeOffers env source label target current future) :
    label = TypeLabel.silent ∧ target = source ∧ current = ∅ ∧ future = ∅ := by
  have hShape := hOffers
  rw [hSkip] at hShape
  cases hShape with
  | skip _ _ hPrem =>
      exact ⟨rfl, hSkip.symm, rfl, typeFutureOffers_skip _⟩

/-- Two matched component steps always assemble into a product step, with the
published pair the parallel rules share. -/
lemma parallel_step_of_components
    {outer leftEnv rightEnv : TypeEnvironment} {interface : Interface}
    {alphabet : PactTypeAlphabet} {left left' right right' : PactType}
    {leftLabel rightLabel : TypeLabel}
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    (hLeftWF : left.AlphabetWellFormed) (hRightWF : right.AlphabetWellFormed)
    (hLeft : TypeOffers leftEnv left leftLabel left' leftCurrent leftFuture)
    (hRight : TypeOffers rightEnv right rightLabel right' rightCurrent rightFuture)
    (hLocalLeft : LocalTypeOfferEnvironment outer interface left rightEnv
      rightCurrent rightFuture leftEnv)
    (hLocalRight : LocalTypeOfferEnvironment outer interface right leftEnv
      leftCurrent leftFuture rightEnv)
    (hEnv : outer.WellFormed alphabet)
    (hSync : TypeLabel.Sync interface leftLabel rightLabel) :
    ∃ target,
      TypeOffers outer (.par alphabet left right interface)
        (TypeLabel.combine interface leftLabel rightLabel) target
        (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
        (if TypeLabel.combine interface leftLabel rightLabel = TypeLabel.tock
          then ∅ else hideTypeOffers interface (leftFuture ∪ rightFuture)) := by
  have hFuse : TypeOffers leftEnv left leftLabel (.skip left.alphabet) leftCurrent
        leftFuture →
      TypeOffers rightEnv right rightLabel (.skip right.alphabet) rightCurrent
        rightFuture →
      ∃ target,
        TypeOffers outer (.par alphabet left right interface)
          (TypeLabel.combine interface leftLabel rightLabel) target
          (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
          (if TypeLabel.combine interface leftLabel rightLabel = TypeLabel.tock
            then ∅ else hideTypeOffers interface (leftFuture ∪ rightFuture)) := by
    intro hLeftTarget hRightTarget
    by_cases hTock : TypeLabel.combine interface leftLabel rightLabel =
        TypeLabel.tock
    · obtain ⟨hLeftTock, hRightTock⟩ :=
        (TypeLabel.combine_eq_tock_iff interface leftLabel rightLabel).mp hTock
      rw [if_pos hTock,
        hLeftTarget.current_eq_empty_of_label_tock hLeftTock,
        hRightTarget.current_eq_empty_of_label_tock hRightTock,
        Finset.union_self, hideTypeOffers_empty]
      exact ⟨.skip alphabet, TypeOffers.par_fuse_tock outer leftEnv rightEnv
        interface alphabet left right leftLabel rightLabel leftCurrent leftFuture
        rightCurrent rightFuture hLeftTarget hRightTarget hLocalLeft hLocalRight
        ⟨hEnv, hSync⟩ hTock⟩
    · rw [if_neg hTock]
      exact ⟨.skip alphabet, TypeOffers.par_fuse outer leftEnv rightEnv interface
        alphabet left right leftLabel rightLabel leftCurrent leftFuture
        rightCurrent rightFuture hLeftTarget hRightTarget hLocalLeft hLocalRight
        ⟨hEnv, hSync⟩ hTock⟩
  by_cases hLeftSkip : left = .skip left.alphabet
  · obtain ⟨hLabel, hTarget, hCurrent, hFuture⟩ := skip_step_shape hLeftSkip hLeft
    subst hLabel; subst hCurrent; subst hFuture
    rw [hTarget] at hLeft
    by_cases hRightTargetSkip : right' = .skip right'.alphabet
    · refine hFuse ?_ ?_
      · rw [← hLeftSkip]; exact hLeft
      · rw [← hRight.preserves_alphabet hRightWF, ← hRightTargetSkip]
        exact hRight
    · have hRightSkip : right ≠ .skip right.alphabet := by
        intro hEq
        obtain ⟨-, hRTarget, -, -⟩ := skip_step_shape hEq hRight
        exact hRightTargetSkip (by rw [hRTarget, ← hEq])
      rw [Finset.empty_union, Finset.empty_union,
        TypeLabel.combine_silent_left interface rightLabel hSync]
      by_cases hTock : rightLabel = TypeLabel.tock
      · rw [if_pos hTock]
        refine ⟨right'.reannotate alphabet, ?_⟩
        have hRule := TypeOffers.left_complete outer leftEnv rightEnv interface
          alphabet left right right' rightLabel ∅ ∅ rightCurrent rightFuture
          hLeftSkip hRightSkip hLeft hRight hRightTargetSkip hLocalLeft
          hLocalRight hEnv hSync
        rwa [hRight.future_eq_empty_of_label_tock hTock, hideTypeOffers_empty]
          at hRule
      · rw [if_neg hTock]
        exact ⟨right'.reannotate alphabet, TypeOffers.left_complete outer leftEnv
          rightEnv interface alphabet left right right' rightLabel ∅ ∅
          rightCurrent rightFuture hLeftSkip hRightSkip hLeft hRight
          hRightTargetSkip hLocalLeft hLocalRight hEnv hSync⟩
  · by_cases hRightSkip : right = .skip right.alphabet
    · obtain ⟨hLabel, hTarget, hCurrent, hFuture⟩ :=
        skip_step_shape hRightSkip hRight
      subst hLabel; subst hCurrent; subst hFuture
      rw [hTarget] at hRight
      by_cases hLeftTargetSkip : left' = .skip left'.alphabet
      · refine hFuse ?_ ?_
        · rw [← hLeft.preserves_alphabet hLeftWF, ← hLeftTargetSkip]; exact hLeft
        · rw [← hRightSkip]; exact hRight
      · rw [Finset.union_empty, Finset.union_empty,
          TypeLabel.combine_silent_right interface leftLabel hSync]
        by_cases hTock : leftLabel = TypeLabel.tock
        · rw [if_pos hTock]
          refine ⟨left'.reannotate alphabet, ?_⟩
          have hRule := TypeOffers.right_complete outer leftEnv rightEnv interface
            alphabet left left' right leftLabel leftCurrent leftFuture ∅ ∅
            hRightSkip hLeftSkip hRight hLeft hLeftTargetSkip hLocalLeft
            hLocalRight hEnv hSync
          rwa [hLeft.future_eq_empty_of_label_tock hTock, hideTypeOffers_empty]
            at hRule
        · rw [if_neg hTock]
          exact ⟨left'.reannotate alphabet, TypeOffers.right_complete outer
            leftEnv rightEnv interface alphabet left left' right leftLabel
            leftCurrent leftFuture ∅ ∅ hRightSkip hLeftSkip hRight hLeft
            hLeftTargetSkip hLocalLeft hLocalRight hEnv hSync⟩
    · by_cases hBoth : left' = .skip left'.alphabet ∧ right' = .skip right'.alphabet
      · refine hFuse ?_ ?_
        · rw [← hLeft.preserves_alphabet hLeftWF, ← hBoth.1]; exact hLeft
        · rw [← hRight.preserves_alphabet hRightWF, ← hBoth.2]; exact hRight
      · exact ⟨.par alphabet left' right' interface, TypeOffers.par outer leftEnv
          rightEnv interface alphabet left left' right right' leftLabel rightLabel
          leftCurrent leftFuture rightCurrent rightFuture hLeftSkip hRightSkip
          hLeft hRight hBoth hLocalLeft hLocalRight ⟨hEnv, hSync⟩⟩

lemma Refines.skip_of_skip {precise abstract : PactType} (h : Refines precise abstract)
    (hPrecise : precise = .skip precise.alphabet) :
    abstract = .skip abstract.alphabet := by
  obtain ⟨alphabet, hEq⟩ := h.skip_iff.mp ⟨precise.alphabet, hPrecise⟩
  rw [hEq, PactType.alphabet]

lemma Refines.skip_of_skip' {precise abstract : PactType} (h : Refines precise abstract)
    (hAbstract : abstract = .skip abstract.alphabet) :
    precise = .skip precise.alphabet := by
  obtain ⟨alphabet, hEq⟩ := h.skip_iff.mpr ⟨abstract.alphabet, hAbstract⟩
  rw [hEq, PactType.alphabet]

/-- Regular equal-alphabet refinements and compatible products with componentwise refinement. -/
def parallelCandidate (interface : Interface) : PactType → PactType → Prop :=
  fun precise abstract =>
    (Refines precise abstract ∧ ResignRegular precise ∧ ResignRegular abstract ∧
      precise.alphabet = abstract.alphabet) ∨
    (∃ alphabet preciseLeft preciseRight abstractLeft abstractRight,
      precise = .par alphabet preciseLeft preciseRight interface ∧
      abstract = .par alphabet abstractLeft abstractRight interface ∧
      Refines preciseLeft abstractLeft ∧ Refines preciseRight abstractRight ∧
      ResignRegular precise ∧ ResignRegular abstract ∧
      preciseLeft.alphabet = abstractLeft.alphabet ∧
      preciseRight.alphabet = abstractRight.alphabet)

set_option maxHeartbeats 1000000 in
lemma parallelCandidate_response {interface : Interface} {alphabet : PactTypeAlphabet}
    {preciseLeft preciseRight abstractLeft abstractRight : PactType}
    (hLeftRef : Refines preciseLeft abstractLeft)
    (hRightRef : Refines preciseRight abstractRight)
    (hPrecise : ResignRegular (.par alphabet preciseLeft preciseRight interface))
    (hAbstract : ResignRegular (.par alphabet abstractLeft abstractRight interface))
    (hAlphaLeft : preciseLeft.alphabet = abstractLeft.alphabet)
    (hAlphaRight : preciseRight.alphabet = abstractRight.alphabet)
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    {target : PactType}
    (hStep : DecoratedTypeTransition env
      (.par alphabet preciseLeft preciseRight interface) label offers target) :
    ∃ abstractTarget,
      DecoratedTypeTransition env
          (.par alphabet abstractLeft abstractRight interface) label offers
          abstractTarget ∧
        parallelCandidate interface target abstractTarget := by
  obtain ⟨current, future⟩ := offers
  obtain ⟨-, hOffers⟩ := hStep
  have hPL := hPrecise.par_left
  have hPR := hPrecise.par_right
  have hAL := hAbstract.par_left
  have hAR := hAbstract.par_right
  have hCompat := by
    have h := hPrecise.alphabetWellFormed
    simp only [PactType.AlphabetWellFormed] at h
    exact h.2.1
  have hOriginal := hOffers
  cases hOffers with
  | par _ leftEnv rightEnv _ _ _ preciseLeft' _ preciseRight' leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeftNotSkip hRightNotSkip
      hLeftStep hRightStep hNotBothSkip hLocalLeft hLocalRight hPrem =>
      obtain ⟨abstractLeft', hAStepL, hRefL⟩ := hLeftRef.step
        (offers := ⟨leftCurrent, leftFuture⟩)
        ⟨hLeftStep.toTypeTransition, hLeftStep⟩
      obtain ⟨abstractRight', hAStepR, hRefR⟩ := hRightRef.step
        (offers := ⟨rightCurrent, rightFuture⟩)
        ⟨hRightStep.toTypeTransition, hRightStep⟩
      have hRule := TypeOffers.par env leftEnv rightEnv interface alphabet
        abstractLeft abstractLeft' abstractRight abstractRight' leftLabel
        rightLabel leftCurrent leftFuture rightCurrent rightFuture
        (fun h => hLeftNotSkip (hLeftRef.skip_of_skip' h))
        (fun h => hRightNotSkip (hRightRef.skip_of_skip' h))
        hAStepL.2 hAStepR.2
        (fun h => hNotBothSkip ⟨hRefL.skip_of_skip' h.1, hRefR.skip_of_skip' h.2⟩)
        hLocalLeft.congr_localType hLocalRight.congr_localType hPrem
      refine ⟨_, ⟨hRule.toTypeTransition, hRule⟩, Or.inr
        ⟨alphabet, preciseLeft', preciseRight', abstractLeft', abstractRight',
          rfl, rfl, hRefL, hRefR, hOriginal.preserves_resignRegular hPrecise,
          hRule.preserves_resignRegular hAbstract, ?_, ?_⟩⟩
      · rw [hLeftStep.preserves_alphabet hPL.alphabetWellFormed,
          hAStepL.2.preserves_alphabet hAL.alphabetWellFormed]
        exact hAlphaLeft
      · rw [hRightStep.preserves_alphabet hPR.alphabetWellFormed,
          hAStepR.2.preserves_alphabet hAR.alphabetWellFormed]
        exact hAlphaRight
  | par_fuse _ leftEnv rightEnv _ _ _ _ leftLabel rightLabel leftCurrent
      leftFuture rightCurrent rightFuture hLeftStep hRightStep hLocalLeft
      hLocalRight hPrem hNotTock =>
      obtain ⟨abstractLeft', hAStepL, hRefL⟩ := hLeftRef.step
        (offers := ⟨leftCurrent, leftFuture⟩)
        ⟨hLeftStep.toTypeTransition, hLeftStep⟩
      obtain ⟨abstractRight', hAStepR, hRefR⟩ := hRightRef.step
        (offers := ⟨rightCurrent, rightFuture⟩)
        ⟨hRightStep.toTypeTransition, hRightStep⟩
      have hSkipL : abstractLeft' = .skip abstractLeft.alphabet := by
        rw [← hAStepL.2.preserves_alphabet hAL.alphabetWellFormed]
        exact hRefL.skip_of_skip (by rw [PactType.alphabet])
      have hSkipR : abstractRight' = .skip abstractRight.alphabet := by
        rw [← hAStepR.2.preserves_alphabet hAR.alphabetWellFormed]
        exact hRefR.skip_of_skip (by rw [PactType.alphabet])
      rw [hSkipL] at hAStepL
      rw [hSkipR] at hAStepR
      have hRule := TypeOffers.par_fuse env leftEnv rightEnv interface alphabet
        abstractLeft abstractRight leftLabel rightLabel leftCurrent leftFuture
        rightCurrent rightFuture hAStepL.2 hAStepR.2 hLocalLeft.congr_localType
        hLocalRight.congr_localType hPrem hNotTock
      exact ⟨_, ⟨hRule.toTypeTransition, hRule⟩, Or.inl
        ⟨Refines.refl _, hOriginal.preserves_resignRegular hPrecise,
          hRule.preserves_resignRegular hAbstract, rfl⟩⟩
  | par_fuse_tock _ leftEnv rightEnv _ _ _ _ leftLabel rightLabel leftCurrent
      leftFuture rightCurrent rightFuture hLeftStep hRightStep hLocalLeft
      hLocalRight hPrem hTock =>
      obtain ⟨abstractLeft', hAStepL, hRefL⟩ := hLeftRef.step
        (offers := ⟨leftCurrent, leftFuture⟩)
        ⟨hLeftStep.toTypeTransition, hLeftStep⟩
      obtain ⟨abstractRight', hAStepR, hRefR⟩ := hRightRef.step
        (offers := ⟨rightCurrent, rightFuture⟩)
        ⟨hRightStep.toTypeTransition, hRightStep⟩
      have hSkipL : abstractLeft' = .skip abstractLeft.alphabet := by
        rw [← hAStepL.2.preserves_alphabet hAL.alphabetWellFormed]
        exact hRefL.skip_of_skip (by rw [PactType.alphabet])
      have hSkipR : abstractRight' = .skip abstractRight.alphabet := by
        rw [← hAStepR.2.preserves_alphabet hAR.alphabetWellFormed]
        exact hRefR.skip_of_skip (by rw [PactType.alphabet])
      rw [hSkipL] at hAStepL
      rw [hSkipR] at hAStepR
      have hRule := TypeOffers.par_fuse_tock env leftEnv rightEnv interface
        alphabet abstractLeft abstractRight leftLabel rightLabel leftCurrent
        leftFuture rightCurrent rightFuture hAStepL.2 hAStepR.2
        hLocalLeft.congr_localType hLocalRight.congr_localType hPrem hTock
      exact ⟨_, ⟨hRule.toTypeTransition, hRule⟩, Or.inl
        ⟨Refines.refl _, hOriginal.preserves_resignRegular hPrecise,
          hRule.preserves_resignRegular hAbstract, rfl⟩⟩
  | left_complete _ leftEnv rightEnv _ _ _ _ preciseRight' _ leftCurrent
      leftFuture rightCurrent rightFuture hLeftSkip hRightNotSkip hLeftStep
      hRightStep hTargetNotSkip hLocalLeft hLocalRight hEnvAlpha hSync =>
      have hAbstractLeftSkip : abstractLeft = .skip abstractLeft.alphabet :=
        hLeftRef.skip_of_skip hLeftSkip
      obtain ⟨abstractLeft', hAStepL, -⟩ := hLeftRef.step
        (offers := ⟨leftCurrent, leftFuture⟩)
        ⟨hLeftStep.toTypeTransition, hLeftStep⟩
      obtain ⟨-, hAbstractLeftTarget, -, -⟩ :=
        skip_step_shape hAbstractLeftSkip hAStepL.2
      rw [hAbstractLeftTarget] at hAStepL
      obtain ⟨abstractRight', hAStepR, hRefR⟩ := hRightRef.step
        (offers := ⟨rightCurrent, rightFuture⟩)
        ⟨hRightStep.toTypeTransition, hRightStep⟩
      have hRule := TypeOffers.left_complete env leftEnv rightEnv interface
        alphabet abstractLeft abstractRight abstractRight' label leftCurrent
        leftFuture rightCurrent rightFuture hAbstractLeftSkip
        (fun h => hRightNotSkip (hRightRef.skip_of_skip' h)) hAStepL.2 hAStepR.2
        (fun h => hTargetNotSkip (hRefR.skip_of_skip' h))
        hLocalLeft.congr_localType hLocalRight.congr_localType hEnvAlpha hSync
      have hRegP : ResignRegular preciseRight' :=
        hRightStep.preserves_resignRegular hPR
      have hRegA : ResignRegular abstractRight' :=
        hAStepR.2.preserves_resignRegular hAR
      have hAlpha : abstractRight'.alphabet = preciseRight'.alphabet := by
        rw [hRightStep.preserves_alphabet hPR.alphabetWellFormed,
          hAStepR.2.preserves_alphabet hAR.alphabetWellFormed, hAlphaRight]
      have hSubset : alphabet.actions ⊆ preciseRight'.alphabet.actions := by
        rw [hRightStep.preserves_alphabet hPR.alphabetWellFormed]
        exact parent_actions_subset_right hCompat
      refine ⟨_, ⟨hRule.toTypeTransition, hRule⟩, Or.inl
        ⟨refines_reannotate hRefR hRegP hRegA hAlpha hSubset,
          hRegP.reannotate hSubset, hRegA.reannotate (by rw [hAlpha]; exact hSubset),
          ?_⟩⟩
      rw [PactType.reannotate_alphabet, PactType.reannotate_alphabet]
  | right_complete _ leftEnv rightEnv _ _ _ preciseLeft' _ _ leftCurrent
      leftFuture rightCurrent rightFuture hRightSkip hLeftNotSkip hRightStep
      hLeftStep hTargetNotSkip hLocalLeft hLocalRight hEnvAlpha hSync =>
      have hAbstractRightSkip : abstractRight = .skip abstractRight.alphabet :=
        hRightRef.skip_of_skip hRightSkip
      obtain ⟨abstractRight', hAStepR, -⟩ := hRightRef.step
        (offers := ⟨rightCurrent, rightFuture⟩)
        ⟨hRightStep.toTypeTransition, hRightStep⟩
      obtain ⟨-, hAbstractRightTarget, -, -⟩ :=
        skip_step_shape hAbstractRightSkip hAStepR.2
      rw [hAbstractRightTarget] at hAStepR
      obtain ⟨abstractLeft', hAStepL, hRefL⟩ := hLeftRef.step
        (offers := ⟨leftCurrent, leftFuture⟩)
        ⟨hLeftStep.toTypeTransition, hLeftStep⟩
      have hRule := TypeOffers.right_complete env leftEnv rightEnv interface
        alphabet abstractLeft abstractLeft' abstractRight label leftCurrent
        leftFuture rightCurrent rightFuture hAbstractRightSkip
        (fun h => hLeftNotSkip (hLeftRef.skip_of_skip' h)) hAStepR.2 hAStepL.2
        (fun h => hTargetNotSkip (hRefL.skip_of_skip' h))
        hLocalLeft.congr_localType hLocalRight.congr_localType hEnvAlpha hSync
      have hRegP : ResignRegular preciseLeft' :=
        hLeftStep.preserves_resignRegular hPL
      have hRegA : ResignRegular abstractLeft' :=
        hAStepL.2.preserves_resignRegular hAL
      have hAlpha : abstractLeft'.alphabet = preciseLeft'.alphabet := by
        rw [hLeftStep.preserves_alphabet hPL.alphabetWellFormed,
          hAStepL.2.preserves_alphabet hAL.alphabetWellFormed, hAlphaLeft]
      have hSubset : alphabet.actions ⊆ preciseLeft'.alphabet.actions := by
        rw [hLeftStep.preserves_alphabet hPL.alphabetWellFormed]
        exact parent_actions_subset_left hCompat
      refine ⟨_, ⟨hRule.toTypeTransition, hRule⟩, Or.inl
        ⟨refines_reannotate hRefL hRegP hRegA hAlpha hSubset,
          hRegP.reannotate hSubset, hRegA.reannotate (by rw [hAlpha]; exact hSubset),
          ?_⟩⟩
      rw [PactType.reannotate_alphabet, PactType.reannotate_alphabet]

set_option maxHeartbeats 1000000 in
lemma parallelCandidate_availability {interface : Interface}
    {alphabet : PactTypeAlphabet}
    {preciseLeft preciseRight abstractLeft abstractRight : PactType}
    (hLeftRef : Refines preciseLeft abstractLeft)
    (hRightRef : Refines preciseRight abstractRight)
    (hPrecise : ResignRegular (.par alphabet preciseLeft preciseRight interface))
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    {abstractTarget : PactType}
    (hStep : DecoratedTypeTransition env
      (.par alphabet abstractLeft abstractRight interface) label offers
      abstractTarget) :
    ∃ target,
      DecoratedTypeTransition env
        (.par alphabet preciseLeft preciseRight interface) label offers target := by
  obtain ⟨current, future⟩ := offers
  obtain ⟨-, hOffers⟩ := hStep
  have hPL := hPrecise.par_left
  have hPR := hPrecise.par_right
  cases hOffers with
  | par _ leftEnv rightEnv _ _ _ abstractLeft' _ abstractRight' leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftNotSkip
      hRightNotSkip hLeftStep hRightStep hNotBothSkip hLocalLeft hLocalRight
      hPrem =>
      obtain ⟨preciseLeft', hPStepL⟩ := hLeftRef.available
        (offers := ⟨leftCurrent, leftFuture⟩)
        ⟨hLeftStep.toTypeTransition, hLeftStep⟩
      obtain ⟨preciseRight', hPStepR⟩ := hRightRef.available
        (offers := ⟨rightCurrent, rightFuture⟩)
        ⟨hRightStep.toTypeTransition, hRightStep⟩
      obtain ⟨target, hRule⟩ := parallel_step_of_components
        hPL.alphabetWellFormed hPR.alphabetWellFormed hPStepL.2 hPStepR.2
        hLocalLeft.congr_localType hLocalRight.congr_localType hPrem.1 hPrem.2
      exact ⟨target, hRule.toTypeTransition, hRule⟩
  | par_fuse _ leftEnv rightEnv _ _ _ _ leftLabel rightLabel leftCurrent
      leftFuture rightCurrent rightFuture hLeftStep hRightStep hLocalLeft
      hLocalRight hPrem hNotTock =>
      obtain ⟨preciseLeft', hPStepL⟩ := hLeftRef.available
        (offers := ⟨leftCurrent, leftFuture⟩)
        ⟨hLeftStep.toTypeTransition, hLeftStep⟩
      obtain ⟨preciseRight', hPStepR⟩ := hRightRef.available
        (offers := ⟨rightCurrent, rightFuture⟩)
        ⟨hRightStep.toTypeTransition, hRightStep⟩
      obtain ⟨target, hRule⟩ := parallel_step_of_components
        hPL.alphabetWellFormed hPR.alphabetWellFormed hPStepL.2 hPStepR.2
        hLocalLeft.congr_localType hLocalRight.congr_localType hPrem.1 hPrem.2
      rw [if_neg hNotTock] at hRule
      exact ⟨target, hRule.toTypeTransition, hRule⟩
  | par_fuse_tock _ leftEnv rightEnv _ _ _ _ leftLabel rightLabel leftCurrent
      leftFuture rightCurrent rightFuture hLeftStep hRightStep hLocalLeft
      hLocalRight hPrem hTock =>
      obtain ⟨hLeftTock, hRightTock⟩ :=
        (TypeLabel.combine_eq_tock_iff interface leftLabel rightLabel).mp hTock
      obtain ⟨preciseLeft', hPStepL⟩ := hLeftRef.available
        (offers := ⟨leftCurrent, leftFuture⟩)
        ⟨hLeftStep.toTypeTransition, hLeftStep⟩
      obtain ⟨preciseRight', hPStepR⟩ := hRightRef.available
        (offers := ⟨rightCurrent, rightFuture⟩)
        ⟨hRightStep.toTypeTransition, hRightStep⟩
      obtain ⟨target, hRule⟩ := parallel_step_of_components
        hPL.alphabetWellFormed hPR.alphabetWellFormed hPStepL.2 hPStepR.2
        hLocalLeft.congr_localType hLocalRight.congr_localType hPrem.1 hPrem.2
      rw [if_pos hTock, hLeftStep.current_eq_empty_of_label_tock hLeftTock,
        hRightStep.current_eq_empty_of_label_tock hRightTock, Finset.union_self,
        hideTypeOffers_empty] at hRule
      exact ⟨target, hRule.toTypeTransition, hRule⟩
  | left_complete _ leftEnv rightEnv _ _ _ _ abstractRight' _ leftCurrent
      leftFuture rightCurrent rightFuture hLeftSkip hRightNotSkip hLeftStep
      hRightStep hTargetNotSkip hLocalLeft hLocalRight hEnvAlpha hSync =>
      obtain ⟨-, -, hLeftCurrent, hLeftFuture⟩ :=
        skip_step_shape hLeftSkip hLeftStep
      obtain ⟨preciseLeft', hPStepL⟩ := hLeftRef.available
        (offers := ⟨leftCurrent, leftFuture⟩)
        ⟨hLeftStep.toTypeTransition, hLeftStep⟩
      obtain ⟨preciseRight', hPStepR⟩ := hRightRef.available
        (offers := ⟨rightCurrent, rightFuture⟩)
        ⟨hRightStep.toTypeTransition, hRightStep⟩
      obtain ⟨target, hRule⟩ := parallel_step_of_components
        hPL.alphabetWellFormed hPR.alphabetWellFormed hPStepL.2 hPStepR.2
        hLocalLeft.congr_localType hLocalRight.congr_localType hEnvAlpha hSync
      rw [TypeLabel.combine_silent_left interface label hSync, hLeftCurrent,
        hLeftFuture, Finset.empty_union, Finset.empty_union] at hRule
      by_cases hTock : label = TypeLabel.tock
      · rw [if_pos hTock, ← hideTypeOffers_empty interface,
          ← hRightStep.future_eq_empty_of_label_tock hTock] at hRule
        exact ⟨target, hRule.toTypeTransition, hRule⟩
      · rw [if_neg hTock] at hRule
        exact ⟨target, hRule.toTypeTransition, hRule⟩
  | right_complete _ leftEnv rightEnv _ _ _ abstractLeft' _ _ leftCurrent
      leftFuture rightCurrent rightFuture hRightSkip hLeftNotSkip hRightStep
      hLeftStep hTargetNotSkip hLocalLeft hLocalRight hEnvAlpha hSync =>
      obtain ⟨-, -, hRightCurrent, hRightFuture⟩ :=
        skip_step_shape hRightSkip hRightStep
      obtain ⟨preciseLeft', hPStepL⟩ := hLeftRef.available
        (offers := ⟨leftCurrent, leftFuture⟩)
        ⟨hLeftStep.toTypeTransition, hLeftStep⟩
      obtain ⟨preciseRight', hPStepR⟩ := hRightRef.available
        (offers := ⟨rightCurrent, rightFuture⟩)
        ⟨hRightStep.toTypeTransition, hRightStep⟩
      obtain ⟨target, hRule⟩ := parallel_step_of_components
        hPL.alphabetWellFormed hPR.alphabetWellFormed hPStepL.2 hPStepR.2
        hLocalLeft.congr_localType hLocalRight.congr_localType hEnvAlpha hSync
      rw [TypeLabel.combine_silent_right interface label hSync, hRightCurrent,
        hRightFuture, Finset.union_empty, Finset.union_empty] at hRule
      by_cases hTock : label = TypeLabel.tock
      · rw [if_pos hTock, ← hideTypeOffers_empty interface,
          ← hLeftStep.future_eq_empty_of_label_tock hTock] at hRule
        exact ⟨target, hRule.toTypeTransition, hRule⟩
      · rw [if_neg hTock] at hRule
        exact ⟨target, hRule.toTypeTransition, hRule⟩

/-! ### Parallel refinement -/

theorem refines_parallel {preciseLeft preciseRight abstractLeft abstractRight : PactType}
    {interface : Interface}
    (hLeftRef : Refines preciseLeft abstractLeft)
    (hRightRef : Refines preciseRight abstractRight)
    (hAlphaLeft : preciseLeft.alphabet = abstractLeft.alphabet)
    (hAlphaRight : preciseRight.alphabet = abstractRight.alphabet)
    (hPrecise : ResignRegular (parallelType preciseLeft preciseRight interface))
    (hAbstract : ResignRegular (parallelType abstractLeft abstractRight interface)) :
    Refines (parallelType preciseLeft preciseRight interface)
      (parallelType abstractLeft abstractRight interface) := by
  have hAlphaEq : PactTypeAlphabet.mergeHidden abstractLeft.alphabet
        abstractRight.alphabet interface =
      PactTypeAlphabet.mergeHidden preciseLeft.alphabet preciseRight.alphabet
        interface := by
    rw [hAlphaLeft, hAlphaRight]
  simp only [parallelType] at hPrecise hAbstract ⊢
  rw [hAlphaEq] at hAbstract ⊢
  refine ⟨{
    relation := parallelCandidate interface
    initial := Or.inr ⟨_, _, _, _, _, rfl, rfl, hLeftRef, hRightRef, hPrecise,
      hAbstract, hAlphaLeft, hAlphaRight⟩
    skipIff := ?_
    availability := ?_
    response := ?_ }⟩
  · rintro _ _ (⟨hRef, -, -, -⟩ | ⟨a, pl, pr, al, ar, rfl, rfl, -⟩)
    · exact hRef.skip_iff
    · simp
  · rintro _ _ _ env label offers
      (⟨hRef, -, -, -⟩ |
        ⟨a, pl, pr, al, ar, rfl, rfl, hLeft, hRight, hReg, -, -, -⟩) hStep
    · exact hRef.available hStep
    · exact parallelCandidate_availability hLeft hRight hReg hStep
  · rintro _ _ _ env label offers
      (⟨hRef, hRegPrecise, hRegAbstract, hAlpha⟩ |
        ⟨a, pl, pr, al, ar, rfl, rfl, hLeft, hRight, hRegP, hRegA, hAL, hAR⟩) hStep
    · obtain ⟨abstractTarget, hAbstractStep, hRef'⟩ := hRef.step hStep
      refine ⟨abstractTarget, hAbstractStep, Or.inl ⟨hRef',
        hStep.2.preserves_resignRegular hRegPrecise,
        hAbstractStep.2.preserves_resignRegular hRegAbstract, ?_⟩⟩
      rw [hStep.2.preserves_alphabet hRegPrecise.alphabetWellFormed,
        hAbstractStep.2.preserves_alphabet hRegAbstract.alphabetWellFormed, hAlpha]
    · exact parallelCandidate_response hLeft hRight hRegP hRegA hAL hAR hStep

/-! ### Fixed compositions -/

lemma composeTypes_alphabet_congr : ∀ (precise abstract : List PactType)
    (interfaces : List Interface)
    (preciseComposition abstractComposition : PactType),
    List.Forall₂ (fun left right => left.alphabet = right.alphabet) precise
      abstract →
    composeTypes precise interfaces = some preciseComposition →
    composeTypes abstract interfaces = some abstractComposition →
    preciseComposition.alphabet = abstractComposition.alphabet := by
  intro precise
  induction precise with
  | nil =>
      intro abstract interfaces _ _ hAlpha hPrecise _
      cases hAlpha
      simp [composeTypes] at hPrecise
  | cons head rest ih =>
      intro abstract interfaces preciseComposition abstractComposition hAlpha
        hPrecise hAbstract
      cases hAlpha with
      | cons hHead hRest =>
          rename_i abstractHead abstractRest
          cases rest with
          | nil =>
              cases hRest
              cases interfaces with
              | nil =>
                  rw [composeTypes] at hPrecise hAbstract
                  cases hPrecise; cases hAbstract
                  exact hHead
              | cons i is => simp [composeTypes] at hPrecise
          | cons next tail =>
              cases abstractRest with
              | nil => cases hRest
              | cons abstractNext abstractTail =>
                  cases interfaces with
                  | nil => simp [composeTypes] at hPrecise
                  | cons i is =>
                      rw [composeTypes] at hPrecise hAbstract
                      cases hPreciseSuffix :
                          composeTypes (next :: tail) is with
                      | none => rw [hPreciseSuffix] at hPrecise; simp at hPrecise
                      | some preciseSuffix =>
                          cases hAbstractSuffix :
                              composeTypes (abstractNext :: abstractTail) is with
                          | none =>
                              rw [hAbstractSuffix] at hAbstract
                              simp at hAbstract
                          | some abstractSuffix =>
                              rw [hPreciseSuffix] at hPrecise
                              rw [hAbstractSuffix] at hAbstract
                              cases hPrecise; cases hAbstract
                              simp only [parallelType]
                              rw [PactType.alphabet, PactType.alphabet, hHead,
                                ih _ is preciseSuffix abstractSuffix hRest
                                  hPreciseSuffix hAbstractSuffix]

theorem refines_compose : ∀ (precise abstract : List PactType)
    (interfaces : List Interface)
    (preciseComposition abstractComposition : PactType),
    List.Forall₂ Refines precise abstract →
    List.Forall₂ (fun left right => left.alphabet = right.alphabet) precise
      abstract →
    composeTypes precise interfaces = some preciseComposition →
    composeTypes abstract interfaces = some abstractComposition →
    ResignRegular preciseComposition → ResignRegular abstractComposition →
    Refines preciseComposition abstractComposition := by
  intro precise
  induction precise with
  | nil =>
      intro abstract interfaces _ _ hRefines _ hPrecise _ _ _
      cases hRefines
      simp [composeTypes] at hPrecise
  | cons head rest ih =>
      intro abstract interfaces preciseComposition abstractComposition hRefines
        hAlpha hPrecise hAbstract hRegPrecise hRegAbstract
      cases hRefines with
      | cons hHeadRef hRestRef =>
          rename_i abstractHead abstractRest
          cases hAlpha with
          | cons hHeadAlpha hRestAlpha =>
              cases rest with
              | nil =>
                  cases hRestRef
                  cases interfaces with
                  | nil =>
                      rw [composeTypes] at hPrecise hAbstract
                      cases hPrecise; cases hAbstract
                      exact hHeadRef
                  | cons i is => simp [composeTypes] at hPrecise
              | cons next tail =>
                  cases abstractRest with
                  | nil => cases hRestRef
                  | cons abstractNext abstractTail =>
                      cases interfaces with
                      | nil => simp [composeTypes] at hPrecise
                      | cons i is =>
                          rw [composeTypes] at hPrecise hAbstract
                          cases hPreciseSuffix :
                              composeTypes (next :: tail) is with
                          | none =>
                              rw [hPreciseSuffix] at hPrecise; simp at hPrecise
                          | some preciseSuffix =>
                              cases hAbstractSuffix :
                                  composeTypes (abstractNext :: abstractTail)
                                    is with
                              | none =>
                                  rw [hAbstractSuffix] at hAbstract
                                  simp at hAbstract
                              | some abstractSuffix =>
                                  rw [hPreciseSuffix] at hPrecise
                                  rw [hAbstractSuffix] at hAbstract
                                  cases hPrecise; cases hAbstract
                                  exact refines_parallel hHeadRef
                                    (ih _ is preciseSuffix abstractSuffix
                                      hRestRef hRestAlpha hPreciseSuffix
                                      hAbstractSuffix hRegPrecise.par_right
                                      hRegAbstract.par_right)
                                    hHeadAlpha
                                    (composeTypes_alphabet_congr _ _ is
                                      preciseSuffix abstractSuffix hRestAlpha
                                      hPreciseSuffix hAbstractSuffix)
                                    hRegPrecise hRegAbstract

/-- Type well-formedness supplies the structural conditions for re-signing. -/
lemma ResignRegular.of_typeWellFormedIn {bound : List String} {processType : PactType}
    (h : TypeWellFormedIn bound processType) : ResignRegular processType := by
  obtain ⟨hA, -, -, hTC, -, hTR, -, -, -, -, -, -, hIS, hIAS, hCMO, -⟩ := h
  exact ⟨hA, hIS, hIAS, hTR, hTC, hCMO⟩

end

end Pact






