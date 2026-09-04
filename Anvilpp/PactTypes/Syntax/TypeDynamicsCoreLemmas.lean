import Anvilpp.PactTypes.Syntax.TypeDynamicsCoreDefs

namespace Pact

noncomputable section

namespace PactType

  @[simp] theorem reannotate_alphabet
      (alphabet : PactTypeAlphabet) (processType : PactType) :
      (reannotate alphabet processType).alphabet = alphabet := by
    cases processType <;> simp [reannotate, PactType.alphabet]

  @[simp] theorem reannotateBranches_nil
      (alphabet : PactTypeAlphabet) :
      reannotateBranches alphabet [] = [] := by
    rw [reannotateBranches.eq_def]

  @[simp] theorem reannotateBranches_cons
      (alphabet : PactTypeAlphabet) (action : BareMessage)
      (processType : PactType) (rest : List (BareMessage × PactType)) :
      reannotateBranches alphabet ((action, processType) :: rest) =
        (action, reannotate alphabet processType) ::
          reannotateBranches alphabet rest := by
    rw [reannotateBranches.eq_def]

  theorem reannotateOfferBranches_nil
      (alphabet : PactTypeAlphabet) (seen : Finset BareMessage) :
      reannotateOfferBranches alphabet seen [] = [] := by
    rw [reannotateOfferBranches.eq_def]

  theorem reannotateOfferBranches_cons
      (alphabet : PactTypeAlphabet) (seen : Finset BareMessage)
      (action : BareMessage) (processType : PactType)
      (rest : List (BareMessage × PactType)) :
      reannotateOfferBranches alphabet seen ((action, processType) :: rest) =
        (action, reannotate alphabet processType) ::
          reannotateOfferBranches alphabet seen rest := by
    rw [reannotateOfferBranches.eq_def]

end PactType

@[simp] theorem singletonTypeXOffer_alphabet
    (branch : BareMessage × PactType) :
    (singletonTypeXOffer branch).alphabet = branch.2.alphabet := by
  rcases branch with ⟨action, processType⟩
  simp [singletonTypeXOffer, singletonTypeXOfferAt, PactType.alphabet]

@[simp] theorem selectedTypeBranch_alphabet
    (branch : BareMessage × PactType) :
    (selectedTypeBranch branch).alphabet = branch.2.alphabet := by
  rcases branch with ⟨action, processType⟩
  simp [selectedTypeBranch, selectedTypeBranchAt, PactType.alphabet]

@[simp] theorem parallelTypeBranchesSelecting_singleton_self
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType) :
    parallelTypeBranchesSelecting alphabet branch [branch] =
      selectedTypeBranchAt alphabet branch := by
  simp [parallelTypeBranchesSelecting, parallelTypeBranchesSelectingWithin]

theorem parallelTypeBranches_alphabet_eq_of_nonempty
    {alphabet : PactTypeAlphabet} :
    ∀ {branches : List (BareMessage × PactType)},
      branches ≠ [] →
      (parallelTypeBranches alphabet branches).alphabet = alphabet
  | [], hNonempty => False.elim (hNonempty rfl)
  | [branch], _ => by
      simp [parallelTypeBranches, parallelTypeBranchesWithin,
        singletonTypeXOfferAt, PactType.alphabet]
  | _ :: _ :: _, _ => rfl

theorem parallelTypeBranchesSelecting_alphabet_eq_of_mem
    {alphabet : PactTypeAlphabet} {selected : BareMessage × PactType} :
    ∀ {branches : List (BareMessage × PactType)},
      selected ∈ branches →
      (parallelTypeBranchesSelecting alphabet selected branches).alphabet =
        alphabet
  | [], hMem => by
      cases hMem
  | [branch], _ => by
      by_cases hSelected : branch = selected <;>
        simp [parallelTypeBranchesSelecting,
          parallelTypeBranchesSelectingWithin, selectedTypeBranchAt,
          singletonTypeXOfferAt, PactType.alphabet, hSelected]
  | _ :: _ :: _, _ => by
      simp only [parallelTypeBranchesSelecting,
        parallelTypeBranchesSelectingWithin]
      split <;> rfl

/-- Reannotation rewrites only alphabets, so it leaves every tail-occurrence
judgement of the underlying term unchanged. -/
theorem PactType.reannotate_tailOccurrences (name : String) :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet) (tail : Prop),
      processType.TailOccurrences name tail →
        (processType.reannotate alphabet).TailOccurrences name tail := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet tail hTail
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (branchTail : Prop),
          sizeOf branches < n →
          PactType.TailBranchOccurrences name branchTail branches →
          PactType.TailBranchOccurrences name branchTail
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet branchTail hBranchesSize hBranchesTail
        induction branches with
        | nil =>
            rw [PactType.reannotateBranches_nil]
            simp [PactType.TailBranchOccurrences]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hFields : branchType.TailOccurrences name branchTail ∧
                PactType.TailBranchOccurrences name branchTail rest := by
              simpa only [PactType.TailBranchOccurrences] using hBranchesTail
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simpa only [PactType.reannotateBranches,
              PactType.TailBranchOccurrences] using
              And.intro (ih (sizeOf branchType) hBranchSize branchType rfl
                  branchAlphabet branchTail hFields.1)
                (restIH hRestSize hFields.2)
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage)
          (branchTail : Prop),
          sizeOf branches < n →
          PactType.TailBranchOccurrences name branchTail branches →
          PactType.TailBranchOccurrences name branchTail
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen branchTail _ _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.TailBranchOccurrences]
        | cons branch rest restIH =>
            intro seen branchTail hBranchesSize hBranchesTail
            rcases branch with ⟨action, branchType⟩
            have hFields : branchType.TailOccurrences name branchTail ∧
                PactType.TailBranchOccurrences name branchTail rest := by
              simpa only [PactType.TailBranchOccurrences] using hBranchesTail
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            rw [PactType.reannotateOfferBranches_cons]
            simp only [PactType.TailBranchOccurrences]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl _
                branchTail hFields.1,
              restIH _ branchTail hRestSize hFields.2⟩
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ =>
          simp [PactType.reannotate, PactType.TailOccurrences]
      | var _ other =>
          simpa only [PactType.reannotate, PactType.TailOccurrences] using hTail
      | recur _ binder body =>
          by_cases hBinder : binder = name
          · simp [PactType.reannotate, PactType.TailOccurrences, hBinder]
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]; simp_wf; omega
            simpa only [PactType.reannotate, PactType.TailOccurrences,
              if_neg hBinder] using
              ih (sizeOf body) hBodySize body rfl alphabet tail
                (by simpa only [PactType.TailOccurrences, if_neg hBinder]
                  using hTail)
      | choice _ left right | fairChoice _ _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.TailOccurrences name tail ∧
              right.TailOccurrences name tail := by
            simpa only [PactType.TailOccurrences] using hTail
          simpa only [PactType.reannotate, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl alphabet tail
                hFields.1)
              (ih (sizeOf right) hRightSize right rfl alphabet tail hFields.2)
      | seq _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name tail := by
            simpa only [PactType.TailOccurrences] using hTail
          simpa only [PactType.reannotate, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl alphabet False
                hFields.1)
              (ih (sizeOf right) hRightSize right rfl alphabet tail hFields.2)
      | par _ left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          simpa only [PactType.reannotate, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl _ False hFields.1)
              (ih (sizeOf right) hRightSize right rfl _ False hFields.2)
      | xoffer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFields : elseType.TailOccurrences name tail ∧
              PactType.TailBranchOccurrences name tail branches := by
            simpa only [PactType.TailOccurrences] using hTail
          simpa only [PactType.reannotate, PactType.TailOccurrences] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl alphabet tail
                hFields.1)
              (hBranches branches alphabet tail hBranchesSize hFields.2)
      | offer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFields : elseType.TailOccurrences name tail ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          simpa only [PactType.reannotate, PactType.TailOccurrences] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl alphabet tail
                hFields.1)
              (hOfferBranches branches alphabet ∅ False hBranchesSize
                hFields.2)

/-- Reannotation changes no alphabet a clock guarantee depends on. -/
theorem PactType.reannotate_mustTockBeforeCompletion :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      (processType.reannotate alphabet).MustTockBeforeCompletion ↔
        processType.MustTockBeforeCompletion := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          (PactType.BranchesMustTockBeforeCompletion
              (PactType.reannotateBranches branchAlphabet branches) ↔
            PactType.BranchesMustTockBeforeCompletion branches) := by
        intro branches branchAlphabet hBranchesSize
        induction branches with
        | nil =>
            simp [PactType.BranchesMustTockBeforeCompletion]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateBranches,
              PactType.BranchesMustTockBeforeCompletion]
            exact and_congr
              (ih (sizeOf branchType) hBranchSize branchType rfl branchAlphabet)
              (restIH hRestSize)
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          (PactType.BranchesMustTockBeforeCompletion
              (PactType.reannotateOfferBranches branchAlphabet seen branches) ↔
            PactType.BranchesMustTockBeforeCompletion branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.BranchesMustTockBeforeCompletion]
        | cons branch rest restIH =>
            intro seen hBranchesSize
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            rw [PactType.reannotateOfferBranches_cons]
            simp only [PactType.BranchesMustTockBeforeCompletion]
            exact and_congr
              (ih (sizeOf branchType) hBranchSize branchType rfl _)
              (restIH _ hRestSize)
      cases processType with
      | message _ _ _ | progress _ _ | skip _ | var _ _ =>
          simp [PactType.reannotate, PactType.MustTockBeforeCompletion]
      | tock _ => simp [PactType.reannotate, PactType.MustTockBeforeCompletion]
      | recur _ _ body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simpa only [PactType.reannotate,
            PactType.MustTockBeforeCompletion] using
            ih (sizeOf body) hBodySize body rfl alphabet
      | seq _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.reannotate, PactType.MustTockBeforeCompletion]
          exact or_congr (ih (sizeOf left) hLeftSize left rfl alphabet)
            (ih (sizeOf right) hRightSize right rfl alphabet)
      | choice _ left right | fairChoice _ _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.reannotate, PactType.MustTockBeforeCompletion]
          exact and_congr (ih (sizeOf left) hLeftSize left rfl alphabet)
            (ih (sizeOf right) hRightSize right rfl alphabet)
      | par _ left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.reannotate, PactType.MustTockBeforeCompletion]
          exact and_congr (ih (sizeOf left) hLeftSize left rfl _)
            (ih (sizeOf right) hRightSize right rfl _)
      | xoffer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.reannotate, PactType.MustTockBeforeCompletion]
          exact and_congr (ih (sizeOf elseType) hElseSize elseType rfl alphabet)
            (hBranches branches alphabet hBranchesSize)
      | offer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.reannotate, PactType.MustTockBeforeCompletion]
          exact and_congr (ih (sizeOf elseType) hElseSize elseType rfl alphabet)
            (hOfferBranches branches alphabet ∅ hBranchesSize)

/-- Reannotation preserves clock guardedness of a name's free occurrences. -/
theorem PactType.reannotate_guardedOccurrences (name : String) :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet) (guarded : Prop),
      processType.GuardedOccurrences name guarded →
        (processType.reannotate alphabet).GuardedOccurrences name guarded := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet guarded hGuarded
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (branchGuarded : Prop),
          sizeOf branches < n →
          PactType.GuardedBranchOccurrences name branchGuarded branches →
          PactType.GuardedBranchOccurrences name branchGuarded
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet branchGuarded hBranchesSize hBranchesGuarded
        induction branches with
        | nil =>
            simp [PactType.GuardedBranchOccurrences]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hFields : branchType.GuardedOccurrences name branchGuarded ∧
                PactType.GuardedBranchOccurrences name branchGuarded rest := by
              simpa only [PactType.GuardedBranchOccurrences] using hBranchesGuarded
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simpa only [PactType.reannotateBranches,
              PactType.GuardedBranchOccurrences] using
              And.intro (ih (sizeOf branchType) hBranchSize branchType rfl
                  branchAlphabet branchGuarded hFields.1)
                (restIH hRestSize hFields.2)
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage)
          (branchGuarded : Prop),
          sizeOf branches < n →
          PactType.GuardedBranchOccurrences name branchGuarded branches →
          PactType.GuardedBranchOccurrences name branchGuarded
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen branchGuarded _ _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.GuardedBranchOccurrences]
        | cons branch rest restIH =>
            intro seen branchGuarded hBranchesSize hBranchesGuarded
            rcases branch with ⟨action, branchType⟩
            have hFields : branchType.GuardedOccurrences name branchGuarded ∧
                PactType.GuardedBranchOccurrences name branchGuarded rest := by
              simpa only [PactType.GuardedBranchOccurrences]
                using hBranchesGuarded
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            rw [PactType.reannotateOfferBranches_cons]
            simp only [PactType.GuardedBranchOccurrences]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl _
                branchGuarded hFields.1,
              restIH _ branchGuarded hRestSize hFields.2⟩
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ =>
          simp [PactType.reannotate, PactType.GuardedOccurrences]
      | var _ other =>
          simpa only [PactType.reannotate, PactType.GuardedOccurrences] using hGuarded
      | recur _ binder body =>
          by_cases hBinder : binder = name
          · simp [PactType.reannotate, PactType.GuardedOccurrences, hBinder]
          · have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            simpa only [PactType.reannotate, PactType.GuardedOccurrences,
              if_neg hBinder] using
              ih (sizeOf body) hBodySize body rfl alphabet guarded
                (by simpa only [PactType.GuardedOccurrences, if_neg hBinder]
                  using hGuarded)
      | seq _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.GuardedOccurrences name guarded ∧
              right.GuardedOccurrences name
                (guarded ∨ left.MustTockBeforeCompletion) := by
            simpa only [PactType.GuardedOccurrences] using hGuarded
          simp only [PactType.reannotate, PactType.GuardedOccurrences]
          refine ⟨ih (sizeOf left) hLeftSize left rfl alphabet guarded
            hFields.1, ?_⟩
          refine PactType.guardedOccurrences_mono name ?_ _
            (ih (sizeOf right) hRightSize right rfl alphabet _ hFields.2)
          rintro (hLeft | hTock)
          · exact Or.inl hLeft
          · exact Or.inr
              ((PactType.reannotate_mustTockBeforeCompletion left alphabet).mpr hTock)
      | choice _ left right | fairChoice _ _ left right | par _ left right _ =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.GuardedOccurrences name guarded ∧
              right.GuardedOccurrences name guarded := by
            simpa only [PactType.GuardedOccurrences] using hGuarded
          simpa only [PactType.reannotate, PactType.GuardedOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl _ guarded hFields.1)
              (ih (sizeOf right) hRightSize right rfl _ guarded hFields.2)
      | xoffer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFields : elseType.GuardedOccurrences name guarded ∧
              PactType.GuardedBranchOccurrences name guarded branches := by
            simpa only [PactType.GuardedOccurrences] using hGuarded
          simpa only [PactType.reannotate, PactType.GuardedOccurrences] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl alphabet
                guarded hFields.1)
              (hBranches branches alphabet guarded hBranchesSize hFields.2)
      | offer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFields : elseType.GuardedOccurrences name guarded ∧
              PactType.GuardedBranchOccurrences name guarded branches := by
            simpa only [PactType.GuardedOccurrences] using hGuarded
          simpa only [PactType.reannotate, PactType.GuardedOccurrences] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl alphabet
                guarded hFields.1)
              (hOfferBranches branches alphabet ∅ guarded hBranchesSize
                hFields.2)

/-- Reannotation preserves tail recursion for the same structural reason. -/
theorem PactType.reannotate_tailRecursive :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      processType.TailRecursive →
        (processType.reannotate alphabet).TailRecursive := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet hRec
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.TailRecursiveBranches branches →
          PactType.TailRecursiveBranches
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet hBranchesSize hBranchesRec
        induction branches with
        | nil =>
            simp [PactType.reannotateBranches, PactType.TailRecursiveBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hFields : branchType.TailRecursive ∧
                PactType.TailRecursiveBranches rest := by
              simpa only [PactType.TailRecursiveBranches] using hBranchesRec
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simpa only [PactType.reannotateBranches,
              PactType.TailRecursiveBranches] using
              And.intro (ih (sizeOf branchType) hBranchSize branchType rfl
                  branchAlphabet hFields.1)
                (restIH hRestSize hFields.2)
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.TailRecursiveBranches branches →
          PactType.TailRecursiveBranches
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _ _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.TailRecursiveBranches]
        | cons branch rest restIH =>
            intro seen hBranchesSize hBranchesRec
            rcases branch with ⟨action, branchType⟩
            have hFields : branchType.TailRecursive ∧
                PactType.TailRecursiveBranches rest := by
              simpa only [PactType.TailRecursiveBranches] using hBranchesRec
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            rw [PactType.reannotateOfferBranches_cons]
            simp only [PactType.TailRecursiveBranches]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl _
                hFields.1,
              restIH _ hRestSize hFields.2⟩
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
          simp [PactType.reannotate, PactType.TailRecursive]
      | recur _ binder body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          have hFields : body.TailOccurrences binder True ∧ body.TailRecursive := by
            simpa only [PactType.TailRecursive] using hRec
          simpa only [PactType.reannotate, PactType.TailRecursive] using
            And.intro (PactType.reannotate_tailOccurrences binder body alphabet
                True hFields.1)
              (ih (sizeOf body) hBodySize body rfl alphabet hFields.2)
      | choice _ left right | fairChoice _ _ left right | seq _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hRec
          simpa only [PactType.reannotate, PactType.TailRecursive] using
            And.intro (ih (sizeOf left) hLeftSize left rfl alphabet hFields.1)
              (ih (sizeOf right) hRightSize right rfl alphabet hFields.2)
      | par _ left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hRec
          simpa only [PactType.reannotate, PactType.TailRecursive] using
            And.intro (ih (sizeOf left) hLeftSize left rfl _ hFields.1)
              (ih (sizeOf right) hRightSize right rfl _ hFields.2)
      | xoffer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFields : elseType.TailRecursive ∧
              PactType.TailRecursiveBranches branches := by
            simpa only [PactType.TailRecursive] using hRec
          simpa only [PactType.reannotate, PactType.TailRecursive] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl alphabet
                hFields.1)
              (hBranches branches alphabet hBranchesSize hFields.2)
      | offer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFields : elseType.TailRecursive ∧
              PactType.TailRecursiveBranches branches := by
            simpa only [PactType.TailRecursive] using hRec
          simpa only [PactType.reannotate, PactType.TailRecursive] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl alphabet
                hFields.1)
              (hOfferBranches branches alphabet ∅ hBranchesSize hFields.2)

/-- Reannotation rewrites only alphabets, so it preserves the syntax size. -/
theorem PactType.reannotate_sizeOf :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      sizeOf (processType.reannotate alphabet) = sizeOf processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          sizeOf (PactType.reannotateBranches branchAlphabet branches) =
            sizeOf branches := by
        intro branches branchAlphabet hBranchesSize
        induction branches with
        | nil => rw [PactType.reannotateBranches_nil]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            rw [PactType.reannotateBranches_cons]
            simp_wf
            rw [ih (sizeOf branchType) hBranchSize branchType rfl branchAlphabet,
              restIH hRestSize]
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          sizeOf (PactType.reannotateOfferBranches branchAlphabet seen
              branches) = sizeOf branches := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _
            rw [PactType.reannotateOfferBranches_nil]
        | cons branch rest restIH =>
            intro seen hBranchesSize
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            rw [PactType.reannotateOfferBranches_cons]
            simp_wf
            rw [ih (sizeOf branchType) hBranchSize branchType rfl _,
              restIH _ hRestSize]
      subst hSize
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
          simp [PactType.reannotate]
      | recur a binder body =>
          have hBodySize : sizeOf body < sizeOf (PactType.recur a binder body) := by
            simp_wf; omega
          simp only [PactType.reannotate]
          simp_wf
          rw [ih _ hBodySize body rfl alphabet]
      | choice a l r =>
          have hL : sizeOf l < sizeOf (PactType.choice a l r) := by simp_wf; omega
          have hR : sizeOf r < sizeOf (PactType.choice a l r) := by simp_wf; omega
          simp only [PactType.reannotate]
          simp_wf
          rw [ih _ hL l rfl alphabet, ih _ hR r rfl alphabet]
      | seq a l r =>
          have hL : sizeOf l < sizeOf (PactType.seq a l r) := by simp_wf; omega
          have hR : sizeOf r < sizeOf (PactType.seq a l r) := by simp_wf; omega
          simp only [PactType.reannotate]
          simp_wf
          rw [ih _ hL l rfl alphabet, ih _ hR r rfl alphabet]
      | fairChoice a b l r =>
          have hL : sizeOf l < sizeOf (PactType.fairChoice a b l r) := by
            simp_wf; omega
          have hR : sizeOf r < sizeOf (PactType.fairChoice a b l r) := by
            simp_wf; omega
          simp only [PactType.reannotate]
          simp_wf
          rw [ih _ hL l rfl alphabet, ih _ hR r rfl alphabet]
      | par a l r bdry =>
          have hL : sizeOf l < sizeOf (PactType.par a l r bdry) := by
            simp_wf; omega
          have hR : sizeOf r < sizeOf (PactType.par a l r bdry) := by
            simp_wf; omega
          simp only [PactType.reannotate]
          simp_wf
          rw [ih _ hL l rfl _, ih _ hR r rfl _]
      | xoffer a e bs =>
          have hE : sizeOf e < sizeOf (PactType.xoffer a e bs) := by simp_wf; omega
          have hB : sizeOf bs < sizeOf (PactType.xoffer a e bs) := by simp_wf; omega
          simp only [PactType.reannotate]
          simp_wf
          rw [ih _ hE e rfl alphabet, hBranches bs alphabet hB]
      | offer a e bs =>
          have hE : sizeOf e < sizeOf (PactType.offer a e bs) := by simp_wf; omega
          have hB : sizeOf bs < sizeOf (PactType.offer a e bs) := by simp_wf; omega
          simp only [PactType.reannotate]
          simp_wf
          rw [ih _ hE e rfl alphabet, hOfferBranches bs alphabet ∅ hB]

/-- Reannotation preserves clock guardedness for the same structural reason. -/
theorem PactType.reannotate_clockGuarded :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      processType.ClockGuarded →
        (processType.reannotate alphabet).ClockGuarded := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet hGuarded
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.ClockGuardedBranches branches →
          PactType.ClockGuardedBranches
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet hBranchesSize hBranchesGuarded
        induction branches with
        | nil =>
            simp [PactType.ClockGuardedBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hFields : branchType.ClockGuarded ∧
                PactType.ClockGuardedBranches rest := by
              simpa only [PactType.ClockGuardedBranches] using hBranchesGuarded
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simpa only [PactType.reannotateBranches,
              PactType.ClockGuardedBranches] using
              And.intro (ih (sizeOf branchType) hBranchSize branchType rfl
                  branchAlphabet hFields.1)
                (restIH hRestSize hFields.2)
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.ClockGuardedBranches branches →
          PactType.ClockGuardedBranches
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _ _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.ClockGuardedBranches]
        | cons branch rest restIH =>
            intro seen hBranchesSize hBranchesGuarded
            rcases branch with ⟨action, branchType⟩
            have hFields : branchType.ClockGuarded ∧
                PactType.ClockGuardedBranches rest := by
              simpa only [PactType.ClockGuardedBranches] using hBranchesGuarded
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            rw [PactType.reannotateOfferBranches_cons]
            simp only [PactType.ClockGuardedBranches]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl _
                hFields.1,
              restIH _ hRestSize hFields.2⟩
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
          simp [PactType.reannotate, PactType.ClockGuarded]
      | recur _ binder body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          have hFields : body.GuardedOccurrences binder False ∧
              body.ClockGuarded := by
            simpa only [PactType.ClockGuarded] using hGuarded
          simpa only [PactType.reannotate, PactType.ClockGuarded] using
            And.intro (PactType.reannotate_guardedOccurrences binder body
                alphabet False hFields.1)
              (ih (sizeOf body) hBodySize body rfl alphabet hFields.2)
      | choice _ left right | fairChoice _ _ left right | seq _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.ClockGuarded ∧ right.ClockGuarded := by
            simpa only [PactType.ClockGuarded] using hGuarded
          simpa only [PactType.reannotate, PactType.ClockGuarded] using
            And.intro (ih (sizeOf left) hLeftSize left rfl alphabet hFields.1)
              (ih (sizeOf right) hRightSize right rfl alphabet hFields.2)
      | par _ left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.ClockGuarded ∧ right.ClockGuarded := by
            simpa only [PactType.ClockGuarded] using hGuarded
          simpa only [PactType.reannotate, PactType.ClockGuarded] using
            And.intro (ih (sizeOf left) hLeftSize left rfl _ hFields.1)
              (ih (sizeOf right) hRightSize right rfl _ hFields.2)
      | xoffer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFields : elseType.ClockGuarded ∧
              PactType.ClockGuardedBranches branches := by
            simpa only [PactType.ClockGuarded] using hGuarded
          simpa only [PactType.reannotate, PactType.ClockGuarded] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl alphabet
                hFields.1)
              (hBranches branches alphabet hBranchesSize hFields.2)
      | offer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFields : elseType.ClockGuarded ∧
              PactType.ClockGuardedBranches branches := by
            simpa only [PactType.ClockGuarded] using hGuarded
          simpa only [PactType.reannotate, PactType.ClockGuarded] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl alphabet
                hFields.1)
              (hOfferBranches branches alphabet ∅ hBranchesSize hFields.2)

/-- A generated singleton offer inherits its branch body's tail properties. -/
theorem singletonTypeXOfferAt_tailOccurrences (name : String)
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (tail : Prop) (hBranch : branch.2.TailOccurrences name False) :
    (singletonTypeXOfferAt alphabet branch).TailOccurrences name tail := by
  simp only [singletonTypeXOfferAt, PactType.TailOccurrences,
    PactType.TailBranchOccurrences]
  refine ⟨trivial, ?_, trivial⟩
  exact PactType.reannotate_tailOccurrences name branch.2 alphabet tail
    (PactType.tailOccurrences_mono name False.elim branch.2 hBranch)

theorem singletonTypeXOfferAt_tailRecursive
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hBranch : branch.2.TailRecursive) :
    (singletonTypeXOfferAt alphabet branch).TailRecursive := by
  simp only [singletonTypeXOfferAt, PactType.TailRecursive,
    PactType.TailRecursiveBranches]
  exact ⟨trivial, PactType.reannotate_tailRecursive branch.2 alphabet hBranch,
    trivial⟩

theorem singletonTypeXOfferAt_clockGuarded
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hBranch : branch.2.ClockGuarded) :
    (singletonTypeXOfferAt alphabet branch).ClockGuarded := by
  simp only [singletonTypeXOfferAt, PactType.ClockGuarded,
    PactType.ClockGuardedBranches]
  exact ⟨trivial, PactType.reannotate_clockGuarded branch.2 alphabet hBranch,
    trivial⟩

/-- The selected branch's commit form inherits its body's tail properties. -/
theorem selectedTypeBranchAt_tailOccurrences (name : String)
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (tail : Prop) (hBranch : branch.2.TailOccurrences name False) :
    (selectedTypeBranchAt alphabet branch).TailOccurrences name tail := by
  simp only [selectedTypeBranchAt, PactType.TailOccurrences]
  exact ⟨trivial, PactType.reannotate_tailOccurrences name branch.2 alphabet
    tail (PactType.tailOccurrences_mono name False.elim branch.2 hBranch)⟩

theorem selectedTypeBranchAt_tailRecursive
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hBranch : branch.2.TailRecursive) :
    (selectedTypeBranchAt alphabet branch).TailRecursive := by
  simp only [selectedTypeBranchAt, PactType.TailRecursive]
  exact ⟨trivial, PactType.reannotate_tailRecursive branch.2 alphabet hBranch⟩

theorem selectedTypeBranchAt_clockGuarded
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hBranch : branch.2.ClockGuarded) :
    (selectedTypeBranchAt alphabet branch).ClockGuarded := by
  simp only [selectedTypeBranchAt, PactType.ClockGuarded]
  exact ⟨trivial, PactType.reannotate_clockGuarded branch.2 alphabet hBranch⟩

/-- The generated parallel product of an offer's branches has no free tail
occurrence of any name absent from every branch body. -/
theorem parallelTypeBranchesWithin_tailOccurrences (name : String) :
    ∀ (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet) (tail : Prop),
      (∀ branch ∈ branches, branch.2.TailOccurrences name False) →
        (parallelTypeBranchesWithin alphabet branches).TailOccurrences
          name tail := by
  intro branches
  induction branches with
  | nil => intro _ _ _; simp [parallelTypeBranchesWithin, PactType.TailOccurrences]
  | cons branch rest ih =>
      intro alphabet tail hBranches
      cases rest with
      | nil =>
          exact singletonTypeXOfferAt_tailOccurrences name alphabet branch tail
            (hBranches branch (by simp))
      | cons next tail' =>
          simp only [parallelTypeBranchesWithin, PactType.TailOccurrences]
          exact ⟨singletonTypeXOfferAt_tailOccurrences name _ branch False
              (hBranches branch (by simp)),
            ih _ False (fun item hItem =>
              hBranches item (List.mem_cons_of_mem branch hItem))⟩

theorem parallelTypeBranchesWithin_tailRecursive :
    ∀ (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet),
      (∀ branch ∈ branches, branch.2.TailRecursive) →
        (parallelTypeBranchesWithin alphabet branches).TailRecursive := by
  intro branches
  induction branches with
  | nil => intro _ _; simp [parallelTypeBranchesWithin, PactType.TailRecursive]
  | cons branch rest ih =>
      intro alphabet hBranches
      cases rest with
      | nil =>
          exact singletonTypeXOfferAt_tailRecursive alphabet branch
            (hBranches branch (by simp))
      | cons next tail' =>
          simp only [parallelTypeBranchesWithin, PactType.TailRecursive]
          exact ⟨singletonTypeXOfferAt_tailRecursive _ branch
              (hBranches branch (by simp)),
            ih _ (fun item hItem =>
              hBranches item (List.mem_cons_of_mem branch hItem))⟩

theorem parallelTypeBranchesWithin_clockGuarded :
    ∀ (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet),
      (∀ branch ∈ branches, branch.2.ClockGuarded) →
        (parallelTypeBranchesWithin alphabet branches).ClockGuarded := by
  intro branches
  induction branches with
  | nil => intro _ _; simp [parallelTypeBranchesWithin, PactType.ClockGuarded]
  | cons branch rest ih =>
      intro alphabet hBranches
      cases rest with
      | nil =>
          exact singletonTypeXOfferAt_clockGuarded alphabet branch
            (hBranches branch (by simp))
      | cons next tail' =>
          simp only [parallelTypeBranchesWithin, PactType.ClockGuarded]
          exact ⟨singletonTypeXOfferAt_clockGuarded _ branch
              (hBranches branch (by simp)),
            ih _ (fun item hItem =>
              hBranches item (List.mem_cons_of_mem branch hItem))⟩

theorem parallelTypeBranchesSelectingWithin_tailOccurrences (name : String)
    (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet) (tail : Prop),
      (∀ branch ∈ branches, branch.2.TailOccurrences name False) →
      selected.2.TailOccurrences name False →
        (parallelTypeBranchesSelectingWithin alphabet selected
          branches).TailOccurrences name tail := by
  intro branches
  induction branches with
  | nil =>
      intro _ _ _ _
      simp [parallelTypeBranchesSelectingWithin, PactType.TailOccurrences]
  | cons branch rest ih =>
      intro alphabet tail hBranches hSelected
      cases rest with
      | nil =>
          by_cases hEq : branch = selected
          · simpa only [parallelTypeBranchesSelectingWithin, if_pos hEq] using
              selectedTypeBranchAt_tailOccurrences name alphabet branch tail
                (hBranches branch (by simp))
          · simpa only [parallelTypeBranchesSelectingWithin, if_neg hEq] using
              singletonTypeXOfferAt_tailOccurrences name alphabet branch tail
                (hBranches branch (by simp))
      | cons next tail' =>
          by_cases hEq : branch = selected
          · simp only [parallelTypeBranchesSelectingWithin, if_pos hEq,
              PactType.TailOccurrences]
            exact ⟨selectedTypeBranchAt_tailOccurrences name _ branch False
                (hBranches branch (by simp)),
              parallelTypeBranchesWithin_tailOccurrences name _ _ False
                (fun item hItem =>
                  hBranches item (List.mem_cons_of_mem branch hItem))⟩
          · simp only [parallelTypeBranchesSelectingWithin, if_neg hEq,
              PactType.TailOccurrences]
            exact ⟨singletonTypeXOfferAt_tailOccurrences name _ branch False
                (hBranches branch (by simp)),
              ih _ False (fun item hItem =>
                hBranches item (List.mem_cons_of_mem branch hItem)) hSelected⟩

theorem parallelTypeBranchesSelectingWithin_tailRecursive
    (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet),
      (∀ branch ∈ branches, branch.2.TailRecursive) →
      selected.2.TailRecursive →
        (parallelTypeBranchesSelectingWithin alphabet selected
          branches).TailRecursive := by
  intro branches
  induction branches with
  | nil =>
      intro _ _ _
      simp [parallelTypeBranchesSelectingWithin, PactType.TailRecursive]
  | cons branch rest ih =>
      intro alphabet hBranches hSelected
      cases rest with
      | nil =>
          by_cases hEq : branch = selected
          · simpa only [parallelTypeBranchesSelectingWithin, if_pos hEq] using
              selectedTypeBranchAt_tailRecursive alphabet branch
                (hBranches branch (by simp))
          · simpa only [parallelTypeBranchesSelectingWithin, if_neg hEq] using
              singletonTypeXOfferAt_tailRecursive alphabet branch
                (hBranches branch (by simp))
      | cons next tail' =>
          by_cases hEq : branch = selected
          · simp only [parallelTypeBranchesSelectingWithin, if_pos hEq,
              PactType.TailRecursive]
            exact ⟨selectedTypeBranchAt_tailRecursive _ branch
                (hBranches branch (by simp)),
              parallelTypeBranchesWithin_tailRecursive _ _
                (fun item hItem =>
                  hBranches item (List.mem_cons_of_mem branch hItem))⟩
          · simp only [parallelTypeBranchesSelectingWithin, if_neg hEq,
              PactType.TailRecursive]
            exact ⟨singletonTypeXOfferAt_tailRecursive _ branch
                (hBranches branch (by simp)),
              ih _ (fun item hItem =>
                hBranches item (List.mem_cons_of_mem branch hItem)) hSelected⟩

/-- Committing a conjunctive offer produces a term with no free occurrence of
any name that the offer's branch bodies do not mention. -/
theorem parallelTypeBranchesSelecting_tailOccurrences (name : String)
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType)) (tail : Prop)
    (hBranches : ∀ branch ∈ branches, branch.2.TailOccurrences name False)
    (hSelected : selected.2.TailOccurrences name False) :
    (parallelTypeBranchesSelecting alphabet selected branches).TailOccurrences
      name tail := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.TailOccurrences]
  | cons branch rest =>
      exact parallelTypeBranchesSelectingWithin_tailOccurrences name selected
        (branch :: rest) alphabet tail hBranches hSelected

theorem parallelTypeBranchesSelecting_tailRecursive
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hBranches : ∀ branch ∈ branches, branch.2.TailRecursive)
    (hSelected : selected.2.TailRecursive) :
    (parallelTypeBranchesSelecting alphabet selected branches).TailRecursive := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.TailRecursive]
  | cons branch rest =>
      exact parallelTypeBranchesSelectingWithin_tailRecursive selected
        (branch :: rest) alphabet hBranches hSelected

theorem parallelTypeBranchesSelectingWithin_clockGuarded
    (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet),
      (∀ branch ∈ branches, branch.2.ClockGuarded) →
      selected.2.ClockGuarded →
        (parallelTypeBranchesSelectingWithin alphabet selected
          branches).ClockGuarded := by
  intro branches
  induction branches with
  | nil =>
      intro _ _ _
      simp [parallelTypeBranchesSelectingWithin, PactType.ClockGuarded]
  | cons branch rest ih =>
      intro alphabet hBranches hSelected
      cases rest with
      | nil =>
          by_cases hEq : branch = selected
          · simpa only [parallelTypeBranchesSelectingWithin, if_pos hEq] using
              selectedTypeBranchAt_clockGuarded alphabet branch
                (hBranches branch (by simp))
          · simpa only [parallelTypeBranchesSelectingWithin, if_neg hEq] using
              singletonTypeXOfferAt_clockGuarded alphabet branch
                (hBranches branch (by simp))
      | cons next tail' =>
          by_cases hEq : branch = selected
          · simp only [parallelTypeBranchesSelectingWithin, if_pos hEq,
              PactType.ClockGuarded]
            exact ⟨selectedTypeBranchAt_clockGuarded _ branch
                (hBranches branch (by simp)),
              parallelTypeBranchesWithin_clockGuarded _ _
                (fun item hItem =>
                  hBranches item (List.mem_cons_of_mem branch hItem))⟩
          · simp only [parallelTypeBranchesSelectingWithin, if_neg hEq,
              PactType.ClockGuarded]
            exact ⟨singletonTypeXOfferAt_clockGuarded _ branch
                (hBranches branch (by simp)),
              ih _ (fun item hItem =>
                hBranches item (List.mem_cons_of_mem branch hItem)) hSelected⟩

theorem parallelTypeBranchesSelecting_clockGuarded
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hBranches : ∀ branch ∈ branches, branch.2.ClockGuarded)
    (hSelected : selected.2.ClockGuarded) :
    (parallelTypeBranchesSelecting alphabet selected branches).ClockGuarded := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.ClockGuarded]
  | cons branch rest =>
      exact parallelTypeBranchesSelectingWithin_clockGuarded selected
        (branch :: rest) alphabet hBranches hSelected

/-- Re-signing changes only alphabet annotations, so it preserves binder
hygiene.  Moved here from `Simultaneous.lean` so that the relation-preservation
proof in `AlphabetPreservation.lean` can use it. -/
theorem PactType.reannotate_binderHygienic (bound : List String) :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.BinderHygienic bound processType →
        PactType.BinderHygienic bound (processType.reannotate alphabet) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType bound with
  | _ n ih =>
      intro alphabet hHolds
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.BinderHygienicBranches bound branches →
          PactType.BinderHygienicBranches bound
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet hBranchesSize hHold
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            PactType.BinderHygienicBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BinderHygienicBranches] at hHold
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateBranches,
              PactType.BinderHygienicBranches]
            exact ⟨ih (sizeOf branchType) hBranchSize bound branchType rfl
                branchAlphabet hHold.1,
              restIH hRestSize hHold.2⟩
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.BinderHygienicBranches bound branches →
          PactType.BinderHygienicBranches bound
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _ _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.BinderHygienicBranches]
        | cons branch rest restIH =>
            intro seen hBranchesSize hHold
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BinderHygienicBranches] at hHold
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateOfferBranches_cons,
              PactType.BinderHygienicBranches]
            exact ⟨ih (sizeOf branchType) hBranchSize bound branchType rfl _
                hHold.1,
              restIH _ hRestSize hHold.2⟩
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.BinderHygienic]
      | progress a p => simp [PactType.reannotate, PactType.BinderHygienic]
      | tock a => simp [PactType.reannotate, PactType.BinderHygienic]
      | skip a => simp [PactType.reannotate, PactType.BinderHygienic]
      | var a name => simp [PactType.reannotate, PactType.BinderHygienic]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderHygienic] at hHolds
          simp only [PactType.reannotate, PactType.BinderHygienic]
          exact ⟨hHolds.1,
            ih (sizeOf body) hB (name :: bound) body rfl alphabet hHolds.2⟩
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderHygienic] at hHolds
          simp only [PactType.reannotate, PactType.BinderHygienic]
          exact ⟨ih (sizeOf l) hL bound l rfl alphabet hHolds.1,
            ih (sizeOf r) hR bound r rfl alphabet hHolds.2⟩
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderHygienic] at hHolds
          simp only [PactType.reannotate, PactType.BinderHygienic]
          exact ⟨ih (sizeOf l) hL bound l rfl alphabet hHolds.1,
            ih (sizeOf r) hR bound r rfl alphabet hHolds.2⟩
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderHygienic] at hHolds
          simp only [PactType.reannotate, PactType.BinderHygienic]
          exact ⟨ih (sizeOf l) hL bound l rfl alphabet hHolds.1,
            ih (sizeOf r) hR bound r rfl alphabet hHolds.2⟩
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderHygienic] at hHolds
          simp only [PactType.reannotate, PactType.BinderHygienic]
          exact ⟨ih (sizeOf l) hL bound l rfl _ hHolds.1,
            ih (sizeOf r) hR bound r rfl _ hHolds.2⟩
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderHygienic] at hHolds
          simp only [PactType.reannotate, PactType.BinderHygienic]
          exact ⟨ih (sizeOf e) hE bound e rfl alphabet hHolds.1,
            hBranches bs alphabet hBs hHolds.2⟩
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderHygienic] at hHolds
          simp only [PactType.reannotate, PactType.BinderHygienic]
          exact ⟨ih (sizeOf e) hE bound e rfl alphabet hHolds.1,
            hOfferBranches bs alphabet ∅ hBs hHolds.2⟩

/-- Re-signing changes only alphabet annotations, never binders, so it
preserves binder freshness. -/
theorem PactType.reannotate_binderFreshFor (bound : List String) :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.BinderFreshFor bound processType →
        PactType.BinderFreshFor bound (processType.reannotate alphabet) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet hHolds
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.BinderFreshForBranches bound branches →
          PactType.BinderFreshForBranches bound
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet hBranchesSize hHold
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            PactType.BinderFreshForBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BinderFreshForBranches] at hHold
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateBranches,
              PactType.BinderFreshForBranches]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl
                branchAlphabet hHold.1,
              restIH hRestSize hHold.2⟩
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.BinderFreshForBranches bound branches →
          PactType.BinderFreshForBranches bound
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _ _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.BinderFreshForBranches]
        | cons branch rest restIH =>
            intro seen hBranchesSize hHold
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BinderFreshForBranches] at hHold
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateOfferBranches_cons,
              PactType.BinderFreshForBranches]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl _
                hHold.1,
              restIH _ hRestSize hHold.2⟩
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.BinderFreshFor]
      | progress a p => simp [PactType.reannotate, PactType.BinderFreshFor]
      | tock a => simp [PactType.reannotate, PactType.BinderFreshFor]
      | skip a => simp [PactType.reannotate, PactType.BinderFreshFor]
      | var a name => simp [PactType.reannotate, PactType.BinderFreshFor]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderFreshFor] at hHolds
          simp only [PactType.reannotate, PactType.BinderFreshFor]
          exact ⟨hHolds.1, ih (sizeOf body) hB body rfl alphabet hHolds.2⟩
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderFreshFor] at hHolds
          simp only [PactType.reannotate, PactType.BinderFreshFor]
          exact ⟨ih (sizeOf l) hL l rfl alphabet hHolds.1,
            ih (sizeOf r) hR r rfl alphabet hHolds.2⟩
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderFreshFor] at hHolds
          simp only [PactType.reannotate, PactType.BinderFreshFor]
          exact ⟨ih (sizeOf l) hL l rfl alphabet hHolds.1,
            ih (sizeOf r) hR r rfl alphabet hHolds.2⟩
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderFreshFor] at hHolds
          simp only [PactType.reannotate, PactType.BinderFreshFor]
          exact ⟨ih (sizeOf l) hL l rfl alphabet hHolds.1,
            ih (sizeOf r) hR r rfl alphabet hHolds.2⟩
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderFreshFor] at hHolds
          simp only [PactType.reannotate, PactType.BinderFreshFor]
          exact ⟨ih (sizeOf l) hL l rfl _ hHolds.1,
            ih (sizeOf r) hR r rfl _ hHolds.2⟩
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderFreshFor] at hHolds
          simp only [PactType.reannotate, PactType.BinderFreshFor]
          exact ⟨ih (sizeOf e) hE e rfl alphabet hHolds.1,
            hBranches bs alphabet hBs hHolds.2⟩
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderFreshFor] at hHolds
          simp only [PactType.reannotate, PactType.BinderFreshFor]
          exact ⟨ih (sizeOf e) hE e rfl alphabet hHolds.1,
            hOfferBranches bs alphabet ∅ hBs hHolds.2⟩

/-- Committing a conjunctive offer introduces no binder: the product is built
from the branch bodies by re-signing and by `xoffer`, `seq` and `par` nodes. -/
theorem parallelTypeBranchesSelecting_binderFreshFor (bound : List String)
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hBranches : ∀ branch ∈ branches, PactType.BinderFreshFor bound branch.2) :
    PactType.BinderFreshFor bound
      (parallelTypeBranchesSelecting alphabet selected branches) := by
  have hSingleton : ∀ (a : PactTypeAlphabet) (branch : BareMessage × PactType),
      PactType.BinderFreshFor bound branch.2 →
      PactType.BinderFreshFor bound (singletonTypeXOfferAt a branch) := by
    intro a branch hBranch
    simp only [singletonTypeXOfferAt, PactType.BinderFreshFor,
      PactType.BinderFreshForBranches]
    exact ⟨trivial,
      PactType.reannotate_binderFreshFor bound branch.2 a hBranch, trivial⟩
  have hSelectedAt : ∀ (a : PactTypeAlphabet) (branch : BareMessage × PactType),
      PactType.BinderFreshFor bound branch.2 →
      PactType.BinderFreshFor bound (selectedTypeBranchAt a branch) := by
    intro a branch hBranch
    simp only [selectedTypeBranchAt, PactType.BinderFreshFor]
    exact ⟨trivial, PactType.reannotate_binderFreshFor bound branch.2 a hBranch⟩
  have hWithin : ∀ (rest : List (BareMessage × PactType))
      (a : PactTypeAlphabet),
      (∀ branch ∈ rest, PactType.BinderFreshFor bound branch.2) →
      PactType.BinderFreshFor bound (parallelTypeBranchesWithin a rest) := by
    intro rest
    induction rest with
    | nil =>
        intro _ _
        simp [parallelTypeBranchesWithin, PactType.BinderFreshFor]
    | cons branch tail ih =>
        intro a hTail
        cases tail with
        | nil => exact hSingleton a branch (hTail branch (by simp))
        | cons next tail' =>
            simp only [parallelTypeBranchesWithin, PactType.BinderFreshFor]
            exact ⟨hSingleton _ branch (hTail branch (by simp)),
              ih _ (fun item hItem =>
                hTail item (List.mem_cons_of_mem branch hItem))⟩
  have hSelectingWithin : ∀ (rest : List (BareMessage × PactType))
      (a : PactTypeAlphabet),
      (∀ branch ∈ rest, PactType.BinderFreshFor bound branch.2) →
      PactType.BinderFreshFor bound
        (parallelTypeBranchesSelectingWithin a selected rest) := by
    intro rest
    induction rest with
    | nil =>
        intro _ _
        simp [parallelTypeBranchesSelectingWithin, PactType.BinderFreshFor]
    | cons branch tail ih =>
        intro a hTail
        cases tail with
        | nil =>
            by_cases hEq : branch = selected
            · simpa only [parallelTypeBranchesSelectingWithin, if_pos hEq] using
                hSelectedAt a branch (hTail branch (by simp))
            · simpa only [parallelTypeBranchesSelectingWithin, if_neg hEq] using
                hSingleton a branch (hTail branch (by simp))
        | cons next tail' =>
            by_cases hEq : branch = selected
            · simp only [parallelTypeBranchesSelectingWithin, if_pos hEq,
                PactType.BinderFreshFor]
              exact ⟨hSelectedAt _ branch (hTail branch (by simp)),
                hWithin _ _ (fun item hItem =>
                  hTail item (List.mem_cons_of_mem branch hItem))⟩
            · simp only [parallelTypeBranchesSelectingWithin, if_neg hEq,
                PactType.BinderFreshFor]
              exact ⟨hSingleton _ branch (hTail branch (by simp)),
                ih _ (fun item hItem =>
                  hTail item (List.mem_cons_of_mem branch hItem))⟩
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.BinderFreshFor]
  | cons branch rest =>
      exact hSelectingWithin (branch :: rest) alphabet hBranches

/-- Re-signing a type by the alphabet it already carries changes nothing. -/
theorem PactType.reannotate_own_alphabet :
    ∀ processType : PactType,
      processType.AlphabetWellFormed →
      processType.reannotate processType.alphabet = processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hXBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ alphabet : PactTypeAlphabet,
          PactType.BranchesAlphabetWellFormed alphabet branches →
          PactType.reannotateBranches alphabet branches = branches := by
        intro branches
        induction branches with
        | nil => intro _ _ _; rw [PactType.reannotateBranches_nil]
        | cons head tail restIH =>
            intro hSizeCons alphabet hWF
            rcases head with ⟨action, body⟩
            simp only [PactType.BranchesAlphabetWellFormed] at hWF
            have hBodySize : sizeOf body < n := by
              have h1 : sizeOf body < sizeOf (action, body) := by simp_wf; omega
              have h2 : sizeOf (action, body) <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have : sizeOf tail < sizeOf ((action, body) :: tail) := by
                simp_wf; omega
              omega
            rw [PactType.reannotateBranches_cons, ← hWF.1,
              ih (sizeOf body) hBodySize body rfl hWF.2.1,
              hWF.1, restIH hTailSize alphabet hWF.2.2]
      have hOBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ (alphabet : PactTypeAlphabet)
            (seen : Finset BareMessage),
          PactType.OfferBranchesWellFormed alphabet seen branches →
          PactType.reannotateOfferBranches alphabet seen branches = branches := by
        intro branches
        induction branches with
        | nil => intro _ _ _ _; rw [PactType.reannotateOfferBranches_nil]
        | cons head tail restIH =>
            intro hSizeCons alphabet seen hWF
            rcases head with ⟨action, body⟩
            simp only [PactType.OfferBranchesWellFormed] at hWF
            have hBodySize : sizeOf body < n := by
              have h1 : sizeOf body < sizeOf (action, body) := by simp_wf; omega
              have h2 : sizeOf (action, body) <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have : sizeOf tail < sizeOf ((action, body) :: tail) := by
                simp_wf; omega
              omega
            rw [PactType.reannotateOfferBranches_cons, ← hWF.1,
              ih (sizeOf body) hBodySize body rfl hWF.2.1,
              hWF.1, restIH hTailSize alphabet seen hWF.2.2]
      intro hWF
      subst hSize
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
          simp [PactType.reannotate, PactType.alphabet]
      | recur alphabet name body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          have hB : sizeOf body < sizeOf
              (PactType.recur alphabet name body) := by simp_wf; omega
          simp only [PactType.reannotate, PactType.alphabet]
          rw [← hWF.2.1, ih (sizeOf body) hB body rfl hWF.2.2, hWF.2.1]
      | choice alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          have hL : sizeOf left < sizeOf
              (PactType.choice alphabet left right) := by simp_wf; omega
          have hR : sizeOf right < sizeOf
              (PactType.choice alphabet left right) := by simp_wf; omega
          simp only [PactType.reannotate, PactType.alphabet]
          rw [← hWF.2.1, ih (sizeOf left) hL left rfl hWF.2.2.2.1, hWF.2.1,
            ← hWF.2.2.1, ih (sizeOf right) hR right rfl hWF.2.2.2.2, hWF.2.2.1]
      | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          have hL : sizeOf left < sizeOf
              (PactType.seq alphabet left right) := by simp_wf; omega
          have hR : sizeOf right < sizeOf
              (PactType.seq alphabet left right) := by simp_wf; omega
          simp only [PactType.reannotate, PactType.alphabet]
          rw [← hWF.2.1, ih (sizeOf left) hL left rfl hWF.2.2.2.1, hWF.2.1,
            ← hWF.2.2.1, ih (sizeOf right) hR right rfl hWF.2.2.2.2, hWF.2.2.1]
      | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          have hL : sizeOf left < sizeOf
              (PactType.fairChoice alphabet bid left right) := by simp_wf; omega
          have hR : sizeOf right < sizeOf
              (PactType.fairChoice alphabet bid left right) := by simp_wf; omega
          simp only [PactType.reannotate, PactType.alphabet]
          rw [← hWF.2.1, ih (sizeOf left) hL left rfl hWF.2.2.2.1, hWF.2.1,
            ← hWF.2.2.1, ih (sizeOf right) hR right rfl hWF.2.2.2.2, hWF.2.2.1]
      | par alphabet left right interface =>
          simp only [PactType.AlphabetWellFormed] at hWF
          have hL : sizeOf left < sizeOf
              (PactType.par alphabet left right interface) := by simp_wf; omega
          have hR : sizeOf right < sizeOf
              (PactType.par alphabet left right interface) := by simp_wf; omega
          have hAlphaPar : (PactType.par alphabet left right interface).alphabet
              = alphabet := rfl
          simp only [PactType.reannotate, hAlphaPar]
          have hProjL : alphabet.projectParallel left.alphabet interface =
              left.alphabet := by
            rw [← hWF.2.1.parent_eq_left]
            refine congrArg PactTypeAlphabet.mk (Finset.ext fun action => ?_)
            simp only [PactTypeAlphabet.projectParallel,
              PactTypeAlphabet.hideInterface, Finset.mem_union,
              Finset.mem_filter]
            constructor
            · rintro (⟨hMem, hIface⟩ | ⟨hMem, -⟩)
              · exact hMem
              · exact hMem
            · intro hMem
              by_cases hIface : action.1 ∈ interface
              · exact Or.inl ⟨hMem, hIface⟩
              · exact Or.inr ⟨hMem, hIface⟩
          have hProjR : alphabet.projectParallel right.alphabet interface =
              right.alphabet := by
            rw [← hWF.2.1.parent_eq_right]
            refine congrArg PactTypeAlphabet.mk (Finset.ext fun action => ?_)
            simp only [PactTypeAlphabet.projectParallel,
              PactTypeAlphabet.hideInterface, Finset.mem_union,
              Finset.mem_filter]
            constructor
            · rintro (⟨hMem, hIface⟩ | ⟨hMem, -⟩)
              · exact hMem
              · exact hMem
            · intro hMem
              by_cases hIface : action.1 ∈ interface
              · exact Or.inl ⟨hMem, hIface⟩
              · exact Or.inr ⟨hMem, hIface⟩
          rw [hProjL, hProjR, ih (sizeOf left) hL left rfl hWF.2.2.1,
            ih (sizeOf right) hR right rfl hWF.2.2.2]
      | xoffer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          have hE : sizeOf elseType < sizeOf
              (PactType.xoffer alphabet elseType branches) := by simp_wf; omega
          have hB : sizeOf branches < sizeOf
              (PactType.xoffer alphabet elseType branches) := by simp_wf; omega
          simp only [PactType.reannotate, PactType.alphabet]
          rw [← hWF.2.1, ih (sizeOf elseType) hE elseType rfl hWF.2.2.1,
            hWF.2.1, hXBranches branches hB alphabet hWF.2.2.2]
      | offer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          have hE : sizeOf elseType < sizeOf
              (PactType.offer alphabet elseType branches) := by simp_wf; omega
          have hB : sizeOf branches < sizeOf
              (PactType.offer alphabet elseType branches) := by simp_wf; omega
          simp only [PactType.reannotate, PactType.alphabet]
          rw [← hWF.2.1, ih (sizeOf elseType) hE elseType rfl hWF.2.2.1,
            hWF.2.1, hOBranches branches hB alphabet ∅ hWF.2.2.2]

end

end Pact
