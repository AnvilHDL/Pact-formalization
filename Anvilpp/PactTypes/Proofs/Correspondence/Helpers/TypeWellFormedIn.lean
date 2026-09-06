import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.OwnershipTransport

/-!
`TypeWF_Γ` and its descent to every written child.  Split out of `Simultaneous`
so that the re-signing transport can state its well-formedness premise without
depending on the simultaneous induction.
-/

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

set_option linter.unusedSimpArgs false

/-- `TypeWF_Γ(σ)`: the conjuncts of `AdmissibleType`, with closure and hygiene
taken relative to the binder context `bound` rather than the empty one, and
with the two ownership predicates that offer determinacy consumes. -/

def TypeWellFormedIn (bound : List String) (processType : PactType) : Prop :=
  processType.AlphabetWellFormed ∧
    PactType.AllVariablesBound bound processType ∧
    PactType.BinderHygienic bound processType ∧
    processType.TailClosed ∧
    PactType.ClockGuarded processType ∧
    PactType.TailRecursive processType ∧
    PactType.SameCycleMessageLinear processType ∧
    PactType.ProgressLinear processType ∧
    PactType.FairChoiceLinear processType ∧
    PactType.ParallelMessageOwnership processType ∧
    PactType.ParallelProgressOwnership processType ∧
    PactType.ParallelFairChoiceOwnership processType ∧
    PactType.InterfaceScoped processType ∧
    PactType.InterfaceAlphabetScoped processType ∧
    PactType.ConjunctiveMessageOwnership processType

/-- An admissible type is well formed in the empty binder context. -/

theorem parallelProgressOwnership_of_progressLinear :
    ∀ processType : PactType,
      PactType.ProgressLinear processType →
      PactType.ParallelProgressOwnership processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.ProgressLinearBranches branches →
          PactType.ParallelProgressOwnershipBranches branches := by
        intro branches hBranches hLinear
        induction branches with
        | nil => simp [PactType.ParallelProgressOwnershipBranches]
        | cons head rest restIH =>
            rcases head with ⟨action, branchType⟩
            have hType : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hRest : sizeOf rest < n := by
              have hTail : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            simp only [PactType.ProgressLinearBranches] at hLinear
            simp only [PactType.ParallelProgressOwnershipBranches]
            exact ⟨ih (sizeOf branchType) hType branchType rfl hLinear.1,
              hLinear.2.1, restIH hRest hLinear.2.2⟩
      intro hLinear
      cases processType with
      | skip alphabet => simp [PactType.ParallelProgressOwnership]
      | message alphabet msg dir => simp [PactType.ParallelProgressOwnership]
      | tock alphabet => simp [PactType.ParallelProgressOwnership]
      | progress alphabet pid => simp [PactType.ParallelProgressOwnership]
      | var alphabet name => simp [PactType.ParallelProgressOwnership]
      | recur alphabet name body =>
          have hBody : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hLinear
          simp only [PactType.ParallelProgressOwnership]
          exact ih (sizeOf body) hBody body rfl hLinear
      | choice alphabet left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hLinear
          simp only [PactType.ParallelProgressOwnership]
          exact ⟨ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | fairChoice alphabet bid left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hLinear
          simp only [PactType.ParallelProgressOwnership]
          exact ⟨ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | seq alphabet left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hLinear
          simp only [PactType.ParallelProgressOwnership]
          exact ⟨ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | par alphabet left right interface =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hLinear
          simp only [PactType.ParallelProgressOwnership]
          exact ⟨hLinear.2.2, ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | xoffer alphabet elseType branches =>
          have hElse : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hLinear
          simp only [PactType.ParallelProgressOwnership]
          exact ⟨ih (sizeOf elseType) hElse elseType rfl hLinear.1,
            hBranches branches hBranchSize hLinear.2.1⟩
      | offer alphabet elseType branches =>
          have hElse : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hLinear
          simp only [PactType.ParallelProgressOwnership]
          exact ⟨ih (sizeOf elseType) hElse elseType rfl hLinear.1,
            hBranches branches hBranchSize hLinear.2.1⟩

/-- Fair-choice linearity already assigns each fair-choice identifier to a
single parallel component. -/

theorem parallelFairChoiceOwnership_of_fairChoiceLinear :
    ∀ processType : PactType,
      PactType.FairChoiceLinear processType →
      PactType.ParallelFairChoiceOwnership processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.FairChoiceLinearBranches branches →
          PactType.ParallelFairChoiceOwnershipBranches branches := by
        intro branches hBranches hLinear
        induction branches with
        | nil => simp [PactType.ParallelFairChoiceOwnershipBranches]
        | cons head rest restIH =>
            rcases head with ⟨action, branchType⟩
            have hType : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hRest : sizeOf rest < n := by
              have hTail : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            simp only [PactType.FairChoiceLinearBranches] at hLinear
            simp only [PactType.ParallelFairChoiceOwnershipBranches]
            exact ⟨ih (sizeOf branchType) hType branchType rfl hLinear.1,
              hLinear.2.1, restIH hRest hLinear.2.2⟩
      intro hLinear
      cases processType with
      | skip alphabet => simp [PactType.ParallelFairChoiceOwnership]
      | message alphabet msg dir => simp [PactType.ParallelFairChoiceOwnership]
      | tock alphabet => simp [PactType.ParallelFairChoiceOwnership]
      | progress alphabet pid => simp [PactType.ParallelFairChoiceOwnership]
      | var alphabet name => simp [PactType.ParallelFairChoiceOwnership]
      | recur alphabet name body =>
          have hBody : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hLinear
          simp only [PactType.ParallelFairChoiceOwnership]
          exact ih (sizeOf body) hBody body rfl hLinear
      | choice alphabet left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hLinear
          simp only [PactType.ParallelFairChoiceOwnership]
          exact ⟨ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | fairChoice alphabet bid left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hLinear
          simp only [PactType.ParallelFairChoiceOwnership]
          exact ⟨ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | seq alphabet left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hLinear
          simp only [PactType.ParallelFairChoiceOwnership]
          exact ⟨ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | par alphabet left right interface =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hLinear
          simp only [PactType.ParallelFairChoiceOwnership]
          exact ⟨hLinear.2.2, ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | xoffer alphabet elseType branches =>
          have hElse : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hLinear
          simp only [PactType.ParallelFairChoiceOwnership]
          exact ⟨ih (sizeOf elseType) hElse elseType rfl hLinear.1,
            hBranches branches hBranchSize hLinear.2.1⟩
      | offer alphabet elseType branches =>
          have hElse : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hLinear
          simp only [PactType.ParallelFairChoiceOwnership]
          exact ⟨ih (sizeOf elseType) hElse elseType rfl hLinear.1,
            hBranches branches hBranchSize hLinear.2.1⟩

/-- Every branch continuation of an offer inherits `TypeWF_Γ`.  One list
induction discharges all thirteen conjuncts at once. -/

private lemma branchesWellFormedIn_of_conjuncts {bound : List String}
    (branches : List (BareMessage × PactType))
    (hA : ∀ entry ∈ branches, PactType.AlphabetWellFormed entry.2)
    (hB : PactType.AllBranchVariablesBound bound branches)
    (hH : PactType.BinderHygienicBranches bound branches)
    (hTC : ∀ other : String, PactType.TailBranchOccurrences other True branches)
    (hCG : PactType.ClockGuardedBranches branches)
    (hTR : PactType.TailRecursiveBranches branches)
    (hSC : PactType.SameCycleMessageLinearBranches branches)
    (hPL : PactType.ProgressLinearBranches branches)
    (hFL : PactType.FairChoiceLinearBranches branches)
    (hMO : ∀ entry ∈ branches, PactType.ParallelMessageOwnership entry.2)
    (hPO : PactType.ParallelProgressOwnershipBranches branches)
    (hFO : PactType.ParallelFairChoiceOwnershipBranches branches)
    (hIS : PactType.InterfaceScopedBranches branches)
    (hIAS : PactType.InterfaceAlphabetScopedBranches branches)
    (hCMO : ∀ entry ∈ branches, PactType.ConjunctiveMessageOwnership entry.2) :
    ∀ entry ∈ branches, TypeWellFormedIn bound entry.2 := by
  induction branches with
  | nil => intro entry hEntry; cases hEntry
  | cons head rest ih =>
      rcases head with ⟨action, branchType⟩
      simp only [PactType.AllBranchVariablesBound] at hB
      simp only [PactType.BinderHygienicBranches] at hH
      simp only [PactType.ClockGuardedBranches] at hCG
      simp only [PactType.TailRecursiveBranches] at hTR
      simp only [PactType.SameCycleMessageLinearBranches] at hSC
      simp only [PactType.ProgressLinearBranches] at hPL
      simp only [PactType.FairChoiceLinearBranches] at hFL
      simp only [PactType.ParallelProgressOwnershipBranches] at hPO
      simp only [PactType.ParallelFairChoiceOwnershipBranches] at hFO
      simp only [PactType.InterfaceScopedBranches] at hIS
      simp only [PactType.InterfaceAlphabetScopedBranches] at hIAS
      have hTCsplit : ∀ other : String,
          PactType.TailOccurrences other True branchType ∧
            PactType.TailBranchOccurrences other True rest := by
        intro other
        simpa only [PactType.TailBranchOccurrences] using hTC other
      intro entry hEntry
      simp only [List.mem_cons] at hEntry
      rcases hEntry with rfl | hRest
      · exact ⟨hA _ (by simp), hB.1, hH.1,
          fun other => (hTCsplit other).1, hCG.1, hTR.1, hSC.1, hPL.1, hFL.1,
          hMO _ (by simp), hPO.1, hFO.1, hIS.1, hIAS.1, hCMO _ (by simp)⟩
      · exact ih (fun e hE => hA e (by simp [hE])) hB.2 hH.2
          (fun other => (hTCsplit other).2) hCG.2 hTR.2 hSC.2.2 hPL.2.2 hFL.2.2
          (fun e hE => hMO e (by simp [hE])) hPO.2.2 hFO.2.2 hIS.2 hIAS.2
          (fun e hE => hCMO e (by simp [hE])) entry hRest

theorem PactType.reannotate_allVariablesBound (bound : List String) :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.AllVariablesBound bound processType →
        PactType.AllVariablesBound bound (processType.reannotate alphabet) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType bound with
  | _ n ih =>
      intro alphabet hHolds
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.AllBranchVariablesBound bound branches →
          PactType.AllBranchVariablesBound bound
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet hBranchesSize hHold
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            PactType.AllBranchVariablesBound]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.AllBranchVariablesBound] at hHold
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
              PactType.AllBranchVariablesBound]
            exact ⟨ih (sizeOf branchType) hBranchSize bound branchType rfl
                branchAlphabet hHold.1,
              restIH hRestSize hHold.2⟩
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.AllBranchVariablesBound bound branches →
          PactType.AllBranchVariablesBound bound
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _ _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.AllBranchVariablesBound]
        | cons branch rest restIH =>
            intro seen hBranchesSize hHold
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.AllBranchVariablesBound] at hHold
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
              PactType.AllBranchVariablesBound]
            exact ⟨ih (sizeOf branchType) hBranchSize bound branchType rfl _
                hHold.1,
              restIH _ hRestSize hHold.2⟩
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.AllVariablesBound]
      | progress a p => simp [PactType.reannotate, PactType.AllVariablesBound]
      | tock a => simp [PactType.reannotate, PactType.AllVariablesBound]
      | skip a => simp [PactType.reannotate, PactType.AllVariablesBound]
      | var a name =>
          simpa [PactType.reannotate, PactType.AllVariablesBound] using hHolds
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AllVariablesBound] at hHolds
          simp only [PactType.reannotate, PactType.AllVariablesBound]
          exact ih (sizeOf body) hB (name :: bound) body rfl alphabet hHolds
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AllVariablesBound] at hHolds
          simp only [PactType.reannotate, PactType.AllVariablesBound]
          exact ⟨ih (sizeOf l) hL bound l rfl alphabet hHolds.1,
            ih (sizeOf r) hR bound r rfl alphabet hHolds.2⟩
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AllVariablesBound] at hHolds
          simp only [PactType.reannotate, PactType.AllVariablesBound]
          exact ⟨ih (sizeOf l) hL bound l rfl alphabet hHolds.1,
            ih (sizeOf r) hR bound r rfl alphabet hHolds.2⟩
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AllVariablesBound] at hHolds
          simp only [PactType.reannotate, PactType.AllVariablesBound]
          exact ⟨ih (sizeOf l) hL bound l rfl alphabet hHolds.1,
            ih (sizeOf r) hR bound r rfl alphabet hHolds.2⟩
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AllVariablesBound] at hHolds
          simp only [PactType.reannotate, PactType.AllVariablesBound]
          exact ⟨ih (sizeOf l) hL bound l rfl _ hHolds.1,
            ih (sizeOf r) hR bound r rfl _ hHolds.2⟩
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AllVariablesBound] at hHolds
          simp only [PactType.reannotate, PactType.AllVariablesBound]
          exact ⟨ih (sizeOf e) hE bound e rfl alphabet hHolds.1,
            hBranches bs alphabet hBs hHolds.2⟩
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AllVariablesBound] at hHolds
          simp only [PactType.reannotate, PactType.AllVariablesBound]
          exact ⟨ih (sizeOf e) hE bound e rfl alphabet hHolds.1,
            hOfferBranches bs alphabet ∅ hBs hHolds.2⟩

theorem reannotateBranches_progressIds (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      PactType.BranchProgressIds
          (PactType.reannotateBranches alphabet branches) =
        PactType.BranchProgressIds branches := by
  intro branches
  induction branches with
  | nil => simp [PactType.reannotateBranches, PactType.BranchProgressIds]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      simp [PactType.reannotateBranches, PactType.BranchProgressIds,
        (PactType.reannotate_ownership_data alphabet branchType).2.2.1, ih]

theorem reannotateOfferBranches_progressIds (alphabet : PactTypeAlphabet) :
    ∀ (branches : List (BareMessage × PactType)) (seen : Finset BareMessage),
      PactType.BranchProgressIds
          (PactType.reannotateOfferBranches alphabet seen branches) =
        PactType.BranchProgressIds branches := by
  intro branches
  induction branches with
  | nil => intro seen; simp [PactType.reannotateOfferBranches_nil,
      PactType.BranchProgressIds]
  | cons branch rest ih =>
      intro seen
      rcases branch with ⟨action, branchType⟩
      simp [PactType.reannotateOfferBranches_cons, PactType.BranchProgressIds,
        (PactType.reannotate_ownership_data _ branchType).2.2.1, ih]

theorem reannotateBranches_fairChoiceIds (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      PactType.BranchFairChoiceIds
          (PactType.reannotateBranches alphabet branches) =
        PactType.BranchFairChoiceIds branches := by
  intro branches
  induction branches with
  | nil => simp [PactType.reannotateBranches, PactType.BranchFairChoiceIds]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      simp [PactType.reannotateBranches, PactType.BranchFairChoiceIds,
        (PactType.reannotate_ownership_data alphabet branchType).2.2.2.1, ih]

theorem reannotateOfferBranches_fairChoiceIds (alphabet : PactTypeAlphabet) :
    ∀ (branches : List (BareMessage × PactType)) (seen : Finset BareMessage),
      PactType.BranchFairChoiceIds
          (PactType.reannotateOfferBranches alphabet seen branches) =
        PactType.BranchFairChoiceIds branches := by
  intro branches
  induction branches with
  | nil => intro seen; simp [PactType.reannotateOfferBranches_nil,
      PactType.BranchFairChoiceIds]
  | cons branch rest ih =>
      intro seen
      rcases branch with ⟨action, branchType⟩
      simp [PactType.reannotateOfferBranches_cons, PactType.BranchFairChoiceIds,
        (PactType.reannotate_ownership_data _ branchType).2.2.2.1, ih]

/-- The eight `TypeWF_Γ` conjuncts that the branch product must carry and that
are neither about alphabets nor already available for it. -/

theorem PactType.reannotate_progressLinear :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.ProgressLinear processType →
        PactType.ProgressLinear (processType.reannotate alphabet) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet hHolds
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.ProgressLinearBranches branches →
          PactType.ProgressLinearBranches
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet hBranchesSize hHold
        induction branches with
        | nil => simp [PactType.reannotateBranches, PactType.ProgressLinearBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.ProgressLinearBranches] at hHold
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
            simp only [PactType.reannotateBranches, PactType.ProgressLinearBranches,
              PactType.reannotate_progressIds, reannotateBranches_progressIds]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl
                branchAlphabet hHold.1, hHold.2.1, restIH hRestSize hHold.2.2⟩
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.ProgressLinearBranches branches →
          PactType.ProgressLinearBranches
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _ _
            simp [PactType.reannotateOfferBranches_nil, PactType.ProgressLinearBranches]
        | cons branch rest restIH =>
            intro seen hBranchesSize hHold
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.ProgressLinearBranches] at hHold
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
            simp only [PactType.reannotateOfferBranches_cons, PactType.ProgressLinearBranches,
              PactType.reannotate_progressIds, reannotateOfferBranches_progressIds]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl _ hHold.1,
              hHold.2.1, restIH _ hRestSize hHold.2.2⟩
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.ProgressLinear]
      | progress a p => simp [PactType.reannotate, PactType.ProgressLinear]
      | tock a => simp [PactType.reannotate, PactType.ProgressLinear]
      | skip a => simp [PactType.reannotate, PactType.ProgressLinear]
      | var a name => simp [PactType.reannotate, PactType.ProgressLinear]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hHolds
          simp only [PactType.reannotate, PactType.ProgressLinear]
          exact ih (sizeOf body) hB body rfl alphabet hHolds
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hHolds
          simp only [PactType.reannotate, PactType.ProgressLinear, PactType.reannotate_progressIds]
          exact ⟨ih (sizeOf l) hL l rfl _ hHolds.1,
            ih (sizeOf r) hR r rfl _ hHolds.2.1, hHolds.2.2⟩
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hHolds
          simp only [PactType.reannotate, PactType.ProgressLinear, PactType.reannotate_progressIds]
          exact ⟨ih (sizeOf l) hL l rfl alphabet hHolds.1,
            ih (sizeOf r) hR r rfl alphabet hHolds.2.1, hHolds.2.2⟩
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hHolds
          simp only [PactType.reannotate, PactType.ProgressLinear, PactType.reannotate_progressIds]
          exact ⟨ih (sizeOf l) hL l rfl _ hHolds.1,
            ih (sizeOf r) hR r rfl _ hHolds.2.1, hHolds.2.2⟩
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hHolds
          simp only [PactType.reannotate, PactType.ProgressLinear, PactType.reannotate_progressIds]
          exact ⟨ih (sizeOf l) hL l rfl _ hHolds.1,
            ih (sizeOf r) hR r rfl _ hHolds.2.1, hHolds.2.2⟩
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hHolds
          simp only [PactType.reannotate, PactType.ProgressLinear, PactType.reannotate_progressIds, reannotateBranches_progressIds]
          exact ⟨ih (sizeOf e) hE e rfl alphabet hHolds.1,
            hBranches bs alphabet hBs hHolds.2.1,
            hHolds.2.2⟩
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hHolds
          simp only [PactType.reannotate, PactType.ProgressLinear, PactType.reannotate_progressIds, reannotateOfferBranches_progressIds]
          exact ⟨ih (sizeOf e) hE e rfl alphabet hHolds.1,
            hOfferBranches bs alphabet ∅ hBs hHolds.2.1,
            hHolds.2.2⟩

theorem PactType.reannotate_fairChoiceLinear :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.FairChoiceLinear processType →
        PactType.FairChoiceLinear (processType.reannotate alphabet) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet hHolds
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.FairChoiceLinearBranches branches →
          PactType.FairChoiceLinearBranches
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet hBranchesSize hHold
        induction branches with
        | nil => simp [PactType.reannotateBranches, PactType.FairChoiceLinearBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.FairChoiceLinearBranches] at hHold
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
            simp only [PactType.reannotateBranches, PactType.FairChoiceLinearBranches,
              PactType.reannotate_fairChoiceIds, reannotateBranches_fairChoiceIds]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl
                branchAlphabet hHold.1, hHold.2.1, restIH hRestSize hHold.2.2⟩
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.FairChoiceLinearBranches branches →
          PactType.FairChoiceLinearBranches
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _ _
            simp [PactType.reannotateOfferBranches_nil, PactType.FairChoiceLinearBranches]
        | cons branch rest restIH =>
            intro seen hBranchesSize hHold
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.FairChoiceLinearBranches] at hHold
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
            simp only [PactType.reannotateOfferBranches_cons, PactType.FairChoiceLinearBranches,
              PactType.reannotate_fairChoiceIds, reannotateOfferBranches_fairChoiceIds]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl _ hHold.1,
              hHold.2.1, restIH _ hRestSize hHold.2.2⟩
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.FairChoiceLinear]
      | progress a p => simp [PactType.reannotate, PactType.FairChoiceLinear]
      | tock a => simp [PactType.reannotate, PactType.FairChoiceLinear]
      | skip a => simp [PactType.reannotate, PactType.FairChoiceLinear]
      | var a name => simp [PactType.reannotate, PactType.FairChoiceLinear]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hHolds
          simp only [PactType.reannotate, PactType.FairChoiceLinear]
          exact ih (sizeOf body) hB body rfl alphabet hHolds
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hHolds
          simp only [PactType.reannotate, PactType.FairChoiceLinear, PactType.reannotate_fairChoiceIds]
          exact ⟨ih (sizeOf l) hL l rfl _ hHolds.1,
            ih (sizeOf r) hR r rfl _ hHolds.2.1, hHolds.2.2⟩
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hHolds
          simp only [PactType.reannotate, PactType.FairChoiceLinear, PactType.reannotate_fairChoiceIds]
          exact ⟨ih (sizeOf l) hL l rfl alphabet hHolds.1,
            ih (sizeOf r) hR r rfl alphabet hHolds.2.1, hHolds.2.2.1,
            hHolds.2.2.2⟩
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hHolds
          simp only [PactType.reannotate, PactType.FairChoiceLinear, PactType.reannotate_fairChoiceIds]
          exact ⟨ih (sizeOf l) hL l rfl _ hHolds.1,
            ih (sizeOf r) hR r rfl _ hHolds.2.1, hHolds.2.2⟩
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hHolds
          simp only [PactType.reannotate, PactType.FairChoiceLinear, PactType.reannotate_fairChoiceIds]
          exact ⟨ih (sizeOf l) hL l rfl _ hHolds.1,
            ih (sizeOf r) hR r rfl _ hHolds.2.1, hHolds.2.2⟩
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hHolds
          simp only [PactType.reannotate, PactType.FairChoiceLinear, PactType.reannotate_fairChoiceIds, reannotateBranches_fairChoiceIds]
          exact ⟨ih (sizeOf e) hE e rfl alphabet hHolds.1,
            hBranches bs alphabet hBs hHolds.2.1,
            hHolds.2.2⟩
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hHolds
          simp only [PactType.reannotate, PactType.FairChoiceLinear, PactType.reannotate_fairChoiceIds, reannotateOfferBranches_fairChoiceIds]
          exact ⟨ih (sizeOf e) hE e rfl alphabet hHolds.1,
            hOfferBranches bs alphabet ∅ hBs hHolds.2.1,
            hHolds.2.2⟩

/-! ### The generated conjunctive child inherits `TypeWF_Γ`

The paper's `<compiler-call-decrease>`, "Generated conjunctive children"
clause.  Eight of the thirteen conjuncts are bundled here and proved by one
induction over the branch list; `AlphabetWellFormed`, `ClockGuarded`,
`TailRecursive` and `TailClosed` come from existing results. -/

/-- Conjunctive ownership speaks only about message identifiers, so re-signing
transports it in both directions. -/

theorem PactType.reannotateBranches_branchMessageIds
    (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      PactType.BranchMessageIds
          (PactType.reannotateBranches alphabet branches) =
        PactType.BranchMessageIds branches := by
  intro branches
  induction branches with
  | nil => simp [PactType.BranchMessageIds]
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      rw [PactType.reannotateBranches_cons]
      simp only [PactType.BranchMessageIds, ih,
        PactType.reannotate_messageIds]

theorem PactType.reannotate_conjunctiveMessageOwnership :
    ∀ (processType : PactType) (target : PactTypeAlphabet),
      (PactType.ConjunctiveMessageOwnership (processType.reannotate target) ↔
        PactType.ConjunctiveMessageOwnership processType) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBodies : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ target : PactTypeAlphabet,
          (PactType.ConjunctiveMessageOwnershipBodies
              (PactType.reannotateBranches target branches) ↔
            PactType.ConjunctiveMessageOwnershipBodies branches) := by
        intro branches
        induction branches with
        | nil =>
            intro _ _
            rw [PactType.reannotateBranches_nil]
        | cons head tail restIH =>
            intro hSizeCons target
            rcases head with ⟨action, body⟩
            have hBodySize : sizeOf body < n := by
              have hPair : sizeOf body < sizeOf (action, body) := by
                simp_wf; omega
              have hHead : sizeOf (action, body) <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have hRest : sizeOf tail <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            rw [PactType.reannotateBranches_cons]
            simp only [PactType.ConjunctiveMessageOwnershipBodies]
            exact and_congr (ih (sizeOf body) hBodySize body rfl target)
              (restIH hTailSize target)
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ (target : PactTypeAlphabet)
            (seen : Finset BareMessage),
          (PactType.ConjunctiveMessageOwnershipBranches
              (PactType.reannotateOfferBranches target seen branches) ↔
            PactType.ConjunctiveMessageOwnershipBranches branches) := by
        intro branches
        induction branches with
        | nil =>
            intro _ _ _
            rw [PactType.reannotateOfferBranches_nil]
        | cons head tail restIH =>
            intro hSizeCons target seen
            rcases head with ⟨action, body⟩
            have hBodySize : sizeOf body < n := by
              have hPair : sizeOf body < sizeOf (action, body) := by
                simp_wf; omega
              have hHead : sizeOf (action, body) <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have hRest : sizeOf tail <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailIds : PactType.BranchMessageIds
                (PactType.reannotateOfferBranches target seen tail) =
                  PactType.BranchMessageIds tail := by
              have hShape : ∀ list : List (BareMessage × PactType),
                  PactType.reannotateOfferBranches target seen list =
                    PactType.reannotateBranches target list := by
                intro list
                induction list with
                | nil =>
                    rw [PactType.reannotateOfferBranches_nil,
                      PactType.reannotateBranches_nil]
                | cons entry rest shapeIH =>
                    rcases entry with ⟨entryAction, entryBody⟩
                    rw [PactType.reannotateOfferBranches_cons,
                      PactType.reannotateBranches_cons, shapeIH]
              rw [hShape tail,
                PactType.reannotateBranches_branchMessageIds]
            rw [PactType.reannotateOfferBranches_cons]
            simp only [PactType.ConjunctiveMessageOwnershipBranches,
              PactType.reannotate_messageIds, hTailIds]
            exact and_congr (ih (sizeOf body) hBodySize body rfl target)
              (and_congr Iff.rfl (restIH hTailSize target seen))
      intro target
      subst hSize
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
          simp [PactType.reannotate, PactType.ConjunctiveMessageOwnership]
      | recur alphabet name body =>
          have hBodySize : sizeOf body < sizeOf
              (PactType.recur alphabet name body) := by simp_wf; omega
          simp only [PactType.reannotate,
            PactType.ConjunctiveMessageOwnership]
          exact ih (sizeOf body) hBodySize body rfl target
      | choice alphabet left right =>
          have hL : sizeOf left < sizeOf
              (PactType.choice alphabet left right) := by simp_wf; omega
          have hR : sizeOf right < sizeOf
              (PactType.choice alphabet left right) := by simp_wf; omega
          simp only [PactType.reannotate,
            PactType.ConjunctiveMessageOwnership]
          exact and_congr (ih (sizeOf left) hL left rfl target)
            (ih (sizeOf right) hR right rfl target)
      | seq alphabet left right =>
          have hL : sizeOf left < sizeOf
              (PactType.seq alphabet left right) := by simp_wf; omega
          have hR : sizeOf right < sizeOf
              (PactType.seq alphabet left right) := by simp_wf; omega
          simp only [PactType.reannotate,
            PactType.ConjunctiveMessageOwnership]
          exact and_congr (ih (sizeOf left) hL left rfl target)
            (ih (sizeOf right) hR right rfl target)
      | fairChoice alphabet bid left right =>
          have hL : sizeOf left < sizeOf
              (PactType.fairChoice alphabet bid left right) := by simp_wf; omega
          have hR : sizeOf right < sizeOf
              (PactType.fairChoice alphabet bid left right) := by simp_wf; omega
          simp only [PactType.reannotate,
            PactType.ConjunctiveMessageOwnership]
          exact and_congr (ih (sizeOf left) hL left rfl target)
            (ih (sizeOf right) hR right rfl target)
      | par alphabet left right interface =>
          have hL : sizeOf left < sizeOf
              (PactType.par alphabet left right interface) := by simp_wf; omega
          have hR : sizeOf right < sizeOf
              (PactType.par alphabet left right interface) := by simp_wf; omega
          simp only [PactType.reannotate,
            PactType.ConjunctiveMessageOwnership]
          exact and_congr
            (ih (sizeOf left) hL left rfl
              (target.projectParallel left.alphabet interface))
            (ih (sizeOf right) hR right rfl
              (target.projectParallel right.alphabet interface))
      | xoffer alphabet elseType branches =>
          have hE : sizeOf elseType < sizeOf
              (PactType.xoffer alphabet elseType branches) := by simp_wf; omega
          have hB : sizeOf branches < sizeOf
              (PactType.xoffer alphabet elseType branches) := by simp_wf; omega
          simp only [PactType.reannotate,
            PactType.ConjunctiveMessageOwnership]
          exact and_congr (ih (sizeOf elseType) hE elseType rfl target)
            (hBodies branches hB target)
      | offer alphabet elseType branches =>
          have hE : sizeOf elseType < sizeOf
              (PactType.offer alphabet elseType branches) := by simp_wf; omega
          have hB : sizeOf branches < sizeOf
              (PactType.offer alphabet elseType branches) := by simp_wf; omega
          simp only [PactType.reannotate,
            PactType.ConjunctiveMessageOwnership]
          exact and_congr (ih (sizeOf elseType) hE elseType rfl target)
            (hBranches branches hB target ∅)

/-- The generated conjunctive child carries the eight `TypeWF_Γ` conjuncts that
are neither alphabet-shaped nor already available for it. -/

theorem PactType.reannotate_canCompleteBeforeTock :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.CanCompleteBeforeTock (processType.reannotate alphabet) =
        PactType.CanCompleteBeforeTock processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.BranchCanCompleteBeforeTock
              (PactType.reannotateBranches branchAlphabet branches) =
            PactType.BranchCanCompleteBeforeTock branches := by
        intro branches branchAlphabet hBranchesSize
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            PactType.BranchCanCompleteBeforeTock]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
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
              PactType.BranchCanCompleteBeforeTock,
              ih (sizeOf branchType) hBranchSize branchType rfl branchAlphabet,
              restIH hRestSize]
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.BranchCanCompleteBeforeTock
              (PactType.reannotateOfferBranches branchAlphabet seen branches) =
            PactType.BranchCanCompleteBeforeTock branches := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.BranchCanCompleteBeforeTock]
        | cons branch rest restIH =>
            intro seen hBranchesSize
            rcases branch with ⟨action, branchType⟩
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
              PactType.BranchCanCompleteBeforeTock,
              ih (sizeOf branchType) hBranchSize branchType rfl _,
              restIH _ hRestSize]
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.CanCompleteBeforeTock]
      | progress a p => simp [PactType.reannotate, PactType.CanCompleteBeforeTock]
      | tock a => simp [PactType.reannotate, PactType.CanCompleteBeforeTock]
      | skip a => simp [PactType.reannotate, PactType.CanCompleteBeforeTock]
      | var a name => simp [PactType.reannotate, PactType.CanCompleteBeforeTock]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.CanCompleteBeforeTock,
            ih (sizeOf body) hB body rfl alphabet]
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.CanCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.CanCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.CanCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.CanCompleteBeforeTock,
            ih (sizeOf l) hL l rfl _, ih (sizeOf r) hR r rfl _]
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.CanCompleteBeforeTock,
            ih (sizeOf e) hE e rfl alphabet, hBranches bs alphabet hBs]
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.CanCompleteBeforeTock,
            ih (sizeOf e) hE e rfl alphabet, hOfferBranches bs alphabet ∅ hBs]

theorem PactType.reannotate_prefixMessageIds :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.PrefixMessageIds (processType.reannotate alphabet) =
        PactType.PrefixMessageIds processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.BranchPrefixMessageIds
              (PactType.reannotateBranches branchAlphabet branches) =
            PactType.BranchPrefixMessageIds branches := by
        intro branches branchAlphabet hBranchesSize
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            PactType.BranchPrefixMessageIds]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
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
              PactType.BranchPrefixMessageIds, PactType.reannotate_canCompleteBeforeTock,
              ih (sizeOf branchType) hBranchSize branchType rfl branchAlphabet,
              restIH hRestSize]
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.BranchPrefixMessageIds
              (PactType.reannotateOfferBranches branchAlphabet seen branches) =
            PactType.BranchPrefixMessageIds branches := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.BranchPrefixMessageIds]
        | cons branch rest restIH =>
            intro seen hBranchesSize
            rcases branch with ⟨action, branchType⟩
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
              PactType.BranchPrefixMessageIds, PactType.reannotate_canCompleteBeforeTock,
              ih (sizeOf branchType) hBranchSize branchType rfl _,
              restIH _ hRestSize]
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | progress a p => simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | tock a => simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | skip a => simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | var a name => simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf body) hB body rfl alphabet]
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl _, ih (sizeOf r) hR r rfl _]
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf e) hE e rfl alphabet, hBranches bs alphabet hBs]
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf e) hE e rfl alphabet, hOfferBranches bs alphabet ∅ hBs]

theorem PactType.reannotate_suffixMessageIds :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.SuffixMessageIds (processType.reannotate alphabet) =
        PactType.SuffixMessageIds processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.BranchSuffixMessageIds
              (PactType.reannotateBranches branchAlphabet branches) =
            PactType.BranchSuffixMessageIds branches := by
        intro branches branchAlphabet hBranchesSize
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            PactType.BranchSuffixMessageIds]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
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
              PactType.BranchSuffixMessageIds, PactType.reannotate_canCompleteBeforeTock,
              ih (sizeOf branchType) hBranchSize branchType rfl branchAlphabet,
              restIH hRestSize]
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.BranchSuffixMessageIds
              (PactType.reannotateOfferBranches branchAlphabet seen branches) =
            PactType.BranchSuffixMessageIds branches := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.BranchSuffixMessageIds]
        | cons branch rest restIH =>
            intro seen hBranchesSize
            rcases branch with ⟨action, branchType⟩
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
              PactType.BranchSuffixMessageIds, PactType.reannotate_canCompleteBeforeTock,
              ih (sizeOf branchType) hBranchSize branchType rfl _,
              restIH _ hRestSize]
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | progress a p => simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | tock a => simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | skip a => simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | var a name => simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf body) hB body rfl alphabet]
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl _, ih (sizeOf r) hR r rfl _]
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf e) hE e rfl alphabet, hBranches bs alphabet hBs]
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf e) hE e rfl alphabet, hOfferBranches bs alphabet ∅ hBs]

/-! ### Same-cycle identifier sets of the generated branch product

`PrefixMessageIds` and `SuffixMessageIds` of the product are exactly the branch
list's own, and the product can always complete before a clock (every factor
carries a `skip` else-arm).  These are stated separately because
`<future-offers-agree>`'s `.offer` case unfolds the same sets. -/

theorem PactType.reannotate_sameCycleMessageLinear :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.SameCycleMessageLinear processType →
        PactType.SameCycleMessageLinear (processType.reannotate alphabet) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet hHolds
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.SameCycleMessageLinearBranches branches →
          PactType.SameCycleMessageLinearBranches
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet hBranchesSize hHold
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            PactType.SameCycleMessageLinearBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.SameCycleMessageLinearBranches] at hHold
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
              PactType.SameCycleMessageLinearBranches,
              PactType.reannotate_prefixMessageIds]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl
                branchAlphabet hHold.1, hHold.2.1, restIH hRestSize hHold.2.2⟩
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.SameCycleMessageLinearBranches branches →
          PactType.SameCycleMessageLinearBranches
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _ _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.SameCycleMessageLinearBranches]
        | cons branch rest restIH =>
            intro seen hBranchesSize hHold
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.SameCycleMessageLinearBranches] at hHold
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
              PactType.SameCycleMessageLinearBranches,
              PactType.reannotate_prefixMessageIds]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl _ hHold.1,
              hHold.2.1, restIH _ hRestSize hHold.2.2⟩
      cases processType with
      | message a m d => simp [PactType.reannotate,
          PactType.SameCycleMessageLinear]
      | progress a p => simp [PactType.reannotate,
          PactType.SameCycleMessageLinear]
      | tock a => simp [PactType.reannotate, PactType.SameCycleMessageLinear]
      | skip a => simp [PactType.reannotate, PactType.SameCycleMessageLinear]
      | var a name => simp [PactType.reannotate,
          PactType.SameCycleMessageLinear]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.SameCycleMessageLinear] at hHolds
          simp only [PactType.reannotate, PactType.SameCycleMessageLinear,
            PactType.reannotate_prefixMessageIds,
            PactType.reannotate_suffixMessageIds]
          exact ⟨ih (sizeOf body) hB body rfl alphabet hHolds.1, hHolds.2⟩
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.SameCycleMessageLinear] at hHolds
          simp only [PactType.reannotate, PactType.SameCycleMessageLinear]
          exact ⟨ih (sizeOf l) hL l rfl alphabet hHolds.1,
            ih (sizeOf r) hR r rfl alphabet hHolds.2⟩
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.SameCycleMessageLinear] at hHolds
          simp only [PactType.reannotate, PactType.SameCycleMessageLinear]
          exact ⟨ih (sizeOf l) hL l rfl alphabet hHolds.1,
            ih (sizeOf r) hR r rfl alphabet hHolds.2⟩
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.SameCycleMessageLinear] at hHolds
          simp only [PactType.reannotate, PactType.SameCycleMessageLinear,
            PactType.reannotate_prefixMessageIds,
            PactType.reannotate_suffixMessageIds]
          exact ⟨ih (sizeOf l) hL l rfl alphabet hHolds.1,
            ih (sizeOf r) hR r rfl alphabet hHolds.2.1, hHolds.2.2⟩
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.SameCycleMessageLinear] at hHolds
          simp only [PactType.reannotate, PactType.SameCycleMessageLinear]
          exact ⟨ih (sizeOf l) hL l rfl _ hHolds.1,
            ih (sizeOf r) hR r rfl _ hHolds.2⟩
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.SameCycleMessageLinear] at hHolds
          simp only [PactType.reannotate, PactType.SameCycleMessageLinear,
            PactType.reannotate_prefixMessageIds]
          refine ⟨ih (sizeOf e) hE e rfl alphabet hHolds.1,
            hBranches bs alphabet hBs hHolds.2.1, ?_⟩
          intro branch hBranchMem
          obtain ⟨source, hSource, hEq⟩ :=
            reannotateBranches_mem hBranchMem
          rw [hEq]
          exact hHolds.2.2 source hSource
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.SameCycleMessageLinear] at hHolds
          simp only [PactType.reannotate, PactType.SameCycleMessageLinear,
            PactType.reannotate_prefixMessageIds]
          refine ⟨ih (sizeOf e) hE e rfl alphabet hHolds.1,
            hOfferBranches bs alphabet ∅ hBs hHolds.2.1, ?_⟩
          intro branch hBranchMem
          obtain ⟨source, hSource, branchAlphabet, hEq⟩ :=
            reannotateOfferBranches_mem alphabet bs ∅ branch
              hBranchMem
          rw [hEq]
          exact hHolds.2.2 source hSource

def GeneratedChildConjuncts (bound : List String) (processType : PactType) :
    Prop :=
  PactType.AllVariablesBound bound processType ∧
    PactType.BinderHygienic bound processType ∧
    PactType.InterfaceScoped processType ∧
    PactType.ProgressLinear processType ∧
    PactType.FairChoiceLinear processType ∧
    PactType.ParallelMessageOwnership processType ∧
    PactType.ParallelProgressOwnership processType ∧
    PactType.ParallelFairChoiceOwnership processType

/-- Re-signing leaves the message identifiers of every branch in place. -/

theorem generatedChildConjuncts_reannotate {bound : List String}
    {processType : PactType} (alphabet : PactTypeAlphabet)
    (h : GeneratedChildConjuncts bound processType) :
    GeneratedChildConjuncts bound (processType.reannotate alphabet) := by
  obtain ⟨hB, hH, hS, hP, hF, hM, hPo, hFo⟩ := h
  exact ⟨PactType.reannotate_allVariablesBound bound processType alphabet hB,
    PactType.reannotate_binderHygienic bound processType alphabet hH,
    PactType.reannotate_interfaceScoped processType alphabet hS,
    PactType.reannotate_progressLinear processType alphabet hP,
    PactType.reannotate_fairChoiceLinear processType alphabet hF,
    (PactType.reannotate_ownership_data alphabet processType).2.2.2.2.1.mpr hM,
    (PactType.reannotate_ownership_data alphabet processType).2.2.2.2.2.1.mpr hPo,
    (PactType.reannotate_ownership_data alphabet processType).2.2.2.2.2.2.mpr hFo⟩

theorem singletonTypeXOfferAt_conjuncts {bound : List String}
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (h : GeneratedChildConjuncts bound branch.2) :
    GeneratedChildConjuncts bound (singletonTypeXOfferAt alphabet branch) := by
  rcases branch with ⟨action, body⟩
  obtain ⟨hB, hH, hS, hP, hF, hM, hPo, hFo⟩ :=
    generatedChildConjuncts_reannotate (bound := bound) alphabet h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [singletonTypeXOfferAt, PactType.AllVariablesBound,
      PactType.AllBranchVariablesBound, PactType.BinderHygienic,
      PactType.BinderHygienicBranches, PactType.InterfaceScoped,
      PactType.InterfaceScopedBranches, PactType.ProgressLinear,
      PactType.ProgressLinearBranches, PactType.FairChoiceLinear,
      PactType.FairChoiceLinearBranches, PactType.ParallelMessageOwnership,
      PactType.ParallelMessageOwnershipBodies,
      PactType.ParallelProgressOwnership,
      PactType.ParallelProgressOwnershipBranches,
      PactType.ParallelFairChoiceOwnership,
      PactType.ParallelFairChoiceOwnershipBranches,
      PactType.ProgressIds, PactType.BranchProgressIds,
      PactType.FairChoiceIds, PactType.BranchFairChoiceIds]
  · exact ⟨trivial, hB, trivial⟩
  · exact ⟨trivial, hH, trivial⟩
  · exact ⟨trivial, hS, trivial⟩
  · exact ⟨trivial, ⟨hP, by simp, trivial⟩, by simp⟩
  · exact ⟨trivial, ⟨hF, by simp, trivial⟩, by simp⟩
  · exact ⟨trivial, hM, trivial⟩
  · exact ⟨trivial, hPo, by simp, trivial⟩
  · exact ⟨trivial, hFo, by simp, trivial⟩

theorem selectedTypeBranchAt_conjuncts {bound : List String}
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (h : GeneratedChildConjuncts bound branch.2) :
    GeneratedChildConjuncts bound (selectedTypeBranchAt alphabet branch) := by
  rcases branch with ⟨action, body⟩
  obtain ⟨hB, hH, hS, hP, hF, hM, hPo, hFo⟩ :=
    generatedChildConjuncts_reannotate (bound := bound) alphabet h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [selectedTypeBranchAt, PactType.AllVariablesBound,
      PactType.BinderHygienic, PactType.InterfaceScoped,
      PactType.ProgressLinear, PactType.FairChoiceLinear,
      PactType.ParallelMessageOwnership, PactType.ParallelProgressOwnership,
      PactType.ParallelFairChoiceOwnership,
      PactType.ProgressIds, PactType.FairChoiceIds]
  · exact ⟨trivial, hB⟩
  · exact ⟨trivial, hH⟩
  · exact ⟨trivial, hS⟩
  · exact ⟨trivial, hP, by simp⟩
  · exact ⟨trivial, hF, by simp⟩
  · exact ⟨trivial, hM⟩
  · exact ⟨trivial, hPo⟩
  · exact ⟨trivial, hFo⟩

theorem singletonTypeXOfferAt_ids (alphabet : PactTypeAlphabet)
    (branch : BareMessage × PactType) :
    PactType.MessageIds (singletonTypeXOfferAt alphabet branch) =
        {branch.1.1} ∪ PactType.MessageIds branch.2 ∧
      PactType.MessageActions (singletonTypeXOfferAt alphabet branch) =
        {branch.1} ∪ PactType.MessageActions branch.2 ∧
      PactType.ProgressIds (singletonTypeXOfferAt alphabet branch) =
        PactType.ProgressIds branch.2 ∧
      PactType.FairChoiceIds (singletonTypeXOfferAt alphabet branch) =
        PactType.FairChoiceIds branch.2 := by
  rcases branch with ⟨action, body⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [singletonTypeXOfferAt, PactType.MessageIds, PactType.BranchMessageIds,
      PactType.MessageActions, PactType.BranchMessageActions,
      PactType.ProgressIds, PactType.BranchProgressIds,
      PactType.FairChoiceIds, PactType.BranchFairChoiceIds,
      PactType.reannotate_messageIds, PactType.reannotate_messageActions,
      PactType.reannotate_progressIds, PactType.reannotate_fairChoiceIds]

theorem selectedTypeBranchAt_ids (alphabet : PactTypeAlphabet)
    (branch : BareMessage × PactType) :
    PactType.MessageIds (selectedTypeBranchAt alphabet branch) =
        {branch.1.1} ∪ PactType.MessageIds branch.2 ∧
      PactType.MessageActions (selectedTypeBranchAt alphabet branch) =
        {branch.1} ∪ PactType.MessageActions branch.2 ∧
      PactType.ProgressIds (selectedTypeBranchAt alphabet branch) =
        PactType.ProgressIds branch.2 ∧
      PactType.FairChoiceIds (selectedTypeBranchAt alphabet branch) =
        PactType.FairChoiceIds branch.2 := by
  rcases branch with ⟨action, body⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [selectedTypeBranchAt, PactType.MessageIds, PactType.MessageActions,
      PactType.ProgressIds, PactType.FairChoiceIds,
      PactType.reannotate_messageIds, PactType.reannotate_messageActions,
      PactType.reannotate_progressIds, PactType.reannotate_fairChoiceIds]

theorem parallelTypeBranchesWithin_conjuncts {bound : List String} :
    ∀ (branches : List (BareMessage × PactType)),
      (∀ b ∈ branches, GeneratedChildConjuncts bound b.2) →
      PactType.ProgressLinearBranches branches →
      PactType.FairChoiceLinearBranches branches →
      PactType.ParallelMessageOwnershipBranches branches →
      PactType.ParallelProgressOwnershipBranches branches →
      PactType.ParallelFairChoiceOwnershipBranches branches →
      ∀ alphabet : PactTypeAlphabet,
        GeneratedChildConjuncts bound
          (parallelTypeBranchesWithin alphabet branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _ _ _ _ _ _ alphabet
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [parallelTypeBranchesWithin, PactType.AllVariablesBound,
          PactType.BinderHygienic, PactType.InterfaceScoped,
          PactType.ProgressLinear, PactType.FairChoiceLinear,
          PactType.ParallelMessageOwnership,
          PactType.ParallelProgressOwnership,
          PactType.ParallelFairChoiceOwnership]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro hBranch hProg hFair hMsgOwn hProgOwn hFairOwn alphabet
      cases rest with
      | nil =>
          simp only [parallelTypeBranchesWithin]
          exact singletonTypeXOfferAt_conjuncts alphabet (action, body)
            (hBranch (action, body) (by simp))
      | cons next tail =>
          simp only [PactType.ProgressLinearBranches] at hProg
          simp only [PactType.FairChoiceLinearBranches] at hFair
          simp only [PactType.ParallelMessageOwnershipBranches] at hMsgOwn
          simp only [PactType.ParallelProgressOwnershipBranches] at hProgOwn
          simp only [PactType.ParallelFairChoiceOwnershipBranches] at hFairOwn
          have hHead := singletonTypeXOfferAt_conjuncts alphabet
            (action, body) (hBranch (action, body) (by simp))
          have hRestConj := ih (fun b hb => hBranch b (by simp [hb]))
            hProg.2.2 hFair.2.2 hMsgOwn.2.2.2 hProgOwn.2.2 hFairOwn.2.2
            alphabet
          obtain ⟨hHB, hHH, hHS, hHP, hHF, hHM, hHPo, hHFo⟩ := hHead
          obtain ⟨hRB, hRH, hRS, hRP, hRF, hRM, hRPo, hRFo⟩ := hRestConj
          obtain ⟨hIdsL, hActsL, hProgL, hFairL⟩ :=
            singletonTypeXOfferAt_ids alphabet (action, body)
          have hIdsR := parallelTypeBranchesWithin_messageIds
            alphabet (next :: tail)
          have hActsR := parallelTypeBranchesWithin_messageActions
            alphabet (next :: tail)
          have hProgR := parallelTypeBranchesWithin_progressIds
            alphabet (next :: tail)
          have hFairR := parallelTypeBranchesWithin_fairChoiceIds
            alphabet (next :: tail)
          simp only [parallelTypeBranchesWithin]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [PactType.AllVariablesBound, PactType.BinderHygienic,
              PactType.InterfaceScoped, PactType.ProgressLinear,
              PactType.FairChoiceLinear, PactType.ParallelMessageOwnership,
              PactType.ParallelProgressOwnership,
              PactType.ParallelFairChoiceOwnership]
          · exact ⟨hHB, hRB⟩
          · exact ⟨hHH, hRH⟩
          · exact ⟨by simp, hHS, hRS⟩
          · refine ⟨hHP, hRP, ?_⟩
            rw [hProgL, hProgR]; exact hProg.2.1
          · refine ⟨hHF, hRF, ?_⟩
            rw [hFairL, hFairR]; exact hFair.2.1
          · refine ⟨?_, hHM, hRM⟩
            rw [hIdsL, hIdsR]
            intro x hx
            exact absurd (Finset.mem_inter.mp hx).2
              (Finset.disjoint_left.mp hMsgOwn.2.1 (Finset.mem_inter.mp hx).1)
          · refine ⟨?_, hHPo, hRPo⟩
            rw [hProgL, hProgR]; exact hProgOwn.2.1
          · refine ⟨?_, hHFo, hRFo⟩
            rw [hFairL, hFairR]; exact hFairOwn.2.1

theorem parallelTypeBranchesSelectingWithin_conjuncts {bound : List String}
    (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType)),
      (∀ b ∈ branches, GeneratedChildConjuncts bound b.2) →
      PactType.ProgressLinearBranches branches →
      PactType.FairChoiceLinearBranches branches →
      PactType.ParallelMessageOwnershipBranches branches →
      PactType.ParallelProgressOwnershipBranches branches →
      PactType.ParallelFairChoiceOwnershipBranches branches →
      ∀ alphabet : PactTypeAlphabet,
        GeneratedChildConjuncts bound
          (parallelTypeBranchesSelectingWithin alphabet selected branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _ _ _ _ _ _ alphabet
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [parallelTypeBranchesSelectingWithin, PactType.AllVariablesBound,
          PactType.BinderHygienic, PactType.InterfaceScoped,
          PactType.ProgressLinear, PactType.FairChoiceLinear,
          PactType.ParallelMessageOwnership,
          PactType.ParallelProgressOwnership,
          PactType.ParallelFairChoiceOwnership]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro hBranch hProg hFair hMsgOwn hProgOwn hFairOwn alphabet
      have hHeadConj := hBranch (action, body) (by simp)
      cases rest with
      | nil =>
          simp only [parallelTypeBranchesSelectingWithin]
          by_cases hSel : (action, body) = selected
          · rw [if_pos hSel]
            exact selectedTypeBranchAt_conjuncts alphabet (action, body) hHeadConj
          · rw [if_neg hSel]
            exact singletonTypeXOfferAt_conjuncts alphabet (action, body) hHeadConj
      | cons next tail =>
          simp only [PactType.ProgressLinearBranches] at hProg
          simp only [PactType.FairChoiceLinearBranches] at hFair
          simp only [PactType.ParallelMessageOwnershipBranches] at hMsgOwn
          simp only [PactType.ParallelProgressOwnershipBranches] at hProgOwn
          simp only [PactType.ParallelFairChoiceOwnershipBranches] at hFairOwn
          simp only [parallelTypeBranchesSelectingWithin]
          by_cases hSel : (action, body) = selected
          · rw [if_pos hSel]
            have hHead := selectedTypeBranchAt_conjuncts alphabet
              (action, body) hHeadConj
            have hRestConj := parallelTypeBranchesWithin_conjuncts (next :: tail)
              (fun b hb => hBranch b (by simp [hb]))
              hProg.2.2 hFair.2.2 hMsgOwn.2.2.2 hProgOwn.2.2 hFairOwn.2.2
              alphabet
            obtain ⟨hHB, hHH, hHS, hHP, hHF, hHM, hHPo, hHFo⟩ := hHead
            obtain ⟨hRB, hRH, hRS, hRP, hRF, hRM, hRPo, hRFo⟩ := hRestConj
            obtain ⟨hIdsL, hActsL, hProgL, hFairL⟩ :=
              selectedTypeBranchAt_ids alphabet (action, body)
            have hIdsRe := parallelTypeBranchesWithin_messageIds
              alphabet (next :: tail)
            have hActsRe := parallelTypeBranchesWithin_messageActions
              alphabet (next :: tail)
            have hProgRe := parallelTypeBranchesWithin_progressIds
              alphabet (next :: tail)
            have hFairRe := parallelTypeBranchesWithin_fairChoiceIds
              alphabet (next :: tail)
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp only [PactType.AllVariablesBound, PactType.BinderHygienic,
                PactType.InterfaceScoped, PactType.ProgressLinear,
                PactType.FairChoiceLinear, PactType.ParallelMessageOwnership,
                PactType.ParallelProgressOwnership,
                PactType.ParallelFairChoiceOwnership]
            · exact ⟨hHB, hRB⟩
            · exact ⟨hHH, hRH⟩
            · exact ⟨by simp, hHS, hRS⟩
            · refine ⟨hHP, hRP, ?_⟩
              rw [hProgL, hProgRe]; exact hProg.2.1
            · refine ⟨hHF, hRF, ?_⟩
              rw [hFairL, hFairRe]; exact hFair.2.1
            · refine ⟨?_, hHM, hRM⟩
              rw [hIdsL, hIdsRe]
              intro x hx
              exact absurd (Finset.mem_inter.mp hx).2
                (Finset.disjoint_left.mp hMsgOwn.2.1 (Finset.mem_inter.mp hx).1)
            · refine ⟨?_, hHPo, hRPo⟩
              rw [hProgL, hProgRe]; exact hProgOwn.2.1
            · refine ⟨?_, hHFo, hRFo⟩
              rw [hFairL, hFairRe]; exact hFairOwn.2.1
          · rw [if_neg hSel]
            have hHead := singletonTypeXOfferAt_conjuncts alphabet
              (action, body) hHeadConj
            have hRestConj := ih (fun b hb => hBranch b (by simp [hb]))
              hProg.2.2 hFair.2.2 hMsgOwn.2.2.2 hProgOwn.2.2 hFairOwn.2.2
              alphabet
            obtain ⟨hHB, hHH, hHS, hHP, hHF, hHM, hHPo, hHFo⟩ := hHead
            obtain ⟨hRB, hRH, hRS, hRP, hRF, hRM, hRPo, hRFo⟩ := hRestConj
            obtain ⟨hIdsL, hActsL, hProgL, hFairL⟩ :=
              singletonTypeXOfferAt_ids alphabet (action, body)
            obtain ⟨hIdsRe, hActsRe, hProgRe, hFairRe⟩ :=
              parallelTypeBranchesSelectingWithin_ownershipData
                alphabet selected
                (next :: tail)
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp only [PactType.AllVariablesBound, PactType.BinderHygienic,
                PactType.InterfaceScoped, PactType.ProgressLinear,
                PactType.FairChoiceLinear, PactType.ParallelMessageOwnership,
                PactType.ParallelProgressOwnership,
                PactType.ParallelFairChoiceOwnership]
            · exact ⟨hHB, hRB⟩
            · exact ⟨hHH, hRH⟩
            · exact ⟨by simp, hHS, hRS⟩
            · refine ⟨hHP, hRP, ?_⟩
              rw [hProgL, hProgRe]; exact hProg.2.1
            · refine ⟨hHF, hRF, ?_⟩
              rw [hFairL, hFairRe]; exact hFair.2.1
            · refine ⟨?_, hHM, hRM⟩
              rw [hIdsL, hIdsRe]
              intro x hx
              exact absurd (Finset.mem_inter.mp hx).2
                (Finset.disjoint_left.mp hMsgOwn.2.1 (Finset.mem_inter.mp hx).1)
            · refine ⟨?_, hHPo, hRPo⟩
              rw [hProgL, hProgRe]; exact hProgOwn.2.1
            · refine ⟨?_, hHFo, hRFo⟩
              rw [hFairL, hFairRe]; exact hFairOwn.2.1

theorem parallelTypeBranchesSelecting_conjuncts {bound : List String}
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hBranch : ∀ b ∈ branches, GeneratedChildConjuncts bound b.2)
    (hProg : PactType.ProgressLinearBranches branches)
    (hFair : PactType.FairChoiceLinearBranches branches)
    (hMsgOwn : PactType.ParallelMessageOwnershipBranches branches)
    (hProgOwn : PactType.ParallelProgressOwnershipBranches branches)
    (hFairOwn : PactType.ParallelFairChoiceOwnershipBranches branches) :
    GeneratedChildConjuncts bound
      (parallelTypeBranchesSelecting alphabet selected branches) := by
  cases branches with
  | nil =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [parallelTypeBranchesSelecting, PactType.AllVariablesBound,
          PactType.BinderHygienic, PactType.InterfaceScoped,
          PactType.ProgressLinear, PactType.FairChoiceLinear,
          PactType.ParallelMessageOwnership,
          PactType.ParallelProgressOwnership,
          PactType.ParallelFairChoiceOwnership]
  | cons branch rest =>
      simp only [parallelTypeBranchesSelecting]
      exact parallelTypeBranchesSelectingWithin_conjuncts selected
        (branch :: rest) hBranch hProg hFair hMsgOwn hProgOwn hFairOwn alphabet

theorem singletonTypeXOfferAt_sameCycleMessageLinear
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hLinear : PactType.SameCycleMessageLinear branch.2)
    (hHead : branch.1.1 ∉ PactType.PrefixMessageIds branch.2) :
    PactType.SameCycleMessageLinear (singletonTypeXOfferAt alphabet branch) := by
  rcases branch with ⟨action, body⟩
  simp only [singletonTypeXOfferAt, PactType.SameCycleMessageLinear,
    PactType.SameCycleMessageLinearBranches, PactType.PrefixMessageIds,
    PactType.reannotate_prefixMessageIds]
  refine ⟨trivial, ⟨PactType.reannotate_sameCycleMessageLinear body alphabet
    hLinear, hHead, trivial⟩, ?_⟩
  intro branch hBranchMem
  simp

theorem selectedTypeBranchAt_sameCycleMessageLinear
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hLinear : PactType.SameCycleMessageLinear branch.2)
    (hHead : branch.1.1 ∉ PactType.PrefixMessageIds branch.2) :
    PactType.SameCycleMessageLinear (selectedTypeBranchAt alphabet branch) := by
  rcases branch with ⟨action, body⟩
  simp only [selectedTypeBranchAt, PactType.SameCycleMessageLinear,
    PactType.SuffixMessageIds, PactType.reannotate_prefixMessageIds]
  refine ⟨trivial, PactType.reannotate_sameCycleMessageLinear body alphabet
    hLinear, ?_⟩
  simpa [Finset.disjoint_left] using hHead

theorem parallelTypeBranchesWithin_sameCycleMessageLinear :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.SameCycleMessageLinearBranches branches →
      ∀ alphabet : PactTypeAlphabet,
        PactType.SameCycleMessageLinear
          (parallelTypeBranchesWithin alphabet branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _ alphabet
      simp [parallelTypeBranchesWithin, PactType.SameCycleMessageLinear]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro hLinear alphabet
      simp only [PactType.SameCycleMessageLinearBranches] at hLinear
      cases rest with
      | nil =>
          simp only [parallelTypeBranchesWithin]
          exact singletonTypeXOfferAt_sameCycleMessageLinear alphabet
            (action, body) hLinear.1 hLinear.2.1
      | cons next tail =>
          simp only [parallelTypeBranchesWithin,
            PactType.SameCycleMessageLinear]
          exact ⟨singletonTypeXOfferAt_sameCycleMessageLinear alphabet
              (action, body) hLinear.1 hLinear.2.1,
            ih hLinear.2.2 alphabet⟩

/-- The branch product synchronises on nothing, so its parallel nodes ask
exactly for the branch separation a conjunctive offer already has. -/

theorem parallelTypeBranchesSelectingWithin_sameCycleMessageLinear
    (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.SameCycleMessageLinearBranches branches →
      ∀ alphabet : PactTypeAlphabet,
        PactType.SameCycleMessageLinear
          (parallelTypeBranchesSelectingWithin alphabet selected branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _ alphabet
      simp [parallelTypeBranchesSelectingWithin,
        PactType.SameCycleMessageLinear]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro hLinear alphabet
      simp only [PactType.SameCycleMessageLinearBranches] at hLinear
      cases rest with
      | nil =>
          simp only [parallelTypeBranchesSelectingWithin]
          by_cases hSel : (action, body) = selected
          · rw [if_pos hSel]
            exact selectedTypeBranchAt_sameCycleMessageLinear alphabet
              (action, body) hLinear.1 hLinear.2.1
          · rw [if_neg hSel]
            exact singletonTypeXOfferAt_sameCycleMessageLinear alphabet
              (action, body) hLinear.1 hLinear.2.1
      | cons next tail =>
          simp only [parallelTypeBranchesSelectingWithin]
          by_cases hSel : (action, body) = selected
          · rw [if_pos hSel]
            simp only [PactType.SameCycleMessageLinear]
            exact ⟨selectedTypeBranchAt_sameCycleMessageLinear alphabet
                (action, body) hLinear.1 hLinear.2.1,
              parallelTypeBranchesWithin_sameCycleMessageLinear (next :: tail)
                hLinear.2.2 alphabet⟩
          · rw [if_neg hSel]
            simp only [PactType.SameCycleMessageLinear]
            exact ⟨singletonTypeXOfferAt_sameCycleMessageLinear alphabet
                (action, body) hLinear.1 hLinear.2.1,
              ih hLinear.2.2 alphabet⟩

/-- The committed product: the selected branch becomes a sequence, the rest
stay singleton offers, and the parallel nodes again synchronise on nothing. -/

theorem parallelTypeBranchesSelecting_sameCycleMessageLinear
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hLinear : PactType.SameCycleMessageLinearBranches branches) :
    PactType.SameCycleMessageLinear
      (parallelTypeBranchesSelecting alphabet selected branches) := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting,
      PactType.SameCycleMessageLinear]
  | cons branch rest =>
      simp only [parallelTypeBranchesSelecting]
      exact parallelTypeBranchesSelectingWithin_sameCycleMessageLinear selected
        (branch :: rest) hLinear alphabet

/-! ### `TypeWF_Γ` for an offer's default and generated children -/

theorem parallelTypeBranchesWithin_conjunctiveMessageOwnership :
    ∀ (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet),
      PactType.ConjunctiveMessageOwnershipBranches branches →
      PactType.ConjunctiveMessageOwnership
        (parallelTypeBranchesWithin alphabet branches) := by
  intro branches
  induction branches with
  | nil =>
      intro alphabet _
      simp [parallelTypeBranchesWithin, PactType.ConjunctiveMessageOwnership]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro alphabet hConj
      simp only [PactType.ConjunctiveMessageOwnershipBranches] at hConj
      have hBody : PactType.ConjunctiveMessageOwnership
          (body.reannotate alphabet) :=
        (PactType.reannotate_conjunctiveMessageOwnership body alphabet).mpr
          hConj.1
      cases rest with
      | nil =>
          simp only [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.ConjunctiveMessageOwnership,
            PactType.ConjunctiveMessageOwnershipBodies]
          exact ⟨trivial, hBody, trivial⟩
      | cons next tail =>
          simp only [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.ConjunctiveMessageOwnership,
            PactType.ConjunctiveMessageOwnershipBodies]
          exact ⟨⟨trivial, hBody, trivial⟩, ih alphabet hConj.2.2⟩

theorem parallelTypeBranchesSelectingWithin_conjunctiveMessageOwnership
    (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet),
      PactType.ConjunctiveMessageOwnershipBranches branches →
      PactType.ConjunctiveMessageOwnership
        (parallelTypeBranchesSelectingWithin alphabet selected branches) := by
  intro branches
  induction branches with
  | nil =>
      intro alphabet _
      simp [parallelTypeBranchesSelectingWithin,
        PactType.ConjunctiveMessageOwnership]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro alphabet hConj
      simp only [PactType.ConjunctiveMessageOwnershipBranches] at hConj
      have hBody : PactType.ConjunctiveMessageOwnership
          (body.reannotate alphabet) :=
        (PactType.reannotate_conjunctiveMessageOwnership body alphabet).mpr
          hConj.1
      cases rest with
      | nil =>
          by_cases hSel : (action, body) = selected
          · rw [parallelTypeBranchesSelectingWithin, if_pos hSel]
            simp only [selectedTypeBranchAt,
              PactType.ConjunctiveMessageOwnership]
            exact ⟨trivial, hBody⟩
          · rw [parallelTypeBranchesSelectingWithin, if_neg hSel]
            simp only [singletonTypeXOfferAt,
              PactType.ConjunctiveMessageOwnership,
              PactType.ConjunctiveMessageOwnershipBodies]
            exact ⟨trivial, hBody, trivial⟩
      | cons next tail =>
          by_cases hSel : (action, body) = selected
          · rw [parallelTypeBranchesSelectingWithin, if_pos hSel]
            simp only [selectedTypeBranchAt,
              PactType.ConjunctiveMessageOwnership]
            · exact ⟨⟨trivial, hBody⟩,
                parallelTypeBranchesWithin_conjunctiveMessageOwnership
                  (next :: tail) alphabet hConj.2.2⟩
            · exact List.cons_ne_nil _ _
          · rw [parallelTypeBranchesSelectingWithin, if_neg hSel]
            simp only [singletonTypeXOfferAt,
              PactType.ConjunctiveMessageOwnership,
              PactType.ConjunctiveMessageOwnershipBodies]
            · exact ⟨⟨trivial, hBody, trivial⟩, ih alphabet hConj.2.2⟩
            · exact List.cons_ne_nil _ _

theorem parallelTypeBranchesSelecting_conjunctiveMessageOwnership
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hConj : PactType.ConjunctiveMessageOwnershipBranches branches) :
    PactType.ConjunctiveMessageOwnership
      (parallelTypeBranchesSelecting alphabet selected branches) := by
  cases branches with
  | nil =>
      simp [parallelTypeBranchesSelecting,
        PactType.ConjunctiveMessageOwnership]
  | cons head tail =>
      simp only [parallelTypeBranchesSelecting]
      exact parallelTypeBranchesSelectingWithin_conjunctiveMessageOwnership
        selected (head :: tail) alphabet hConj

private lemma tailBranchOccurrences_of_mem {name : String}
    {branches : List (BareMessage × PactType)}
    (h : PactType.TailBranchOccurrences name False branches) :
    ∀ branch ∈ branches, branch.2.TailOccurrences name False := by
  induction branches with
  | nil => intro branch hMem; cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      simp only [PactType.TailBranchOccurrences] at h
      intro branch hMem
      simp only [List.mem_cons] at hMem
      rcases hMem with rfl | hTail
      · exact h.1
      · exact ih h.2 branch hTail

private lemma branchesGeneratedChildConjuncts {bound : List String}
    (branches : List (BareMessage × PactType))
    (hBound : PactType.AllBranchVariablesBound bound branches)
    (hHyg : PactType.BinderHygienicBranches bound branches)
    (hScope : PactType.InterfaceScopedBranches branches)
    (hProg : PactType.ProgressLinearBranches branches)
    (hFair : PactType.FairChoiceLinearBranches branches)
    (hMsgOwn : PactType.ParallelMessageOwnershipBranches branches)
    (hProgOwn : PactType.ParallelProgressOwnershipBranches branches)
    (hFairOwn : PactType.ParallelFairChoiceOwnershipBranches branches) :
    ∀ b ∈ branches, GeneratedChildConjuncts bound b.2 := by
  induction branches with
  | nil => intro b hMem; cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      simp only [PactType.AllBranchVariablesBound] at hBound
      simp only [PactType.BinderHygienicBranches] at hHyg
      simp only [PactType.InterfaceScopedBranches] at hScope
      simp only [PactType.ProgressLinearBranches] at hProg
      simp only [PactType.FairChoiceLinearBranches] at hFair
      simp only [PactType.ParallelMessageOwnershipBranches] at hMsgOwn
      simp only [PactType.ParallelProgressOwnershipBranches] at hProgOwn
      simp only [PactType.ParallelFairChoiceOwnershipBranches] at hFairOwn
      intro b hMem
      simp only [List.mem_cons] at hMem
      rcases hMem with rfl | hTail
      · exact ⟨hBound.1, hHyg.1, hScope.1, hProg.1, hFair.1, hMsgOwn.1,
          hProgOwn.1, hFairOwn.1⟩
      · exact ih hBound.2 hHyg.2 hScope.2 hProg.2.2 hFair.2.2 hMsgOwn.2.2.2
          hProgOwn.2.2 hFairOwn.2.2 b hTail

/-- The committed offer inherits conjunctive ownership from the offer. -/

theorem typeWellFormedIn_nil_of_admissible {processType : PactType}
    (hAdmissible : AdmissibleType processType) :
    TypeWellFormedIn [] processType := by
  obtain ⟨hAlphabet, hProgress, hFair, hBound, hHygienic, hClock, hTail,
    hLinear, hMsgOwn, hScoped⟩ := hAdmissible
  exact ⟨hAlphabet, hBound, hHygienic,
    PactType.tailClosed_of_allVariablesBound_nil hBound, hClock, hTail,
    hLinear, hProgress, hFair, hMsgOwn,
    parallelProgressOwnership_of_progressLinear processType hProgress,
    parallelFairChoiceOwnership_of_fairChoiceLinear processType hFair,
    hScoped⟩

lemma typeWellFormedIn_xoffer {bound : List String}
    {alphabet : PactTypeAlphabet} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    (h : TypeWellFormedIn bound (.xoffer alphabet elseType branches)) :
    TypeWellFormedIn bound elseType ∧
      ∀ entry ∈ branches, TypeWellFormedIn bound entry.2 := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO⟩ := h
  simp only [PactType.AlphabetWellFormed] at hA
  simp only [PactType.AllVariablesBound] at hB
  simp only [PactType.BinderHygienic] at hH
  simp only [PactType.ClockGuarded] at hCG
  simp only [PactType.TailRecursive] at hTR
  simp only [PactType.SameCycleMessageLinear] at hSC
  simp only [PactType.ProgressLinear] at hPL
  simp only [PactType.FairChoiceLinear] at hFL
  simp only [PactType.ParallelMessageOwnership] at hMO
  simp only [PactType.ParallelProgressOwnership] at hPO
  simp only [PactType.ParallelFairChoiceOwnership] at hFO
  simp only [PactType.InterfaceScoped] at hIS
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  simp only [PactType.ConjunctiveMessageOwnership] at hCMO
  have hTCsplit : ∀ other : String,
      PactType.TailOccurrences other True elseType ∧
        PactType.TailBranchOccurrences other True branches := by
    intro other
    simpa only [PactType.TailOccurrences] using hTC other
  have hBranchAlphabet : ∀ entry ∈ branches,
      PactType.AlphabetWellFormed entry.2 := by
    have hAux : ∀ list : List (BareMessage × PactType),
        PactType.BranchesAlphabetWellFormed alphabet list →
        ∀ entry ∈ list, PactType.AlphabetWellFormed entry.2 := by
      intro list
      induction list with
      | nil => intro _ entry hEntry; cases hEntry
      | cons head tail ihList =>
          rcases head with ⟨headAction, headType⟩
          intro hList entry hEntry
          simp only [PactType.BranchesAlphabetWellFormed] at hList
          simp only [List.mem_cons] at hEntry
          rcases hEntry with rfl | hTail
          · exact hList.2.1
          · exact ihList hList.2.2 entry hTail
    exact hAux branches hA.2.2.2
  have hBranchOwnership : ∀ entry ∈ branches,
      PactType.ParallelMessageOwnership entry.2 := by
    have hAux : ∀ list : List (BareMessage × PactType),
        PactType.ParallelMessageOwnershipBodies list →
        ∀ entry ∈ list, PactType.ParallelMessageOwnership entry.2 := by
      intro list
      induction list with
      | nil => intro _ entry hEntry; cases hEntry
      | cons head tail ihList =>
          rcases head with ⟨headAction, headType⟩
          intro hList entry hEntry
          simp only [PactType.ParallelMessageOwnershipBodies] at hList
          simp only [List.mem_cons] at hEntry
          rcases hEntry with rfl | hTail
          · exact hList.1
          · exact ihList hList.2 entry hTail
    exact hAux branches hMO.2
  have hBranchConjunctive : ∀ entry ∈ branches,
      PactType.ConjunctiveMessageOwnership entry.2 := by
    have hAux : ∀ list : List (BareMessage × PactType),
        PactType.ConjunctiveMessageOwnershipBodies list →
        ∀ entry ∈ list, PactType.ConjunctiveMessageOwnership entry.2 := by
      intro list
      induction list with
      | nil => intro _ entry hEntry; cases hEntry
      | cons head tail ihList =>
          rcases head with ⟨headAction, headType⟩
          intro hList entry hEntry
          simp only [PactType.ConjunctiveMessageOwnershipBodies] at hList
          simp only [List.mem_cons] at hEntry
          rcases hEntry with rfl | hTail
          · exact hList.1
          · exact ihList hList.2 entry hTail
    exact hAux branches hCMO.2
  exact ⟨⟨hA.2.2.1, hB.1, hH.1, fun other => (hTCsplit other).1, hCG.1, hTR.1,
      hSC.1, hPL.1, hFL.1, hMO.1, hPO.1, hFO.1, hIS.1, hIAS.2.1, hCMO.1⟩,
    branchesWellFormedIn_of_conjuncts branches hBranchAlphabet hB.2 hH.2
      (fun other => (hTCsplit other).2) hCG.2 hTR.2 hSC.2.1 hPL.2.1 hFL.2.1
      hBranchOwnership hPO.2 hFO.2 hIS.2 hIAS.2.2 hBranchConjunctive⟩

/-! ### Same-cycle completion at the base fragments

These five are `helper_h14_same_cycle_completion`'s own base cases, restated
as standalone lemmas so that the simultaneous induction can use them without
re-entering that theorem's `sizeOf` induction. -/

lemma typeWellFormedIn_choice {bound : List String}
    {alphabet : PactTypeAlphabet} {left right : PactType}
    (h : TypeWellFormedIn bound (.choice alphabet left right)) :
    TypeWellFormedIn bound left ∧ TypeWellFormedIn bound right := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO⟩ := h
  simp only [PactType.AlphabetWellFormed] at hA
  simp only [PactType.AllVariablesBound] at hB
  simp only [PactType.BinderHygienic] at hH
  simp only [PactType.ClockGuarded] at hCG
  simp only [PactType.TailRecursive] at hTR
  simp only [PactType.SameCycleMessageLinear] at hSC
  simp only [PactType.ProgressLinear] at hPL
  simp only [PactType.FairChoiceLinear] at hFL
  simp only [PactType.ParallelMessageOwnership] at hMO
  simp only [PactType.ParallelProgressOwnership] at hPO
  simp only [PactType.ParallelFairChoiceOwnership] at hFO
  simp only [PactType.InterfaceScoped] at hIS
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  simp only [PactType.ConjunctiveMessageOwnership] at hCMO
  have hSplit : ∀ other : String,
      PactType.TailOccurrences other True left ∧
        PactType.TailOccurrences other True right := by
    intro other
    simpa only [PactType.TailOccurrences] using hTC other
  have hLeftClosed : left.TailClosed := fun other => (hSplit other).1
  have hRightClosed : right.TailClosed := fun other => (hSplit other).2
  exact ⟨⟨hA.2.2.2.1, hB.1, hH.1, hLeftClosed,
      hCG.1, hTR.1, hSC.1, hPL.1, hFL.1, hMO.1, hPO.1, hFO.1, hIS.1,
      hIAS.2.1, hCMO.1⟩,
    ⟨hA.2.2.2.2, hB.2, hH.2, hRightClosed,
      hCG.2, hTR.2, hSC.2, hPL.2.1, hFL.2.1, hMO.2, hPO.2, hFO.2, hIS.2,
      hIAS.2.2, hCMO.2⟩⟩

lemma typeWellFormedIn_fairChoice {bound : List String}
    {alphabet : PactTypeAlphabet} {bid : BranchId} {left right : PactType}
    (h : TypeWellFormedIn bound (.fairChoice alphabet bid left right)) :
    TypeWellFormedIn bound left ∧ TypeWellFormedIn bound right := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO⟩ := h
  simp only [PactType.AlphabetWellFormed] at hA
  simp only [PactType.AllVariablesBound] at hB
  simp only [PactType.BinderHygienic] at hH
  simp only [PactType.ClockGuarded] at hCG
  simp only [PactType.TailRecursive] at hTR
  simp only [PactType.SameCycleMessageLinear] at hSC
  simp only [PactType.ProgressLinear] at hPL
  simp only [PactType.FairChoiceLinear] at hFL
  simp only [PactType.ParallelMessageOwnership] at hMO
  simp only [PactType.ParallelProgressOwnership] at hPO
  simp only [PactType.ParallelFairChoiceOwnership] at hFO
  simp only [PactType.InterfaceScoped] at hIS
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  simp only [PactType.ConjunctiveMessageOwnership] at hCMO
  have hSplit : ∀ other : String,
      PactType.TailOccurrences other True left ∧
        PactType.TailOccurrences other True right := by
    intro other
    simpa only [PactType.TailOccurrences] using hTC other
  have hLeftClosed : left.TailClosed := fun other => (hSplit other).1
  have hRightClosed : right.TailClosed := fun other => (hSplit other).2
  exact ⟨⟨hA.2.2.2.1, hB.1, hH.1, hLeftClosed,
      hCG.1, hTR.1, hSC.1, hPL.1, hFL.1, hMO.1, hPO.1, hFO.1, hIS.1,
      hIAS.2.1, hCMO.1⟩,
    ⟨hA.2.2.2.2, hB.2, hH.2, hRightClosed,
      hCG.2, hTR.2, hSC.2, hPL.2.1, hFL.2.1, hMO.2, hPO.2, hFO.2, hIS.2,
      hIAS.2.2, hCMO.2⟩⟩

lemma typeWellFormedIn_seq {bound : List String}
    {alphabet : PactTypeAlphabet} {left right : PactType}
    (h : TypeWellFormedIn bound (.seq alphabet left right)) :
    TypeWellFormedIn bound left ∧ TypeWellFormedIn bound right := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO⟩ := h
  simp only [PactType.AlphabetWellFormed] at hA
  simp only [PactType.AllVariablesBound] at hB
  simp only [PactType.BinderHygienic] at hH
  simp only [PactType.ClockGuarded] at hCG
  simp only [PactType.TailRecursive] at hTR
  simp only [PactType.SameCycleMessageLinear] at hSC
  simp only [PactType.ProgressLinear] at hPL
  simp only [PactType.FairChoiceLinear] at hFL
  simp only [PactType.ParallelMessageOwnership] at hMO
  simp only [PactType.ParallelProgressOwnership] at hPO
  simp only [PactType.ParallelFairChoiceOwnership] at hFO
  simp only [PactType.InterfaceScoped] at hIS
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  simp only [PactType.ConjunctiveMessageOwnership] at hCMO
  have hSplit : ∀ other : String,
      PactType.TailOccurrences other False left ∧
        PactType.TailOccurrences other True right := by
    intro other
    simpa only [PactType.TailOccurrences] using hTC other
  have hLeftClosed : left.TailClosed := fun other =>
    PactType.tailOccurrences_mono other False.elim left (hSplit other).1
  have hRightClosed : right.TailClosed := fun other => (hSplit other).2
  exact ⟨⟨hA.2.2.2.1, hB.1, hH.1, hLeftClosed, hCG.1, hTR.1, hSC.1, hPL.1,
      hFL.1, hMO.1, hPO.1, hFO.1, hIS.1, hIAS.2.1, hCMO.1⟩,
    ⟨hA.2.2.2.2, hB.2, hH.2, hRightClosed,
      hCG.2, hTR.2, hSC.2.1, hPL.2.1, hFL.2.1, hMO.2, hPO.2, hFO.2, hIS.2,
      hIAS.2.2, hCMO.2⟩⟩

lemma typeWellFormedIn_par {bound : List String}
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    (h : TypeWellFormedIn bound (.par alphabet left right interface)) :
    TypeWellFormedIn bound left ∧ TypeWellFormedIn bound right := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO⟩ := h
  simp only [PactType.AlphabetWellFormed] at hA
  simp only [PactType.AllVariablesBound] at hB
  simp only [PactType.BinderHygienic] at hH
  simp only [PactType.ClockGuarded] at hCG
  simp only [PactType.TailRecursive] at hTR
  simp only [PactType.SameCycleMessageLinear] at hSC
  simp only [PactType.ProgressLinear] at hPL
  simp only [PactType.FairChoiceLinear] at hFL
  simp only [PactType.ParallelMessageOwnership] at hMO
  simp only [PactType.ParallelProgressOwnership] at hPO
  simp only [PactType.ParallelFairChoiceOwnership] at hFO
  simp only [PactType.InterfaceScoped] at hIS
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  simp only [PactType.ConjunctiveMessageOwnership] at hCMO
  have hSplit : ∀ other : String,
      PactType.TailOccurrences other False left ∧
        PactType.TailOccurrences other False right := by
    intro other
    simpa only [PactType.TailOccurrences] using hTC other
  have hLeftClosed : left.TailClosed := fun other =>
    PactType.tailOccurrences_mono other False.elim left (hSplit other).1
  have hRightClosed : right.TailClosed := fun other =>
    PactType.tailOccurrences_mono other False.elim right (hSplit other).2
  exact ⟨⟨hA.2.2.1, hB.1, hH.1, hLeftClosed, hCG.1, hTR.1, hSC.1, hPL.1, hFL.1,
      hMO.2.1, hPO.2.1, hFO.2.1, hIS.2.1, hIAS.2.1, hCMO.1⟩,
    ⟨hA.2.2.2, hB.2, hH.2, hRightClosed, hCG.2, hTR.2, hSC.2, hPL.2.1, hFL.2.1,
      hMO.2.2, hPO.2.2, hFO.2.2, hIS.2.2, hIAS.2.2, hCMO.2⟩⟩

lemma typeWellFormedIn_recur {bound : List String}
    {alphabet : PactTypeAlphabet} {name : String} {body : PactType}
    (h : TypeWellFormedIn bound (.recur alphabet name body)) :
    TypeWellFormedIn (name :: bound) body := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO⟩ := h
  simp only [PactType.AlphabetWellFormed] at hA
  simp only [PactType.AllVariablesBound] at hB
  simp only [PactType.BinderHygienic] at hH
  simp only [PactType.ClockGuarded] at hCG
  simp only [PactType.TailRecursive] at hTR
  simp only [PactType.SameCycleMessageLinear] at hSC
  simp only [PactType.ProgressLinear] at hPL
  simp only [PactType.FairChoiceLinear] at hFL
  simp only [PactType.ParallelMessageOwnership] at hMO
  simp only [PactType.ParallelProgressOwnership] at hPO
  simp only [PactType.ParallelFairChoiceOwnership] at hFO
  simp only [PactType.InterfaceScoped] at hIS
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  simp only [PactType.ConjunctiveMessageOwnership] at hCMO
  have hBodyClosed : body.TailClosed := by
    intro other
    by_cases hName : name = other
    · subst hName; exact hTR.1
    · have hOther := hTC other
      simpa only [PactType.TailOccurrences, if_neg hName] using hOther
  exact ⟨hA.2.2, hB, hH.2, hBodyClosed, hCG.2, hTR.2, hSC.1, hPL, hFL, hMO,
    hPO, hFO, hIS, hIAS.2, hCMO⟩

/-! ### Re-signing preserves the structural well-formedness conjuncts

`reannotate` rewrites alphabet annotations and leaves every constructor, every
binder name and every declared identifier in place, so each conjunct of
`TypeWF_Γ` that is not itself about alphabets transfers. -/

/-- A surviving parallel component, re-signed by the node's own alphabet, is
well formed in the same binder context.  The node alphabet declares none of the
interfaces inside either component, which is what makes the re-signing
alphabet-correct. -/

lemma typeWellFormedIn_survivor {bound : List String}
    {alphabet : PactTypeAlphabet} {left right : PactType}
    {interface : Interface}
    (h : TypeWellFormedIn bound (.par alphabet left right interface)) :
    TypeWellFormedIn bound (left.reannotate alphabet) ∧
      TypeWellFormedIn bound (right.reannotate alphabet) := by
  obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_par h
  obtain ⟨hA, -, -, -, -, -, -, -, -, -, -, -, -, hIAS, -⟩ := h
  have hAlphaWF : alphabet.WellFormed := by
    simp only [PactType.AlphabetWellFormed] at hA
    exact hA.1
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  have hAvoid : ∀ (child : PactType),
      PactType.ParallelInterfaces child ⊆
        interface ∪ PactType.ParallelInterfaces left ∪
          PactType.ParallelInterfaces right →
      ∀ action ∈ alphabet.actions,
        action.1 ∉ PactType.ParallelInterfaces child := by
    intro child hSub action hAction hIn
    exact Finset.disjoint_left.mp hIAS.1
      (Finset.mem_image.mpr ⟨action, hAction, rfl⟩) (hSub hIn)
  have hLeftAvoid := hAvoid left
    (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)
  have hRightAvoid := hAvoid right Finset.subset_union_right
  refine ⟨?_, ?_⟩
  · obtain ⟨gA, gB, gH, gTC, gCG, gTR, gSC, gPL, gFL, gMO, gPO, gFO, gIS,
      gIAS⟩ := hLeftWF
    have hOwn := PactType.reannotate_ownership_data alphabet left
    exact ⟨PactType.reannotate_alphabetWellFormed_avoiding left alphabet gA
        hAlphaWF gIS hLeftAvoid,
      PactType.reannotate_allVariablesBound bound left alphabet gB,
      PactType.reannotate_binderHygienic bound left alphabet gH,
      fun other => PactType.reannotate_tailOccurrences other left alphabet True
        (gTC other),
      PactType.reannotate_clockGuarded left alphabet gCG,
      PactType.reannotate_tailRecursive left alphabet gTR,
      PactType.reannotate_sameCycleMessageLinear left alphabet gSC,
      PactType.reannotate_progressLinear left alphabet gPL,
      PactType.reannotate_fairChoiceLinear left alphabet gFL,
      hOwn.2.2.2.2.1.mpr gMO, hOwn.2.2.2.2.2.1.mpr gPO,
      hOwn.2.2.2.2.2.2.mpr gFO,
      PactType.reannotate_interfaceScoped left alphabet gIS,
      PactType.reannotate_interfaceAlphabetScoped left alphabet gIAS.1
        hLeftAvoid,
      (PactType.reannotate_conjunctiveMessageOwnership left alphabet).mpr
        gIAS.2⟩
  · obtain ⟨gA, gB, gH, gTC, gCG, gTR, gSC, gPL, gFL, gMO, gPO, gFO, gIS,
      gIAS⟩ := hRightWF
    have hOwn := PactType.reannotate_ownership_data alphabet right
    exact ⟨PactType.reannotate_alphabetWellFormed_avoiding right alphabet gA
        hAlphaWF gIS hRightAvoid,
      PactType.reannotate_allVariablesBound bound right alphabet gB,
      PactType.reannotate_binderHygienic bound right alphabet gH,
      fun other => PactType.reannotate_tailOccurrences other right alphabet True
        (gTC other),
      PactType.reannotate_clockGuarded right alphabet gCG,
      PactType.reannotate_tailRecursive right alphabet gTR,
      PactType.reannotate_sameCycleMessageLinear right alphabet gSC,
      PactType.reannotate_progressLinear right alphabet gPL,
      PactType.reannotate_fairChoiceLinear right alphabet gFL,
      hOwn.2.2.2.2.1.mpr gMO, hOwn.2.2.2.2.2.1.mpr gPO,
      hOwn.2.2.2.2.2.2.mpr gFO,
      PactType.reannotate_interfaceScoped right alphabet gIS,
      PactType.reannotate_interfaceAlphabetScoped right alphabet gIAS.1
        hRightAvoid,
      (PactType.reannotate_conjunctiveMessageOwnership right alphabet).mpr
        gIAS.2⟩

/-- The paper's `<compiler-call-decrease>` at a conjunctive offer: the default
continuation and every generated child are well formed in the same context. -/

theorem typeWellFormedIn_offer {bound : List String}
    {alphabet : PactTypeAlphabet} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    (h : TypeWellFormedIn bound (.offer alphabet elseType branches)) :
    TypeWellFormedIn bound elseType ∧
      ∀ selected ∈ branches,
        TypeWellFormedIn bound
          (parallelTypeBranchesSelecting alphabet selected branches) := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO⟩ := h
  have hAoffer := hA
  have hISoffer := hIS
  have hIASoffer := hIAS
  simp only [PactType.AlphabetWellFormed] at hA
  simp only [PactType.AllVariablesBound] at hB
  simp only [PactType.BinderHygienic] at hH
  simp only [PactType.ClockGuarded] at hCG
  simp only [PactType.TailRecursive] at hTR
  simp only [PactType.SameCycleMessageLinear] at hSC
  simp only [PactType.ProgressLinear] at hPL
  simp only [PactType.FairChoiceLinear] at hFL
  simp only [PactType.ParallelMessageOwnership] at hMO
  simp only [PactType.ParallelProgressOwnership] at hPO
  simp only [PactType.ParallelFairChoiceOwnership] at hFO
  simp only [PactType.InterfaceScoped] at hIS
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  simp only [PactType.ConjunctiveMessageOwnership] at hCMO
  have hBundle := PactType.parallelMessageOwnershipBranches_of_conjuncts
    branches hMO.2 hCMO.2
  have hTCsplit : ∀ other : String,
      PactType.TailOccurrences other True elseType ∧
        PactType.TailBranchOccurrences other False branches := by
    intro other
    simpa only [PactType.TailOccurrences] using hTC other
  have hPairwise : List.Pairwise BranchDeclarationsDisjoint branches :=
    branchDeclarationsDisjoint_pairwise branches hBundle hPO.2 hFO.2
  have hConj := branchesGeneratedChildConjuncts (bound := bound) branches
    hB.2 hH.2 hIS.2 hPL.2.1 hFL.2.1 hBundle hPO.2 hFO.2
  refine ⟨⟨hA.2.2.1, hB.1, hH.1, fun other => (hTCsplit other).1, hCG.1, hTR.1,
      hSC.1, hPL.1, hFL.1, hMO.1, hPO.1, hFO.1, hIS.1, hIAS.2.1,
      hCMO.1⟩, ?_⟩
  intro selected hSelected
  obtain ⟨gB, gH, gS, gP, gF, gM, gPo, gFo⟩ :=
    parallelTypeBranchesSelecting_conjuncts (bound := bound) alphabet selected
      branches hConj hPL.2.1 hFL.2.1 hBundle hPO.2 hFO.2
  have hBranchTailRec : ∀ branch ∈ branches, branch.2.TailRecursive := by
    intro branch hMem
    exact tailRecursive_of_mem_branches hTR.2 hMem
  have hBranchClock : ∀ branch ∈ branches, branch.2.ClockGuarded := by
    have hAux : ∀ list : List (BareMessage × PactType),
        PactType.ClockGuardedBranches list →
        ∀ branch ∈ list, branch.2.ClockGuarded := by
      intro list
      induction list with
      | nil => intro _ branch hMem; cases hMem
      | cons hd tl ihList =>
          rcases hd with ⟨a, t⟩
          intro hList branch hMem
          simp only [PactType.ClockGuardedBranches] at hList
          simp only [List.mem_cons] at hMem
          rcases hMem with rfl | hTail
          · exact hList.1
          · exact ihList hList.2 branch hTail
    exact hAux branches hCG.2
  have hBranchLinear : PactType.SameCycleMessageLinearBranches branches :=
    hSC.2.1
  exact ⟨committedOffer_alphabetWellFormed alphabet elseType branches selected
      hAoffer hISoffer hIASoffer hSelected,
    gB, gH,
    fun other => parallelTypeBranchesSelecting_tailOccurrences other alphabet
      selected branches True
      (tailBranchOccurrences_of_mem (hTCsplit other).2)
      (tailBranchOccurrences_of_mem (hTCsplit other).2 selected hSelected),
    parallelTypeBranchesSelecting_clockGuarded alphabet selected branches
      hBranchClock (hBranchClock selected hSelected),
    parallelTypeBranchesSelecting_tailRecursive alphabet selected branches
      hBranchTailRec (hBranchTailRec selected hSelected),
    parallelTypeBranchesSelecting_sameCycleMessageLinear alphabet selected
      branches hBranchLinear,
    gP, gF, gM, gPo, gFo, gS,
    parallelTypeBranchesSelecting_interfaceAlphabetScoped alphabet selected
      branches hIAS.2.2
      (fun action hAction hIn =>
        Finset.disjoint_left.mp hIAS.1
          (Finset.mem_image.mpr ⟨action, hAction, rfl⟩)
          (Finset.mem_union_right _ hIn)),
    parallelTypeBranchesSelecting_conjunctiveMessageOwnership alphabet selected
      branches hCMO.2⟩

end

end Pact
