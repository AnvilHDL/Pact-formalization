import Anvilpp.ProofHelpers.Inference.LiftingPrelude

/-!
# Selecting the parallel rule

The paper's *Parallel* phase: a lifted component step need not reach the target
recorded in the abstract derivation, so the concrete parent rule is chosen from
the concrete sources and targets.  All four rules publish the hidden union of
the component pairs, with `(∅,∅)` on a finished side, so the published pair does
not depend on which rule is selected.
-/

namespace Pact

noncomputable section

open Classical

/-! ## A step keeps the node alphabet -/

theorem alphabet_procExprReplace (process : Proc) (name : String) (value : Bool) :
    (Semantics.procExprReplace process name value).alphabet = process.alphabet := by
  cases process <;> rw [Semantics.procExprReplace] <;> rfl

theorem alphabet_procReplace {process replacement : Proc} (name : String)
    (hAlpha : process.alphabet = replacement.alphabet) :
    (Semantics.procReplace process name replacement).alphabet = process.alphabet := by
  cases process with
  | var alphabet other =>
      rw [Semantics.procReplace]
      by_cases hName : name = other
      · rw [if_pos hName]; exact hAlpha.symm
      · rw [if_neg hName]
  | recur alphabet other body =>
      rw [Semantics.procReplace]
      by_cases hName : name = other
      · rw [if_pos hName]
      · rw [if_neg hName]; rfl
  | _ => rw [Semantics.procReplace] <;> rfl

theorem Proc.branchesAlphabetWellFormed_of_mem {alphabet : PactTypeAlphabet}
    {branches : List ChoiceBranch} {branch : ChoiceBranch}
    (hWF : Proc.BranchesAlphabetWellFormed alphabet branches)
    (hMem : branch ∈ branches) :
    (ChoiceBranch.continuation branch).alphabet = alphabet ∧
      Proc.AlphabetWellFormed (ChoiceBranch.continuation branch) := by
  induction branches with
  | nil => exact absurd hMem (by simp)
  | cons head rest ih =>
      rw [Proc.BranchesAlphabetWellFormed] at hWF
      rcases List.mem_cons.1 hMem with rfl | hTail
      · exact ⟨hWF.1, hWF.2.1⟩
      · exact ih hWF.2.2 hTail

theorem alphabet_parallelProcessBranchesSelectingWithin
    (alphabet : PactTypeAlphabet) (selected : ChoiceBranch) :
    ∀ branches : List ChoiceBranch, branches ≠ [] →
      (parallelProcessBranchesSelectingWithin alphabet selected branches).alphabet =
        alphabet := by
  intro branches
  induction branches with
  | nil => intro h; exact absurd rfl h
  | cons head rest ih =>
      intro _
      cases rest with
      | nil =>
          rw [parallelProcessBranchesSelectingWithin]
          by_cases hEq : head = selected
          · rw [if_pos hEq]; cases head <;> rfl
          · rw [if_neg hEq]; rfl
      | cons second tail =>
          rw [parallelProcessBranchesSelectingWithin_cons_cons]
          by_cases hEq : head = selected
          · rw [if_pos hEq]; rfl
          · rw [if_neg hEq]; rfl

theorem alphabet_parallelProcessBranchesSelecting (alphabet : PactTypeAlphabet)
    (selected : ChoiceBranch) {branches : List ChoiceBranch}
    (hNonempty : branches ≠ []) :
    (parallelProcessBranchesSelecting alphabet selected branches).alphabet =
      alphabet := by
  cases branches with
  | nil => exact absurd rfl hNonempty
  | cons head rest =>
      rw [parallelProcessBranchesSelecting]
      exact alphabet_parallelProcessBranchesSelectingWithin alphabet selected _
        (by simp)

/-- A step keeps the written alphabet of its source. -/
theorem Offers.preserves_alphabet {env : Environment} {source target : Proc}
    {label : Label} {current : Finset Offer} {future : Finset BareMessage}
    (hOffers : Offers env source label target current future)
    (hWF : Proc.AlphabetWellFormed source) : target.alphabet = source.alphabet := by
  induction hOffers with
  | send _ _ _ _ _ _ _ _ => rw [Proc.AlphabetWellFormed] at hWF; exact hWF.2.1
  | send_wait _ _ _ _ _ _ _ _ => rfl
  | recv _ alphabet _ varName p value _ _ =>
      rw [Proc.AlphabetWellFormed] at hWF
      rw [alphabet_procExprReplace]; exact hWF.2.1
  | recv_wait _ _ _ _ _ _ _ => rfl
  | cycle _ _ _ => rfl
  | cycle_wait _ _ _ => rfl
  | skip _ _ _ => rfl
  | progress _ _ _ _ => rfl
  | letp _ alphabet varName expr p value _ =>
      rw [Proc.AlphabetWellFormed] at hWF
      rw [alphabet_procExprReplace]; exact hWF.2.1
  | if_true _ _ _ _ _ _ => rw [Proc.AlphabetWellFormed] at hWF; exact hWF.2.1
  | if_false _ _ _ _ _ _ => rw [Proc.AlphabetWellFormed] at hWF; exact hWF.2.2.1
  | fair_true _ _ _ _ _ _ _ => rw [Proc.AlphabetWellFormed] at hWF; exact hWF.2.1
  | fair_false _ _ _ _ _ _ _ => rw [Proc.AlphabetWellFormed] at hWF; exact hWF.2.2.1
  | recur _ alphabet varName body _ =>
      rw [Proc.AlphabetWellFormed] at hWF
      rw [alphabet_procReplace varName (by rw [hWF.2.1]; rfl)]
      exact hWF.2.1
  | seq _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  | seq_tock _ _ _ _ _ _ _ _ _ _ => rfl
  | seq_fuse _ _ _ _ _ _ _ _ _ _ _ =>
      rw [Proc.AlphabetWellFormed] at hWF; exact hWF.2.2.1
  | seq_fuse_tock _ _ _ _ _ _ _ _ _ =>
      rw [Proc.AlphabetWellFormed] at hWF; exact hWF.2.2.1
  | xoffer_send _ _ _ _ _ _ _ _ hPrem _ =>
      rw [Proc.AlphabetWellFormed] at hWF
      exact (Proc.branchesAlphabetWellFormed_of_mem hWF.2.2.2 hPrem.2.1).1
  | xoffer_recv _ _ _ _ _ _ _ _ hPrem _ =>
      rw [Proc.AlphabetWellFormed] at hWF
      rw [alphabet_procExprReplace]
      exact (Proc.branchesAlphabetWellFormed_of_mem hWF.2.2.2 hPrem.2.1).1
  | xoffer_else _ _ _ _ _ _ => rw [Proc.AlphabetWellFormed] at hWF; exact hWF.2.1
  | xoffer_wait _ _ _ _ _ _ => rfl
  | offer_some _ alphabet _ branches enabled hPrem _ =>
      exact alphabet_parallelProcessBranchesSelecting alphabet enabled
        (by rintro rfl; exact absurd hPrem.2.1 (by simp))
  | offer_else _ _ _ _ _ _ => rw [Proc.AlphabetWellFormed] at hWF; exact hWF.2.1
  | offer_wait _ _ _ _ _ _ => rfl
  | par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  | par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  | par_fuse_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact Proc.alphabet_reannotate _ _
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact Proc.alphabet_reannotate _ _

/-! ## Combining with the silent stutter -/

theorem Label.combine_silent_left (interface : Interface) (label : Label)
    (hSync : Label.Sync interface Label.silent label) :
    Label.combine interface Label.silent label = label := by
  classical
  obtain ⟨hSends, hRecvs, hTock⟩ := hSync
  cases label with
  | tock =>
      exact absurd (hTock.mpr trivial) (by simp [Label.silent, Label.isTock])
  | actions observations =>
      have hNoSends : interface ∩ (Label.actions observations).sends = ∅ := by
        rw [← hRecvs]
        simp [Label.silent, Label.recvs, Label.messageIdsWith]
      have hEmptySends : (Label.actions ∅).sends = (∅ : Finset MessageId) := by
        simp [Label.sends, Label.messageIdsWith]
      have hSynced :
          Label.synced interface (.actions ∅) (.actions observations) = ∅ := by
        show (interface ∩ (Label.actions ∅).sends) ∪
          (interface ∩ (Label.actions observations).sends) = ∅
        rw [hEmptySends, Finset.inter_empty, Finset.empty_union, hNoSends]
      have hFilter : (∅ ∪ observations).filter
          (fun observation => !(Label.isRawSyncedMessage ∅ observation)) =
          observations := by
        rw [Finset.empty_union]
        refine Finset.filter_true_of_mem ?_
        intro observation _
        cases observation <;> simp [Label.isRawSyncedMessage]
      simp only [Label.silent, Label.combine, hSynced, hFilter,
        Finset.image_empty, Finset.union_empty]

theorem Label.combine_silent_right (interface : Interface) (label : Label)
    (hSync : Label.Sync interface label Label.silent) :
    Label.combine interface label Label.silent = label := by
  classical
  obtain ⟨hSends, hRecvs, hTock⟩ := hSync
  cases label with
  | tock =>
      exact absurd (hTock.mp trivial) (by simp [Label.silent, Label.isTock])
  | actions observations =>
      have hNoSends : interface ∩ (Label.actions observations).sends = ∅ := by
        rw [hSends]
        simp [Label.silent, Label.recvs, Label.messageIdsWith]
      have hEmptySends : (Label.actions ∅).sends = (∅ : Finset MessageId) := by
        simp [Label.sends, Label.messageIdsWith]
      have hSynced :
          Label.synced interface (.actions observations) (.actions ∅) = ∅ := by
        show (interface ∩ (Label.actions observations).sends) ∪
          (interface ∩ (Label.actions ∅).sends) = ∅
        rw [hEmptySends, Finset.inter_empty, Finset.union_empty, hNoSends]
      have hFilter : observations.filter
          (fun observation => !(Label.isRawSyncedMessage ∅ observation)) =
          observations := by
        refine Finset.filter_true_of_mem ?_
        intro observation _
        cases observation <;> simp [Label.isRawSyncedMessage]
      simp only [Label.silent, Label.combine, hSynced, hFilter,
        Finset.image_empty, Finset.union_empty]

/-! ## The parent rule -/

/-- All four parallel rules publish the hidden union of the component pairs, so
the parent rule may be selected from the concrete sources and targets. -/
theorem par_lift {outer leftEnv rightEnv : Environment} {interface : Interface}
    {alphabet : PactTypeAlphabet} {left right leftTarget rightTarget : Proc}
    {leftLabel rightLabel : Label} {leftCurrent rightCurrent : Finset Offer}
    {leftFuture rightFuture : Finset BareMessage}
    (hLeftWF : Proc.AlphabetWellFormed left)
    (hRightWF : Proc.AlphabetWellFormed right)
    (hLeft : Offers leftEnv left leftLabel leftTarget leftCurrent leftFuture)
    (hRight : Offers rightEnv right rightLabel rightTarget rightCurrent rightFuture)
    (hLocalLeft : LocalOfferEnvironment outer interface left rightEnv rightCurrent
      rightFuture leftEnv)
    (hLocalRight : LocalOfferEnvironment outer interface right leftEnv leftCurrent
      leftFuture rightEnv)
    (hWF : outer.WellFormed alphabet)
    (hSync : Label.Sync interface leftLabel rightLabel)
    (hClock : outer.clock = false) :
    ∃ target, Offers outer (Proc.par alphabet left right interface)
      (Label.combine interface leftLabel rightLabel) target
      (hideOfferSet interface (leftCurrent ∪ rightCurrent))
      (hideProcOffers interface (leftFuture ∪ rightFuture)) := by
  have hLeftClock : leftEnv.clock = false := hLocalLeft.clock_false hClock
  have hRightClock : rightEnv.clock = false := hLocalRight.clock_false hClock
  have hNotTock : Label.combine interface leftLabel rightLabel ≠ Label.tock := by
    intro hAbsurd
    exact hLeft.label_ne_tock hLeftClock
      ((Label.combine_eq_tock_iff _ _ _).1 hAbsurd).1
  have hLeftAlpha := hLeft.preserves_alphabet hLeftWF
  have hRightAlpha := hRight.preserves_alphabet hRightWF
  by_cases hBoth : leftTarget = Proc.skip left.alphabet ∧
      rightTarget = Proc.skip right.alphabet
  · obtain ⟨hLeftEq, hRightEq⟩ := hBoth
    subst hLeftEq; subst hRightEq
    exact ⟨_, Offers.par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ hLeft hRight hLocalLeft
      hLocalRight ⟨hWF, hSync⟩ hNotTock⟩
  · by_cases hLeftSkip : left = Proc.skip left.alphabet
    · obtain ⟨hLabel, hTarget, hCurrent, hFuture, -⟩ :=
        Offers.skip_inversion (by rw [← hLeftSkip]; exact hLeft)
      have hTargetLeft : leftTarget = left := hTarget.trans hLeftSkip.symm
      have hRightNotSkip : right ≠ Proc.skip right.alphabet := by
        intro hAbsurd
        obtain ⟨-, hRightTarget, -, -, -⟩ :=
          Offers.skip_inversion (by rw [← hAbsurd]; exact hRight)
        exact hBoth ⟨hTarget, hRightTarget⟩
      have hRightTargetNotSkip : rightTarget ≠ Proc.skip rightTarget.alphabet := by
        rw [hRightAlpha]
        intro hAbsurd
        exact hBoth ⟨hTarget, hAbsurd⟩
      subst hLabel; subst hCurrent; subst hFuture
      have hLeftStep : Offers leftEnv left Label.silent left ∅ ∅ := hTargetLeft ▸ hLeft
      have hStep := Offers.left_complete outer leftEnv rightEnv interface alphabet
        left right rightTarget rightLabel ∅ rightCurrent ∅ rightFuture
        hLeftSkip hRightNotSkip hLeftStep hRight hRightTargetNotSkip hLocalLeft
        hLocalRight hWF hSync
      rw [Label.combine_silent_left interface rightLabel hSync, Finset.empty_union,
        Finset.empty_union]
      exact ⟨_, hStep⟩
    · by_cases hRightSkip : right = Proc.skip right.alphabet
      · obtain ⟨hLabel, hTarget, hCurrent, hFuture, -⟩ :=
          Offers.skip_inversion (by rw [← hRightSkip]; exact hRight)
        have hTargetRight : rightTarget = right := hTarget.trans hRightSkip.symm
        have hLeftTargetNotSkip : leftTarget ≠ Proc.skip leftTarget.alphabet := by
          rw [hLeftAlpha]
          intro hAbsurd
          exact hBoth ⟨hAbsurd, hTarget⟩
        subst hLabel; subst hCurrent; subst hFuture
        have hRightStep : Offers rightEnv right Label.silent right ∅ ∅ :=
          hTargetRight ▸ hRight
        have hStep := Offers.right_complete outer leftEnv rightEnv interface
          alphabet left leftTarget right leftLabel leftCurrent ∅ leftFuture ∅
          hRightSkip hLeftSkip hRightStep hLeft hLeftTargetNotSkip hLocalLeft
          hLocalRight hWF hSync
        rw [Label.combine_silent_right interface leftLabel hSync,
          Finset.union_empty, Finset.union_empty]
        exact ⟨_, hStep⟩
      · have hNotBoth : ¬ (leftTarget = Proc.skip leftTarget.alphabet ∧
            rightTarget = Proc.skip rightTarget.alphabet) := by
          rintro ⟨hLeftEq, hRightEq⟩
          rw [hLeftAlpha] at hLeftEq
          rw [hRightAlpha] at hRightEq
          exact hBoth ⟨hLeftEq, hRightEq⟩
        have hStep := Offers.par outer leftEnv rightEnv interface alphabet left
          leftTarget right rightTarget leftLabel rightLabel leftCurrent
          rightCurrent leftFuture rightFuture hLeftSkip hRightSkip hLeft hRight
          hNotBoth hLocalLeft hLocalRight ⟨hWF, hSync⟩
        rw [if_neg hNotTock] at hStep
        exact ⟨_, hStep⟩

end

end Pact
