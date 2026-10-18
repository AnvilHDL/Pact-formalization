import Anvilpp.ProofHelpers.WeakRefinementStrategies

namespace Pact.WeakRefinement.OfferDelay

noncomputable section

open Classical

def leftAlphabet : PactTypeAlphabet := ⟨{("d", .send), ("e", .send)}⟩
def rightAlphabet : PactTypeAlphabet := ⟨{("d", .recv), ("e", .recv)}⟩
def receiverAlphabet : PactTypeAlphabet :=
  ⟨{("d", .recv), ("e", .recv), ("c", .recv)}⟩
def offerAlphabet : PactTypeAlphabet :=
  ⟨{("d", .recv), ("e", .recv), ("c", .send)}⟩
def boundary : Interface := {"d", "e"}

def clockLoop (alphabet : PactTypeAlphabet) : PactType :=
  .recur alphabet "X" (.seq alphabet (.tock alphabet) (.var alphabet "X"))

def exclusive : PactType :=
  .xoffer leftAlphabet (.message leftAlphabet "e" .send)
    [(("d", .send), .skip leftAlphabet)]

def receiver : PactType :=
  .seq receiverAlphabet (.message receiverAlphabet "c" .recv) (clockLoop receiverAlphabet)

def branches : List (BareMessage × PactType) :=
  [(("c", .send), .skip offerAlphabet), (("d", .recv), .skip offerAlphabet)]

def conjunctive : PactType := .offer offerAlphabet (.skip offerAlphabet) branches

def rightSide : PactType :=
  .par rightAlphabet (skipPrefix receiver) conjunctive {"c"}

def original : PactType := .par .empty exclusive rightSide boundary
def delayed : PactType := .par .empty (skipPrefix exclusive) rightSide boundary

def selectedC : PactType :=
  parallelTypeBranchesSelecting offerAlphabet (("c", .send), .skip offerAlphabet) branches
def selectedD : PactType :=
  parallelTypeBranchesSelecting offerAlphabet (("d", .recv), .skip offerAlphabet) branches

private theorem alphabets :
    leftAlphabet.WellFormed ∧ rightAlphabet.WellFormed ∧
      receiverAlphabet.WellFormed ∧ offerAlphabet.WellFormed ∧
      PactTypeAlphabet.ParallelCompatible .empty leftAlphabet rightAlphabet boundary ∧
      PactTypeAlphabet.ParallelCompatible rightAlphabet receiverAlphabet offerAlphabet {"c"} := by
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    simp [PactTypeAlphabet.WellFormed, PactTypeAlphabet.OnePolarity,
      leftAlphabet, rightAlphabet, receiverAlphabet, offerAlphabet,
      PactTypeAlphabet.ComplementaryOn, PactTypeAlphabet.hideInterface,
      PactTypeAlphabet.empty, boundary, Finset.filter_insert, Finset.filter_singleton]

/-- Both products satisfy the alphabet, ownership, recursion, and menu-separation conditions. -/
theorem wellFormed : TypeWellFormedIn [] original ∧ TypeWellFormedIn [] delayed := by
  have hAlphabets := alphabets
  simp_all [TypeWellFormedIn, original, delayed, rightSide, exclusive, receiver,
    conjunctive, branches, clockLoop, skipPrefix, boundary,
    PactType.AlphabetWellFormed, PactType.BranchesAlphabetWellFormed,
    PactType.OfferBranchesWellFormed, PactType.alphabet,
    PactType.AllVariablesBound, PactType.AllBranchVariablesBound,
    PactType.BinderHygienic, PactType.BinderHygienicBranches,
    PactType.TailClosed, PactType.TailOccurrences, PactType.TailBranchOccurrences,
    PactType.ClockGuarded, PactType.ClockGuardedBranches,
    PactType.GuardedOccurrences, PactType.MustTockBeforeCompletion,
    PactType.TailRecursive, PactType.TailRecursiveBranches,
    PactType.SameCycleMessageLinear, PactType.SameCycleMessageLinearBranches,
    PactType.PrefixMessageIds, PactType.BranchPrefixMessageIds,
    PactType.SuffixMessageIds,
    PactType.ProgressLinear, PactType.ProgressLinearBranches, PactType.ProgressIds,
    PactType.BranchProgressIds, PactType.FairChoiceLinear, PactType.FairChoiceLinearBranches,
    PactType.FairChoiceIds, PactType.BranchFairChoiceIds,
    PactType.ParallelMessageOwnership, PactType.ParallelMessageOwnershipBodies,
    PactType.MessageIds, PactType.BranchMessageIds,
    PactType.ParallelProgressOwnership, PactType.ParallelProgressOwnershipBranches,
    PactType.ParallelFairChoiceOwnership, PactType.ParallelFairChoiceOwnershipBranches,
    PactType.InterfaceScoped, PactType.InterfaceScopedBranches,
    PactType.InterfaceAlphabetScoped, PactType.InterfaceAlphabetScopedBranches,
    PactType.ParallelInterfaces, PactType.ParallelBranchInterfaces,
    PactType.ConjunctiveMessageOwnership, PactType.ConjunctiveMessageOwnershipBranches,
    PactType.ConjunctiveMessageOwnershipBodies,
    OfferMenuLinear, OfferMenuLinearBranches, BranchHeadsAbsentFromMenu,
    typeFutureOffers, typeFutureOffersFuel,
    PactTypeAlphabet.messageIds, leftAlphabet, rightAlphabet, receiverAlphabet, offerAlphabet,
    PactTypeAlphabet.WellFormed, PactTypeAlphabet.OnePolarity, PactTypeAlphabet.empty]

private def env (current future : Finset BareMessage) : TypeEnvironment :=
  ⟨current, future, false⟩

local macro "offer_simp" : tactic =>
  `(tactic| simp [env, TypeEnvironment.empty, TypeEnvironment.WellFormed,
    TypeEnvironment.hasNeed, TypeResolved, TypeNoImmediateBranch, TypeBranchEnabled,
    typeBranchNeeds, typeNeed, typeBranchActions, typeWaitingOffers,
    typeFutureOffers_sequence, typeFutureOffers_recur, typeFutureOffers_xoffer,
    typeFutureOffers_offer, typeFutureOffers_parallel, typeFutureOffers_message,
    typeFutureOffers_tock, typeFutureOffers_skip, MessageDir.invert,
    hideTypeOffers, restrictTypeOffers, sequenceRightMenu,
    TypeLabel.Sync, TypeLabel.sends, TypeLabel.recvs, TypeLabel.messageIdsWith,
    TypeLabel.isTock, TypeLabel.silent, TypeLabel.message, TypeLabel.combine,
    TypeLabel.synced, TypeLabel.isRawSyncedMessage,
    Finset.filter_insert, Finset.filter_singleton, Finset.insert_subset_iff,
    Finset.insert_sdiff_of_notMem, Finset.insert_sdiff_of_mem, Finset.pair_comm,
    Finset.sdiff_eq_self_of_disjoint, Finset.disjoint_singleton_left,
    PactType.alphabet, PactType.reannotate, PactType.reannotateBranches,
    parallelTypeBranchesSelecting, parallelTypeBranchesSelectingWithin,
    parallelTypeBranchesWithin, selectedTypeBranchAt, singletonTypeXOfferAt,
    selectedC, selectedD, branches, exclusive, receiver, clockLoop, conjunctive,
    skipPrefix, leftAlphabet, rightAlphabet, receiverAlphabet, offerAlphabet,
    PactTypeAlphabet.empty, boundary])

private theorem localEnv {outer sibling localEnv : TypeEnvironment}
    {interface : Interface} {source : PactType} {current future : Finset BareMessage}
    (hOuter : outer.clock = false) (hSibling : sibling.clock = false)
    (hLocal : localEnv.clock = false)
    (hCurrent : localEnv.immediate = outer.immediate ∪ restrictTypeOffers interface current)
    (hFuture : localEnv.future =
      (outer.future ∪ restrictTypeOffers interface future) \ localEnv.immediate) :
    LocalTypeOfferEnvironment outer interface source sibling current future localEnv :=
  .ordinary _ _ _ _ _ _ _ hOuter hSibling hLocal hCurrent hFuture

private theorem product {outer leftEnv rightEnv : TypeEnvironment} {interface : Interface}
    {alphabet : PactTypeAlphabet} {left left' right right' : PactType}
    {leftLabel rightLabel : TypeLabel} {lc lf rc rf : Finset BareMessage}
    (hLeft : TypeOffers leftEnv left leftLabel left' lc lf)
    (hRight : TypeOffers rightEnv right rightLabel right' rc rf)
    (hL : left ≠ .skip left.alphabet) (hR : right ≠ .skip right.alphabet)
    (hTarget : ¬ (left' = .skip left'.alphabet ∧ right' = .skip right'.alphabet))
    (hLocalL : LocalTypeOfferEnvironment outer interface left rightEnv rc rf leftEnv)
    (hLocalR : LocalTypeOfferEnvironment outer interface right leftEnv lc lf rightEnv)
    (hWF : outer.WellFormed alphabet) (hSync : TypeLabel.Sync interface leftLabel rightLabel) :
    TypeOffers outer (.par alphabet left right interface)
      (TypeLabel.combine interface leftLabel rightLabel) (.par alphabet left' right' interface)
      (hideTypeOffers interface (lc ∪ rc))
      (if TypeLabel.combine interface leftLabel rightLabel = .tock then ∅
        else hideTypeOffers interface (lf ∪ rf)) :=
  .par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL hR hLeft hRight hTarget hLocalL hLocalR ⟨hWF, hSync⟩

def delayed1 : PactType :=
  .par .empty exclusive (.par rightAlphabet receiver conjunctive {"c"}) boundary

def delayed2 : PactType :=
  .par .empty exclusive (.par rightAlphabet receiver selectedC {"c"}) boundary

def delayed3 : PactType :=
  .par .empty (.message leftAlphabet "e" .send)
    (.par rightAlphabet (clockLoop receiverAlphabet) (.skip offerAlphabet) {"c"}) boundary

def loopBody (alphabet : PactTypeAlphabet) : PactType :=
  .seq alphabet (.tock alphabet) (clockLoop alphabet)

def trap : PactType :=
  .par .empty (.message leftAlphabet "e" .send) (loopBody rightAlphabet) boundary

def original1 : PactType :=
  .par .empty exclusive (.par rightAlphabet receiver selectedD {"c"}) boundary

/-- Without the added delay, the conjunction commits to d while its c partner finishes skip. -/
theorem original_first : TypeOffers .empty original .silent original1 ∅ ∅ := by
  have hA : TypeOffers (env ∅ {("d", .recv)}) exclusive .silent exclusive
      {("d", .send)} {("e", .send)} := by
    simpa only [exclusive] using TypeOffers.xoffer_wait _ _ _ _ (by offer_simp)
  have hB : TypeOffers (env {("d", .send)} {("e", .send), ("c", .send)})
      (skipPrefix receiver) .silent receiver ∅ {("c", .recv)} := by
    apply skipPrefix_offers_iff.mpr
    offer_simp
  have hC : TypeOffers (env {("d", .send)} {("e", .send), ("c", .recv)})
      conjunctive .silent selectedD ∅ {("c", .send), ("d", .recv)} := by
    convert TypeOffers.offer_some (env {("d", .send)} {("e", .send), ("c", .recv)})
      offerAlphabet (.skip offerAlphabet) branches
      (("d", .recv), .skip offerAlphabet) (by offer_simp) using 1
    offer_simp
  have hBC : TypeOffers (env {("d", .send)} {("e", .send)}) rightSide .silent
      (.par rightAlphabet receiver selectedD {"c"}) ∅ {("d", .recv)} := by
    unfold rightSide
    convert product (outer := env {("d", .send)} {("e", .send)})
      (alphabet := rightAlphabet) (interface := {"c"}) hB hC
      (by offer_simp) (by offer_simp) (by offer_simp)
      (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
      (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
      (by offer_simp) (by offer_simp) using 1
  unfold original original1
  convert product (outer := .empty) (alphabet := .empty) (interface := boundary) hA hBC
    (by offer_simp) (by simp [rightSide]) (by simp [exclusive])
    (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
    (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
    (by offer_simp) (by offer_simp) using 1

private theorem right_target_not_skip {environment : TypeEnvironment} {label : TypeLabel}
    {target : PactType} {current future : Finset BareMessage}
    (hOffers : TypeOffers environment rightSide label target current future) :
    target ≠ .skip target.alphabet := by
  have hNoB (environment : TypeEnvironment) (label : TypeLabel) (alphabet : PactTypeAlphabet)
      (current future : Finset BareMessage) :
      ¬ TypeOffers environment (skipPrefix receiver) label (.skip alphabet) current future := by
    intro h
    have hTarget := (skipPrefix_offers_iff.mp h).2.2.2.1
    cases hTarget
  unfold rightSide at hOffers
  cases hOffers <;> simp only [hNoB] at *
  all_goals simp [PactType.alphabet, skipPrefix, receiver, conjunctive] at *

private theorem right_no_skip {environment : TypeEnvironment} {label : TypeLabel}
    {alphabet : PactTypeAlphabet} {current future : Finset BareMessage} :
    ¬ TypeOffers environment rightSide label (.skip alphabet) current future :=
  fun h => right_target_not_skip h rfl

set_option maxHeartbeats 400000 in
/-- Every first response of the undelayed product has the same label and residual. -/
theorem original_first_forced {label : TypeLabel} {target : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers .empty original label target current future) :
    label = .silent ∧ target = original1 := by
  unfold original at hOffers
  cases hOffers <;> try simp only [right_no_skip] at *
  all_goals simp [PactType.alphabet, exclusive, rightSide, receiver, conjunctive, skipPrefix] at *
  all_goals casesm TypeOffers _ (.par _ _ _ _) _ _ _ _
  all_goals casesm* TypeOffers _ (.seq _ (.skip _) _) _ _ _ _
  all_goals casesm* TypeOffers _ (.skip _) _ _ _ _
  all_goals simp_all only [PactType.alphabet, ne_eq, not_true_eq_false]
  all_goals casesm* TypeOffers _ (.xoffer _ _ _) _ _ _ _
  all_goals try casesm* TypeOffers _ (.offer _ _ _) _ _ _ _
  all_goals simp only [branches, List.mem_cons, Prod.mk.injEq] at *
  all_goals casesm* _ ∧ _
  all_goals try casesm* _ ∨ _
  all_goals subst_vars
  all_goals repeat' (casesm LocalTypeOfferEnvironment _ _ _ _ _ _ _ <;>
    simp_all only [TypeEnvironment.empty, TypeEnvironment.tock,
      Bool.false_eq_true, Bool.true_eq_false])
  all_goals simp_all [TypeBranchEnabled, TypeResolved, TypeNoImmediateBranch,
    typeBranchNeeds, typeNeed, MessageDir.invert, typeWaitingOffers,
    hideTypeOffers, restrictTypeOffers, typeBranchActions,
    typeFutureOffers_sequence, typeFutureOffers_recur, typeFutureOffers_xoffer,
    typeFutureOffers_offer, typeFutureOffers_message, typeFutureOffers_parallel,
    typeFutureOffers_tock, typeFutureOffers_skip, sequenceRightMenu,
    Finset.filter_insert, Finset.filter_singleton,
    Finset.pair_comm, Finset.sdiff_eq_self_of_disjoint,
    TypeLabel.silent, TypeLabel.message, TypeLabel.combine, TypeLabel.synced,
    TypeLabel.sends, TypeLabel.messageIdsWith, TypeLabel.isRawSyncedMessage,
    original1, selectedD, branches, clockLoop, receiver,
    exclusive, leftAlphabet, rightAlphabet, offerAlphabet, receiverAlphabet,
    parallelTypeBranchesSelecting, parallelTypeBranchesSelectingWithin,
    parallelTypeBranchesWithin, selectedTypeBranchAt, singletonTypeXOfferAt,
    PactType.reannotate,
    boundary]

/-- The delayed product first postpones both offer heads and exposes the receiver. -/
theorem delayed_first : TypeOffers .empty delayed .silent delayed1 ∅ ∅ := by
  have hA : TypeOffers (env {("d", .recv)} ∅)
      (skipPrefix exclusive) .silent exclusive ∅ {("d", .send), ("e", .send)} := by
    apply skipPrefix_offers_iff.mpr
    offer_simp
  have hB : TypeOffers (env {("c", .send)} {("d", .send), ("e", .send)})
      (skipPrefix receiver) .silent receiver ∅ {("c", .recv)} := by
    apply skipPrefix_offers_iff.mpr
    offer_simp
  have hC : TypeOffers (env ∅ {("c", .recv), ("d", .send), ("e", .send)})
      conjunctive .silent conjunctive {("c", .send), ("d", .recv)} ∅ := by
    simpa only [conjunctive] using TypeOffers.offer_wait _ _ _ _ (by offer_simp)
  have hBC : TypeOffers (env ∅ {("d", .send), ("e", .send)}) rightSide .silent
      (.par rightAlphabet receiver conjunctive {"c"}) {("d", .recv)} ∅ := by
    unfold rightSide
    convert product (outer := env ∅ {("d", .send), ("e", .send)})
      (alphabet := rightAlphabet) (interface := {"c"}) hB hC
      (by offer_simp) (by offer_simp) (by offer_simp)
      (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
      (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
      (by offer_simp) (by offer_simp) using 1
  unfold delayed delayed1
  convert product (outer := .empty) (alphabet := .empty) (interface := boundary) hA hBC
    (by offer_simp) (by simp [rightSide]) (by simp [exclusive])
    (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
    (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
    (by offer_simp) (by offer_simp) using 1

/-- Once both heads are exposed, the conjunction can select c and leave d optional. -/
theorem delayed_second : TypeOffers .empty delayed1 .silent delayed2 ∅ ∅ := by
  have hA : TypeOffers (env ∅ {("d", .recv)}) exclusive .silent exclusive
      {("d", .send)} {("e", .send)} := by
    simpa only [exclusive] using TypeOffers.xoffer_wait _ _ _ _ (by offer_simp)
  have hB : TypeOffers (env {("d", .send)} {("e", .send), ("c", .send)})
      receiver .silent receiver {("c", .recv)} ∅ := by
    have hHead := TypeOffers.action_wait
      (env {("d", .send)} {("e", .send), ("c", .send)}) receiverAlphabet "c" .recv
      (by offer_simp)
    convert TypeOffers.seq _ receiverAlphabet _ _ (clockLoop receiverAlphabet) _ _ _ hHead
      (by simp) (by simp [TypeLabel.silent]) using 1
    offer_simp
  have hC : TypeOffers (env {("d", .send), ("c", .recv)} {("e", .send)})
      conjunctive .silent selectedC ∅ {("c", .send), ("d", .recv)} := by
    convert TypeOffers.offer_some (env {("d", .send), ("c", .recv)} {("e", .send)})
      offerAlphabet (.skip offerAlphabet) branches
      (("c", .send), .skip offerAlphabet) (by offer_simp) using 1
    offer_simp
  have hBC : TypeOffers (env {("d", .send)} {("e", .send)})
      (.par rightAlphabet receiver conjunctive {"c"}) .silent
      (.par rightAlphabet receiver selectedC {"c"}) ∅ {("d", .recv)} := by
    convert product (outer := env {("d", .send)} {("e", .send)})
      (alphabet := rightAlphabet) (interface := {"c"}) hB hC
      (by offer_simp) (by offer_simp) (by offer_simp)
      (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
      (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
      (by offer_simp) (by offer_simp) using 1
  unfold delayed1 delayed2
  convert product (outer := .empty) (alphabet := .empty) (interface := boundary) hA hBC
    (by offer_simp) (by simp) (by simp [exclusive])
    (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
    (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
    (by offer_simp) (by offer_simp) using 1

/- Superseded by defaults advertising declared heads: the two d defaults no longer compose.
/-- The two optional d offers may both default while the mandatory c handshake fires. -/
theorem delayed_third : TypeOffers .empty delayed2 (.actions {.resolved "c"}) delayed3 ∅ ∅ := by
  have hA : TypeOffers .empty exclusive .silent (.message leftAlphabet "e" .send)
      ∅ {("e", .send)} := by
    simpa only [exclusive] using TypeOffers.xoffer_else _ _ _ _ (by offer_simp)
  have hB : TypeOffers (env {("c", .send)} {("e", .send)})
      receiver (TypeLabel.message "c" .recv) (clockLoop receiverAlphabet) {("c", .recv)} ∅ := by
    have hHead := TypeOffers.action (env {("c", .send)} {("e", .send)})
      receiverAlphabet "c" .recv (by offer_simp)
    convert TypeOffers.seq_fuse _ receiverAlphabet receiverAlphabet _ (clockLoop receiverAlphabet)
      _ _ _ hHead (by simp [TypeLabel.message]) using 1
    offer_simp
  have hSelected : TypeOffers (env {("c", .recv)} {("e", .send)})
      (selectedTypeBranchAt offerAlphabet (("c", .send), .skip offerAlphabet))
      (TypeLabel.message "c" .send) (.skip offerAlphabet) {("c", .send)} ∅ := by
    have hHead := TypeOffers.action (env {("c", .recv)} {("e", .send)})
      offerAlphabet "c" .send (by offer_simp)
    convert TypeOffers.seq_fuse _ offerAlphabet offerAlphabet _ (.skip offerAlphabet)
      _ _ _ hHead (by simp [TypeLabel.message]) using 1 <;> offer_simp
  have hOptional : TypeOffers (env {("c", .recv)} {("e", .send)})
      (singletonTypeXOfferAt offerAlphabet (("d", .recv), .skip offerAlphabet))
      .silent (.skip offerAlphabet) ∅ ∅ := by
    convert TypeOffers.xoffer_else (env {("c", .recv)} {("e", .send)})
      offerAlphabet (.skip offerAlphabet)
      [(("d", .recv), .skip offerAlphabet)] (by offer_simp) using 1
    offer_simp
  have hC : TypeOffers (env {("c", .recv)} {("e", .send)}) selectedC
      (TypeLabel.message "c" .send) (.skip offerAlphabet) {("c", .send)} ∅ := by
    convert TypeOffers.par_fuse (env {("c", .recv)} {("e", .send)}) _ _ ∅ offerAlphabet
      _ _ _ _ _ _ _ _ hSelected hOptional
      (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
      (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
      ⟨by offer_simp, by offer_simp⟩ (by offer_simp) using 1
    offer_simp
  have hBC : TypeOffers (env ∅ {("e", .send)})
      (.par rightAlphabet receiver selectedC {"c"}) (.actions {.resolved "c"})
      (.par rightAlphabet (clockLoop receiverAlphabet) (.skip offerAlphabet) {"c"}) ∅ ∅ := by
    convert product (outer := env ∅ {("e", .send)})
      (alphabet := rightAlphabet) (interface := {"c"}) hB hC
      (by offer_simp) (by offer_simp) (by offer_simp)
      (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
      (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
      (by offer_simp) (by offer_simp) using 1
    offer_simp
  unfold delayed2 delayed3
  convert product (outer := .empty) (alphabet := .empty) (interface := boundary) hA hBC
    (by offer_simp) (by simp) (by simp)
    (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
    (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
    (by offer_simp) (by offer_simp) using 1
  offer_simp

-/

/-- A default continues to advertise its declared head. -/
theorem exclusive_default_current :
    TypeOffers .empty exclusive .silent (.message leftAlphabet "e" .send)
      {("d", .send)} {("e", .send)} := by
  convert TypeOffers.xoffer_else .empty leftAlphabet (.message leftAlphabet "e" .send)
    [(("d", .send), .skip leftAlphabet)] (by offer_simp) using 1

/-- A complementary head advertised by the sibling excludes the exclusive default. -/
theorem exclusive_default_excluded {leftEnv rightEnv : TypeEnvironment}
    (hLocal : LocalTypeOfferEnvironment .empty boundary exclusive rightEnv
      {("d", .recv)} ∅ leftEnv) :
    ¬ TypeOffers leftEnv exclusive .silent (.message leftAlphabet "e" .send)
      {("d", .send)} {("e", .send)} := by
  intro hStep
  generalize hLabel : TypeLabel.silent = label at hStep
  generalize hCurrent : ({("d", .send)} : Finset BareMessage) = current at hStep
  generalize hFuture : ({("e", .send)} : Finset BareMessage) = future at hStep
  cases hStep <;> cases hLocal <;>
    simp_all [TypeEnvironment.empty, TypeNoImmediateBranch,
      typeBranchNeeds, typeNeed, MessageDir.invert, restrictTypeOffers, boundary,
      Finset.filter_singleton]

/-- The remaining clock loop unfolds, while the unmatched e prefix waits. -/
theorem delayed_fourth : TypeOffers .empty delayed3 .silent trap ∅ ∅ := by
  have hA : TypeOffers .empty (.message leftAlphabet "e" .send) .silent
      (.message leftAlphabet "e" .send) {("e", .send)} ∅ := by
    simpa using TypeOffers.action_wait .empty leftAlphabet "e" .send (by offer_simp)
  have hLoop : TypeOffers (env {("e", .send)} ∅) (clockLoop receiverAlphabet) .silent
      (loopBody receiverAlphabet) ∅ ∅ := by
    convert TypeOffers.recur (env {("e", .send)} ∅) receiverAlphabet "X"
      (.seq receiverAlphabet (.tock receiverAlphabet) (.var receiverAlphabet "X"))
      (by offer_simp) using 1 <;> simp [loopBody, PactType.replaceVar] <;> offer_simp
  have hSkip : TypeOffers (env {("e", .send)} ∅) (.skip offerAlphabet) .silent
      (.skip offerAlphabet) ∅ ∅ := by
    simpa using TypeOffers.skip (env {("e", .send)} ∅) offerAlphabet (by offer_simp)
  have hRight : TypeOffers (env {("e", .send)} ∅)
      (.par rightAlphabet (clockLoop receiverAlphabet) (.skip offerAlphabet) {"c"})
      .silent (loopBody rightAlphabet) ∅ ∅ := by
    convert TypeOffers.right_complete (env {("e", .send)} ∅) _ _ {"c"} rightAlphabet
      _ _ _ _ _ _ _ _ rfl (by simp [clockLoop]) hSkip hLoop (by simp [loopBody])
      (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
      (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
      (by offer_simp) (by offer_simp) using 1
    simp [loopBody]
    offer_simp
  unfold delayed3 trap
  convert product (outer := .empty) (alphabet := .empty) (interface := boundary) hA hRight
    (by simp) (by simp) (by simp)
    (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
    (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
    (by offer_simp) (by offer_simp) using 1

/-- The unmatched e prefix and the clock wait silently forever under the empty environment. -/
theorem trap_wait : TypeOffers .empty trap .silent trap ∅ ∅ := by
  have hA : TypeOffers .empty (.message leftAlphabet "e" .send) .silent
      (.message leftAlphabet "e" .send) {("e", .send)} ∅ := by
    simpa using TypeOffers.action_wait .empty leftAlphabet "e" .send (by offer_simp)
  have hClock := TypeOffers.cycle_wait (env {("e", .send)} ∅) rightAlphabet (by offer_simp)
  have hRight : TypeOffers (env {("e", .send)} ∅) (loopBody rightAlphabet)
      .silent (loopBody rightAlphabet) ∅ ∅ := by
    convert TypeOffers.seq _ rightAlphabet _ _ (clockLoop rightAlphabet) _ _ _ hClock
      (by simp) (by simp [TypeLabel.silent]) using 1
    offer_simp
  unfold trap
  convert product (outer := .empty) (alphabet := .empty) (interface := boundary) hA hRight
    (by simp) (by simp [loopBody]) (by simp)
    (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
    (localEnv rfl rfl rfl (by offer_simp) (by offer_simp))
    (by offer_simp) (by offer_simp) using 1

private theorem parallel_no_clock {left right : PactType} {alphabet : PactTypeAlphabet}
    {interface : Interface} (hLeft : ¬ TypeReady .tock left) :
    ¬ TypeReady .tock (.par alphabet left right interface) := by
  rintro ⟨label, target, hStep⟩
  cases hStep with
  | par outer leftEnv rightEnv interface alphabet left left' right right' leftLabel rightLabel
      lc lf rc rf hL hR hChild hLO hRS hRO hTarget hPrem =>
      exact hLeft ⟨_, _, (hPrem.2.1.tock_of_clock rfl) ▸ hChild⟩
  | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel rightLabel
      lc lf rc rf hChild hLO hRS hRO hPrem =>
      exact hLeft ⟨_, _, (hPrem.2.1.tock_of_clock rfl) ▸ hChild⟩
  | left_complete outer leftEnv rightEnv interface alphabet left right right' rightLabel
      lc lf rc rf hL hR hChild hLO hRS hRO hTarget hLocal hLocalR hWF hSync =>
      exact hLeft ⟨_, _, (hLocal.tock_of_clock rfl) ▸ hChild⟩
  | right_complete outer leftEnv rightEnv interface alphabet left left' right leftLabel
      lc lf rc rf hR hL hRS hRO hChild hLO hTarget hLocal hLocalR hWF hSync =>
      exact hLeft ⟨_, _, (hLocal.tock_of_clock rfl) ▸ hChild⟩

private theorem exclusive_no_clock : ¬ TypeReady .tock exclusive := by
  rintro ⟨label, target, hStep⟩
  cases hStep <;>
    simp_all [TypeBranchEnabled, TypeEnvironment.tock]

private theorem message_no_clock (alphabet : PactTypeAlphabet) (msg : MessageId)
    (dir : MessageDir) : ¬ TypeReady .tock (.message alphabet msg dir) := by
  rintro ⟨label, target, hStep⟩
  cases hStep <;> simp_all [TypeEnvironment.hasNeed, TypeEnvironment.tock]

/-- No clock can cross a product whose unmatched e prefix is still active. -/
theorem trap_no_clock : ¬ TypeReady .tock trap :=
  parallel_no_clock (message_no_clock _ _ _)

private theorem residual_alphabets :
    delayed1.AlphabetWellFormed ∧ delayed2.AlphabetWellFormed ∧
      delayed3.AlphabetWellFormed ∧ trap.AlphabetWellFormed := by
  have hA := alphabets
  have hSelf : PactTypeAlphabet.ParallelCompatible offerAlphabet offerAlphabet offerAlphabet ∅ :=
    ⟨by simp, by simp [PactTypeAlphabet.ComplementaryOn],
      by simp [PactTypeAlphabet.hideInterface], by simp [PactTypeAlphabet.hideInterface]⟩
  simp_all [delayed1, delayed2, delayed3, trap, loopBody, exclusive, receiver, conjunctive,
    selectedC, branches, clockLoop, boundary, parallelTypeBranchesSelecting,
    parallelTypeBranchesSelectingWithin, parallelTypeBranchesWithin,
    selectedTypeBranchAt, singletonTypeXOfferAt, PactType.reannotate,
    PactType.AlphabetWellFormed, PactType.BranchesAlphabetWellFormed,
    PactType.OfferBranchesWellFormed, PactType.alphabet,
    PactTypeAlphabet.WellFormed, PactTypeAlphabet.OnePolarity, PactTypeAlphabet.empty]

private theorem ready_environment_empty {source : PactType} {environment : TypeEnvironment}
    (hAlphabet : source.AlphabetWellFormed) (hBoundary : source.alphabet = .empty)
    (hClock : ¬ TypeReady .tock source) (hReady : TypeReady environment source) :
    environment = .empty := by
  obtain ⟨label, target, hStep⟩ := hReady
  obtain ⟨offers, hOffers⟩ := hStep.exists_decorated
  have hWF := hOffers.2.env_wellFormed hAlphabet
  rw [hBoundary] at hWF
  have hImmediate : environment.immediate = ∅ :=
    Finset.subset_empty.mp (by simpa [PactTypeAlphabet.empty] using hWF.2.2.1)
  have hFuture : environment.future = ∅ :=
    Finset.subset_empty.mp (by simpa [PactTypeAlphabet.empty] using hWF.2.2.2)
  cases environment with
  | mk immediate future clock =>
      dsimp only at hImmediate hFuture
      subst immediate future
      cases clock with
      | false => rfl
      | true => exact (hClock ⟨_, _, hStep⟩).elim

private theorem winning_continuation {source target : PactType} {strategy : TypeStrategy}
    {label : TypeLabel} (hStep : TypeTransition (strategy []) source label target)
    (hWins : ∀ log, CompletedTypeLog source strategy log → TypeWinningObjective source ∅ log) :
    SemanticTypeCompatible target ∅ := by
  refine ⟨fun entries => strategy ((strategy [], label, target) :: entries),
    fun log hCompleted => ?_⟩
  have hWin := hWins _ (completedTypeLog_prepend hStep hCompleted)
  refine ⟨fun index => hWin.1 (index + 1), ?_, by simp⟩
  exact (LogMonitor.infinite_succ_iff _).mpr hWin.2.1

private theorem compatible_after_empty_step {source target : PactType} {label : TypeLabel}
    (hAlphabet : source.AlphabetWellFormed) (hBoundary : source.alphabet = .empty)
    (hClock : ¬ TypeReady .tock source) (hStep : TypeTransition .empty source label target)
    (hCompatible : SemanticTypeCompatible source ∅) : SemanticTypeCompatible target ∅ := by
  obtain ⟨strategy, hWins⟩ := hCompatible
  have hEnv := ready_environment_empty hAlphabet hBoundary hClock
    (strategy_ready hWins FollowsTypeStrategy.root)
  exact winning_continuation (hEnv ▸ hStep) hWins

/-- Every strategy at the closed waiting state either blocks or admits an endless silent execution. -/
theorem trap_incompatible : ¬ SemanticTypeCompatible trap ∅ := by
  rintro ⟨strategy, hWins⟩
  have hStep := trap_wait.toTypeTransition
  have hValid : ∀ n, TypePrefixValid trap
      (List.replicate n (TypeEnvironment.empty, TypeLabel.silent, trap)) trap := by
    intro n
    induction n with
    | zero => exact .root
    | succ n ih => simpa [List.replicate_succ'] using ih.step hStep
  let prefixAt (n : Nat) : TypePrefix trap := ⟨_, _, hValid n⟩
  have hFollows : ∀ n, FollowsTypeStrategy trap strategy (prefixAt n) := by
    intro n
    induction n with
    | zero => exact .root
    | succ n ih =>
        have hEnv := ready_environment_empty residual_alphabets.2.2.2 rfl trap_no_clock
          (strategy_ready hWins ih)
        simpa [prefixAt, hEnv, List.replicate_succ'] using ih.step (hEnv ▸ hStep)
  have hEnv (n : Nat) : strategy (prefixAt n).entries = .empty :=
    ready_environment_empty residual_alphabets.2.2.2 rfl trap_no_clock
      (strategy_ready hWins (hFollows n))
  have hCompleted : CompletedTypeLog trap strategy (fun _ => (.empty, .silent)) := by
    refine ⟨prefixAt, rfl, Or.inl fun n => ⟨(hEnv n).symm, ?_, hStep⟩⟩
    simp [prefixAt, List.replicate_succ']
  have hClock := (hWins _ hCompleted).2.1
  simp [TypeTockOccursInfinitely, TypeLabel.silent] at hClock

/- Superseded: the third transition used empty-current defaults.
/-- A single leading skip admits a path to a closed state from which clocks cannot recur. -/
theorem delayed_incompatible : ¬ SemanticTypeCompatible delayed ∅ := by
  intro hCompatible
  have hClock0 : ¬ TypeReady .tock delayed := by
    apply parallel_no_clock
    rintro ⟨label, target, hStep⟩
    have hClock := (skip_prefix_transition_iff.mp hStep).2.1
    simp [TypeEnvironment.tock] at hClock
  have hOne := compatible_after_empty_step wellFormed.2.1 rfl hClock0
    delayed_first.toTypeTransition hCompatible
  have hTwo := compatible_after_empty_step residual_alphabets.1 rfl
    (parallel_no_clock exclusive_no_clock) delayed_second.toTypeTransition hOne
  have hThree := compatible_after_empty_step residual_alphabets.2.1 rfl
    (parallel_no_clock exclusive_no_clock) delayed_third.toTypeTransition hTwo
  have hFour := compatible_after_empty_step residual_alphabets.2.2.1 rfl
    (parallel_no_clock (message_no_clock _ _ _)) delayed_fourth.toTypeTransition hThree
  exact trap_incompatible hFour

/-- The compiled game for the delayed product is incompatible, even with no progress requirements. -/
theorem delayed_game_incompatible : ¬ TypeCompatible delayed ∅ :=
  fun h => delayed_incompatible (game_reduction_forward wellFormed.2 h)
-/

end

end Pact.WeakRefinement.OfferDelay
