import Anvilpp.PactTypes.Syntax.TypeFutureOffersFuel

/-!
# Per-constructor typeFutureOffers equations, substitution, and marker-reachability transport
-/

namespace Pact

noncomputable section

/-- Syntax-derived futures of a sequence include the right menu exactly when
the left syntax may optimistically complete before the next clock. -/
theorem typeFutureOffers_sequence
    (alphabet : PactTypeAlphabet) (left right : PactType) :
    typeFutureOffers (.seq alphabet left right) =
      if left.CanCompleteBeforeTock then
        typeFutureOffers left ∪ typeFutureOffers right
      else typeFutureOffers left := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.seq alphabet left right) := by
    simp_wf
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.seq alphabet left right) := by
    simp_wf
    omega
  have hCompleteFuel : sizeOf left <
      sizeOf (PactType.seq alphabet left right) := by
    simp_wf
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.seq alphabet left right) + 1)
      (PactType.seq alphabet left right) = _
  simp only [typeFutureOffersFuel]
  rw [typeCanCompleteThisCycleFuel_eq_canCompleteBeforeTock
      _ left hCompleteFuel,
    typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- Syntax-derived futures distribute over ordinary choice. -/
theorem typeFutureOffers_choice
    (alphabet : PactTypeAlphabet) (left right : PactType) :
    typeFutureOffers (.choice alphabet left right) =
      typeFutureOffers left ∪ typeFutureOffers right := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.choice alphabet left right) := by
    change sizeOf left + 1 ≤ 1 + sizeOf left + sizeOf right
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.choice alphabet left right) := by
    change sizeOf right + 1 ≤ 1 + sizeOf left + sizeOf right
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.choice alphabet left right) + 1)
      (PactType.choice alphabet left right) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- Syntax-derived futures distribute over fair choice. -/
theorem typeFutureOffers_fairChoice
    (alphabet : PactTypeAlphabet) (bid : BranchId) (left right : PactType) :
    typeFutureOffers (.fairChoice alphabet bid left right) =
      typeFutureOffers left ∪ typeFutureOffers right := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.fairChoice alphabet bid left right) := by
    change sizeOf left + 1 ≤ 1 + bid + sizeOf left + sizeOf right
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.fairChoice alphabet bid left right) := by
    change sizeOf right + 1 ≤ 1 + bid + sizeOf left + sizeOf right
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.fairChoice alphabet bid left right) + 1)
      (PactType.fairChoice alphabet bid left right) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- Syntax-derived futures of an exclusive offer contain the else menu, every
branch head, and every branch continuation menu. -/
theorem typeFutureOffers_xoffer
    (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType)) :
    typeFutureOffers (.xoffer alphabet elseType branches) =
      branches.foldl (fun offers branch =>
        offers ∪ {branch.1} ∪ typeFutureOffers branch.2)
        (typeFutureOffers elseType) := by
  let fuel := sizeOf (PactType.xoffer alphabet elseType branches)
  have hElseFuel : sizeOf elseType + 1 ≤ fuel := by
    simp [fuel]
    omega
  have hBranchFuel : ∀ branch ∈ branches,
      sizeOf branch.2 + 1 ≤ fuel := by
    intro branch hBranch
    have hPairSize := List.sizeOf_lt_of_mem hBranch
    have hComponentSize : sizeOf branch.2 < sizeOf branch := by
      rcases branch
      simp_wf
      omega
    simp [fuel]
    omega
  have hFold : ∀ rest : List (BareMessage × PactType),
      (∀ branch ∈ rest, sizeOf branch.2 + 1 ≤ fuel) →
      ∀ initial,
        rest.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2) initial =
        rest.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffers branch.2) initial := by
    intro rest hRest
    induction rest with
    | nil => simp
    | cons branch tail ih =>
        intro initial
        simp only [List.foldl_cons]
        rw [typeFutureOffersFuel_eq_typeFutureOffers branch.2 fuel
          (hRest branch (by simp))]
        apply ih
        intro entry hEntry
        exact hRest entry (by simp [hEntry])
  change branches.foldl (fun offers branch =>
      offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
      (typeFutureOffersFuel fuel elseType) = _
  rw [typeFutureOffersFuel_eq_typeFutureOffers elseType fuel hElseFuel]
  exact hFold branches hBranchFuel (typeFutureOffers elseType)

/-- Conjunctive offers have the same optimistic syntax menu as exclusive
offers: the else continuation, every branch head, and every branch menu. -/
theorem typeFutureOffers_offer
    (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType)) :
    typeFutureOffers (.offer alphabet elseType branches) =
      branches.foldl (fun offers branch =>
        offers ∪ {branch.1} ∪ typeFutureOffers branch.2)
        (typeFutureOffers elseType) := by
  simpa only [typeFutureOffers, typeFutureOffersFuel] using
    typeFutureOffers_xoffer alphabet elseType branches

/-- Parallel future offers are the optimistic union of both syntax-derived
component menus, with the synchronization interface hidden. -/
theorem typeFutureOffers_parallel
    (alphabet : PactTypeAlphabet) (left right : PactType) (interface : Interface) :
    typeFutureOffers (.par alphabet left right interface) =
      hideTypeOffers interface
        (typeFutureOffers left ∪ typeFutureOffers right) := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.par alphabet left right interface) := by
    simp_wf
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.par alphabet left right interface) := by
    simp_wf
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.par alphabet left right interface) + 1)
      (PactType.par alphabet left right interface) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- A recursion binder exposes the same syntactic same-cycle future menu as
its body; guardedness is used separately when replacing recursive calls. -/
theorem typeFutureOffers_recur
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType) :
    typeFutureOffers (.recur alphabet name body) = typeFutureOffers body := by
  have hBodyFuel : sizeOf body + 1 ≤
      sizeOf (PactType.recur alphabet name body) := by
    simp_wf
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.recur alphabet name body) + 1)
      (PactType.recur alphabet name body) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers body _ hBodyFuel]

/-- Branch offers selected by the future part of this environment. -/
def typeWaitingOffers (env : TypeEnvironment)
    (branches : List (BareMessage × PactType)) : Finset BareMessage :=
  (env.future.image typeNeed) ∩ typeBranchActions branches

/-
Environment-indexed current/future offers and the sibling-local environment
relation are mutually defined: parallel offers depend on the two local steps,
while each local environment depends on the sibling step's offers.
-/

/-- Restrict a boundary environment menu to the actions visible to a type
with fixed alphabet `alphabet`.  Environments contain the complementary
polarities needed by type actions, so the projection uses `typeNeed`. -/
def projectTypeEnvironmentOffers
    (alphabet : PactTypeAlphabet) (offers : Finset BareMessage) :
    Finset BareMessage :=
  offers.filter fun action => action ∈ alphabet.actions.image typeNeed

/-- The offer-indexed sibling-local environment relation used by the
decorated parallel rule.

The ordinary case is intentionally indexed by the concrete sibling offer
sets.  This rules out the spurious situation where the parallel step combines
one pair of child offers, but the local environment is justified by a
different sibling offer witness. -/
inductive LocalTypeOfferEnvironment :
    TypeEnvironment → Interface → PactType → TypeEnvironment →
      Finset BareMessage → Finset BareMessage → TypeEnvironment → Prop where
  | clock (outer : TypeEnvironment) (interface : Interface)
      (localType : PactType) (current future : Finset BareMessage) :
      outer.clock = true →
      LocalTypeOfferEnvironment outer interface localType TypeEnvironment.tock
        current future TypeEnvironment.tock
  | ordinary (outer siblingEnv localEnv : TypeEnvironment)
      (interface : Interface) (localType : PactType)
      (current future : Finset BareMessage) :
      outer.clock = false →
      siblingEnv.clock = false →
      localEnv.clock = false →
      localEnv.immediate =
        projectTypeEnvironmentOffers localType.alphabet outer.immediate ∪
          restrictTypeOffers interface current →
      localEnv.future =
        (projectTypeEnvironmentOffers localType.alphabet outer.future ∪
          restrictTypeOffers interface future) \ localEnv.immediate →
      LocalTypeOfferEnvironment outer interface localType siblingEnv current
        future localEnv

mutual
  @[aesop unsafe]
  inductive TypeOffers :
      TypeEnvironment → PactType → TypeLabel → PactType →
        Finset BareMessage → Finset BareMessage → Prop where
    | action (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (msg : MessageId) (dir : MessageDir) :
        env.WellFormed ∧ env.hasNeed (msg, dir) →
        TypeOffers env (.message alphabet msg dir) (TypeLabel.message msg dir)
          (.skip alphabet) {(msg, dir)} (typeFutureOffers (.skip alphabet))
    | action_wait (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (msg : MessageId) (dir : MessageDir) :
        env.WellFormed ∧ ¬ env.hasNeed (msg, dir) ∧ env.clock = false →
        TypeOffers env (.message alphabet msg dir) TypeLabel.silent
          (.message alphabet msg dir) {(msg, dir)}
          (typeFutureOffers (.message alphabet msg dir) \ {(msg, dir)})
    | choice_left (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (left right : PactType) :
        env.WellFormed ∧ env.clock = false →
        TypeOffers env (.choice alphabet left right) TypeLabel.silent left
          ∅ (typeFutureOffers left)
    | choice_right (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (left right : PactType) :
        env.WellFormed ∧ env.clock = false →
        TypeOffers env (.choice alphabet left right) TypeLabel.silent right
          ∅ (typeFutureOffers right)
    | fair_left (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (bid : BranchId)
        (left right : PactType) :
        env.WellFormed ∧ env.clock = false →
        TypeOffers env (.fairChoice alphabet bid left right)
          (TypeLabel.fair bid true) left ∅ (typeFutureOffers left)
    | fair_right (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (bid : BranchId)
        (left right : PactType) :
        env.WellFormed ∧ env.clock = false →
        TypeOffers env (.fairChoice alphabet bid left right)
          (TypeLabel.fair bid false) right ∅ (typeFutureOffers right)
    | cycle (env : TypeEnvironment) (alphabet : PactTypeAlphabet) :
        env.WellFormed ∧ env.clock = true →
        TypeOffers env (.tock alphabet) .tock (.skip alphabet) ∅ ∅
    | cycle_wait (env : TypeEnvironment) (alphabet : PactTypeAlphabet) :
        env.WellFormed ∧ env.clock = false →
        TypeOffers env (.tock alphabet) TypeLabel.silent (.tock alphabet) ∅ ∅
    | skip (env : TypeEnvironment) (alphabet : PactTypeAlphabet) :
        env.WellFormed ∧ env.clock = false →
        TypeOffers env (.skip alphabet) TypeLabel.silent (.skip alphabet) ∅ ∅
    | progress (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (pid : ProcId) :
        env.WellFormed ∧ env.clock = false →
        TypeOffers env (.progress alphabet pid) (TypeLabel.progress pid)
          (.skip alphabet) ∅ ∅
    | recur (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (name : String) (body : PactType) :
        env.WellFormed ∧ env.clock = false →
        TypeOffers env (.recur alphabet name body) TypeLabel.silent
          (body.replaceVar name (.recur alphabet name body)) ∅
          (typeFutureOffers (body.replaceVar name (.recur alphabet name body)))
    | seq (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (left left' right : PactType)
        (label : TypeLabel) (current childFuture : Finset BareMessage) :
        TypeOffers env left label left' current childFuture →
        left' ≠ .skip left'.alphabet →
        TypeOffers env (.seq alphabet left right) label
          (.seq alphabet left' right) current
          (typeFutureOffers (.seq alphabet left' right) \ current)
    | seq_fuse (env : TypeEnvironment) (alphabet skipAlphabet : PactTypeAlphabet)
        (left right : PactType)
        (label : TypeLabel) (current childFuture : Finset BareMessage) :
        TypeOffers env left label (.skip skipAlphabet) current childFuture →
        label ≠ TypeLabel.tock →
        TypeOffers env (.seq alphabet left right) label right current
          (typeFutureOffers right \ current)
    | seq_fuse_tock (env : TypeEnvironment) (alphabet skipAlphabet : PactTypeAlphabet)
        (left right : PactType)
        (current childFuture : Finset BareMessage) :
        TypeOffers env left TypeLabel.tock (.skip skipAlphabet) current childFuture →
        TypeOffers env (.seq alphabet left right) TypeLabel.tock right current ∅
    | xoffer_branch (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (elseType : PactType)
        (branches : List (BareMessage × PactType))
        (action : BareMessage) (processType : PactType) :
        env.WellFormed ∧
          (action, processType) ∈ branches ∧
          TypeBranchEnabled env (action, processType) ∧
          TypeResolved env branches →
        TypeOffers env (.xoffer alphabet elseType branches)
          (TypeLabel.message action.1 action.2) processType
          {action} (typeFutureOffers processType)
    | xoffer_else (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed ∧ env.clock = false ∧
          TypeNoImmediateBranch env branches ∧ TypeResolved env branches →
        TypeOffers env (.xoffer alphabet elseType branches) TypeLabel.silent
          elseType ∅ (typeFutureOffers elseType)
    | xoffer_wait (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed ∧ ¬ TypeResolved env branches ∧ env.clock = false →
        TypeOffers env (.xoffer alphabet elseType branches) TypeLabel.silent
          (.xoffer alphabet elseType branches) (typeWaitingOffers env branches)
          (typeFutureOffers (.xoffer alphabet elseType branches) \
            typeWaitingOffers env branches)
    | offer_some (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (elseType : PactType)
        (branches : List (BareMessage × PactType))
        (enabled : BareMessage × PactType) :
        env.WellFormed ∧ enabled ∈ branches ∧ TypeBranchEnabled env enabled →
        TypeOffers env (.offer alphabet elseType branches) TypeLabel.silent
          (parallelTypeBranchesSelecting enabled branches) ∅
          (typeFutureOffers (parallelTypeBranchesSelecting enabled branches))
    | offer_else (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed ∧ env.clock = false ∧
          TypeNoImmediateBranch env branches ∧ TypeResolved env branches →
        TypeOffers env (.offer alphabet elseType branches) TypeLabel.silent
          elseType (typeBranchActions branches) (typeFutureOffers elseType)
    | offer_wait (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed ∧ env.clock = false ∧
          TypeNoImmediateBranch env branches ∧ ¬ TypeResolved env branches →
        TypeOffers env (.offer alphabet elseType branches) TypeLabel.silent
          (.offer alphabet elseType branches) (typeWaitingOffers env branches)
          (typeFutureOffers (.offer alphabet elseType branches) \
            typeWaitingOffers env branches)
    | par (outer leftEnv rightEnv : TypeEnvironment) (interface : Interface)
        (left left' right right' : PactType) (leftLabel rightLabel : TypeLabel)
        (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
        TypeOffers leftEnv left leftLabel left' leftCurrent leftFuture →
        TypeOffers rightEnv right rightLabel right' rightCurrent rightFuture →
        ¬ (left' = .skip left'.alphabet ∧ right' = .skip right'.alphabet) →
        LocalTypeOfferEnvironment outer interface left rightEnv rightCurrent
          rightFuture leftEnv →
        LocalTypeOfferEnvironment outer interface right leftEnv leftCurrent
          leftFuture rightEnv →
        outer.WellFormed ∧ TypeLabel.Sync interface leftLabel rightLabel →
        TypeOffers outer (.par (PactTypeAlphabet.mergeHidden left.alphabet
            right.alphabet interface) left right interface)
          (TypeLabel.combine interface leftLabel rightLabel)
          (.par (PactTypeAlphabet.mergeHidden left.alphabet
            right.alphabet interface) left' right' interface)
          (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
          (hideTypeOffers interface (leftFuture ∪ rightFuture))
    | par_fuse (outer leftEnv rightEnv : TypeEnvironment) (interface : Interface)
        (left right : PactType) (leftLabel rightLabel : TypeLabel)
        (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
        TypeOffers leftEnv left leftLabel (.skip left.alphabet)
          leftCurrent leftFuture →
        TypeOffers rightEnv right rightLabel (.skip right.alphabet)
          rightCurrent rightFuture →
        LocalTypeOfferEnvironment outer interface left rightEnv rightCurrent
          rightFuture leftEnv →
        LocalTypeOfferEnvironment outer interface right leftEnv leftCurrent
          leftFuture rightEnv →
        outer.WellFormed ∧ TypeLabel.Sync interface leftLabel rightLabel →
        TypeOffers outer (.par (PactTypeAlphabet.mergeHidden left.alphabet
            right.alphabet interface) left right interface)
          (TypeLabel.combine interface leftLabel rightLabel)
          (.skip (PactTypeAlphabet.mergeHidden left.alphabet
            right.alphabet interface))
          (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
          (hideTypeOffers interface (leftFuture ∪ rightFuture))

end

end

end Pact
