import Anvilpp.PactTypes.Syntax.TypeErasure

/-!
# Type-level offer/branch helper definitions
-/

namespace Pact

noncomputable section

/-! ## Type dynamics and semantic correspondence -/

def typeBranchNeeds (branches : List (BareMessage × PactType)) :
    Finset BareMessage :=
  (branches.map fun branch => typeNeed branch.1).toFinset

def TypeResolved (env : TypeEnvironment)
    (branches : List (BareMessage × PactType)) : Prop :=
  typeBranchNeeds branches ∩ env.future = ∅

def TypeNoImmediateBranch (env : TypeEnvironment)
    (branches : List (BareMessage × PactType)) : Prop :=
  typeBranchNeeds branches ∩ env.immediate = ∅

def TypeBranchEnabled (env : TypeEnvironment)
    (branch : BareMessage × PactType) : Prop :=
  typeNeed branch.1 ∈ env.immediate

namespace PactTypeAlphabet

  /-- The part of `parent` used by one conjunctive-offer branch. -/
  def branchPart (parent : PactTypeAlphabet)
      (branch : BareMessage × PactType) : PactTypeAlphabet :=
    { actions := parent.actions ∩
        ({branch.1} ∪ PactType.MessageActions branch.2) }

  /-- The declarations left after assigning one component of an internal
  parallel product. -/
  def remove (parent assigned : PactTypeAlphabet) : PactTypeAlphabet :=
    { actions := parent.actions \ assigned.actions }

  /-- Project a new parallel boundary alphabet to one of the old children.
  Interface actions remain local to the child even though they are hidden at
  the parent boundary. -/
  def projectParallelChild (parent child : PactTypeAlphabet)
      (interface : Interface) : PactTypeAlphabet :=
    { actions := child.actions.filter fun action =>
        action.1 ∈ interface ∨ action ∈ parent.actions }

  /-- Project a new parallel alphabet to the left child.  The left child keeps
  its own projection, and additionally absorbs the declarations that are new to
  the reannotated parallel node, so the two projected children still
  reconstruct the whole parent alphabet. -/
  def projectParallelLeft (parent left right : PactTypeAlphabet)
      (interface : Interface) : PactTypeAlphabet :=
    let rightPart := projectParallelChild parent right interface
    { actions :=
        (projectParallelChild parent left interface).actions ∪
          (parent.actions \ rightPart.actions) }

end PactTypeAlphabet

namespace PactType

  /- Change the fixed alphabet of a type without changing its type
  operators.  Non-parallel descendants receive the same alphabet.  At a
  parallel node, the new boundary alphabet is projected to the two children;
  their interface actions are retained. -/
  mutual
    def reannotate (alphabet : PactTypeAlphabet) : PactType → PactType
      | .message _ msg dir => .message alphabet msg dir
      | .progress _ pid => .progress alphabet pid
      | .tock _ => .tock alphabet
      | .skip _ => .skip alphabet
      | .choice _ left right =>
          .choice alphabet (reannotate alphabet left)
            (reannotate alphabet right)
      | .seq _ left right =>
          .seq alphabet (reannotate alphabet left)
            (reannotate alphabet right)
      | .par _ left right interface =>
          let leftAlphabet := PactTypeAlphabet.projectParallelLeft alphabet
            left.alphabet right.alphabet interface
          let rightAlphabet := PactTypeAlphabet.projectParallelChild alphabet
            right.alphabet interface
          .par alphabet (reannotate leftAlphabet left)
            (reannotate rightAlphabet right) interface
      | .var _ name => .var alphabet name
      | .recur _ name body => .recur alphabet name (reannotate alphabet body)
      | .fairChoice _ bid left right =>
          .fairChoice alphabet bid (reannotate alphabet left)
            (reannotate alphabet right)
      | .xoffer _ elseType branches =>
          .xoffer alphabet (reannotate alphabet elseType)
            (reannotateBranches alphabet branches)
      | .offer _ elseType branches =>
          .offer alphabet (reannotate alphabet elseType)
            (reannotateBranches alphabet branches)
    termination_by processType => sizeOf processType

    def reannotateBranches (alphabet : PactTypeAlphabet) :
        List (BareMessage × PactType) → List (BareMessage × PactType)
      | [] => []
      | (action, processType) :: rest =>
          (action, reannotate alphabet processType) ::
            reannotateBranches alphabet rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

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

end PactType

def singletonTypeXOfferAt (alphabet : PactTypeAlphabet)
    (branch : BareMessage × PactType) : PactType :=
  let branch := (branch.1, branch.2.reannotate alphabet)
  .xoffer alphabet (.skip alphabet) [branch]

def singletonTypeXOffer (branch : BareMessage × PactType) : PactType :=
  singletonTypeXOfferAt branch.2.alphabet branch

/-- A selected conjunctive-offer branch has no synthetic else alternative:
its head action is now mandatory, followed by its continuation. -/
def selectedTypeBranchAt (alphabet : PactTypeAlphabet)
    (branch : BareMessage × PactType) : PactType :=
  .seq alphabet (.message alphabet branch.1.1 branch.1.2)
    (branch.2.reannotate alphabet)

def selectedTypeBranch (branch : BareMessage × PactType) : PactType :=
  selectedTypeBranchAt branch.2.alphabet branch

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

def parallelType (left right : PactType) (interface : Interface) : PactType :=
  .par (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet interface)
    left right interface

/- The worker partitions `alphabet` from left to right.  Each non-final branch
receives its own declared alphabet.  The final branch receives the remainder,
so the product retains the enclosing offer's fixed alphabet. -/
def parallelTypeBranchesWithin (alphabet : PactTypeAlphabet) :
    List (BareMessage × PactType) → PactType
  | [] => .skip alphabet
  | [branch] => singletonTypeXOfferAt alphabet branch
  | branch :: rest =>
      let leftAlphabet := branch.2.alphabet
      let rightAlphabet : PactTypeAlphabet :=
        { actions := PactType.branchAlphabetActions rest }
      .par alphabet (singletonTypeXOfferAt leftAlphabet branch)
        (parallelTypeBranchesWithin rightAlphabet rest) ∅

/-- Rewrite a conjunctive type offer into parallel singleton exclusive offers
whose component alphabets partition the enclosing offer alphabet. -/
def parallelTypeBranches (alphabet : PactTypeAlphabet) :
    List (BareMessage × PactType) → PactType
  | [] => .skip PactTypeAlphabet.empty
  | branch :: rest => parallelTypeBranchesWithin alphabet (branch :: rest)

/-- Post-process the singleton-`xoffer` product after `selected` witnesses that
the conjunctive offer fired.  Exactly that singleton loses its synthetic
`skip` else-arm; all other singleton offers are retained.  Consequently the
single outcome in which every singleton selects else is absent. -/
def parallelTypeBranchesSelectingWithin (alphabet : PactTypeAlphabet)
    (selected : BareMessage × PactType) :
    List (BareMessage × PactType) → PactType
  | [] => .skip alphabet
  | [branch] =>
      if branch = selected then selectedTypeBranchAt alphabet branch
      else singletonTypeXOfferAt alphabet branch
  | branch :: rest =>
      let leftAlphabet := branch.2.alphabet
      let rightAlphabet : PactTypeAlphabet :=
        { actions := PactType.branchAlphabetActions rest }
      if branch = selected then
        .par alphabet (selectedTypeBranchAt leftAlphabet branch)
          (parallelTypeBranchesWithin rightAlphabet rest) ∅
      else
        .par alphabet (singletonTypeXOfferAt leftAlphabet branch)
          (parallelTypeBranchesSelectingWithin rightAlphabet selected rest) ∅

def parallelTypeBranchesSelecting (alphabet : PactTypeAlphabet)
    (selected : BareMessage × PactType) :
    List (BareMessage × PactType) → PactType
  | [] => .skip PactTypeAlphabet.empty
  | branch :: rest =>
      parallelTypeBranchesSelectingWithin alphabet selected (branch :: rest)

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
              (hBranches branches alphabet False hBranchesSize hFields.2)

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
      | xoffer _ elseType branches | offer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.reannotate, PactType.MustTockBeforeCompletion]
          exact and_congr (ih (sizeOf elseType) hElseSize elseType rfl alphabet)
            (hBranches branches alphabet hBranchesSize)

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
      | xoffer _ elseType branches | offer _ elseType branches =>
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
      | xoffer _ elseType branches | offer _ elseType branches =>
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
          rw [ih _ hE e rfl alphabet, hBranches bs alphabet hB]

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
      | xoffer _ elseType branches | offer _ elseType branches =>
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

/-- Actions appearing at the heads of an offer's branches. -/
def typeBranchActions
    (branches : List (BareMessage × PactType)) : Finset BareMessage :=
  (branches.map Prod.fst).toFinset

/-- Keep only offers whose message identifier belongs to `interface`. -/
def restrictTypeOffers (interface : Interface) (offers : Finset BareMessage) :
    Finset BareMessage :=
  offers.filter fun offer => offer.1 ∈ interface

/-- Remove offers hidden by a parallel interface. -/
def hideTypeOffers (interface : Interface) (offers : Finset BareMessage) :
    Finset BareMessage :=
  offers.filter fun offer => offer.1 ∉ interface

end

end Pact
