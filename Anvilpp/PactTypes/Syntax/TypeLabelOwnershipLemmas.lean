import Anvilpp.PactTypes.Syntax.TypeLabelOwnershipDefs

namespace Pact

set_option maxHeartbeats 1000000

open Classical

/-! ## Membership helpers for `sends` and `combine` -/

/-- A message id is sent by a label exactly when the label carries the send observation. -/
private theorem mem_sends_iff' (label : TypeLabel) (msg : MessageId) :
    msg ∈ label.sends ↔ label.contains (.message msg .send) := by
  cases label with
  | tock => simp [TypeLabel.sends, TypeLabel.contains]
  | actions observations =>
      simp only [TypeLabel.sends, TypeLabel.messageIdsWith, Finset.mem_image,
        Finset.mem_filter, TypeLabel.contains]
      constructor
      · rintro ⟨observation, ⟨hMem, hDir⟩, hMsg⟩
        cases observation <;> simp_all
      · intro hMem
        exact ⟨.message msg .send, ⟨hMem, rfl⟩, rfl⟩

/-- A raw message observation survives `combine` when it is not synchronised away. -/
private theorem contains_combine_message' (interface : Interface)
    (left right : Finset TypeObservation) (msg : MessageId) (dir : MessageDir) :
    (TypeLabel.combine interface (.actions left) (.actions right)).contains
        (.message msg dir) ↔
      (((TypeLabel.actions left).contains (.message msg dir) ∨
          (TypeLabel.actions right).contains (.message msg dir)) ∧
        msg ∉ TypeLabel.synced interface (.actions left) (.actions right)) := by
  simp [TypeLabel.combine, TypeLabel.contains, TypeLabel.isRawSyncedMessage,
    Finset.mem_union, Finset.mem_filter, Finset.mem_image]

/-- A resolved observation is in `combine` when it is raw in a component or newly synchronised. -/
private theorem contains_combine_resolved' (interface : Interface)
    (left right : Finset TypeObservation) (msg : MessageId) :
    (TypeLabel.combine interface (.actions left) (.actions right)).contains
        (.resolved msg) ↔
      ((TypeLabel.actions left).contains (.resolved msg) ∨
        (TypeLabel.actions right).contains (.resolved msg) ∨
        msg ∈ TypeLabel.synced interface (.actions left) (.actions right)) := by
  simp [TypeLabel.combine, TypeLabel.contains, TypeLabel.isRawSyncedMessage,
    Finset.mem_union, Finset.mem_filter, Finset.mem_image, or_assoc]

/-- Fair observations pass through `combine` untouched. -/
private theorem contains_combine_fair' (interface : Interface)
    (left right : Finset TypeObservation) (bid : BranchId) (taken : Bool) :
    (TypeLabel.combine interface (.actions left) (.actions right)).contains
        (.fair bid taken) ↔
      ((TypeLabel.actions left).contains (.fair bid taken) ∨
        (TypeLabel.actions right).contains (.fair bid taken)) := by
  simp [TypeLabel.combine, TypeLabel.contains, TypeLabel.isRawSyncedMessage,
    Finset.mem_union, Finset.mem_filter, Finset.mem_image]

/-- Progress observations pass through `combine` untouched. -/
private theorem contains_combine_progress' (interface : Interface)
    (left right : Finset TypeObservation) (pid : ProcId) :
    (TypeLabel.combine interface (.actions left) (.actions right)).contains
        (.progress pid) ↔
      ((TypeLabel.actions left).contains (.progress pid) ∨
        (TypeLabel.actions right).contains (.progress pid)) := by
  simp [TypeLabel.combine, TypeLabel.contains, TypeLabel.isRawSyncedMessage,
    Finset.mem_union, Finset.mem_filter, Finset.mem_image]

/-! ## Branch declarations -/

/-- Everything one branch declares by name is declared by the branch list. -/
theorem branch_subset_branchMessageIds
    {branches : List (BareMessage × PactType)} {branch : BareMessage × PactType}
    (hMem : branch ∈ branches) :
    {branch.1.1} ∪ PactType.MessageIds branch.2 ⊆
      PactType.BranchMessageIds branches := by
  induction branches with
  | nil => cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      simp only [PactType.BranchMessageIds]
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hTail
      · cases hEq
        exact Finset.subset_union_left
      · exact (ih hTail).trans Finset.subset_union_right

namespace PactType.LabelOwned

/-- The silent label observes nothing. -/
theorem silent (source : PactType) : source.LabelOwned TypeLabel.silent := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [TypeLabel.silent, TypeLabel.contains]

/-- The clock label observes nothing. -/
theorem tock (source : PactType) : source.LabelOwned TypeLabel.tock := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [TypeLabel.contains]

/-- Ownership transfers along declaration inclusions. -/
theorem mono {source source' : PactType} {label : TypeLabel}
    (hOwned : source.LabelOwned label)
    (hActions : source.MessageActions ⊆ source'.MessageActions)
    (hIds : source.MessageIds ⊆ source'.MessageIds)
    (hProgress : source.ProgressIds ⊆ source'.ProgressIds)
    (hFair : source.FairChoiceIds ⊆ source'.FairChoiceIds)
    (hInterfaces : source.ParallelInterfaces ⊆ source'.ParallelInterfaces) :
    source'.LabelOwned label := by
  obtain ⟨hMessage, hProg, hFairObs, hResolved⟩ := hOwned
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro msg dir hIn
    exact ⟨hActions (hMessage msg dir hIn).1, hIds (hMessage msg dir hIn).2⟩
  · intro pid hIn
    exact hProgress (hProg pid hIn)
  · intro bid taken hIn
    exact hFair (hFairObs bid taken hIn)
  · intro msg hIn
    exact ⟨hInterfaces (hResolved msg hIn).1, hIds (hResolved msg hIn).2⟩

/-- Ownership passes from a component of a parallel node to the node itself. -/
theorem of_left {alphabet : PactTypeAlphabet} {left right : PactType}
    {interface : Interface} {label : TypeLabel}
    (hOwned : left.LabelOwned label) :
    (PactType.par alphabet left right interface).LabelOwned label := by
  refine hOwned.mono ?_ ?_ ?_ ?_ ?_ <;>
    simp only [PactType.MessageActions, PactType.MessageIds, PactType.ProgressIds,
      PactType.FairChoiceIds, PactType.ParallelInterfaces]
  · exact Finset.subset_union_left
  · exact Finset.subset_union_left
  · exact Finset.subset_union_left
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right.trans Finset.subset_union_left

/-- Ownership passes from a component of a parallel node to the node itself. -/
theorem of_right {alphabet : PactTypeAlphabet} {left right : PactType}
    {interface : Interface} {label : TypeLabel}
    (hOwned : right.LabelOwned label) :
    (PactType.par alphabet left right interface).LabelOwned label := by
  refine hOwned.mono ?_ ?_ ?_ ?_ ?_ <;>
    simp only [PactType.MessageActions, PactType.MessageIds, PactType.ProgressIds,
      PactType.FairChoiceIds, PactType.ParallelInterfaces]
  · exact Finset.subset_union_right
  · exact Finset.subset_union_right
  · exact Finset.subset_union_right
  · exact Finset.subset_union_right
  · exact Finset.subset_union_right

/-- A combined parallel label is owned by the parallel node.  A message observation
survives from one component; a resolved observation is either raw in a component or
is minted here, in which case its name is this node's own interface and is sent by a
component. -/
theorem combine {alphabet : PactTypeAlphabet} {left right : PactType}
    {interface : Interface} {leftLabel rightLabel : TypeLabel}
    (hLeft : left.LabelOwned leftLabel) (hRight : right.LabelOwned rightLabel) :
    (PactType.par alphabet left right interface).LabelOwned
      (TypeLabel.combine interface leftLabel rightLabel) := by
  cases leftLabel with
  | tock =>
      cases rightLabel with
      | tock => exact tock _
      | actions rightObservations => exact silent _
  | actions leftObservations =>
      cases rightLabel with
      | tock => exact silent _
      | actions rightObservations =>
          obtain ⟨hLeftMessage, hLeftProgress, hLeftFair, hLeftResolved⟩ := hLeft
          obtain ⟨hRightMessage, hRightProgress, hRightFair, hRightResolved⟩ := hRight
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            simp only [PactType.MessageActions, PactType.MessageIds,
              PactType.ProgressIds, PactType.FairChoiceIds,
              PactType.ParallelInterfaces]
          · intro msg dir hIn
            rcases ((contains_combine_message' interface leftObservations
              rightObservations msg dir).mp hIn).1 with h | h
            · exact ⟨Finset.mem_union_left _ (hLeftMessage msg dir h).1,
                Finset.mem_union_left _ (hLeftMessage msg dir h).2⟩
            · exact ⟨Finset.mem_union_right _ (hRightMessage msg dir h).1,
                Finset.mem_union_right _ (hRightMessage msg dir h).2⟩
          · intro pid hIn
            rcases (contains_combine_progress' interface leftObservations
              rightObservations pid).mp hIn with h | h
            · exact Finset.mem_union_left _ (hLeftProgress pid h)
            · exact Finset.mem_union_right _ (hRightProgress pid h)
          · intro bid taken hIn
            rcases (contains_combine_fair' interface leftObservations
              rightObservations bid taken).mp hIn with h | h
            · exact Finset.mem_union_left _ (hLeftFair bid taken h)
            · exact Finset.mem_union_right _ (hRightFair bid taken h)
          · intro msg hIn
            rcases (contains_combine_resolved' interface leftObservations
              rightObservations msg).mp hIn with h | h | h
            · refine ⟨?_, Finset.mem_union_left _ (hLeftResolved msg h).2⟩
              exact Finset.mem_union_left _
                (Finset.mem_union_right _ (hLeftResolved msg h).1)
            · refine ⟨?_, Finset.mem_union_right _ (hRightResolved msg h).2⟩
              exact Finset.mem_union_right _ (hRightResolved msg h).1
            · simp only [TypeLabel.synced, Finset.mem_union, Finset.mem_inter] at h
              refine ⟨?_, ?_⟩
              · rcases h with ⟨hInterface, _⟩ | ⟨hInterface, _⟩ <;>
                  exact Finset.mem_union_left _ (Finset.mem_union_left _ hInterface)
              · rcases h with ⟨_, hSend⟩ | ⟨_, hSend⟩
                · exact Finset.mem_union_left _
                    (hLeftMessage msg .send ((mem_sends_iff' _ _).mp hSend)).2
                · exact Finset.mem_union_right _
                    (hRightMessage msg .send ((mem_sends_iff' _ _).mp hSend)).2

end PactType.LabelOwned

/-! ## A decorated step only observes what its source declares -/

/-- A decorated step's label observations are all drawn from its source type. -/
theorem TypeOffers.labelOwned
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future) :
    source.LabelOwned label := by
  induction hOffers with
  | action env alphabet msg dir =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
        simp_all [TypeLabel.message, TypeLabel.contains, PactType.MessageActions,
          PactType.MessageIds]
  | action_wait => exact PactType.LabelOwned.silent _
  | choice_left => exact PactType.LabelOwned.silent _
  | choice_right => exact PactType.LabelOwned.silent _
  | fair_left env alphabet bid left right =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
        simp_all [TypeLabel.fair, TypeLabel.contains, PactType.FairChoiceIds]
  | fair_right env alphabet bid left right =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
        simp_all [TypeLabel.fair, TypeLabel.contains, PactType.FairChoiceIds]
  | cycle => exact PactType.LabelOwned.tock _
  | cycle_wait => exact PactType.LabelOwned.silent _
  | skip => exact PactType.LabelOwned.silent _
  | progress env alphabet pid =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
        simp_all [TypeLabel.progress, TypeLabel.contains, PactType.ProgressIds]
  | recur => exact PactType.LabelOwned.silent _
  | seq env alphabet left left' right label current childFuture hChild hNotSkip
      hNotTock ihChild =>
      refine ihChild.mono ?_ ?_ ?_ ?_ ?_ <;>
        simp only [PactType.MessageActions, PactType.MessageIds, PactType.ProgressIds,
          PactType.FairChoiceIds, PactType.ParallelInterfaces] <;>
        exact Finset.subset_union_left
  | seq_tock => exact PactType.LabelOwned.tock _
  | seq_fuse env alphabet skipAlphabet left right label current childFuture hChild
      hNotTock ihChild =>
      refine ihChild.mono ?_ ?_ ?_ ?_ ?_ <;>
        simp only [PactType.MessageActions, PactType.MessageIds, PactType.ProgressIds,
          PactType.FairChoiceIds, PactType.ParallelInterfaces] <;>
        exact Finset.subset_union_left
  | seq_fuse_tock => exact PactType.LabelOwned.tock _
  | xoffer_branch env alphabet elseType branches action processType hConditions
      hAlphabet =>
      have hAction : action ∈ PactType.BranchMessageActions branches :=
        branch_subset_branchMessageActions hConditions.2.1
          (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      have hName : action.1 ∈ PactType.BranchMessageIds branches :=
        branch_subset_branchMessageIds hConditions.2.1
          (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro msg dir hIn
        simp only [TypeLabel.message, TypeLabel.contains, Finset.mem_singleton] at hIn
        cases hIn
        simp only [PactType.MessageActions, PactType.MessageIds]
        refine ⟨Finset.mem_union_right _ ?_, Finset.mem_union_right _ hName⟩
        simpa using hAction
      · intro pid hIn
        simp [TypeLabel.message, TypeLabel.contains] at hIn
      · intro bid taken hIn
        simp [TypeLabel.message, TypeLabel.contains] at hIn
      · intro msg hIn
        simp [TypeLabel.message, TypeLabel.contains] at hIn
  | xoffer_else => exact PactType.LabelOwned.silent _
  | xoffer_wait => exact PactType.LabelOwned.silent _
  | offer_some => exact PactType.LabelOwned.silent _
  | offer_else => exact PactType.LabelOwned.silent _
  | offer_wait => exact PactType.LabelOwned.silent _
  | par outer leftEnv rightEnv interface alphabet left left' right right' leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeftNotSkip hRightNotSkip
      hLeft hRight hNotBothSkip hLocalLeft hLocalRight hConditions ihLeft ihRight =>
      exact PactType.LabelOwned.combine ihLeft ihRight
  | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeft hRight hLocalLeft
      hLocalRight hConditions hNotTock ihLeft ihRight =>
      exact PactType.LabelOwned.combine ihLeft ihRight
  | par_fuse_tock outer leftEnv rightEnv interface alphabet left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeft hRight hLocalLeft
      hLocalRight hConditions hTock ihLeft ihRight =>
      exact PactType.LabelOwned.combine ihLeft ihRight
  | left_complete outer rightEnv interface alphabet left right right' rightLabel rightCurrent
      rightFuture hLeftSkip hRightNotSkip hRight hNotSkip hCurrent hFuture hLocal
      hWF hNotTock ihRight =>
      exact PactType.LabelOwned.of_right ihRight
  | left_complete_tock outer rightEnv interface alphabet left right right' rightLabel
      rightCurrent rightFuture hLeftSkip hRightNotSkip hRight hNotSkip hCurrent
      hFuture hLocal hWF hTock ihRight =>
      exact PactType.LabelOwned.of_right ihRight
  | right_complete outer leftEnv interface alphabet left left' right leftLabel leftCurrent
      leftFuture hRightSkip hLeftNotSkip hLeft hNotSkip hCurrent hFuture hLocal
      hWF hNotTock ihLeft =>
      exact PactType.LabelOwned.of_left ihLeft
  | right_complete_tock outer leftEnv interface alphabet left left' right leftLabel
      leftCurrent leftFuture hRightSkip hLeftNotSkip hLeft hNotSkip hCurrent
      hFuture hLocal hWF hTock ihLeft =>
      exact PactType.LabelOwned.of_left ihLeft

/-! ## Separation of sibling labels at a parallel node -/

/-- Sibling steps of a parallel node observe nothing in common.  Message actions and the
two identifier kinds are separated by the corresponding ownership predicate; a resolved
message is separated because interface scoping puts it outside this node's interface,
where the two components own disjoint message names. -/
theorem PactType.LabelOwned.separated
    {left right : PactType} {interface : Interface}
    {leftLabel rightLabel : TypeLabel}
    (hActions : Disjoint left.MessageActions right.MessageActions)
    (hIds : Disjoint (left.MessageIds \ interface) (right.MessageIds \ interface))
    (hProgress : Disjoint left.ProgressIds right.ProgressIds)
    (hFair : Disjoint left.FairChoiceIds right.FairChoiceIds)
    (hScoped :
      Disjoint interface (left.ParallelInterfaces ∪ right.ParallelInterfaces))
    (hLeft : left.LabelOwned leftLabel) (hRight : right.LabelOwned rightLabel) :
    ∀ observation, leftLabel.contains observation → ¬ rightLabel.contains observation := by
  obtain ⟨hLeftMessage, hLeftProgress, hLeftFair, hLeftResolved⟩ := hLeft
  obtain ⟨hRightMessage, hRightProgress, hRightFair, hRightResolved⟩ := hRight
  intro observation hIn hIn'
  cases observation with
  | message msg dir =>
      exact Finset.disjoint_left.mp hActions (hLeftMessage msg dir hIn).1
        (hRightMessage msg dir hIn').1
  | resolved msg =>
      have hOutside : msg ∉ interface := fun hMem =>
        Finset.disjoint_left.mp hScoped hMem
          (Finset.mem_union_left _ (hLeftResolved msg hIn).1)
      exact Finset.disjoint_left.mp hIds
        (Finset.mem_sdiff.mpr ⟨(hLeftResolved msg hIn).2, hOutside⟩)
        (Finset.mem_sdiff.mpr ⟨(hRightResolved msg hIn').2, hOutside⟩)
  | fair bid taken =>
      exact Finset.disjoint_left.mp hFair (hLeftFair bid taken hIn)
        (hRightFair bid taken hIn')
  | progress pid =>
      exact Finset.disjoint_left.mp hProgress (hLeftProgress pid hIn)
        (hRightProgress pid hIn')

/-- A step of a component never mints a resolved observation for a name the enclosing
parallel node synchronises: resolved names come from binders inside the component, and
interface scoping keeps those away from the enclosing interface. -/
theorem PactType.LabelOwned.fresh
    {source : PactType} {interface : Interface} {label : TypeLabel}
    (hScoped : Disjoint interface source.ParallelInterfaces)
    (hOwned : source.LabelOwned label) :
    ∀ msg ∈ interface, ¬ label.contains (.resolved msg) := fun msg hMem hIn =>
  Finset.disjoint_left.mp hScoped hMem (hOwned.2.2.2 msg hIn).1

/-- The six label-level hypotheses of `TypeLabel.combine_inj`, discharged at a parallel
node from its type-level ownership and interface-scoping invariants and two pairs of
decorated component steps. -/
theorem TypeOffers.par_combine_inj_hypotheses
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    (hMessage : (PactType.par alphabet left right interface).ParallelMessageOwnership)
    (hProgress : (PactType.par alphabet left right interface).ParallelProgressOwnership)
    (hFair : (PactType.par alphabet left right interface).ParallelFairChoiceOwnership)
    (hScoped : (PactType.par alphabet left right interface).InterfaceScoped)
    {envA₁ envA₂ envB₁ envB₂ : TypeEnvironment}
    {a₁ a₂ b₁ b₂ : TypeLabel}
    {leftA rightA leftB rightB : PactType}
    {currentA₁ futureA₁ currentA₂ futureA₂ : Finset BareMessage}
    {currentB₁ futureB₁ currentB₂ futureB₂ : Finset BareMessage}
    (hA₁ : TypeOffers envA₁ left a₁ leftA currentA₁ futureA₁)
    (hA₂ : TypeOffers envA₂ right a₂ rightA currentA₂ futureA₂)
    (hB₁ : TypeOffers envB₁ left b₁ leftB currentB₁ futureB₁)
    (hB₂ : TypeOffers envB₂ right b₂ rightB currentB₂ futureB₂) :
    (∀ observation, a₁.contains observation → ¬ a₂.contains observation) ∧
      (∀ observation, b₁.contains observation → ¬ b₂.contains observation) ∧
      (∀ observation, a₁.contains observation → ¬ b₂.contains observation) ∧
      (∀ observation, b₁.contains observation → ¬ a₂.contains observation) ∧
      (∀ msg ∈ interface,
        ¬ a₁.contains (.resolved msg) ∧ ¬ a₂.contains (.resolved msg)) ∧
      (∀ msg ∈ interface,
        ¬ b₁.contains (.resolved msg) ∧ ¬ b₂.contains (.resolved msg)) := by
  simp only [PactType.ParallelMessageOwnership] at hMessage
  simp only [PactType.ParallelProgressOwnership] at hProgress
  simp only [PactType.ParallelFairChoiceOwnership] at hFair
  simp only [PactType.InterfaceScoped] at hScoped
  have hLeftFresh : Disjoint interface left.ParallelInterfaces :=
    hScoped.1.mono_right Finset.subset_union_left
  have hRightFresh : Disjoint interface right.ParallelInterfaces :=
    hScoped.1.mono_right Finset.subset_union_right
  have hSeparate : ∀ {leftLabel rightLabel : TypeLabel},
      left.LabelOwned leftLabel → right.LabelOwned rightLabel →
      ∀ observation, leftLabel.contains observation →
        ¬ rightLabel.contains observation := fun hL hR =>
    PactType.LabelOwned.separated hMessage.2.1 hMessage.1 hProgress.1 hFair.1
      hScoped.1 hL hR
  refine ⟨hSeparate hA₁.labelOwned hA₂.labelOwned,
    hSeparate hB₁.labelOwned hB₂.labelOwned,
    hSeparate hA₁.labelOwned hB₂.labelOwned,
    hSeparate hB₁.labelOwned hA₂.labelOwned, ?_, ?_⟩
  · exact fun msg hMem =>
      ⟨PactType.LabelOwned.fresh hLeftFresh hA₁.labelOwned msg hMem,
        PactType.LabelOwned.fresh hRightFresh hA₂.labelOwned msg hMem⟩
  · exact fun msg hMem =>
      ⟨PactType.LabelOwned.fresh hLeftFresh hB₁.labelOwned msg hMem,
        PactType.LabelOwned.fresh hRightFresh hB₂.labelOwned msg hMem⟩

end Pact
