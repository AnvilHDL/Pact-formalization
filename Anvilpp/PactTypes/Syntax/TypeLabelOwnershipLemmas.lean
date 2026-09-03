import Anvilpp.PactTypes.Syntax.TypeLabelOwnershipDefs

namespace Pact

set_option maxHeartbeats 1000000

open Classical

/-! ## Membership helpers for `sends` and `combine` -/

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
                    (hLeftMessage msg .send ((TypeLabel.mem_sends_iff _ _).mp hSend)).2
                · exact Finset.mem_union_right _
                    (hRightMessage msg .send ((TypeLabel.mem_sends_iff _ _).mp hSend)).2

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


/-- A step's label mentions only messages the step currently offers.  The two
message-carrying rules publish exactly the fired action, and every composite
rule hides the same interface from label and offers alike. -/
theorem TypeOffers.labelActions_subset_current
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future) :
    ∀ msg dir, label.contains (.message msg dir) → (msg, dir) ∈ current := by
  induction hOffers with
  | action env alphabet msg dir =>
      intro m d hIn
      simp only [TypeLabel.message, TypeLabel.contains,
        Finset.mem_singleton] at hIn
      cases hIn
      simp
  | xoffer_branch env alphabet elseType branches action processType =>
      intro m d hIn
      simp only [TypeLabel.message, TypeLabel.contains,
        Finset.mem_singleton] at hIn
      cases hIn
      simp
  | action_wait | choice_left | choice_right | cycle | cycle_wait | skip
  | recur | seq_tock | seq_fuse_tock | xoffer_else | xoffer_wait
  | offer_some | offer_else | offer_wait =>
      intro m d hIn
      simp [TypeLabel.silent, TypeLabel.tock, TypeLabel.contains] at hIn
  | fair_left | fair_right | progress =>
      intro m d hIn
      simp [TypeLabel.fair, TypeLabel.progress, TypeLabel.contains] at hIn
  | seq _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | seq_fuse _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | par_fuse_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTock _ _ =>
      intro m d hIn
      rw [hTock] at hIn
      simp [TypeLabel.tock, TypeLabel.contains] at hIn
  | par _ _ _ interface _ _ _ _ _ leftLabel rightLabel _ _ _ _ _ _ _ _ _ _ _ hCond
      ihLeft ihRight =>
      intro m d hIn
      cases leftLabel with
      | tock =>
          cases rightLabel with
          | tock => simp [TypeLabel.combine, TypeLabel.contains] at hIn
          | actions _ =>
              simp [TypeLabel.combine, TypeLabel.silent,
                TypeLabel.contains] at hIn
      | actions leftObs =>
          cases rightLabel with
          | tock =>
              simp [TypeLabel.combine, TypeLabel.silent,
                TypeLabel.contains] at hIn
          | actions rightObs =>
              rw [contains_combine_message'] at hIn
              obtain ⟨hSide, hUnsynced⟩ := hIn
              have hNotIface : m ∉ interface := by
                intro hMem
                refine hUnsynced ?_
                simp only [TypeLabel.synced, Finset.mem_union, Finset.mem_inter]
                rcases hSide with hL | hR
                · cases d with
                  | send =>
                      exact Or.inl ⟨hMem, (TypeLabel.mem_sends_iff _ _).mpr hL⟩
                  | recv =>
                      refine Or.inr ⟨hMem, ?_⟩
                      have hEq := hCond.2.2.1
                      have : m ∈ interface ∩
                          (TypeLabel.actions rightObs).sends := by
                        rw [← hEq]
                        exact Finset.mem_inter.mpr
                          ⟨hMem, (TypeLabel.mem_recvs_iff _ _).mpr hL⟩
                      exact (Finset.mem_inter.mp this).2
                · cases d with
                  | send =>
                      exact Or.inr ⟨hMem, (TypeLabel.mem_sends_iff _ _).mpr hR⟩
                  | recv =>
                      refine Or.inl ⟨hMem, ?_⟩
                      have hEq := hCond.2.1
                      have : m ∈ interface ∩
                          (TypeLabel.actions leftObs).sends := by
                        rw [hEq]
                        exact Finset.mem_inter.mpr
                          ⟨hMem, (TypeLabel.mem_recvs_iff _ _).mpr hR⟩
                      exact (Finset.mem_inter.mp this).2
              simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union]
              refine ⟨?_, hNotIface⟩
              rcases hSide with hL | hR
              · exact Or.inl (ihLeft m d hL)
              · exact Or.inr (ihRight m d hR)
  | par_fuse _ _ _ interface _ _ _ leftLabel rightLabel _ _ _ _ _ _ _ _ hCond
      _ ihLeft ihRight =>
      intro m d hIn
      cases leftLabel with
      | tock =>
          cases rightLabel with
          | tock => simp [TypeLabel.combine, TypeLabel.contains] at hIn
          | actions _ =>
              simp [TypeLabel.combine, TypeLabel.silent,
                TypeLabel.contains] at hIn
      | actions leftObs =>
          cases rightLabel with
          | tock =>
              simp [TypeLabel.combine, TypeLabel.silent,
                TypeLabel.contains] at hIn
          | actions rightObs =>
              rw [contains_combine_message'] at hIn
              obtain ⟨hSide, hUnsynced⟩ := hIn
              have hNotIface : m ∉ interface := by
                intro hMem
                refine hUnsynced ?_
                simp only [TypeLabel.synced, Finset.mem_union, Finset.mem_inter]
                rcases hSide with hL | hR
                · cases d with
                  | send =>
                      exact Or.inl ⟨hMem, (TypeLabel.mem_sends_iff _ _).mpr hL⟩
                  | recv =>
                      refine Or.inr ⟨hMem, ?_⟩
                      have : m ∈ interface ∩
                          (TypeLabel.actions rightObs).sends := by
                        rw [← hCond.2.2.1]
                        exact Finset.mem_inter.mpr
                          ⟨hMem, (TypeLabel.mem_recvs_iff _ _).mpr hL⟩
                      exact (Finset.mem_inter.mp this).2
                · cases d with
                  | send =>
                      exact Or.inr ⟨hMem, (TypeLabel.mem_sends_iff _ _).mpr hR⟩
                  | recv =>
                      refine Or.inl ⟨hMem, ?_⟩
                      have : m ∈ interface ∩
                          (TypeLabel.actions leftObs).sends := by
                        rw [hCond.2.1]
                        exact Finset.mem_inter.mpr
                          ⟨hMem, (TypeLabel.mem_recvs_iff _ _).mpr hR⟩
                      exact (Finset.mem_inter.mp this).2
              simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union]
              refine ⟨?_, hNotIface⟩
              rcases hSide with hL | hR
              · exact Or.inl (ihLeft m d hL)
              · exact Or.inr (ihRight m d hR)
  | left_complete _ _ interface _ _ _ _ _ rightCurrent _ _ _ _ _ hRestC _ _ _
      _ ih =>
      intro m d hIn
      have hMem := ih m d hIn
      have hNotIface : m ∉ interface := by
        intro hIface
        have : (m, d) ∈ restrictTypeOffers interface rightCurrent := by
          simp only [restrictTypeOffers, Finset.mem_filter]
          exact ⟨hMem, hIface⟩
        rw [hRestC] at this
        exact Finset.notMem_empty _ this
      simp only [hideTypeOffers, Finset.mem_filter]
      exact ⟨hMem, hNotIface⟩
  | left_complete_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTock _ =>
      intro m d hIn
      rw [hTock] at hIn
      simp [TypeLabel.contains] at hIn
  | right_complete _ _ interface _ _ _ _ _ leftCurrent _ _ _ _ _ hRestC _ _ _
      _ ih =>
      intro m d hIn
      have hMem := ih m d hIn
      have hNotIface : m ∉ interface := by
        intro hIface
        have : (m, d) ∈ restrictTypeOffers interface leftCurrent := by
          simp only [restrictTypeOffers, Finset.mem_filter]
          exact ⟨hMem, hIface⟩
        rw [hRestC] at this
        exact Finset.notMem_empty _ this
      simp only [hideTypeOffers, Finset.mem_filter]
      exact ⟨hMem, hNotIface⟩
  | right_complete_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTock _ =>
      intro m d hIn
      rw [hTock] at hIn
      simp [TypeLabel.contains] at hIn

/-- Every message a step observes is declared by the source's own alphabet.
The two message-carrying rules gate on the alphabet, and every other rule
either carries no message or inherits one from a component the enclosing node
re-signs with its own alphabet. -/
theorem TypeOffers.labelActionsDeclared
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future)
    (hWF : source.AlphabetWellFormed) :
    ∀ msg dir, label.contains (.message msg dir) →
      (msg, dir) ∈ source.alphabet.actions := by
  induction hOffers with
  | action env alphabet msg dir _ hDecl =>
      intro m d hIn
      simp only [TypeLabel.message, TypeLabel.contains,
        Finset.mem_singleton] at hIn
      cases hIn
      simpa [PactType.alphabet] using hDecl
  | xoffer_branch env alphabet elseType branches action processType hCond
      hDecl =>
      intro m d hIn
      simp only [TypeLabel.message, TypeLabel.contains,
        Finset.mem_singleton] at hIn
      cases hIn
      simpa [PactType.alphabet] using hDecl _ hCond.2.1
  | seq env alphabet left left' right label current childFuture hChild
      hNotSkip hNotTock ih =>
      intro m d hIn
      simp only [PactType.AlphabetWellFormed] at hWF
      have := ih hWF.2.2.2.1 m d hIn
      rw [hWF.2.1] at this
      simpa [PactType.alphabet] using this
  | seq_fuse env alphabet skipAlphabet left right label current childFuture
      hChild hNotTock ih =>
      intro m d hIn
      simp only [PactType.AlphabetWellFormed] at hWF
      have := ih hWF.2.2.2.1 m d hIn
      rw [hWF.2.1] at this
      simpa [PactType.alphabet] using this
  | action_wait | choice_left | choice_right | cycle | cycle_wait | skip
  | recur | seq_tock | seq_fuse_tock | xoffer_else | xoffer_wait
  | offer_some | offer_else | offer_wait =>
      intro m d hIn
      simp [TypeLabel.silent, TypeLabel.tock, TypeLabel.contains] at hIn
  | fair_left | fair_right | progress =>
      intro m d hIn
      simp [TypeLabel.fair, TypeLabel.progress, TypeLabel.contains] at hIn
  | par_fuse_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTock _ _ =>
      intro m d hIn
      rw [hTock] at hIn
      simp [TypeLabel.tock, TypeLabel.contains] at hIn
  | left_complete _ _ interface _ _ _ _ _ rightCurrent _ _ _ hChild _ hRestC _ _
      _ _ ih =>
      intro m d hIn
      simp only [PactType.AlphabetWellFormed] at hWF
      have hDecl := ih hWF.2.2.2 m d hIn
      have hNotIface : m ∉ interface := by
        intro hIface
        have : (m, d) ∈ restrictTypeOffers interface rightCurrent := by
          simp only [restrictTypeOffers, Finset.mem_filter]
          exact ⟨hChild.labelActions_subset_current m d hIn, hIface⟩
        rw [hRestC] at this
        exact Finset.notMem_empty _ this
      have hParent := hWF.2.1.parent_eq_right
      simp only [PactType.alphabet]
      rw [← hParent]
      simp only [PactTypeAlphabet.hideInterface, Finset.mem_filter]
      exact ⟨hDecl, hNotIface⟩
  | right_complete _ _ interface _ _ _ _ _ leftCurrent _ _ _ hChild _ hRestC _ _
      _ _ ih =>
      intro m d hIn
      simp only [PactType.AlphabetWellFormed] at hWF
      have hDecl := ih hWF.2.2.1 m d hIn
      have hNotIface : m ∉ interface := by
        intro hIface
        have : (m, d) ∈ restrictTypeOffers interface leftCurrent := by
          simp only [restrictTypeOffers, Finset.mem_filter]
          exact ⟨hChild.labelActions_subset_current m d hIn, hIface⟩
        rw [hRestC] at this
        exact Finset.notMem_empty _ this
      have hParent := hWF.2.1.parent_eq_left
      simp only [PactType.alphabet]
      rw [← hParent]
      simp only [PactTypeAlphabet.hideInterface, Finset.mem_filter]
      exact ⟨hDecl, hNotIface⟩
  | left_complete_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTock _ =>
      intro m d hIn
      rw [hTock] at hIn
      simp [TypeLabel.contains] at hIn
  | right_complete_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTock _ =>
      intro m d hIn
      rw [hTock] at hIn
      simp [TypeLabel.contains] at hIn
  | par _ _ _ interface _ _ _ _ _ leftLabel rightLabel _ _ _ _ _ _ _ _ _ _ _
      hCond ihLeft ihRight =>
      intro m d hIn
      simp only [PactType.AlphabetWellFormed] at hWF
      cases leftLabel with
      | tock =>
          cases rightLabel with
          | tock => simp [TypeLabel.combine, TypeLabel.contains] at hIn
          | actions _ =>
              simp [TypeLabel.combine, TypeLabel.silent,
                TypeLabel.contains] at hIn
      | actions leftObs =>
          cases rightLabel with
          | tock =>
              simp [TypeLabel.combine, TypeLabel.silent,
                TypeLabel.contains] at hIn
          | actions rightObs =>
              rw [contains_combine_message'] at hIn
              obtain ⟨hSide, hUnsynced⟩ := hIn
              have hNotIface : m ∉ interface := by
                intro hMem
                refine hUnsynced ?_
                simp only [TypeLabel.synced, Finset.mem_union, Finset.mem_inter]
                rcases hSide with hL | hR
                · cases d with
                  | send =>
                      exact Or.inl ⟨hMem, (TypeLabel.mem_sends_iff _ _).mpr hL⟩
                  | recv =>
                      refine Or.inr ⟨hMem, ?_⟩
                      have : m ∈ interface ∩
                          (TypeLabel.actions rightObs).sends := by
                        rw [← hCond.2.2.1]
                        exact Finset.mem_inter.mpr
                          ⟨hMem, (TypeLabel.mem_recvs_iff _ _).mpr hL⟩
                      exact (Finset.mem_inter.mp this).2
                · cases d with
                  | send =>
                      exact Or.inr ⟨hMem, (TypeLabel.mem_sends_iff _ _).mpr hR⟩
                  | recv =>
                      refine Or.inl ⟨hMem, ?_⟩
                      have : m ∈ interface ∩
                          (TypeLabel.actions leftObs).sends := by
                        rw [hCond.2.1]
                        exact Finset.mem_inter.mpr
                          ⟨hMem, (TypeLabel.mem_recvs_iff _ _).mpr hR⟩
                      exact (Finset.mem_inter.mp this).2
              simp only [PactType.alphabet]
              rcases hSide with hL | hR
              · rw [← hWF.2.1.parent_eq_left]
                simp only [PactTypeAlphabet.hideInterface, Finset.mem_filter]
                exact ⟨ihLeft hWF.2.2.1 m d hL, hNotIface⟩
              · rw [← hWF.2.1.parent_eq_right]
                simp only [PactTypeAlphabet.hideInterface, Finset.mem_filter]
                exact ⟨ihRight hWF.2.2.2 m d hR, hNotIface⟩
  | par_fuse _ _ _ interface _ _ _ leftLabel rightLabel _ _ _ _ _ _ _ _ hCond
      _ ihLeft ihRight =>
      intro m d hIn
      simp only [PactType.AlphabetWellFormed] at hWF
      cases leftLabel with
      | tock =>
          cases rightLabel with
          | tock => simp [TypeLabel.combine, TypeLabel.contains] at hIn
          | actions _ =>
              simp [TypeLabel.combine, TypeLabel.silent,
                TypeLabel.contains] at hIn
      | actions leftObs =>
          cases rightLabel with
          | tock =>
              simp [TypeLabel.combine, TypeLabel.silent,
                TypeLabel.contains] at hIn
          | actions rightObs =>
              rw [contains_combine_message'] at hIn
              obtain ⟨hSide, hUnsynced⟩ := hIn
              have hNotIface : m ∉ interface := by
                intro hMem
                refine hUnsynced ?_
                simp only [TypeLabel.synced, Finset.mem_union, Finset.mem_inter]
                rcases hSide with hL | hR
                · cases d with
                  | send =>
                      exact Or.inl ⟨hMem, (TypeLabel.mem_sends_iff _ _).mpr hL⟩
                  | recv =>
                      refine Or.inr ⟨hMem, ?_⟩
                      have : m ∈ interface ∩
                          (TypeLabel.actions rightObs).sends := by
                        rw [← hCond.2.2.1]
                        exact Finset.mem_inter.mpr
                          ⟨hMem, (TypeLabel.mem_recvs_iff _ _).mpr hL⟩
                      exact (Finset.mem_inter.mp this).2
                · cases d with
                  | send =>
                      exact Or.inr ⟨hMem, (TypeLabel.mem_sends_iff _ _).mpr hR⟩
                  | recv =>
                      refine Or.inl ⟨hMem, ?_⟩
                      have : m ∈ interface ∩
                          (TypeLabel.actions leftObs).sends := by
                        rw [hCond.2.1]
                        exact Finset.mem_inter.mpr
                          ⟨hMem, (TypeLabel.mem_recvs_iff _ _).mpr hR⟩
                      exact (Finset.mem_inter.mp this).2
              simp only [PactType.alphabet]
              rcases hSide with hL | hR
              · rw [← hWF.2.1.parent_eq_left]
                simp only [PactTypeAlphabet.hideInterface, Finset.mem_filter]
                exact ⟨ihLeft hWF.2.2.1 m d hL, hNotIface⟩
              · rw [← hWF.2.1.parent_eq_right]
                simp only [PactTypeAlphabet.hideInterface, Finset.mem_filter]
                exact ⟨ihRight hWF.2.2.2 m d hR, hNotIface⟩

/-! ## Separation of sibling labels at a parallel node -/

/-- Sibling steps of a parallel node observe nothing in common.  Message actions and the
two identifier kinds are separated by the corresponding ownership predicate; a resolved
message is separated because interface scoping puts it outside this node's interface,
where the two components own disjoint message names. -/
theorem PactType.LabelOwned.separated
    {left right : PactType} {interface : Interface}
    {leftLabel rightLabel : TypeLabel}
    (hDeclLeft : ∀ msg dir, leftLabel.contains (.message msg dir) →
      (msg, dir) ∈ left.alphabet.actions)
    (hDeclRight : ∀ msg dir, rightLabel.contains (.message msg dir) →
      (msg, dir) ∈ right.alphabet.actions)
    (hComplementary :
      PactTypeAlphabet.ComplementaryOn left.alphabet right.alphabet interface)
    (hLeftPolarity : left.alphabet.WellFormed)
    (hRightPolarity : right.alphabet.WellFormed)
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
      by_cases hMem : msg ∈ interface
      · -- On the interface the two children carry opposite polarities.
        rcases hComplementary msg hMem with ⟨hL, hR⟩ | ⟨hL, hR⟩
        · cases dir with
          | send =>
              exact hRightPolarity msg ⟨hDeclRight msg .send hIn', hR⟩
          | recv =>
              exact hLeftPolarity msg ⟨hL, hDeclLeft msg .recv hIn⟩
        · cases dir with
          | send =>
              exact hLeftPolarity msg ⟨hDeclLeft msg .send hIn, hL⟩
          | recv =>
              exact hRightPolarity msg ⟨hR, hDeclRight msg .recv hIn'⟩
      · -- Outside the interface parallel ownership separates the identifiers.
        exact Finset.disjoint_left.mp hIds
          (Finset.mem_sdiff.mpr ⟨(hLeftMessage msg dir hIn).2, hMem⟩)
          (Finset.mem_sdiff.mpr ⟨(hRightMessage msg dir hIn').2, hMem⟩)
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
    (hAlphabet : (PactType.par alphabet left right interface).AlphabetWellFormed)
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
  have hIds : Disjoint (left.MessageIds \ interface)
      (right.MessageIds \ interface) := by
    refine Finset.disjoint_left.mpr ?_
    intro msg hLeftMem hRightMem
    rw [Finset.mem_sdiff] at hLeftMem hRightMem
    exact hLeftMem.2 (hMessage.1 (Finset.mem_inter.mpr
      ⟨hLeftMem.1, hRightMem.1⟩))
  have hLeftFresh : Disjoint interface left.ParallelInterfaces :=
    hScoped.1.mono_right Finset.subset_union_left
  have hRightFresh : Disjoint interface right.ParallelInterfaces :=
    hScoped.1.mono_right Finset.subset_union_right
  simp only [PactType.AlphabetWellFormed] at hAlphabet
  have hLeftPolarity : left.alphabet.WellFormed := by
    cases left <;>
      simp only [PactType.AlphabetWellFormed] at hAlphabet <;>
      first
        | exact hAlphabet.2.2.1
        | exact hAlphabet.2.2.1.1
  have hRightPolarity : right.alphabet.WellFormed := by
    cases right <;>
      simp only [PactType.AlphabetWellFormed] at hAlphabet <;>
      first
        | exact hAlphabet.2.2.2
        | exact hAlphabet.2.2.2.1
  have hSeparate : ∀ {leftLabel rightLabel : TypeLabel}
      {envL envR : TypeEnvironment} {tL tR : PactType}
      {cL fL cR fR : Finset BareMessage},
      TypeOffers envL left leftLabel tL cL fL →
      TypeOffers envR right rightLabel tR cR fR →
      ∀ observation, leftLabel.contains observation →
        ¬ rightLabel.contains observation := fun hL hR =>
    PactType.LabelOwned.separated
      (hL.labelActionsDeclared hAlphabet.2.2.1)
      (hR.labelActionsDeclared hAlphabet.2.2.2)
      hAlphabet.2.1.complementary hLeftPolarity hRightPolarity
      hIds hProgress.1 hFair.1 hScoped.1 hL.labelOwned hR.labelOwned
  refine ⟨hSeparate hA₁ hA₂, hSeparate hB₁ hB₂,
    hSeparate hA₁ hB₂, hSeparate hB₁ hA₂, ?_, ?_⟩
  · exact fun msg hMem =>
      ⟨PactType.LabelOwned.fresh hLeftFresh hA₁.labelOwned msg hMem,
        PactType.LabelOwned.fresh hRightFresh hA₂.labelOwned msg hMem⟩
  · exact fun msg hMem =>
      ⟨PactType.LabelOwned.fresh hLeftFresh hB₁.labelOwned msg hMem,
        PactType.LabelOwned.fresh hRightFresh hB₂.labelOwned msg hMem⟩

end Pact
