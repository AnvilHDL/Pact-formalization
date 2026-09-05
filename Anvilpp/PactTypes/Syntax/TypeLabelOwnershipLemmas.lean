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

/-! ## Separation of sibling labels at a parallel node -/

end Pact
