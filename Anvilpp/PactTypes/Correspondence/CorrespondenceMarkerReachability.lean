import Anvilpp.PactTypes.Correspondence.CorrespondenceRecursionClosure

/-!
# Marker reachability vs. the syntactic marker analysis; compilationMarkerReachable_iff
-/

namespace Pact

noncomputable section

/-! ### Marker reachability against the syntactic marker analysis -/

/-- A branch list reaches a marker exactly when one of its continuations
does. -/
private theorem branchMarkerReachableSubst_iff_exists (name : String) :
    ∀ branches : List (BareMessage × PactType),
      (PactType.branchMarkerReachableSubst name branches = true ↔
        ∃ entry ∈ branches,
          PactType.markerReachableSubst name entry.2 = true) :=
  sorry
private theorem not_buildExclusiveOfferAutomaton_markerSource_root
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (name : String) :
    ¬ MarkerSource (buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata) name .root :=
  sorry
private theorem not_buildSelectedConjunctiveOfferAutomaton_markerSource_root
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (name : String) :
    ¬ MarkerSource (buildSelectedConjunctiveOfferAutomaton signature branches
      elseAutomaton selectedConjunctions) name .root :=
  sorry
private theorem not_buildSequenceAutomaton_markerSource_left
    (signature : TypeAlphabet) (left right : AutomatonFragment) (name : String)
    (hLeftNoMarkers : ∀ edge ∈ left.edges,
      edge.label ≠ AutomatonConstructionLabel.variable name)
    (state : TypeAutomatonState) :
    ¬ MarkerSource (buildSequenceAutomaton signature left right) name
      (.child 0 state) :=
  sorry
private theorem buildSequenceAutomaton_markerReachable_left
    (signature : TypeAlphabet) (left right : AutomatonFragment) (name : String)
    (hLeftNoMarkers : ∀ edge ∈ left.edges,
      edge.label ≠ AutomatonConstructionLabel.variable name)
    (state : TypeAutomatonState)
    (hLeftState : state ∈ left.states)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    (MarkerReachable (buildSequenceAutomaton signature left right) name
        (.child 0 state) ↔
      ((∃ completed ∈ (sequenceExecutionAutomaton left).futureReachable state,
          completed ∈ left.accepting ∨ completed ∈ left.completing) ∧
        MarkerReachable right name right.initial)) :=
  sorry
private theorem card_le_of_childStates_subset
    (child parent : AutomatonFragment) (index : Nat)
    (hSubset : childStates index child ⊆ parent.states) :
    child.states.card ≤ parent.states.card :=
  sorry
private theorem buildChoiceAutomaton_markerReachable_classified
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel) (name : String)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftIH : ∀ q r, TypeCompilationRelation left q r →
      (MarkerReachable (compileTypeFuel signature (typeCompilationFuel left)
        left) name q ↔ PactType.markerReachableSubst name r = true))
    (hRightIH : ∀ q r, TypeCompilationRelation right q r →
      (MarkerReachable (compileTypeFuel signature (typeCompilationFuel right)
        right) name q ↔ PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let fragment := buildChoiceAutomaton signature
      (compileTypeFuel signature fuel left) (compileTypeFuel signature fuel right)
      selectionLeft selectionRight
    (MarkerReachable fragment name .root ↔
        (PactType.markerReachableSubst name left = true ∨
          PactType.markerReachableSubst name right = true)) ∧
      (∀ q r, TypeCompilationRelation left q r →
        (MarkerReachable fragment name (.child 0 q) ↔
          PactType.markerReachableSubst name r = true)) ∧
      (∀ q r, TypeCompilationRelation right q r →
        (MarkerReachable fragment name (.child 1 q) ↔
          PactType.markerReachableSubst name r = true)) :=
  sorry
private theorem buildSequenceAutomaton_markerReachable_classified
    (signature : TypeAlphabet) (left right : PactType) (name : String)
    (hLeftAbsent : left.TailOccurrences name False)
    (hLeftExecution : CompilationSequenceExecutionCorrect signature left)
    (hRightIH : ∀ q r, TypeCompilationRelation right q r →
      (MarkerReachable (compileTypeFuel signature (typeCompilationFuel right)
        right) name q ↔ PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let fragment := buildSequenceAutomaton signature
      (compileTypeFuel signature fuel left)
      (compileTypeFuel signature fuel right)
    (∀ q r, TypeCompilationRelation left q r →
        (MarkerReachable fragment name (.child 0 q) ↔
          PactType.markerReachableSubst name (.seq r right) = true)) ∧
      (∀ q r, TypeCompilationRelation right q r →
        (MarkerReachable fragment name (.child 1 q) ↔
          PactType.markerReachableSubst name r = true)) :=
  sorry
private theorem exists_getElem?_of_mem
    {Element : Type} {element : Element} {items : List Element}
    (hMember : element ∈ items) :
    ∃ index : Nat, items[index]? = some element :=
  sorry
private theorem mem_zipIdx_of_getElem?
    {Element : Type} {items : List Element} {index : Nat} {element : Element}
    (hEntry : items[index]? = some element) :
    (element, index) ∈ items.zipIdx :=
  sorry
private theorem buildExclusiveOfferAutomaton_markerReachable_classified
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (name : String)
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hElseIH : ∀ q r, TypeCompilationRelation elseType q r →
      (MarkerReachable (compileTypeFuel signature
        (typeCompilationFuel elseType) elseType) name q ↔
          PactType.markerReachableSubst name r = true))
    (hBranchIH : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
      ∀ q r, TypeCompilationRelation branchType q r →
        (MarkerReachable (compileTypeFuel signature
          (typeCompilationFuel branchType) branchType) name q ↔
            PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel elseType)
      (typeBranchCompilationFuel branches)
    let fragment := buildExclusiveOfferAutomaton signature branches
      (compileTypeFuel signature fuel elseType)
      (branches.map fun branch =>
        (branch.1, compileTypeFuel signature fuel branch.2))
    (MarkerReachable fragment name .root ↔
        PactType.markerReachableSubst name (.xoffer elseType branches) = true) ∧
      (∀ q r, TypeCompilationRelation elseType q r →
        (MarkerReachable fragment name (.child 0 q) ↔
          PactType.markerReachableSubst name r = true)) ∧
      (∀ (action : BareMessage) (branchType : PactType) (index : Nat),
        branches[index]? = some (action, branchType) →
        ∀ q r, TypeCompilationRelation branchType q r →
          (MarkerReachable fragment name (.child (index + 1) q) ↔
            PactType.markerReachableSubst name r = true)) :=
  sorry
theorem selectedConjunction_zipIdx_cases
    (signature : TypeAlphabet) (fuel : Nat)
    (branches : List (BareMessage × PactType))
    (indexed : (BareMessage × AutomatonFragment) × Nat)
    (hIndexed : indexed ∈
      (branches.map fun selected =>
        (selected.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches))).zipIdx) :
    ∃ selected : BareMessage × PactType,
      branches[indexed.2]? = some selected ∧
        indexed.1 = (selected.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches)) :=
  sorry
private theorem tailOccurrences_false_of_branch_mem (name : String) :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.TailBranchOccurrences name False branches →
      ∀ entry ∈ branches, PactType.TailOccurrences name False entry.2 :=
  sorry
private theorem buildSelectedConjunctiveOfferAutomaton_markerReachable_classified
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (name : String)
    (hSupports : signature.Supports (.offer elseType branches))
    (hBranchesAbsent : PactType.TailBranchOccurrences name False branches)
    (hElseIH : ∀ q r, TypeCompilationRelation elseType q r →
      (MarkerReachable (compileTypeFuel signature
        (typeCompilationFuel elseType) elseType) name q ↔
          PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel elseType)
      (conjunctiveCompilationFuel branches)
    let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
      (compileTypeFuel signature fuel elseType)
      (branches.map fun selected =>
        (selected.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches)))
    (MarkerReachable fragment name .root ↔
        PactType.markerReachableSubst name (.offer elseType branches) = true) ∧
      (∀ q r, TypeCompilationRelation elseType q r →
        (MarkerReachable fragment name (.child 0 q) ↔
          PactType.markerReachableSubst name r = true)) ∧
      (∀ (selected : BareMessage × PactType) (index : Nat),
        branches[index]? = some selected →
        ∀ q r, TypeCompilationRelation
            (parallelTypeBranchesSelecting selected branches) q r →
          (MarkerReachable fragment name (.child (index + 1) q) ↔
            PactType.markerReachableSubst name r = true)) :=
  sorry
theorem tailOccurrences_branch_of_mem (name : String) (tail : Prop) :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.TailBranchOccurrences name tail branches →
      ∀ entry ∈ branches, PactType.TailOccurrences name tail entry.2 :=
  sorry
private theorem branch_sizeOf_lt (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (entry : BareMessage × PactType) (hMember : entry ∈ branches) :
    sizeOf entry.2 < sizeOf (PactType.xoffer elseType branches) ∧
      sizeOf entry.2 < sizeOf (PactType.offer elseType branches) :=
  sorry
private theorem not_sequenceExecutionMarkerReachable_of_tailOccurrences_false
    (signature : TypeAlphabet) (name : String) (fuel : Nat)
    (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel)
    (hTail : processType.TailOccurrences name False)
    (state : TypeAutomatonState) :
    ¬ MarkerReachable
      (sequenceExecutionFragment
        (compileTypeFuel signature fuel processType)) name state :=
  sorry
private theorem compileTypeFuel_variableEdge_target_sink
    (signature : TypeAlphabet) (name : String) :
    ∀ (fuel : Nat) (processType : PactType),
      TypeCompilationFuelSufficient processType fuel →
      processType.TailOccurrences name True →
      ∀ marker ∈ (compileTypeFuel signature fuel processType).edges,
        marker.label = AutomatonConstructionLabel.variable name →
        ∀ edge ∈ (compileTypeFuel signature fuel processType).edges,
          edge.source ≠ marker.target :=
  sorry
private theorem markerStopped_sequenceExecution_markerReachable_iff
    (signature : TypeAlphabet) (stoppedName query : String)
    (fuel : Nat) (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel)
    (hTail : processType.TailOccurrences stoppedName True)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature fuel processType).states) :
    MarkerReachable
        (markerStoppedFragment
          (sequenceExecutionFragment
            (compileTypeFuel signature fuel processType)) stoppedName)
        query state ↔
      MarkerReachable
        (sequenceExecutionFragment
          (compileTypeFuel signature fuel processType)) query state :=
  sorry
theorem markerStopped_sequenceExecution_computeFuture
    (signature : TypeAlphabet) (stoppedName : String)
    (fuel : Nat) (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel)
    (hTail : processType.TailOccurrences stoppedName True)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature fuel processType).states) :
    computeFuture
        (markerStoppedFragment
          (sequenceExecutionFragment
            (compileTypeFuel signature fuel processType)) stoppedName).toPending
        state =
      computeFuture
        (sequenceExecutionAutomaton
          (compileTypeFuel signature fuel processType)) state :=
  sorry
theorem compilationMarkerReachable_iff (signature : TypeAlphabet) :
    ∀ (bound : List String) (name : String) (processType : PactType),
      name ∈ bound →
      PactType.AllTailOccurrences bound True processType →
      signature.WellFormed →
      signature.Supports processType →
      PactType.AllVariablesBound bound processType →
      PactType.BinderHygienic bound processType →
      PactType.ClockGuarded processType →
      PactType.TailRecursive processType →
      PactType.SameCycleMessageLinear processType →
      PactType.InterfaceScoped processType →
      (∀ child : PactType, sizeOf child < sizeOf processType →
        signature.Supports child → PactType.AllVariablesBound [] child →
        PactType.BinderHygienic [] child → PactType.ClockGuarded child →
        PactType.TailRecursive child →
        PactType.SameCycleMessageLinear child →
        PactType.InterfaceScoped child →
          CompilationProofBundle signature child) →
      ∀ state residual,
        TypeCompilationRelation processType state residual →
          (MarkerReachable (compileTypeFuel signature
              (typeCompilationFuel processType) processType) name state ↔
            PactType.markerReachableSubst name residual = true) :=
  sorry
end

noncomputable section

/-! ### Marker reachability in the sequence-execution view -/

/-- If a constructor root reaches exactly a finite collection of entries in
both graph views, marker reachability agrees at the root as soon as it agrees
at every entry. -/
private theorem sequenceExecution_markerReachable_iff_raw_of_entries
    (fragment : AutomatonFragment) (name : String)
    (entries : Finset TypeAutomatonState)
    (hTargets : fragment.FutureTargetsInStates)
    (hRoot : (.root : TypeAutomatonState) ∈ fragment.states)
    (hShape : ∀ edge ∈ fragment.edges, edge.source = .root →
      edge.label ≠ .future ∧
        ∃ removed, edge.future = .at edge.target removed)
    (hRawClosed : fragment.toPending.ReferencesClosed)
    (hUpper : fragment.toPending.referencedStates .root ⊆
      insert .root entries)
    (hEntries : entries ⊆ fragment.toPending.referencedStates .root)
    (hEntry : ∀ entry ∈ entries,
      MarkerReachable (sequenceExecutionFragment fragment) name entry ↔
        MarkerReachable fragment name entry) :
    MarkerReachable (sequenceExecutionFragment fragment) name .root ↔
      MarkerReachable fragment name .root :=
  sorry
private theorem buildChoiceAutomaton_sequenceExecutionMarkerReachable_classified
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel) (name : String)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftIH : ∀ q r, TypeCompilationRelation left q r →
      (MarkerReachable (sequenceExecutionFragment
        (compileTypeFuel signature (typeCompilationFuel left) left)) name q ↔
          PactType.markerReachableSubst name r = true))
    (hRightIH : ∀ q r, TypeCompilationRelation right q r →
      (MarkerReachable (sequenceExecutionFragment
        (compileTypeFuel signature (typeCompilationFuel right) right)) name q ↔
          PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let fragment := buildChoiceAutomaton signature
      (compileTypeFuel signature fuel left)
      (compileTypeFuel signature fuel right)
      selectionLeft selectionRight
    (MarkerReachable (sequenceExecutionFragment fragment) name .root ↔
        (PactType.markerReachableSubst name left = true ∨
          PactType.markerReachableSubst name right = true)) ∧
      (∀ q r, TypeCompilationRelation left q r →
        (MarkerReachable (sequenceExecutionFragment fragment) name
            (.child 0 q) ↔
          PactType.markerReachableSubst name r = true)) ∧
      (∀ q r, TypeCompilationRelation right q r →
        (MarkerReachable (sequenceExecutionFragment fragment) name
            (.child 1 q) ↔
          PactType.markerReachableSubst name r = true)) :=
  sorry
private theorem buildSequenceAutomaton_sequenceExecutionMarkerReachable_classified
    (signature : TypeAlphabet) (left right : PactType) (name : String)
    (hLeftAbsent : left.TailOccurrences name False)
    (hLeftExecution : CompilationSequenceExecutionCorrect signature left)
    (hRightIH : ∀ q r, TypeCompilationRelation right q r →
      (MarkerReachable (sequenceExecutionFragment
        (compileTypeFuel signature (typeCompilationFuel right) right)) name q ↔
          PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let fragment := buildSequenceAutomaton signature
      (compileTypeFuel signature fuel left)
      (compileTypeFuel signature fuel right)
    (∀ q r, TypeCompilationRelation left q r →
        (MarkerReachable (sequenceExecutionFragment fragment) name
            (.child 0 q) ↔
          PactType.markerReachableSubst name (.seq r right) = true)) ∧
      (∀ q r, TypeCompilationRelation right q r →
        (MarkerReachable (sequenceExecutionFragment fragment) name
            (.child 1 q) ↔
          PactType.markerReachableSubst name r = true)) :=
  sorry
private theorem buildExclusiveOfferAutomaton_sequenceExecutionMarkerReachable_classified
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (name : String)
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hElseIH : ∀ q r, TypeCompilationRelation elseType q r →
      (MarkerReachable (sequenceExecutionFragment
        (compileTypeFuel signature (typeCompilationFuel elseType) elseType))
          name q ↔ PactType.markerReachableSubst name r = true))
    (hBranchIH : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
      ∀ q r, TypeCompilationRelation branchType q r →
        (MarkerReachable (sequenceExecutionFragment
          (compileTypeFuel signature (typeCompilationFuel branchType)
            branchType)) name q ↔
              PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel elseType)
      (typeBranchCompilationFuel branches)
    let fragment := buildExclusiveOfferAutomaton signature branches
      (compileTypeFuel signature fuel elseType)
      (branches.map fun branch =>
        (branch.1, compileTypeFuel signature fuel branch.2))
    (MarkerReachable (sequenceExecutionFragment fragment) name .root ↔
        PactType.markerReachableSubst name (.xoffer elseType branches) = true) ∧
      (∀ q r, TypeCompilationRelation elseType q r →
        (MarkerReachable (sequenceExecutionFragment fragment) name
            (.child 0 q) ↔
          PactType.markerReachableSubst name r = true)) ∧
      (∀ (action : BareMessage) (branchType : PactType) (index : Nat),
        branches[index]? = some (action, branchType) →
        ∀ q r, TypeCompilationRelation branchType q r →
          (MarkerReachable (sequenceExecutionFragment fragment) name
              (.child (index + 1) q) ↔
            PactType.markerReachableSubst name r = true)) :=
  sorry
private theorem buildSelectedConjunctiveOfferAutomaton_sequenceExecutionMarkerReachable_classified
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (name : String)
    (hSupports : signature.Supports (.offer elseType branches))
    (hBranchesAbsent : PactType.TailBranchOccurrences name False branches)
    (hElseIH : ∀ q r, TypeCompilationRelation elseType q r →
      (MarkerReachable (sequenceExecutionFragment
        (compileTypeFuel signature (typeCompilationFuel elseType) elseType))
          name q ↔ PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel elseType)
      (conjunctiveCompilationFuel branches)
    let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
      (compileTypeFuel signature fuel elseType)
      (branches.map fun selected =>
        (selected.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches)))
    (MarkerReachable (sequenceExecutionFragment fragment) name .root ↔
        PactType.markerReachableSubst name (.offer elseType branches) = true) ∧
      (∀ q r, TypeCompilationRelation elseType q r →
        (MarkerReachable (sequenceExecutionFragment fragment) name
            (.child 0 q) ↔
          PactType.markerReachableSubst name r = true)) ∧
      (∀ (selected : BareMessage × PactType) (index : Nat),
        branches[index]? = some selected →
        ∀ q r, TypeCompilationRelation
            (parallelTypeBranchesSelecting selected branches) q r →
          (MarkerReachable (sequenceExecutionFragment fragment) name
              (.child (index + 1) q) ↔
            PactType.markerReachableSubst name r = true)) :=
  sorry
theorem compilationSequenceExecutionMarkerReachable_iff
    (signature : TypeAlphabet) :
    ∀ (bound : List String) (name : String) (processType : PactType),
      name ∈ bound →
      PactType.AllTailOccurrences bound True processType →
      signature.WellFormed →
      signature.Supports processType →
      PactType.AllVariablesBound bound processType →
      PactType.BinderHygienic bound processType →
      PactType.ClockGuarded processType →
      PactType.TailRecursive processType →
      PactType.SameCycleMessageLinear processType →
      PactType.InterfaceScoped processType →
      (∀ child : PactType, sizeOf child < sizeOf processType →
        signature.Supports child → PactType.AllVariablesBound [] child →
        PactType.BinderHygienic [] child → PactType.ClockGuarded child →
        PactType.TailRecursive child →
        PactType.SameCycleMessageLinear child →
        PactType.InterfaceScoped child →
          CompilationProofBundle signature child) →
      ∀ state residual,
        TypeCompilationRelation processType state residual →
          (MarkerReachable (sequenceExecutionFragment
              (compileTypeFuel signature (typeCompilationFuel processType)
                processType)) name state ↔
            PactType.markerReachableSubst name residual = true) :=
  sorry
end

end Pact
