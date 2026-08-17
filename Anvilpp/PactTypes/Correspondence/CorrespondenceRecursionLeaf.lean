import Anvilpp.PactTypes.Correspondence.CorrespondenceMarkerReachability

/-!
# Recursion leaf: future-references-target, RecursionBodyScopedStepCorrect, bounded leaf assembly
-/

namespace Pact

noncomputable section

/-- Tagging preserves "the symbolic future reference is the edge's own
target". -/
private theorem childPendingEdge_futureReferencesTarget
    (index : Nat) (edge : PendingAutomatonEdge)
    (hEdge : ∀ inner removed, edge.future = .at inner removed →
      inner = edge.target) :
    ∀ inner removed,
      (childPendingEdge index edge).future = .at inner removed →
        inner = (childPendingEdge index edge).target :=
  sorry
private theorem compileTypeFuel_futureReferencesTarget
    (signature : TypeAlphabet) :
    ∀ (fuel : Nat) (processType : PactType),
      ∀ edge ∈ (compileTypeFuel signature fuel processType).edges,
        ∀ inner removed, edge.future = .at inner removed →
          inner = edge.target :=
  sorry
private theorem typeOffers_tailOccurrences_false (name : String) :
    ∀ source : PactType, ∀ env label target current future,
      TypeOffers env source label target current future →
        source.TailOccurrences name False →
          target.TailOccurrences name False :=
  sorry
private theorem typeOffers_future_subset_targetFuture :
    ∀ source : PactType, ∀ env label target current future,
      TypeOffers env source label target current future →
        future ⊆ typeFutureOffers target :=
  sorry
private inductive SemanticFuturePolicy where
  | explicit (future : Finset BareMessage)
  | subtract (removed : Finset BareMessage)

private def resolveSemanticFuture (target : PactType) :
    SemanticFuturePolicy → Finset BareMessage
  | .explicit future => future
  | .subtract removed => typeFutureOffers target \ removed

/- `TypeOffers` with the exact compiler decoration policy retained.  The
constructors deliberately mirror the constructor compiler: atomic and
parallel edges carry explicit futures; constructor-selection edges point at
their target with an empty removal; sequence and waiting edges remove exactly
the set used by their operational rule. -/
private inductive PolicyTypeOffers :
    TypeEnvironment → PactType → TypeLabel → PactType →
      Finset BareMessage → SemanticFuturePolicy → Prop where
  | action (env : TypeEnvironment) (msg : MessageId) (dir : MessageDir) :
      env.WellFormed ∧ env.hasNeed (msg, dir) →
      PolicyTypeOffers env (.message msg dir) (.message msg dir) .skip
        {(msg, dir)} (.explicit ∅)
  | action_wait (env : TypeEnvironment) (msg : MessageId) (dir : MessageDir) :
      env.WellFormed ∧ ¬ env.hasNeed (msg, dir) ∧ env.clock = false →
      PolicyTypeOffers env (.message msg dir) .silent (.message msg dir)
        {(msg, dir)} (.explicit ∅)
  | choice_left (env : TypeEnvironment) (left right : PactType) :
      env.WellFormed →
      PolicyTypeOffers env (.choice left right) .silent left ∅ (.subtract ∅)
  | choice_right (env : TypeEnvironment) (left right : PactType) :
      env.WellFormed →
      PolicyTypeOffers env (.choice left right) .silent right ∅ (.subtract ∅)
  | fair_left (env : TypeEnvironment) (bid : BranchId)
      (left right : PactType) :
      env.WellFormed →
      PolicyTypeOffers env (.fairChoice bid left right) (.fair bid true) left
        ∅ (.subtract ∅)
  | fair_right (env : TypeEnvironment) (bid : BranchId)
      (left right : PactType) :
      env.WellFormed →
      PolicyTypeOffers env (.fairChoice bid left right) (.fair bid false) right
        ∅ (.subtract ∅)
  | cycle (env : TypeEnvironment) :
      env.WellFormed ∧ env.clock = true →
      PolicyTypeOffers env .tock .tock .skip ∅ (.explicit ∅)
  | cycle_wait (env : TypeEnvironment) :
      env.WellFormed ∧ env.clock = false →
      PolicyTypeOffers env .tock .silent .tock ∅ (.explicit ∅)
  | skip (env : TypeEnvironment) :
      env.WellFormed ∧ env.clock = false ∧ env.immediate = ∅ →
      PolicyTypeOffers env .skip .silent .skip ∅ (.explicit ∅)
  | skip_seq (env : TypeEnvironment) (processType : PactType) :
      env.WellFormed →
      PolicyTypeOffers env (.seq .skip processType) .silent processType ∅
        (.subtract ∅)
  | progress (env : TypeEnvironment) (pid : ProcId) :
      env.WellFormed →
      PolicyTypeOffers env (.progress pid) (.progress pid) .skip ∅
        (.explicit ∅)
  | recur (env : TypeEnvironment) (binder : String) (body : PactType) :
      env.WellFormed →
      PolicyTypeOffers env (.recur binder body) .silent
        (body.replaceVar binder (.recur binder body)) ∅ (.subtract ∅)
  | seq (env : TypeEnvironment) (left left' right : PactType)
      (label : TypeLabel) (current : Finset BareMessage)
      (childPolicy : SemanticFuturePolicy) :
      PolicyTypeOffers env left label left' current childPolicy →
      PolicyTypeOffers env (.seq left right) label (.seq left' right) current
        (.subtract current)
  | xoffer_branch (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType))
      (action : BareMessage) (processType : PactType) :
      env.WellFormed ∧ (action, processType) ∈ branches ∧
        TypeBranchEnabled env (action, processType) ∧ TypeResolved env branches →
      PolicyTypeOffers env (.xoffer elseType branches)
        (.message action.1 action.2) processType {action} (.subtract ∅)
  | xoffer_else (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧ TypeNoImmediateBranch env branches ∧
        TypeResolved env branches →
      PolicyTypeOffers env (.xoffer elseType branches) .silent elseType ∅
        (.subtract ∅)
  | xoffer_wait (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧ ¬ TypeResolved env branches ∧ env.clock = false →
      PolicyTypeOffers env (.xoffer elseType branches) .silent
        (.xoffer elseType branches) (typeWaitingOffers env branches)
        (.subtract (typeWaitingOffers env branches))
  | offer_some (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType))
      (enabled : BareMessage × PactType) :
      env.WellFormed ∧ enabled ∈ branches ∧ TypeBranchEnabled env enabled →
      PolicyTypeOffers env (.offer elseType branches) .silent
        (parallelTypeBranchesSelecting enabled branches) ∅ (.subtract ∅)
  | offer_else (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧ TypeNoImmediateBranch env branches ∧
        TypeResolved env branches →
      PolicyTypeOffers env (.offer elseType branches) .silent elseType
        (typeBranchActions branches) (.subtract ∅)
  | offer_wait (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧ TypeNoImmediateBranch env branches ∧
        ¬ TypeResolved env branches ∧ env.clock = false →
      PolicyTypeOffers env (.offer elseType branches) .silent
        (.offer elseType branches) (typeWaitingOffers env branches)
        (.subtract (typeWaitingOffers env branches))
  | par (outer leftEnv rightEnv : TypeEnvironment) (interface : Interface)
      (left left' right right' : PactType) (leftLabel rightLabel : TypeLabel)
      (leftCurrent rightCurrent : Finset BareMessage)
      (leftPolicy rightPolicy : SemanticFuturePolicy) :
      PolicyTypeOffers leftEnv left leftLabel left' leftCurrent leftPolicy →
      PolicyTypeOffers rightEnv right rightLabel right' rightCurrent rightPolicy →
      LocalTypeEnvironment outer interface rightEnv right rightLabel leftEnv →
      LocalTypeEnvironment outer interface leftEnv left leftLabel rightEnv →
      outer.WellFormed ∧ TypeLabel.Sync interface leftLabel rightLabel →
      PolicyTypeOffers outer (.par left right interface)
        (TypeLabel.combine interface leftLabel rightLabel)
        (.par left' right' interface)
        (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
        (.explicit (hideTypeOffers interface
          (resolveSemanticFuture left' leftPolicy ∪
            resolveSemanticFuture right' rightPolicy)))

private theorem PolicyTypeOffers.xoffer_root_policy
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)} {label : TypeLabel}
    {target : PactType} {current : Finset BareMessage}
    {policy : SemanticFuturePolicy}
    (hOffers : PolicyTypeOffers env (.xoffer elseType branches) label target
      current policy) :
    (policy = .subtract ∅ ∧ TypeResolved env branches) ∨
      (current = ∅ ∧ policy = .subtract ∅) ∨
      (policy = .subtract current ∧ ¬ TypeResolved env branches) :=
  sorry
private theorem PolicyTypeOffers.offer_root_policy
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)} {label : TypeLabel}
    {target : PactType} {current : Finset BareMessage}
    {policy : SemanticFuturePolicy}
    (hOffers : PolicyTypeOffers env (.offer elseType branches) label target
      current policy) :
    (current = ∅ ∧ policy = .subtract ∅) ∨
      (policy = .subtract ∅ ∧ TypeResolved env branches) ∨
      (policy = .subtract current ∧ ¬ TypeResolved env branches) :=
  sorry
private theorem binderFreshFor_branch_of_mem_policy
    (forbidden : List String) :
    ∀ (branches : List (BareMessage × PactType)) entry,
      PactType.BinderFreshForBranches forbidden branches →
      entry ∈ branches → entry.2.BinderFreshFor forbidden :=
  sorry
private theorem binderFreshFor_parallelTypeBranches_policy
    (forbidden : List String) :
    ∀ branches : List (BareMessage × PactType),
      PactType.BinderFreshForBranches forbidden branches →
      (parallelTypeBranches branches).BinderFreshFor forbidden :=
  sorry
private theorem binderFreshFor_parallelTypeBranchesSelecting_policy
    (forbidden : List String) (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType),
      PactType.BinderFreshForBranches forbidden branches →
      (parallelTypeBranchesSelecting selected branches).BinderFreshFor
        forbidden :=
  sorry
private theorem PolicyTypeOffers.target_binderFreshFor
    {env : TypeEnvironment} {source : PactType} {label : TypeLabel}
    {target : PactType} {current : Finset BareMessage}
    {policy : SemanticFuturePolicy}
    (hOffers : PolicyTypeOffers env source label target current policy) :
    ∀ forbidden, source.BinderFreshFor forbidden →
      target.BinderFreshFor forbidden :=
  sorry
private theorem PolicyTypeOffers.toTypeOffers
    {env : TypeEnvironment} {source : PactType} {label : TypeLabel}
    {target : PactType} {current : Finset BareMessage}
    {policy : SemanticFuturePolicy}
    (hOffers : PolicyTypeOffers env source label target current policy) :
    TypeOffers env source label target current
      (resolveSemanticFuture target policy) :=
  sorry
private theorem typeOffers_toPolicy :
    ∀ source : PactType, ∀ env label target current future,
      TypeOffers env source label target current future →
        ∃ policy,
          PolicyTypeOffers env source label target current policy ∧
            future = resolveSemanticFuture target policy :=
  sorry
private theorem typeBranchNeeds_replaceBranches
    (branches : List (BareMessage × PactType)) (name : String)
    (replacement : PactType) :
    typeBranchNeeds (PactType.replaceBranches branches name replacement) =
      typeBranchNeeds branches :=
  sorry
private theorem typeBranchActions_replaceBranches
    (branches : List (BareMessage × PactType)) (name : String)
    (replacement : PactType) :
    typeBranchActions (PactType.replaceBranches branches name replacement) =
      typeBranchActions branches :=
  sorry
private theorem typeWaitingOffers_replaceBranches
    (env : TypeEnvironment) (branches : List (BareMessage × PactType))
    (name : String) (replacement : PactType) :
    typeWaitingOffers env
        (PactType.replaceBranches branches name replacement) =
      typeWaitingOffers env branches :=
  sorry
private theorem policyTypeOffers_replaceVar_forward
    (bound : List String) (name : String) (body : PactType)
    (hBoundBody : body.AllVariablesBound (name :: bound)) :
    ∀ {env : TypeEnvironment} {source : PactType} {label : TypeLabel}
      {target : PactType} {current : Finset BareMessage}
      {policy : SemanticFuturePolicy},
      source.TailOccurrences name True →
      source.AllVariablesBound (name :: bound) →
      source.BinderFreshFor (name :: bound) →
      PolicyTypeOffers env source label target current policy →
      PolicyTypeOffers env
        (source.replaceVar name (.recur name body)) label
        (target.replaceVar name (.recur name body)) current policy :=
  sorry
private theorem policyTypeOffers_replaceVar_backward
    (bound : List String) (name : String) (body : PactType)
    (hBoundBody : body.AllVariablesBound (name :: bound)) :
    ∀ {env : TypeEnvironment} {source : PactType} {label : TypeLabel}
      {target : PactType} {current : Finset BareMessage}
      {policy : SemanticFuturePolicy},
      source.TailOccurrences name True →
      source.AllVariablesBound (name :: bound) →
      source.BinderFreshFor (name :: bound) →
      source ≠ .var name →
      PolicyTypeOffers env
          (source.replaceVar name (.recur name body)) label target current
            policy →
      ∃ bodyTarget,
        PolicyTypeOffers env source label bodyTarget current policy ∧
          target = bodyTarget.replaceVar name (.recur name body) :=
  sorry
private def futureSpecMatchesPolicy (edge : PendingAutomatonEdge) :
    SemanticFuturePolicy → Prop
  | .explicit _ => ∃ future, edge.future = .explicit future
  | .subtract removed => edge.future = .at edge.target removed

private theorem futureSpecMatchesPolicy_childPendingEdge
    (index : Nat) (edge : PendingAutomatonEdge)
    (policy : SemanticFuturePolicy) :
    futureSpecMatchesPolicy (childPendingEdge index edge) policy ↔
      futureSpecMatchesPolicy edge policy :=
  sorry
private theorem PactType.seq_ne_right (left right : PactType) :
    PactType.seq left right ≠ right :=
  sorry
private theorem PolicyTypeOffers.par_policy_explicit
    {env : TypeEnvironment} {left right : PactType} {interface : Interface}
    {label : TypeLabel} {target : PactType}
    {current : Finset BareMessage} {policy : SemanticFuturePolicy}
    (hPolicy : PolicyTypeOffers env (.par left right interface) label target
      current policy) :
    ∃ future, policy = .explicit future :=
  sorry
private theorem replaceVar_recur_eq_var_for_policy
    {source : PactType} {binder markerName : String} {body : PactType}
    (hEqual : source.replaceVar binder (.recur binder body) =
      .var markerName) :
    source = .var markerName ∧ ¬ binder = markerName :=
  sorry
private theorem compileTypeFuel_variableRelation_outgoing_label
    (signature : TypeAlphabet) (markerName : String) :
    ∀ (fuel : Nat) (processType : PactType),
      TypeCompilationFuelSufficient processType fuel →
      PactType.TailOccurrences markerName True processType →
      ∀ state residual, TypeCompilationRelation processType state residual →
        residual = .var markerName →
        ∀ edge ∈ (compileTypeFuel signature fuel processType).edges,
          edge.source = state → edge.label = .variable markerName :=
  sorry
private theorem compilationRelation_futureSpecMatchesPolicy
    (signature : TypeAlphabet) :
    ∀ {original state residual},
      TypeCompilationRelation original state residual →
      ∀ (bound : List String),
        original.AllVariablesBound bound →
        original.BinderHygienic bound →
        original.TailRecursive →
        ∀ {edge : PendingAutomatonEdge} {label : TypeLabel}
          {targetResidual : PactType} {policy : SemanticFuturePolicy},
          edge ∈ (compileTypeFuel signature (typeCompilationFuel original)
            original).edges →
          edge.source = state →
          edge.label = .visible label →
          TypeCompilationRelation original edge.target targetResidual →
          PolicyTypeOffers edge.environment residual label targetResidual
            edge.current policy →
          futureSpecMatchesPolicy edge policy :=
  sorry
private theorem decoratedTypeTransition_iff_typeOffers
    (env : TypeEnvironment) (source : PactType) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : PactType) :
    DecoratedTypeTransition env source label offers target ↔
      TypeOffers env source label target offers.current offers.future :=
  sorry
private theorem replaceVar_recur_eq_var
    {source : PactType} {binder markerName : String} {body : PactType}
    (hEqual : source.replaceVar binder (.recur binder body) =
      .var markerName) :
    source = .var markerName ∧ ¬ binder = markerName :=
  sorry
private theorem compileTypeFuel_markerEdge_of_variableRelation
    (signature : TypeAlphabet) (markerName : String) :
    ∀ (fuel : Nat) (processType : PactType),
      TypeCompilationFuelSufficient processType fuel →
      PactType.TailOccurrences markerName True processType →
      ∀ state residual, TypeCompilationRelation processType state residual →
        residual = PactType.var markerName →
        ∀ env ∈ signature.localEnvironments,
          ∃ edge ∈ (compileTypeFuel signature fuel processType).edges,
            edge.source = state ∧
              edge.label = AutomatonConstructionLabel.variable markerName ∧
              edge.environment = env :=
  sorry
private theorem recursionBodyFutureCorrect_of_bundle
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hTailBody : body.TailOccurrences name True)
    (hTailRecursiveBody : body.TailRecursive)
    (hBodyFuture : CompilationFutureCorrect signature body)
    (hMarker : ∀ q r, TypeCompilationRelation body q r →
      (MarkerReachable (compileTypeFuel signature (typeCompilationFuel body)
        body) name q ↔ PactType.markerReachableSubst name r = true)) :
    RecursionBodyFutureCorrect signature name body :=
  sorry
private def RecursionBodyScopedStepCorrect
    (signature : TypeAlphabet) (name : String) (body : PactType) : Prop :=
  sorry
private theorem recursionBodyScopedStep_marker
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hTailBody : body.TailOccurrences name True)
    (hBodyStep : CompilationScopedFragmentStepCorrect signature body)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    {state : TypeAutomatonState} {residual' : PactType}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation body state (.var name))
    (hLocal : env ∈ signature.localEnvironments)
    (hAvoids : env.AvoidsInterface body.ParallelInterfaces) :
    (DecoratedTypeTransition env
        ((PactType.var name).replaceVar name (.recur name body)) label offers
          residual' ↔
      ∃ target,
        (compileTypeFuel signature (typeCompilationFuel (.recur name body))
          (.recur name body)).HasResolvedEdge signature (.recur name body)
            (.child 0 state) env label offers target ∧
        TypeCompilationRelation (.recur name body) target residual') :=
  sorry
private theorem recursionBodyScopedStep_nonMarker
    (signature : TypeAlphabet) (bound : List String) (name : String)
    (body : PactType)
    (hBoundBody : body.AllVariablesBound (name :: bound))
    (hHygienicBody : body.BinderHygienic (name :: bound))
    (hTailBody : body.TailOccurrences name True)
    (hTailRecursiveBody : body.TailRecursive)
    (hBodyStep : CompilationScopedFragmentStepCorrect signature body)
    (hBodyFutureCorrect : CompilationFutureCorrect signature body)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    {state : TypeAutomatonState} {residual residual' : PactType}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation body state residual)
    (hNotMarker : ¬ residual = PactType.var name)
    (hLocal : env ∈ signature.localEnvironments)
    (hAvoids : env.AvoidsInterface body.ParallelInterfaces) :
    (DecoratedTypeTransition env
        (residual.replaceVar name (.recur name body)) label offers residual' ↔
      ∃ target,
        (compileTypeFuel signature (typeCompilationFuel (.recur name body))
          (.recur name body)).HasResolvedEdge signature (.recur name body)
            (.child 0 state) env label offers target ∧
        TypeCompilationRelation (.recur name body) target residual') :=
  sorry
private theorem recursionBodyScopedStepCorrect_of_bundle
    (signature : TypeAlphabet) (bound : List String) (name : String)
    (body : PactType)
    (hBoundBody : body.AllVariablesBound (name :: bound))
    (hHygienicBody : body.BinderHygienic (name :: bound))
    (hTailBody : body.TailOccurrences name True)
    (hTailRecursiveBody : body.TailRecursive)
    (hBodyStep : CompilationScopedFragmentStepCorrect signature body)
    (hBodyFutureCorrect : CompilationFutureCorrect signature body)
    (hFuture : RecursionBodyFutureCorrect signature name body) :
    RecursionBodyScopedStepCorrect signature name body := by
  sorry -- TODO(redevelopment): proof broken by upstream TypeCompilationRelation/EntryCanonical changes; .

private theorem compilationScopedFragmentStepCorrect_recursion_of_body
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    (hBodyStep : RecursionBodyScopedStepCorrect signature name body) :
    CompilationScopedFragmentStepCorrect signature (.recur name body) :=
  sorry
private theorem compilationSequenceExecutionCorrect_recursion_bounded_leaf
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.recur name body))
    (hHygienic : PactType.BinderHygienic [] (.recur name body))
    (hGuarded : PactType.ClockGuarded (.recur name body))
    (hTail : PactType.TailRecursive (.recur name body))
    (hLinear : PactType.SameCycleMessageLinear (.recur name body))
    (hBodyBundle : CompilationProofBundle signature body)
    (hBodyFuture : RecursionBodyFutureCorrect signature name body)
    (hExecutionMarker : ∀ q r, TypeCompilationRelation body q r →
      (MarkerReachable (sequenceExecutionFragment
        (compileTypeFuel signature (typeCompilationFuel body) body)) name q ↔
          PactType.markerReachableSubst name r = true)) :
    CompilationSequenceExecutionCorrect signature (.recur name body) :=
  sorry
private theorem compilationScopedFragmentStepCorrect_recursion_bounded_leaf
    (signature : TypeAlphabet) (bound : List String) (name : String)
    (body : PactType)
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.recur name body))
    (hBoundBody : body.AllVariablesBound (name :: bound))
    (hHygienic : PactType.BinderHygienic bound (.recur name body))
    (hGuarded : PactType.ClockGuarded (.recur name body))
    (hTail : PactType.TailRecursive (.recur name body))
    (hLinear : PactType.SameCycleMessageLinear (.recur name body))
    (hScoped : PactType.InterfaceScoped (.recur name body))
    (hBodyBundle : CompilationProofBundle signature body)
    (hBodyFuture : RecursionBodyFutureCorrect signature name body) :
    CompilationScopedFragmentStepCorrect signature (.recur name body) :=
  sorry
theorem compilationProofBundle_recursion_bounded_leaf
    (signature : TypeAlphabet) (bound : List String) (name : String)
    (body : PactType)
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.recur name body))
    (hBoundBody : body.AllVariablesBound (name :: bound))
    (hHygienic : PactType.BinderHygienic bound (.recur name body))
    (hGuarded : PactType.ClockGuarded (.recur name body))
    (hTail : PactType.TailRecursive (.recur name body))
    (hLinear : PactType.SameCycleMessageLinear (.recur name body))
    (hScoped : PactType.InterfaceScoped (.recur name body))
    (hBodyBundle : CompilationProofBundle signature body)
    (hMarker : ∀ q r, TypeCompilationRelation body q r →
      (MarkerReachable (compileTypeFuel signature (typeCompilationFuel body)
        body) name q ↔ PactType.markerReachableSubst name r = true))
    (hExecutionMarker : ∀ q r, TypeCompilationRelation body q r →
      (MarkerReachable (sequenceExecutionFragment
        (compileTypeFuel signature (typeCompilationFuel body) body)) name q ↔
          PactType.markerReachableSubst name r = true)) :
    CompilationProofBundle signature (.recur name body) :=
  sorry
end

end Pact
