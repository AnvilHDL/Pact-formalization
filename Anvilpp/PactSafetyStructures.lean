import Anvilpp.PactTypes.Automata.CompileType

namespace Pact

noncomputable section

open Classical

/-- The process-side committed form of a conjunctive-offer branch.  This is
the concrete counterpart of `selectedTypeBranch`: the chosen branch performs
its head action instead of remaining behind a synthetic singleton `xoffer`. -/
def selectedProcessBranch : ChoiceBranch → Proc
  | .send msg expr process => .send msg expr process
  | .recv msg var process => .recv msg var process

/-- Rewrite a conjunctive process offer after the selected branch has been
committed.  Branch selection is indexed by the erased branch because this is
the transformation whose abstraction is compared with
`parallelTypeBranchesSelecting`. -/
def parallelProcessBranchesSelecting
    (selected : BareMessage × PactType) : List ChoiceBranch → Proc
  | [] => .skip
  | [branch] =>
      if inferBranch branch = selected then selectedProcessBranch branch
      else ChoiceBranch.toXOffer branch
  | branch :: rest =>
      if inferBranch branch = selected then
        .par (selectedProcessBranch branch) (parallelBranches rest) ∅
      else
        .par (ChoiceBranch.toXOffer branch)
          (parallelProcessBranchesSelecting selected rest) ∅


/-- The step-for-step relation of Lemma 4.5. -/
structure TypeAutomatonCorrespondence
    (processType : PactType) (automaton : TypeAutomaton) : Type where
  relation : PactType → TypeAutomatonState → Prop
  initial : relation processType automaton.initial
  initial_mem : automaton.initial ∈ automaton.states
  stepIff :
    ∀ {residual residual' : PactType} {state : TypeAutomatonState}
      {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
      relation residual state →
      ({ environment := env, label := label, offers := offers } :
          TypeAutomatonSymbol) ∈ automaton.alphabet →
      (DecoratedTypeTransition env residual label offers residual' ↔
        ∃ state',
          automaton.HasEdge state env label offers state' ∧
          relation residual' state')

structure ProcessAutomatonCorrespondence
    (process : Proc) (processType : PactType) (automaton : TypeAutomaton) : Type where
  relation : Proc → TypeAutomatonState → Prop
  initial : relation process automaton.initial
  matchStep :
    ∀ {p₀ p₁ : Proc} {state : TypeAutomatonState}
      {env : Environment} {label : Label},
      relation p₀ state →
      ProcessTransition env p₀ label p₁ →
      ∃ state' offers,
        automaton.HasEdge state (eraseEnvironment env) (eraseLabel label) offers state' ∧
        relation p₁ state'
