import Anvilpp.PactTypes.Correspondence.CorrespondenceOfferLeaf

/-!
# Top-level proof-bundle assembly and ProcessAutomatonCorrespondence
-/

namespace Pact

noncomputable section

private theorem allBranchVariablesBound_nil_of_bound (bound : List String) :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.AllBranchVariablesBound bound branches →
      (∀ m ∈ bound, PactType.TailBranchOccurrences m False branches) →
        PactType.AllBranchVariablesBound [] branches := by
  intro branches
  induction branches with
  | nil => intro _ _; simp [PactType.AllBranchVariablesBound]
  | cons branch rest ih =>
      obtain ⟨action, branchType⟩ := branch
      intro hBound hTail
      simp only [PactType.AllBranchVariablesBound] at hBound ⊢
      refine ⟨?_, ih hBound.2 (fun m hm => by
        have hEntry := hTail m hm
        simp only [PactType.TailBranchOccurrences] at hEntry
        exact hEntry.2)⟩
      apply PactType.allVariablesBound_drop_of_allTailOccurrences_false bound []
        branchType (fun m hm => by
          have hEntry := hTail m hm
          simp only [PactType.TailBranchOccurrences] at hEntry
          exact hEntry.1)
      simpa using hBound.1

/-- Top-down structural assembly of all compiler invariants, against an
ambient list of enclosing binder names.  Carrying `bound` is what lets a
recursion body be compiled *open*: the `.recur` case descends into `body` with
`binder :: bound` rather than demanding closedness, and closedness is recovered
only where a constructor genuinely needs it (below a product, and in the
generated conjunctions of an `offer`), using the fact that a bound name cannot
occur there. -/
theorem compilationProofBundle_of_boundedRegular
    (signature : TypeAlphabet) : ∀ processType (bound : List String),
    signature.WellFormed →
    signature.Supports processType →
    PactType.AllTailOccurrences bound True processType →
    PactType.AllVariablesBound bound processType →
    PactType.BinderHygienic bound processType →
    PactType.ClockGuarded processType →
    PactType.TailRecursive processType →
    PactType.SameCycleMessageLinear processType →
    PactType.InterfaceScoped processType →
    CompilationProofBundle signature processType := by
  sorry -- TODO(redevelopment): proof broken by upstream EntryCanonical/TypeCompilationRelation changes; .

theorem compilationProofBundle_of_closedGuardedRegular
    (signature : TypeAlphabet) : ∀ processType,
    signature.WellFormed →
    signature.Supports processType →
    PactType.AllVariablesBound [] processType →
    PactType.BinderHygienic [] processType →
    PactType.ClockGuarded processType →
    PactType.TailRecursive processType →
    PactType.SameCycleMessageLinear processType →
    PactType.InterfaceScoped processType →
    CompilationProofBundle signature processType :=
  fun processType hSignature hSupports hClosed hHygienic hGuarded hTail
      hLinear hScoped =>
    compilationProofBundle_of_boundedRegular signature processType []
      hSignature hSupports (by intro m hm; simp at hm) hClosed hHygienic
        hGuarded hTail hLinear hScoped

/-- Public one-step bisimulation follows immediately from the hierarchical
bundle and the uniform fragment-to-public exporter. -/
theorem compilationStepCorrect_of_closedGuardedRegular
    (signature : TypeAlphabet) (processType : PactType)
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports processType)
    (hClosed : PactType.AllVariablesBound [] processType)
    (hHygienic : PactType.BinderHygienic [] processType)
    (hGuarded : PactType.ClockGuarded processType)
    (hTail : PactType.TailRecursive processType)
    (hLinear : PactType.SameCycleMessageLinear processType)
    (hScoped : PactType.InterfaceScoped processType) :
    CompilationStepCorrect signature processType := by
  sorry -- TODO(redevelopment): proof broken by upstream EntryCanonical/TypeCompilationRelation changes; .
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

end

end Pact
