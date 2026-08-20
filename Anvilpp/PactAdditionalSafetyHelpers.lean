import Anvilpp.PactSafetyHelpers

namespace Pact

noncomputable section

open Classical

/-- Defines the related-state shape for a compiled binary choice: the root represents `whole`, a tagged child state represents its own relation's residual. -/
def binaryChoiceRelationShape
    (signature : TypeAlphabet) (whole left right : PactType)
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (whole, TypeAutomatonState.root) ∨
    (∃ q, entry.2 = .child 0 q ∧
      relationMembership (buildRelationSet left (compileType signature left))
        entry.1 q) ∨
    (∃ q, entry.2 = .child 1 q ∧
      relationMembership (buildRelationSet right (compileType signature right))
        entry.1 q)

/-- Proves every related choice pair has the binary-choice shape. -/
lemma relationMembership_choice_cases
    (signature : TypeAlphabet) (left right : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.choice left right)
          (compileType signature (.choice left right)))
        residual state) :
    binaryChoiceRelationShape signature (.choice left right) left right
      (residual, state) := by
  sorry

/-- Proves every related fair-choice pair has the binary-choice shape. -/
lemma relationMembership_fairChoice_cases
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.fairChoice bid left right)
          (compileType signature (.fairChoice bid left right)))
        residual state) :
    binaryChoiceRelationShape signature (.fairChoice bid left right) left
      right (residual, state) := by
  sorry

/-- Defines the related-state shape for a compiled sequence: a retained left state represents `ρ1 ; τ2`, a right state represents its own relation's residual. -/
def seqRelationShape
    (signature : TypeAlphabet) (left right : PactType)
    (entry : PactType × TypeAutomatonState) : Prop :=
  (∃ q1 residualLeft, entry = (.seq residualLeft right, .child 0 q1) ∧
      relationMembership (buildRelationSet left (compileType signature left))
        residualLeft q1) ∨
    (∃ q2, entry.2 = .child 1 q2 ∧
      relationMembership (buildRelationSet right (compileType signature right))
        entry.1 q2)

/-- Proves every related sequence pair has the sequence shape. -/
lemma relationMembership_seq_cases
    (signature : TypeAlphabet) (left right : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.seq left right)
          (compileType signature (.seq left right)))
        residual state) :
    seqRelationShape signature left right (residual, state) := by
  sorry

/-- Defines the related-state shape for a compiled parallel product: a product state represents the pointwise composition, or `skip` once both components finish. -/
def parRelationShape
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    (entry : PactType × TypeAutomatonState) : Prop :=
  (∃ q1 q2 residualLeft residualRight,
      entry = (.par residualLeft residualRight interface, .pair q1 q2) ∧
      relationMembership (buildRelationSet left (compileType signature left))
        residualLeft q1 ∧
      relationMembership (buildRelationSet right (compileType signature right))
        residualRight q2) ∨
    (∃ q1 q2, entry = (.skip, .pair q1 q2) ∧
      relationMembership (buildRelationSet left (compileType signature left))
        .skip q1 ∧
      relationMembership (buildRelationSet right (compileType signature right))
        .skip q2)

/-- Proves every related parallel pair has the parallel shape. -/
lemma relationMembership_par_cases
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.par left right interface)
          (compileType signature (.par left right interface)))
        residual state) :
    parRelationShape signature left right interface (residual, state) := by
  sorry

/-- Defines the related-state shape for a compiled recursion: the root represents `μX.body`, a copied body state represents its residual substituted for `X`. -/
def recurRelationShape
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.recur name body, TypeAutomatonState.root) ∨
    (∃ q residual,
      entry = (residual.replaceVar name (.recur name body), .child 0 q) ∧
      relationMembership (buildRelationSet body (compileType signature body))
        residual q)

/-- Proves every related recursion pair has the recursion shape. -/
lemma relationMembership_recur_cases
    (signature : TypeAlphabet) (name : String) (body : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.recur name body)
          (compileType signature (.recur name body)))
        residual state) :
    recurRelationShape signature name body (residual, state) := by
  sorry

/-- Defines the related-state shape for a compiled exclusive offer: the root represents the whole offer, a tagged child represents its own relation's residual, else or branch. -/
def xofferRelationShape
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.xoffer elseType branches, TypeAutomatonState.root) ∨
    (∃ q, entry.2 = .child 0 q ∧
      relationMembership
        (buildRelationSet elseType (compileType signature elseType))
        entry.1 q) ∨
    (∃ i action branchType q,
      branches[i]? = some (action, branchType) ∧
      entry.2 = .child (i + 1) q ∧
      relationMembership
        (buildRelationSet branchType (compileType signature branchType))
        entry.1 q)

/-- Proves every related exclusive-offer pair has the exclusive-offer shape. -/
lemma relationMembership_xoffer_cases
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.xoffer elseType branches)
          (compileType signature (.xoffer elseType branches)))
        residual state) :
    xofferRelationShape signature elseType branches (residual, state) := by
  sorry

/-- Defines the related-state shape for a compiled conjunctive offer: the root represents the whole offer, a tagged child represents a residual of `τ0` or a generated branch commit. -/
def offerRelationShape
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.offer elseType branches, TypeAutomatonState.root) ∨
    (∃ q, entry.2 = .child 0 q ∧
      relationMembership
        (buildRelationSet elseType (compileType signature elseType))
        entry.1 q) ∨
    (∃ i selected q,
      branches[i]? = some selected ∧
      entry.2 = .child (i + 1) q ∧
      relationMembership
        (buildRelationSet (parallelTypeBranchesSelecting selected branches)
          (compileType signature
            (parallelTypeBranchesSelecting selected branches)))
        entry.1 q)

/-- Proves every related conjunctive-offer pair has the conjunctive-offer shape. -/
lemma relationMembership_offer_cases
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.offer elseType branches)
          (compileType signature (.offer elseType branches)))
        residual state) :
    offerRelationShape signature elseType branches (residual, state) := by
  sorry

/-- Defines the only related pair for a variable marker as its own seed. -/
def varRelationShape
    (name : String) (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.var name, TypeAutomatonState.root)

/-- Proves no decorated step is ever available at a variable marker. -/
lemma var_not_decoratedTypeTransition
    (name : String) {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary} {target : PactType} :
    ¬ DecoratedTypeTransition env (.var name) label offers target := by
  rintro ⟨hTrans, -⟩
  cases hTrans

/-- Proves the relation builder never grows past a variable-marker entry. -/
lemma relationSuccessors_var_eq_empty
    (signature : TypeAlphabet) (name : String)
    (entry : PactType × TypeAutomatonState) (hEntry : entry.1 = .var name) :
    relationSuccessors (compileType signature (.var name)) entry = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro pair hPair
  simp only [relationSuccessors, Finset.mem_biUnion] at hPair
  obtain ⟨edge, -, hPair⟩ := hPair
  split at hPair
  · split at hPair
    · rename_i hStep
      obtain ⟨residual', hStep'⟩ := hStep
      rw [hEntry] at hStep'
      exact var_not_decoratedTypeTransition name hStep'
    · simp at hPair
  · simp at hPair

/-- Proves every related variable-marker pair is the seed pair. -/
lemma relationMembership_var_cases
    (signature : TypeAlphabet) (name : String)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.var name) (compileType signature (.var name)))
        residual state) :
    residual = .var name ∧ state = TypeAutomatonState.root := by
  have hShape :=
    buildRelationSet_preserves (.var name) (compileType signature (.var name))
      (varRelationShape name)
      (by
        simp [varRelationShape, compileType, typeCompilationFuel,
          compileTypeFuel, finishAutomatonFragment])
      (by
        intro entry hEntry successor hSuccessor
        rw [relationSuccessors_var_eq_empty signature name entry
          (by rw [hEntry])] at hSuccessor
        exact absurd hSuccessor (by simp))
      (residual, state) hRelated
  simpa [varRelationShape, Prod.ext_iff] using hShape

end

end Pact
