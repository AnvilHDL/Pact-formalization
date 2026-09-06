import Anvilpp.PactTypes.Spec.Syntax.TypeErasure
import Anvilpp.PactTypes.Spec.Automata.SyncEdgesDefs
import Anvilpp.PactTypes.Proofs.Syntax.LiveEquivalenceLemmas
import Anvilpp.PactTypes.Proofs.Syntax.TypeLabelOwnershipLemmas
import Anvilpp.PactTypes.Proofs.Syntax.TypeOffersAlphabet
import Anvilpp.PactTypes.Proofs.Syntax.PactTypeRegularityLemmas
import Anvilpp.PactTypes.Proofs.Syntax.TypeTransitionSystemLemmas
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.LiveStepLemmas
import Anvilpp.PactTypes.Proofs.Syntax.TypeOfferEnvironmentAgreementLemmas
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.EnvironmentAndAlphabet
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.Parallel
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.Variables
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.FutureClosure
import Anvilpp.PactTypes.Proofs.Automata.MarkerAbsenceLemmas

/-!
Helper lemmas of the pen-and-paper proof of Lemma 4.5, under the names used
there.  Each entry either reuses an existing result or proves the missing one.
-/

namespace Pact

noncomputable section

/-! ### Uniform offer law -/

/-! ### Offer determinacy -/

/-! ### Synchronization premises agree -/

/-! ### Final states represent completion -/

/-- Forward half: an accepting state represents a completed residual. -/
theorem final_state_represents_skip
    (processType : PactType) {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType processType)) residual state)
    (hAccept : state ∈ (compileType processType).accepting) :
    ∃ skipAlphabet, residual = .skip skipAlphabet := by
  obtain ⟨skipAlphabet, hSkip⟩ :=
    relationMembership_of_accepting processType hAccept
  exact ⟨skipAlphabet,
    relationMembership_functional processType (compileType processType)
      hRelated hSkip⟩


/-! ### Re-signing invariance -/

/-- Non-clock half of the uniform offer law: a non-clock step's future offer is
the menu at its own target, less what it already offers now. -/
theorem TypeOffers.future_eq_sdiff_of_label_ne_tock
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future)
    (hLabel : label ≠ TypeLabel.tock) :
    future = typeFutureOffers target \ current := by
  induction hOffers using TypeOffers.rec with
  | action => simp [typeFutureOffers, typeFutureOffersFuel]
  | action_wait => rfl
  | choice_left => simp
  | choice_right => simp
  | fair_left => simp
  | fair_right => simp
  | cycle => exact absurd rfl hLabel
  | cycle_wait => simp
  | skip => simp
  | progress => simp
  | recur => simp
  | seq => rfl
  | seq_tock => exact absurd rfl hLabel
  | seq_fuse => rfl
  | seq_fuse_tock => exact absurd rfl hLabel
  | xoffer_branch => rfl
  | xoffer_else => simp
  | xoffer_wait => rfl
  | offer_some => simp
  | offer_else => rfl
  | offer_wait => rfl
  | par _ _ _ interface alphabet _ _ _ _ leftLabel rightLabel _ _ _ _ _ _ _ _ _ _ _ _ =>
      simp only [if_neg hLabel]
  | par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ hLeft hRight _ _ _ _ _ _ =>
      rw [hLeft.future_eq_empty_of_target_skip rfl,
        hRight.future_eq_empty_of_target_skip rfl]
      simp [hideTypeOffers, typeFutureOffers, typeFutureOffersFuel]
  | par_fuse_tock => simp_all
  | left_complete => rfl
  | left_complete_tock => exact absurd (by assumption) hLabel
  | right_complete => rfl
  | right_complete_tock => exact absurd (by assumption) hLabel

/-- A residual whose body is `skip` sits at an accepting state.  Converse half
of `final_state_represents_skip`. -/
theorem accepting_of_skip_residual
    (processType : PactType) {skipAlphabet : PactTypeAlphabet}
    {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType processType))
        (.skip skipAlphabet) state) :
    state ∈ (compileType processType).accepting := by
  induction hSize : typeCompilationFuel processType using Nat.strong_induction_on
      generalizing processType skipAlphabet state with
  | _ n ih =>
    cases processType with
    | skip alphabet =>
        obtain ⟨-, hState⟩ :=
          NewCorrespondence.relationMembership_skip_cases alphabet hRelated
        subst hState
        show TypeAutomatonState.root ∈
          (compileTypeFuel (typeCompilationFuel (.skip alphabet))
            (.skip alphabet)).accepting
        simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    | message alphabet msg dir =>
        rcases NewCorrespondence.relationMembership_message_cases alphabet msg dir
            hRelated with ⟨hResidual, -⟩ | ⟨-, hState⟩
        · exact absurd hResidual (by simp)
        · subst hState
          show TypeAutomatonState.final ∈
            (compileTypeFuel (typeCompilationFuel (.message alphabet msg dir))
              (.message alphabet msg dir)).accepting
          simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    | tock alphabet =>
        rcases NewCorrespondence.relationMembership_tock_cases alphabet hRelated with
          ⟨hResidual, -⟩ | ⟨-, hState⟩
        · exact absurd hResidual (by simp)
        · subst hState
          show TypeAutomatonState.final ∈
            (compileTypeFuel (typeCompilationFuel (.tock alphabet))
              (.tock alphabet)).accepting
          simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    | progress alphabet pid =>
        rcases NewCorrespondence.relationMembership_progress_cases alphabet pid
            hRelated with ⟨hResidual, -⟩ | ⟨-, hState⟩
        · exact absurd hResidual (by simp)
        · subst hState
          show TypeAutomatonState.final ∈
            (compileTypeFuel (typeCompilationFuel (.progress alphabet pid))
              (.progress alphabet pid)).accepting
          simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    | var alphabet name =>
        obtain ⟨hResidual, -⟩ := relationMembership_var_cases alphabet name hRelated
        exact absurd hResidual (by simp)
    | choice alphabet left right =>
        have hFuelEq : typeCompilationFuel (.choice alphabet left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq :
            (compileType (.choice alphabet left right)).accepting =
            childAccepting 0 (compileTypeFuel (typeCompilationFuel left) left) ∪
              childAccepting 1
                (compileTypeFuel (typeCompilationFuel right) right) := by
          show (compileTypeFuel
            (typeCompilationFuel (.choice alphabet left right))
            (.choice alphabet left right)).accepting = _
          rw [hFuelEq, compileTypeFuel.eq_def]
          show (buildChoiceAutomaton alphabet
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            TypeLabel.silent TypeLabel.silent).accepting = _
          rw [compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
          simp [buildChoiceAutomaton, finishAutomatonFragment]
        rcases relationMembership_choice_cases alphabet left right
            hRelated with hRoot | ⟨q, hState, hChild⟩ | ⟨q, hState, hChild⟩
        · exact absurd (congrArg Prod.fst hRoot) (by simp)
        · have hq := ih (typeCompilationFuel left)
            (by rw [← hSize, hFuelEq]; omega) left hChild rfl
          simp only [hAcceptEq, childAccepting, childState,
            Finset.mem_union, Finset.mem_image]
          exact Or.inl ⟨q, hq, hState.symm⟩
        · have hq := ih (typeCompilationFuel right)
            (by rw [← hSize, hFuelEq]; omega) right hChild rfl
          simp only [hAcceptEq, childAccepting, childState,
            Finset.mem_union, Finset.mem_image]
          exact Or.inr ⟨q, hq, hState.symm⟩
    | fairChoice alphabet bid left right =>
        have hFuelEq : typeCompilationFuel (.fairChoice alphabet bid left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq :
            (compileType (.fairChoice alphabet bid left right)).accepting =
            childAccepting 0 (compileTypeFuel (typeCompilationFuel left) left) ∪
              childAccepting 1
                (compileTypeFuel (typeCompilationFuel right) right) := by
          show (compileTypeFuel
            (typeCompilationFuel (.fairChoice alphabet bid left right))
            (.fairChoice alphabet bid left right)).accepting = _
          rw [hFuelEq, compileTypeFuel.eq_def]
          show (buildChoiceAutomaton alphabet
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            (TypeLabel.fair bid true) (TypeLabel.fair bid false)).accepting = _
          rw [compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
          simp [buildChoiceAutomaton, finishAutomatonFragment]
        rcases relationMembership_fairChoice_cases alphabet bid
            left right hRelated with hRoot | ⟨q, hState, hChild⟩ | ⟨q, hState, hChild⟩
        · exact absurd (congrArg Prod.fst hRoot) (by simp)
        · have hq := ih (typeCompilationFuel left)
            (by rw [← hSize, hFuelEq]; omega) left hChild rfl
          simp only [hAcceptEq, childAccepting, childState,
            Finset.mem_union, Finset.mem_image]
          exact Or.inl ⟨q, hq, hState.symm⟩
        · have hq := ih (typeCompilationFuel right)
            (by rw [← hSize, hFuelEq]; omega) right hChild rfl
          simp only [hAcceptEq, childAccepting, childState,
            Finset.mem_union, Finset.mem_image]
          exact Or.inr ⟨q, hq, hState.symm⟩
    | seq alphabet left right =>
        have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq :
            (compileType (.seq alphabet left right)).accepting =
            childAccepting 1
              (compileTypeFuel (typeCompilationFuel right) right) := by
          show (compileTypeFuel
            (typeCompilationFuel (.seq alphabet left right))
            (.seq alphabet left right)).accepting = _
          rw [hFuelEq, compileTypeFuel.eq_def]
          show (buildSequenceAutomaton
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right))
              right)).accepting = _
          rw [compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
          simp [buildSequenceAutomaton, finishAutomatonFragment]
        rcases relationMembership_seq_cases alphabet left right
            hRelated with ⟨q, residualLeft, hEntry, -, -⟩ | ⟨q, hState, hChild⟩
        · exact absurd (congrArg Prod.fst hEntry) (by simp)
        · have hq := ih (typeCompilationFuel right)
            (by rw [← hSize, hFuelEq]; omega) right hChild rfl
          simp only [hAcceptEq, childAccepting, childState,
            Finset.mem_image]
          exact ⟨q, hq, hState.symm⟩
    | par alphabet left right interface =>
        have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq :
            (compileType (.par alphabet left right interface)).accepting =
            {TypeAutomatonState.final} := by
          show (compileTypeFuel
            (typeCompilationFuel (.par alphabet left right interface))
            (.par alphabet left right interface)).accepting = _
          rw [hFuelEq, compileTypeFuel.eq_def]
          show (buildParallelAutomaton alphabet left.alphabet
            right.alphabet interface
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right))
              (left.reannotate alphabet))
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right))
              (right.reannotate alphabet))
            (compiledChildFutureFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compiledChildFutureFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            (compiledChildFutureFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right))
              (left.reannotate alphabet))
            (compiledChildFutureFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right))
              (right.reannotate alphabet))).accepting = _
          simp [buildParallelAutomaton, finishAutomatonFragment]
        rcases relationMembership_par_cases alphabet left right interface
            hRelated with
          ⟨q1, q2, residualLeft, residualRight, hEntry, -, -⟩ |
          ⟨q1, residualLeft, hEntry, hChild, hNotAccept⟩ |
          ⟨q2, residualRight, hEntry, hChild, hNotAccept⟩ | hDone
        · exact absurd (congrArg Prod.fst hEntry) (by simp)
        · rw [Prod.mk.injEq] at hEntry
          obtain ⟨hFst, -⟩ := hEntry
          subst hFst
          exact absurd
            (ih (typeCompilationFuel (left.reannotate alphabet))
              (by rw [← hSize, hFuelEq, typeCompilationFuel_reannotate]; omega)
              (left.reannotate alphabet) hChild rfl)
            hNotAccept
        · rw [Prod.mk.injEq] at hEntry
          obtain ⟨hFst, -⟩ := hEntry
          subst hFst
          exact absurd
            (ih (typeCompilationFuel (right.reannotate alphabet))
              (by rw [← hSize, hFuelEq, typeCompilationFuel_reannotate]; omega)
              (right.reannotate alphabet) hChild rfl)
            hNotAccept
        · rw [hAcceptEq, Finset.mem_singleton]
          exact congrArg Prod.snd hDone
    | recur alphabet name body =>
        have hFuelEq : typeCompilationFuel (.recur alphabet name body) =
            typeCompilationFuel body + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq :
            (compileType (.recur alphabet name body)).accepting =
            childAccepting 0
              (compileTypeFuel (typeCompilationFuel body) body) := by
          show (compileTypeFuel
            (typeCompilationFuel (.recur alphabet name body))
            (.recur alphabet name body)).accepting = _
          rw [hFuelEq, compileTypeFuel.eq_def]
          show (buildRecursionAutomaton alphabet name
            (compileTypeFuel (typeCompilationFuel body) body)).accepting = _
          simp [buildRecursionAutomaton, finishAutomatonFragment]
        rcases relationMembership_recur_cases alphabet name body hRelated with
          hRoot | ⟨q, residual, hEntry, hBody⟩
        · exact absurd (congrArg Prod.fst hRoot) (by simp)
        · rw [Prod.mk.injEq] at hEntry
          obtain ⟨hFst, hSnd⟩ := hEntry
          have hResidual : residual = .skip skipAlphabet := by
            cases residual <;>
              first
                | (simp_all [PactType.replaceVar]; done)
                | (simp only [PactType.replaceVar] at hFst
                   split_ifs at hFst <;> simp_all)
          subst hResidual
          have hq := ih (typeCompilationFuel body)
            (by rw [← hSize, hFuelEq]; omega) body hBody rfl
          rw [hAcceptEq, hSnd]
          simp only [childAccepting, childState, Finset.mem_image]
          exact ⟨q, hq, rfl⟩
    | xoffer alphabet elseType branches =>
        have hFuelEq :
            typeCompilationFuel (.xoffer alphabet elseType branches) =
            max (typeCompilationFuel elseType)
              (typeBranchCompilationFuel branches) + 1 := by
          simp only [typeCompilationFuel]; omega
        let branchAutomata := List.map (fun branch => (branch.1,
          compileTypeFuel (typeCompilationFuel branch.2) branch.2)) branches
        have hMapEq :
            List.map (fun branch => (branch.1,
              compileTypeFuel (max (typeCompilationFuel elseType)
                (typeBranchCompilationFuel branches)) branch.2)) branches =
              branchAutomata := by
          dsimp [branchAutomata]
          apply List.map_congr_left
          intro branch hMem
          have hLeBranch : typeCompilationFuel branch.2 ≤
              typeBranchCompilationFuel branches :=
            typeCompilationFuel_le_typeBranchCompilationFuel branches branch hMem
          rw [compileTypeFuel_eq_of_sufficient branch.2
            (le_trans hLeBranch (le_max_right _ _)) le_rfl]
        have hAcceptEq :
            (compileType (.xoffer alphabet elseType branches)).accepting =
            childAccepting 0
                (compileTypeFuel (typeCompilationFuel elseType) elseType) ∪
              indexedFragmentAccepting branchAutomata := by
          show (compileTypeFuel
            (typeCompilationFuel (.xoffer alphabet elseType branches))
            (.xoffer alphabet elseType branches)).accepting = _
          rw [hFuelEq, compileTypeFuel.eq_def]
          show (buildExclusiveOfferAutomaton alphabet branches
            (compileTypeFuel (max (typeCompilationFuel elseType)
              (typeBranchCompilationFuel branches)) elseType)
            (List.map (fun branch => (branch.1,
              compileTypeFuel (max (typeCompilationFuel elseType)
                (typeBranchCompilationFuel branches)) branch.2))
              branches)).accepting = _
          rw [compileTypeFuel_eq_of_sufficient elseType (le_max_left _ _) le_rfl,
            hMapEq]
          simp [buildExclusiveOfferAutomaton, finishAutomatonFragment,
            branchAutomata]
        rcases relationMembership_xoffer_cases alphabet elseType branches
            hRelated with hRoot | ⟨q, hState, hChild⟩ |
            ⟨i, action, branchType, q, hGet, hState, hChild⟩
        · exact absurd (congrArg Prod.fst hRoot) (by simp)
        · have hState' : state = TypeAutomatonState.child 0 q := hState
          have hq := ih (typeCompilationFuel elseType)
            (by rw [← hSize, hFuelEq]; omega) elseType hChild rfl
          rw [hAcceptEq, hState']
          exact Finset.mem_union_left _
            (by simpa [childAccepting, childState] using
              Finset.mem_image_of_mem (childState 0) hq)
        · have hBranchMem : (action, branchType) ∈ branches :=
            List.mem_of_getElem? hGet
          have hLeBranch : typeCompilationFuel branchType ≤
              typeBranchCompilationFuel branches :=
            typeCompilationFuel_le_typeBranchCompilationFuel branches
              (action, branchType) hBranchMem
          have hState' : state = TypeAutomatonState.child (i + 1) q := hState
          have hq := ih (typeCompilationFuel branchType)
            (by rw [← hSize, hFuelEq]; omega) branchType hChild rfl
          rw [hAcceptEq, hState']
          refine Finset.mem_union_right _ ?_
          rw [indexedFragmentAccepting, mem_foldl_union_iff]
          refine Or.inr ⟨((action,
            compileTypeFuel (typeCompilationFuel branchType) branchType), i),
            ?_, ?_⟩
          · rw [List.mk_mem_zipIdx_iff_getElem?]
            rw [branches_map_getElem?_eq_some_iff branches i action _]
            exact ⟨branchType, hGet, rfl⟩
          · simpa [childAccepting, childState] using
              Finset.mem_image_of_mem (childState (i + 1)) hq
    | offer alphabet elseType branches =>
        have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
            max (typeCompilationFuel elseType)
              (conjunctiveCompilationFuel branches) + 1 := by
          simp only [typeCompilationFuel]; omega
        let selectedConjunctions := List.map (fun selected => (selected.1,
          compileTypeFuel
            (typeCompilationFuel
              (parallelTypeBranchesSelecting alphabet selected branches))
            (parallelTypeBranchesSelecting alphabet selected branches))) branches
        have hMapEq :
            List.map (fun selected => (selected.1,
              compileTypeFuel
                (max (typeCompilationFuel elseType)
                  (conjunctiveCompilationFuel branches))
                (parallelTypeBranchesSelecting alphabet selected branches)))
                branches = selectedConjunctions := by
          dsimp [selectedConjunctions]
          apply List.map_congr_left
          intro selected hSelected
          rw [compileTypeFuel_eq_of_sufficient
            (parallelTypeBranchesSelecting alphabet selected branches) ?_ le_rfl]
          show typeCompilationFuel
              (parallelTypeBranchesSelecting alphabet selected branches) ≤
            max (typeCompilationFuel elseType)
              (conjunctiveCompilationFuel branches)
          rw [typeCompilationFuel_parallelTypeBranchesSelecting]
          exact le_max_right _ _
        have hAcceptEq :
            (compileType (.offer alphabet elseType branches)).accepting =
            childAccepting 0
                (compileTypeFuel (typeCompilationFuel elseType) elseType) ∪
              indexedFragmentAccepting selectedConjunctions := by
          show (compileTypeFuel
            (typeCompilationFuel (.offer alphabet elseType branches))
            (.offer alphabet elseType branches)).accepting = _
          rw [hFuelEq, compileTypeFuel.eq_def]
          show (buildSelectedConjunctiveOfferAutomaton alphabet branches
            (compileTypeFuel
              (max (typeCompilationFuel elseType)
                (conjunctiveCompilationFuel branches)) elseType)
            (List.map (fun selected => (selected.1,
              compileTypeFuel
                (max (typeCompilationFuel elseType)
                  (conjunctiveCompilationFuel branches))
                (parallelTypeBranchesSelecting alphabet selected branches)))
              branches)).accepting = _
          rw [compileTypeFuel_eq_of_sufficient elseType (le_max_left _ _) le_rfl,
            hMapEq]
          simp [buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, selectedConjunctions]
        rcases relationMembership_offer_cases alphabet elseType branches
            hRelated with hRoot | ⟨q, hState, hChild⟩ |
            ⟨i, selected, q, hGet, hState, hChild⟩
        · exact absurd (congrArg Prod.fst hRoot) (by simp)
        · have hState' : state = TypeAutomatonState.child 0 q := hState
          have hq := ih (typeCompilationFuel elseType)
            (by rw [← hSize, hFuelEq]; omega) elseType hChild rfl
          rw [hAcceptEq, hState']
          exact Finset.mem_union_left _
            (by simpa [childAccepting, childState] using
              Finset.mem_image_of_mem (childState 0) hq)
        · have hState' : state = TypeAutomatonState.child (i + 1) q := hState
          have hq := ih
            (typeCompilationFuel
              (parallelTypeBranchesSelecting alphabet selected branches))
            (by rw [← hSize, hFuelEq,
                  typeCompilationFuel_parallelTypeBranchesSelecting]; omega)
            (parallelTypeBranchesSelecting alphabet selected branches)
            hChild rfl
          rw [hAcceptEq, hState']
          refine Finset.mem_union_right _ ?_
          rw [indexedFragmentAccepting, mem_foldl_union_iff]
          refine Or.inr ⟨((selected.1,
            compileTypeFuel
              (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches))
              (parallelTypeBranchesSelecting alphabet selected branches)), i),
            ?_, ?_⟩
          · rw [List.mk_mem_zipIdx_iff_getElem?]
            simp [selectedConjunctions, List.getElem?_map, hGet]
          · simpa [childAccepting, childState] using
              Finset.mem_image_of_mem (childState (i + 1)) hq

/-- Both halves together: a related state is accepting exactly when the residual
it represents has completed. -/
theorem final_states_completion
    (processType : PactType) {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType processType)) residual state) :
    state ∈ (compileType processType).accepting ↔
      ∃ skipAlphabet, residual = .skip skipAlphabet :=
  ⟨fun hAccept => final_state_represents_skip processType hRelated hAccept,
    fun ⟨_, hSkip⟩ =>
      accepting_of_skip_residual processType (hSkip ▸ hRelated)⟩

/-! ### Recursion marker invariant -/

/-- Every alphabet admits the empty environment, so an unresolved call always
emits its marker edge. -/
theorem empty_mem_localEnvironments (alphabet : PactTypeAlphabet) :
    TypeEnvironment.empty ∈ alphabet.localEnvironments := by
  classical
  simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
    Finset.mem_image]
  exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩

/-- A related state sources a marker for `name` exactly when the residual it
represents is that call.  `TailOccurrences name True` is the tail-recursion
side condition: it keeps calls out of a sequence's left operand, out of either
side of a parallel, and out of a conjunctive branch. -/
theorem markerSource_iff_var_residual
    (processType : PactType) (name : String)
    (hTail : PactType.TailOccurrences name True processType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType processType))
        residual state) :
    MarkerSource
        (compileTypeFuel (typeCompilationFuel processType) processType)
        name state ↔
      ∃ alphabet, residual = .var alphabet name := by
  induction hSize : typeCompilationFuel processType using Nat.strong_induction_on
      generalizing processType residual state with
  | _ n ih =>
    subst hSize
    have atomic : ∀ (ty : PactType) (q' : TypeAutomatonState),
        PactType.TailOccurrences name False ty →
        ¬ MarkerSource (compileTypeFuel (typeCompilationFuel ty) ty) name
          q' := by
      intro ty q' hAbsent hMarker
      obtain ⟨edge, hEdge, -, hLabel⟩ := hMarker
      exact absurd hLabel
        (compileTypeFuel_noMarkerFor name (typeCompilationFuel ty) ty hAbsent
          edge hEdge)
    cases processType with
    | skip alphabet =>
        obtain ⟨hResidual, -⟩ :=
          NewCorrespondence.relationMembership_skip_cases alphabet hRelated
        constructor
        · intro hMarker
          exact absurd hMarker
            (atomic _ _ (by rw [PactType.TailOccurrences]; trivial))
        · rintro ⟨a, hEq⟩; rw [hResidual] at hEq; simp at hEq
    | message alphabet msg dir =>
        constructor
        · intro hMarker
          exact absurd hMarker
            (atomic _ _ (by rw [PactType.TailOccurrences]; trivial))
        · rintro ⟨a, hEq⟩
          rcases NewCorrespondence.relationMembership_message_cases alphabet msg
              dir hRelated with ⟨hR, -⟩ | ⟨hR, -⟩ <;> rw [hR] at hEq <;>
            simp at hEq
    | tock alphabet =>
        constructor
        · intro hMarker
          exact absurd hMarker
            (atomic _ _ (by rw [PactType.TailOccurrences]; trivial))
        · rintro ⟨a, hEq⟩
          rcases NewCorrespondence.relationMembership_tock_cases alphabet
              hRelated with ⟨hR, -⟩ | ⟨hR, -⟩ <;> rw [hR] at hEq <;> simp at hEq
    | progress alphabet pid =>
        constructor
        · intro hMarker
          exact absurd hMarker
            (atomic _ _ (by rw [PactType.TailOccurrences]; trivial))
        · rintro ⟨a, hEq⟩
          rcases NewCorrespondence.relationMembership_progress_cases alphabet pid
              hRelated with ⟨hR, -⟩ | ⟨hR, -⟩ <;> rw [hR] at hEq <;> simp at hEq
    | var alphabet other =>
        obtain ⟨hResidual, hState⟩ :=
          relationMembership_var_cases alphabet other hRelated
        subst hState
        subst hResidual
        constructor
        · rintro ⟨edge, hEdge, -, hLabel⟩
          simp only [typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment, Finset.mem_image,
            Finset.mem_filter] at hEdge
          obtain ⟨environment, -, rfl⟩ := hEdge
          simp only [AutomatonConstructionLabel.variable.injEq] at hLabel
          exact ⟨alphabet, by rw [hLabel]⟩
        · rintro ⟨a, hEq⟩
          have hName : other = name := by
            injection hEq with hAlpha hName
          refine ⟨{ source := .root
                    environment := TypeEnvironment.empty
                    label := .variable other
                    current := ∅
                    future := .at .final ∅
                    target := .final }, ?_, rfl, by rw [hName]⟩
          simp only [typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment, Finset.mem_image, Finset.mem_filter]
          exact ⟨TypeEnvironment.empty,
            ⟨empty_mem_localEnvironments alphabet, rfl⟩, rfl⟩
    | choice alphabet left right =>
        have hFuelEq : typeCompilationFuel (PactType.choice alphabet left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hCompileEq :
            compileTypeFuel (typeCompilationFuel (PactType.choice alphabet left right)) (PactType.choice alphabet left right) =
              buildChoiceAutomaton alphabet
                (compileTypeFuel (typeCompilationFuel left) left)
                (compileTypeFuel (typeCompilationFuel right) right)
                TypeLabel.silent TypeLabel.silent := by
          rw [hFuelEq, compileTypeFuel.eq_def]
          show buildChoiceAutomaton alphabet
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            TypeLabel.silent TypeLabel.silent = _
          rw [compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
        rw [PactType.TailOccurrences] at hTail
        rcases relationMembership_choice_cases alphabet left right hRelated with
          hRoot | ⟨q, hState, hChild⟩ | ⟨q, hState, hChild⟩
        · have hStateEq : state = TypeAutomatonState.root :=
            congrArg Prod.snd hRoot
          have hResidual : residual = PactType.choice alphabet left right := congrArg Prod.fst hRoot
          subst hStateEq
          rw [hCompileEq]
          constructor
          · intro hMarker
            exact absurd hMarker (buildChoiceAutomaton_markerSource_root _ _ _ _ _ _)
          · rintro ⟨a, hEq⟩; rw [hResidual] at hEq; simp at hEq
        · have hStateEq : state = TypeAutomatonState.child 0 q := hState
          subst hStateEq
          rw [hCompileEq, show TypeAutomatonState.child 0 q = childState 0 q from rfl,
            buildChoiceAutomaton_markerSource_child0]
          exact ih (typeCompilationFuel left) (by rw [hFuelEq]; omega) left
            hTail.1 hChild rfl
        · have hStateEq : state = TypeAutomatonState.child 1 q := hState
          subst hStateEq
          rw [hCompileEq, show TypeAutomatonState.child 1 q = childState 1 q from rfl,
            buildChoiceAutomaton_markerSource_child1]
          exact ih (typeCompilationFuel right) (by rw [hFuelEq]; omega) right
            hTail.2 hChild rfl
    | fairChoice alphabet bid left right =>
        have hFuelEq : typeCompilationFuel (PactType.fairChoice alphabet bid left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hCompileEq :
            compileTypeFuel (typeCompilationFuel (PactType.fairChoice alphabet bid left right)) (PactType.fairChoice alphabet bid left right) =
              buildChoiceAutomaton alphabet
                (compileTypeFuel (typeCompilationFuel left) left)
                (compileTypeFuel (typeCompilationFuel right) right)
                (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
          rw [hFuelEq, compileTypeFuel.eq_def]
          show buildChoiceAutomaton alphabet
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            (TypeLabel.fair bid true) (TypeLabel.fair bid false) = _
          rw [compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
        rw [PactType.TailOccurrences] at hTail
        rcases relationMembership_fairChoice_cases alphabet bid left right hRelated with
          hRoot | ⟨q, hState, hChild⟩ | ⟨q, hState, hChild⟩
        · have hStateEq : state = TypeAutomatonState.root :=
            congrArg Prod.snd hRoot
          have hResidual : residual = PactType.fairChoice alphabet bid left right := congrArg Prod.fst hRoot
          subst hStateEq
          rw [hCompileEq]
          constructor
          · intro hMarker
            exact absurd hMarker (buildChoiceAutomaton_markerSource_root _ _ _ _ _ _)
          · rintro ⟨a, hEq⟩; rw [hResidual] at hEq; simp at hEq
        · have hStateEq : state = TypeAutomatonState.child 0 q := hState
          subst hStateEq
          rw [hCompileEq, show TypeAutomatonState.child 0 q = childState 0 q from rfl,
            buildChoiceAutomaton_markerSource_child0]
          exact ih (typeCompilationFuel left) (by rw [hFuelEq]; omega) left
            hTail.1 hChild rfl
        · have hStateEq : state = TypeAutomatonState.child 1 q := hState
          subst hStateEq
          rw [hCompileEq, show TypeAutomatonState.child 1 q = childState 1 q from rfl,
            buildChoiceAutomaton_markerSource_child1]
          exact ih (typeCompilationFuel right) (by rw [hFuelEq]; omega) right
            hTail.2 hChild rfl
    | seq alphabet left right =>
        have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hCompileEq :
            compileTypeFuel (typeCompilationFuel (.seq alphabet left right))
                (.seq alphabet left right) =
              buildSequenceAutomaton
                (compileTypeFuel (typeCompilationFuel left) left)
                (compileTypeFuel (typeCompilationFuel right) right) := by
          rw [hFuelEq, compileTypeFuel.eq_def]
          show buildSequenceAutomaton
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right))
              right) = _
          rw [compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
        rw [PactType.TailOccurrences] at hTail
        rcases relationMembership_seq_cases alphabet left right hRelated with
          ⟨q, residualLeft, hEntry, -, -⟩ | ⟨q, hState, hChild⟩
        · have hResidual : residual = .seq alphabet residualLeft right :=
            congrArg Prod.fst hEntry
          have hStateEq : state = TypeAutomatonState.child 0 q :=
            congrArg Prod.snd hEntry
          subst hStateEq
          rw [hCompileEq]
          constructor
          · intro hMarker
            exact absurd
              (buildSequenceAutomaton_markerSource_child0 _ _ name q hMarker)
              (atomic left q hTail.1)
          · rintro ⟨a, hEq⟩; rw [hResidual] at hEq; simp at hEq
        · have hStateEq : state = TypeAutomatonState.child 1 q := hState
          subst hStateEq
          rw [hCompileEq,
            show TypeAutomatonState.child 1 q = childState 1 q from rfl,
            buildSequenceAutomaton_markerSource_child1]
          exact ih (typeCompilationFuel right) (by rw [hFuelEq]; omega) right
            hTail.2 hChild rfl
    | par alphabet left right interface =>
        have hFuelEq :
            typeCompilationFuel (.par alphabet left right interface) =
              max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        rw [PactType.TailOccurrences] at hTail
        have hTailPar : PactType.TailOccurrences name False
            (.par alphabet left right interface) := by
          rw [PactType.TailOccurrences]; exact hTail
        constructor
        · intro hMarker
          exact absurd hMarker (atomic _ state hTailPar)
        · rintro ⟨a, hEq⟩
          exfalso
          rcases relationMembership_par_cases alphabet left right interface
              hRelated with
            ⟨q1, q2, rL, rR, hEntry, -, -⟩ | ⟨q1, rL, hEntry, hChild, -⟩ |
            ⟨q2, rR, hEntry, hChild, -⟩ | hDone
          · have hR : residual = .par alphabet rL rR interface :=
              congrArg Prod.fst hEntry
            rw [hEq] at hR; simp at hR
          · have hR : residual = rL := congrArg Prod.fst hEntry
            have hStateEq : state = TypeAutomatonState.survivor 0 q1 :=
              congrArg Prod.snd hEntry
            have hAbsentChild : PactType.TailOccurrences name False
                (left.reannotate alphabet) :=
              PactType.reannotate_tailOccurrences name left alphabet False
                hTail.1
            refine absurd ?_ (atomic (left.reannotate alphabet) q1 hAbsentChild)
            refine (ih (typeCompilationFuel (left.reannotate alphabet))
              (by rw [hFuelEq, typeCompilationFuel_reannotate]; omega)
              (left.reannotate alphabet)
              (PactType.tailOccurrences_mono name False.elim _ hAbsentChild)
              hChild rfl).mpr ⟨a, by rw [← hR, hEq]⟩
          · have hR : residual = rR := congrArg Prod.fst hEntry
            have hAbsentChild : PactType.TailOccurrences name False
                (right.reannotate alphabet) :=
              PactType.reannotate_tailOccurrences name right alphabet False
                hTail.2
            refine absurd ?_ (atomic (right.reannotate alphabet) q2 hAbsentChild)
            refine (ih (typeCompilationFuel (right.reannotate alphabet))
              (by rw [hFuelEq, typeCompilationFuel_reannotate]; omega)
              (right.reannotate alphabet)
              (PactType.tailOccurrences_mono name False.elim _ hAbsentChild)
              hChild rfl).mpr ⟨a, by rw [← hR, hEq]⟩
          · have hR : residual = .skip alphabet := congrArg Prod.fst hDone
            rw [hEq] at hR; simp at hR
    | xoffer alphabet elseType branches =>
        have hFuelEq :
            typeCompilationFuel (.xoffer alphabet elseType branches) =
              max (typeCompilationFuel elseType)
                (typeBranchCompilationFuel branches) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hMapEq :
            List.map (fun branch => (branch.1,
              compileTypeFuel (max (typeCompilationFuel elseType)
                (typeBranchCompilationFuel branches)) branch.2)) branches =
              List.map (fun branch => (branch.1,
                compileTypeFuel (typeCompilationFuel branch.2) branch.2))
                branches := by
          apply List.map_congr_left
          intro branch hMem
          have hLeBranch : typeCompilationFuel branch.2 ≤
              typeBranchCompilationFuel branches :=
            typeCompilationFuel_le_typeBranchCompilationFuel branches branch hMem
          rw [compileTypeFuel_eq_of_sufficient branch.2
            (le_trans hLeBranch (le_max_right _ _)) le_rfl]
        have hCompileEq :
            compileTypeFuel (typeCompilationFuel (.xoffer alphabet elseType
                branches)) (.xoffer alphabet elseType branches) =
              buildExclusiveOfferAutomaton alphabet branches
                (compileTypeFuel (typeCompilationFuel elseType) elseType)
                (List.map (fun branch => (branch.1,
                  compileTypeFuel (typeCompilationFuel branch.2) branch.2))
                  branches) := by
          rw [hFuelEq, compileTypeFuel.eq_def]
          show buildExclusiveOfferAutomaton alphabet branches
            (compileTypeFuel (max (typeCompilationFuel elseType)
              (typeBranchCompilationFuel branches)) elseType)
            (List.map (fun branch => (branch.1,
              compileTypeFuel (max (typeCompilationFuel elseType)
                (typeBranchCompilationFuel branches)) branch.2))
              branches) = _
          rw [compileTypeFuel_eq_of_sufficient elseType (le_max_left _ _) le_rfl,
            hMapEq]
        rw [PactType.TailOccurrences] at hTail
        obtain ⟨hElse, hBranches⟩ := hTail
        have hEach : ∀ branch ∈ branches,
            PactType.TailOccurrences name True branch.2 :=
          tailBranchOccurrences_forall name True branches hBranches
        rcases relationMembership_xoffer_cases alphabet elseType branches
            hRelated with hRoot | ⟨q, hState, hChild⟩ |
            ⟨i, action, branchType, q, hGet, hState, hChild⟩
        · have hResidual : residual = .xoffer alphabet elseType branches :=
            congrArg Prod.fst hRoot
          have hStateEq : state = TypeAutomatonState.root :=
            congrArg Prod.snd hRoot
          subst hStateEq
          rw [hCompileEq]
          constructor
          · intro hMarker
            exact absurd hMarker
              (buildExclusiveOfferAutomaton_markerSource_root _ _ _ _ _)
          · rintro ⟨a, hEq⟩; rw [hResidual] at hEq; simp at hEq
        · have hStateEq : state = TypeAutomatonState.child 0 q := hState
          subst hStateEq
          rw [hCompileEq,
            show TypeAutomatonState.child 0 q = childState 0 q from rfl,
            buildExclusiveOfferAutomaton_markerSource_child0]
          exact ih (typeCompilationFuel elseType) (by rw [hFuelEq]; omega)
            elseType hElse hChild rfl
        · have hStateEq : state = TypeAutomatonState.child (i + 1) q := hState
          have hBranchMem : (action, branchType) ∈ branches :=
            List.mem_of_getElem? hGet
          have hLeBranch : typeCompilationFuel branchType ≤
              typeBranchCompilationFuel branches :=
            typeCompilationFuel_le_typeBranchCompilationFuel branches
              (action, branchType) hBranchMem
          have hEntry :
              (List.map (fun branch => (branch.1,
                compileTypeFuel (typeCompilationFuel branch.2) branch.2))
                branches)[i]? =
                some (action,
                  compileTypeFuel (typeCompilationFuel branchType) branchType) :=
            (branches_map_getElem?_eq_some_iff branches i action _).mpr
              ⟨branchType, hGet, rfl⟩
          subst hStateEq
          rw [hCompileEq,
            show TypeAutomatonState.child (i + 1) q = childState (i + 1) q
              from rfl,
            buildExclusiveOfferAutomaton_markerSource_branch alphabet branches _
              _ name i _ hEntry q]
          exact ih (typeCompilationFuel branchType) (by rw [hFuelEq]; omega)
            branchType (hEach _ hBranchMem) hChild rfl
    | offer alphabet elseType branches =>
        have hFuelEq :
            typeCompilationFuel (.offer alphabet elseType branches) =
              max (typeCompilationFuel elseType)
                (conjunctiveCompilationFuel branches) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hMapEq :
            List.map (fun selected => (selected.1,
              compileTypeFuel (max (typeCompilationFuel elseType)
                (conjunctiveCompilationFuel branches))
                (parallelTypeBranchesSelecting alphabet selected branches)))
                branches =
              List.map (fun selected => (selected.1,
                compileTypeFuel (typeCompilationFuel
                  (parallelTypeBranchesSelecting alphabet selected branches))
                  (parallelTypeBranchesSelecting alphabet selected branches)))
                branches := by
          apply List.map_congr_left
          intro selected hSelected
          rw [compileTypeFuel_eq_of_sufficient
            (parallelTypeBranchesSelecting alphabet selected branches) ?_ le_rfl]
          show typeCompilationFuel
              (parallelTypeBranchesSelecting alphabet selected branches) ≤
            max (typeCompilationFuel elseType)
              (conjunctiveCompilationFuel branches)
          rw [typeCompilationFuel_parallelTypeBranchesSelecting]
          exact le_max_right _ _
        have hCompileEq :
            compileTypeFuel (typeCompilationFuel (.offer alphabet elseType
                branches)) (.offer alphabet elseType branches) =
              buildSelectedConjunctiveOfferAutomaton alphabet branches
                (compileTypeFuel (typeCompilationFuel elseType) elseType)
                (List.map (fun selected => (selected.1,
                  compileTypeFuel (typeCompilationFuel
                    (parallelTypeBranchesSelecting alphabet selected branches))
                    (parallelTypeBranchesSelecting alphabet selected branches)))
                  branches) := by
          rw [hFuelEq, compileTypeFuel.eq_def]
          show buildSelectedConjunctiveOfferAutomaton alphabet branches
            (compileTypeFuel (max (typeCompilationFuel elseType)
              (conjunctiveCompilationFuel branches)) elseType)
            (List.map (fun selected => (selected.1,
              compileTypeFuel (max (typeCompilationFuel elseType)
                (conjunctiveCompilationFuel branches))
                (parallelTypeBranchesSelecting alphabet selected branches)))
              branches) = _
          rw [compileTypeFuel_eq_of_sufficient elseType (le_max_left _ _) le_rfl,
            hMapEq]
        rw [PactType.TailOccurrences] at hTail
        obtain ⟨hElse, hBranches⟩ := hTail
        have hEach : ∀ branch ∈ branches,
            PactType.TailOccurrences name False branch.2 :=
          tailBranchOccurrences_forall name False branches hBranches
        rcases relationMembership_offer_cases alphabet elseType branches
            hRelated with hRoot | ⟨q, hState, hChild⟩ |
            ⟨i, selected, q, hGet, hState, hChild⟩
        · have hResidual : residual = .offer alphabet elseType branches :=
            congrArg Prod.fst hRoot
          have hStateEq : state = TypeAutomatonState.root :=
            congrArg Prod.snd hRoot
          subst hStateEq
          rw [hCompileEq]
          constructor
          · intro hMarker
            exact absurd hMarker
              (buildSelectedConjunctiveOfferAutomaton_markerSource_root
                _ _ _ _ _)
          · rintro ⟨a, hEq⟩; rw [hResidual] at hEq; simp at hEq
        · have hStateEq : state = TypeAutomatonState.child 0 q := hState
          subst hStateEq
          rw [hCompileEq,
            show TypeAutomatonState.child 0 q = childState 0 q from rfl,
            buildSelectedConjunctiveOfferAutomaton_markerSource_child0]
          exact ih (typeCompilationFuel elseType) (by rw [hFuelEq]; omega)
            elseType hElse hChild rfl
        · have hStateEq : state = TypeAutomatonState.child (i + 1) q := hState
          have hSelectedMem : selected ∈ branches := List.mem_of_getElem? hGet
          have hAbsentChild : PactType.TailOccurrences name False
              (parallelTypeBranchesSelecting alphabet selected branches) :=
            parallelTypeBranchesSelecting_tailOccurrences name alphabet selected
              branches False hEach (hEach selected hSelectedMem)
          have hEntry :
              (List.map (fun sel => (sel.1,
                compileTypeFuel (typeCompilationFuel
                  (parallelTypeBranchesSelecting alphabet sel branches))
                  (parallelTypeBranchesSelecting alphabet sel branches)))
                branches)[i]? =
                some (selected.1,
                  compileTypeFuel (typeCompilationFuel
                    (parallelTypeBranchesSelecting alphabet selected branches))
                    (parallelTypeBranchesSelecting alphabet selected
                      branches)) := by
            simp [List.getElem?_map, hGet]
          subst hStateEq
          rw [hCompileEq,
            show TypeAutomatonState.child (i + 1) q = childState (i + 1) q
              from rfl,
            buildSelectedConjunctiveOfferAutomaton_markerSource_branch alphabet
              branches _ _ name i _ hEntry q]
          constructor
          · intro hMarker
            exact absurd hMarker (atomic _ q hAbsentChild)
          · rintro ⟨a, hEq⟩
            refine absurd ?_ (atomic _ q hAbsentChild)
            exact (ih (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches))
              (by rw [hFuelEq, typeCompilationFuel_parallelTypeBranchesSelecting];
                  omega)
              _ (PactType.tailOccurrences_mono name False.elim _ hAbsentChild)
              hChild rfl).mpr ⟨a, hEq⟩
    | recur alphabet binder body =>
        have hFuelEq : typeCompilationFuel (.recur alphabet binder body) =
            typeCompilationFuel body + 1 := by
          simp only [typeCompilationFuel]; omega
        have hCompileEq :
            compileTypeFuel (typeCompilationFuel (.recur alphabet binder body))
                (.recur alphabet binder body) =
              buildRecursionAutomaton alphabet binder
                (compileTypeFuel (typeCompilationFuel body) body) := by
          rw [hFuelEq, compileTypeFuel.eq_def]
        rw [PactType.TailOccurrences] at hTail
        rcases relationMembership_recur_cases alphabet binder body hRelated with
          hRoot | ⟨q, rho, hEntry, hBody⟩
        · have hResidual : residual = .recur alphabet binder body :=
            congrArg Prod.fst hRoot
          have hStateEq : state = TypeAutomatonState.root :=
            congrArg Prod.snd hRoot
          subst hStateEq
          rw [hCompileEq]
          constructor
          · intro hMarker
            exact absurd hMarker
              (not_buildRecursionAutomaton_markerSource_root _ _ _ _)
          · rintro ⟨a, hEq⟩; rw [hResidual] at hEq; simp at hEq
        · have hResidual :
              residual = rho.replaceVar binder (.recur alphabet binder body) :=
            congrArg Prod.fst hEntry
          have hStateEq : state = TypeAutomatonState.child 0 q :=
            congrArg Prod.snd hEntry
          subst hStateEq
          by_cases hBinder : binder = name
          · subst hBinder
            constructor
            · intro hMarker
              refine absurd hMarker (atomic _ _ ?_)
              rw [PactType.TailOccurrences]; simp
            · rintro ⟨a, hEq⟩
              exfalso
              rw [hResidual] at hEq
              cases rho <;>
                first
                  | (simp [PactType.replaceVar] at hEq; done)
                  | (simp only [PactType.replaceVar] at hEq
                     split_ifs at hEq <;> simp_all)
          · rw [hCompileEq,
              show TypeAutomatonState.child 0 q = childState 0 q from rfl,
              buildRecursionAutomaton_markerSource_child alphabet binder name
                (compileTypeFuel (typeCompilationFuel body) body)
                (fun hEq => hBinder hEq.symm) q]
            have hRhoIff : (∃ a, residual = .var a name) ↔
                ∃ a, rho = .var a name := by
              rw [hResidual]
              constructor
              · rintro ⟨a, hEq⟩
                cases rho <;>
                  first
                    | (simp [PactType.replaceVar] at hEq; done)
                    | (simp only [PactType.replaceVar] at hEq
                       split_ifs at hEq <;> simp_all)
              · rintro ⟨a, rfl⟩
                exact ⟨a, by simp [PactType.replaceVar, hBinder]⟩
            rw [hRhoIff]
            exact ih (typeCompilationFuel body) (by rw [hFuelEq]; omega) body
              (by simpa [hBinder] using hTail) hBody rfl

end

end Pact
