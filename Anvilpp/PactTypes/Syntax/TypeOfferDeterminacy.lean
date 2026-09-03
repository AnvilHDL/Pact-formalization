import Anvilpp.PactTypes.Syntax.TypeTransitionSystemLemmas
import Anvilpp.PactTypes.Syntax.PactTypeRegularityLemmas
import Anvilpp.PactTypes.Syntax.PactTypeShapeLemmas
import Anvilpp.PactTypes.Syntax.TypeOffersAlphabet
import Anvilpp.PactTypes.Syntax.TypeOfferEnvironmentAgreementLemmas
import Anvilpp.PactTypes.Syntax.TypeLabelCombine
import Anvilpp.PactTypes.Syntax.TypeLabelOwnershipLemmas

namespace Pact
open Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000000

/-- `LocalTypeOfferEnvironment` pins the local environment from the outer one
and the sibling's offers; the sibling environment itself is inert. -/
theorem localTypeOfferEnvironment_unique
    {outer : TypeEnvironment} {interface : Interface} {localType : PactType}
    {sib₁ sib₂ localEnv₁ localEnv₂ : TypeEnvironment}
    {c f : Finset BareMessage}
    (h₁ : LocalTypeOfferEnvironment outer interface localType sib₁ c f localEnv₁)
    (h₂ : LocalTypeOfferEnvironment outer interface localType sib₂ c f localEnv₂) :
    localEnv₁ = localEnv₂ := by
  rcases localEnv₁ with ⟨i₁, u₁, k₁⟩
  rcases localEnv₂ with ⟨i₂, u₂, k₂⟩
  cases h₁ <;> cases h₂ <;> simp_all

/-- A sequence is never its own right operand. -/
theorem seq_ne_right (alphabet : PactTypeAlphabet) (left right : PactType) :
    PactType.seq alphabet left right ≠ right := by
  intro h
  have hLt : sizeOf right < sizeOf (PactType.seq alphabet left right) := by
    simp_wf
    omega
  rw [h] at hLt
  omega

/-- Observable labels are not silent. -/
@[simp] theorem message_ne_silent (msg : MessageId) (dir : MessageDir) :
    TypeLabel.message msg dir ≠ TypeLabel.silent := by
  simp [TypeLabel.message, TypeLabel.silent, TypeLabel.actions.injEq,
    Finset.singleton_ne_empty]

@[simp] theorem progress_ne_silent (pid : ProcId) :
    TypeLabel.progress pid ≠ TypeLabel.silent := by
  simp [TypeLabel.progress, TypeLabel.silent, TypeLabel.actions.injEq,
    Finset.singleton_ne_empty]

@[simp] theorem fair_ne_silent (bid : BranchId) (taken : Bool) :
    TypeLabel.fair bid taken ≠ TypeLabel.silent := by
  simp [TypeLabel.fair, TypeLabel.silent, TypeLabel.actions.injEq,
    Finset.singleton_ne_empty]

/-- A branch that the environment enables immediately contradicts the
"no immediate branch" side condition of the else/wait clauses. -/
theorem not_typeBranchEnabled_of_noImmediate
    {env : TypeEnvironment} {branches : List (BareMessage × PactType)}
    {enabled : BareMessage × PactType}
    (hNo : TypeNoImmediateBranch env branches) (hMem : enabled ∈ branches)
    (hEnabled : TypeBranchEnabled env enabled) : False := by
  rw [TypeNoImmediateBranch, Finset.eq_empty_iff_forall_notMem] at hNo
  refine hNo (typeNeed enabled.1) (Finset.mem_inter.mpr ⟨?_, hEnabled⟩)
  simp only [typeBranchNeeds, List.mem_toFinset, List.mem_map]
  exact ⟨enabled, hMem, rfl⟩

/-- Observable message labels name their action. -/
theorem bareMessage_of_message_label {a b : BareMessage}
    (h : TypeLabel.message a.1 a.2 = TypeLabel.message b.1 b.2) : a = b := by
  obtain ⟨msg₁, dir₁⟩ := a
  obtain ⟨msg₂, dir₂⟩ := b
  simp only [TypeLabel.message, TypeLabel.actions.injEq, Finset.singleton_inj,
    TypeObservation.message.injEq] at h
  simp [h.1, h.2]

@[simp] theorem silent_ne_message (msg : MessageId) (dir : MessageDir) :
    TypeLabel.silent ≠ TypeLabel.message msg dir :=
  Ne.symm (message_ne_silent msg dir)

@[simp] theorem silent_ne_progress (pid : ProcId) :
    TypeLabel.silent ≠ TypeLabel.progress pid :=
  Ne.symm (progress_ne_silent pid)

@[simp] theorem silent_ne_fair (bid : BranchId) (taken : Bool) :
    TypeLabel.silent ≠ TypeLabel.fair bid taken :=
  Ne.symm (fair_ne_silent bid taken)

/-- Reannotation preserves the head constructor, so only a `skip` reannotates
to a `skip`. -/
theorem eq_skip_of_reannotate_eq_skip {target : PactType}
    {alphabet skipAlphabet : PactTypeAlphabet}
    (h : PactType.skip skipAlphabet = target.reannotate alphabet) :
    target = .skip target.alphabet := by
  cases hForm : target <;> rw [hForm] at h <;>
    simp [PactType.reannotate, PactType.alphabet] at h ⊢

/-- The `else`/`wait` clauses of a conjunctive offer carry the
"no immediate branch" side condition. -/
theorem noImmediate_of_elseCond {env : TypeEnvironment}
    {branches : List (BareMessage × PactType)} {A B C : Prop}
    (h : A ∧ B ∧ TypeNoImmediateBranch env branches ∧ C) :
    TypeNoImmediateBranch env branches := h.2.2.1

/-- The `some` clause of a conjunctive offer carries an immediately enabled
branch, which the `else`/`wait` side condition forbids. -/
theorem noImmediate_absurd_of_someEnabled {env : TypeEnvironment}
    {branches : List (BareMessage × PactType)}
    {enabled : BareMessage × PactType} {A : Prop}
    (hNo : TypeNoImmediateBranch env branches)
    (hSome : A ∧ enabled ∈ branches ∧ TypeBranchEnabled env enabled) : False :=
  not_typeBranchEnabled_of_noImmediate hNo hSome.2.1 hSome.2.2

/-- An exclusive offer is never its own else arm. -/
theorem xoffer_ne_else (alphabet : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) :
    PactType.xoffer alphabet elseType branches ≠ elseType := by
  intro h
  have hLt : sizeOf elseType <
      sizeOf (PactType.xoffer alphabet elseType branches) := by
    simp_wf
    omega
  rw [h] at hLt
  omega

/-- A conjunctive offer is never its own else arm. -/
theorem offer_ne_else (alphabet : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) :
    PactType.offer alphabet elseType branches ≠ elseType := by
  intro h
  have hLt : sizeOf elseType <
      sizeOf (PactType.offer alphabet elseType branches) := by
    simp_wf
    omega
  rw [h] at hLt
  omega

/-- The `some` clause of a conjunctive offer witnesses a non-empty branch list. -/
theorem branches_ne_nil_of_someEnabled {env : TypeEnvironment}
    {branches : List (BareMessage × PactType)}
    {enabled : BareMessage × PactType} {A : Prop}
    (h : A ∧ enabled ∈ branches ∧ TypeBranchEnabled env enabled) :
    branches ≠ [] := by
  intro hNil
  rw [hNil] at h
  exact absurd h.2.1 (by simp)



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


/-- Currents and futures agree away from an accumulated hidden set `H`, given
environments that agree away from `H`.  Currents are indexed by the *shape* of
the target (which `reannotate` preserves); futures by the target itself. -/
theorem typeOffers_unique_aux :
    ∀ {e₁ : TypeEnvironment} {s₁ : PactType} {l₁ : TypeLabel} {t₁ : PactType}
      {c₁ f₁ : Finset BareMessage},
      TypeOffers e₁ s₁ l₁ t₁ c₁ f₁ →
      s₁.AlphabetWellFormed → s₁.SameCycleMessageLinear →
      s₁.ParallelMessageOwnership → s₁.ParallelProgressOwnership →
      s₁.ParallelFairChoiceOwnership → s₁.InterfaceScoped →
    ∀ (H : Interface) {e₂ : TypeEnvironment} {s₂ : PactType} {l₂ : TypeLabel}
      {t₂ : PactType} {c₂ f₂ : Finset BareMessage},
      TypeOffers e₂ s₂ l₂ t₂ c₂ f₂ →
      EnvAgreeOutside H e₁ e₂ → s₁ = s₂ → l₁ = l₂ →
      (PactType.shape t₁ = PactType.shape t₂ →
          hideTypeOffers H c₁ = hideTypeOffers H c₂) ∧
        (t₁ = t₂ → hideTypeOffers H f₁ = hideTypeOffers H f₂) := by
   intro e₁ s₁ l₁ t₁ c₁ f₁ h₁
   induction h₁ with
   | seq env alphabet left left' right label current childFuture hChild
       hNotSkip hNotTock ih =>
       intro hWF hLin hMsg hProg hFair hScop H e₂ s₂ l₂ t₂ c₂ f₂ h₂ hAgree hSource hLabel
       cases h₂ <;>
         (try (first
                 | (exfalso; cases hSource; done)
                 | (injection hSource; subst_vars; contradiction)
                 | (refine absurd hLabel ?_; simp; done))) <;>
         (try refine ⟨fun hShape => ?_, fun hTarget => ?_⟩) <;>
         (try (have hShape := congrArg PactType.shape hTarget)) <;>
         first
           | rfl
           | (subst hTarget; rfl)
           | (injection hSource; subst_vars; rfl)
           | exact absurd hTarget (seq_ne_right _ _ _)
           | exact absurd hTarget.symm (seq_ne_right _ _ _)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget) (by assumption)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget.symm) (by assumption)
           | (exfalso
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              try clear hTarget
              injection hSource
              subst_vars
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              injection hSource with _ hElseEq hBranchEq
              try rw [hElseEq] at hTarget
              try rw [hBranchEq] at hTarget
              first
                | exact absurd hTarget (Ne.symm (xoffer_ne_else _ _ _))
                | exact absurd hTarget (xoffer_ne_else _ _ _)
                | exact absurd hTarget (Ne.symm (offer_ne_else _ _ _))
                | exact absurd hTarget (offer_ne_else _ _ _))
           | (exfalso
              injection hSource with hSA hSL hSR
              try rw [hSA] at hTarget
              try rw [hSL] at hTarget
              try rw [hSR] at hTarget
              first
                | exact absurd hTarget (seq_ne_right _ _ _)
                | exact absurd hTarget.symm (seq_ne_right _ _ _))
           | (obtain rfl := bareMessage_of_message_label hLabel
              first
                | rfl
                | (subst hTarget; rfl)
                | (injection hSource; subst_vars; rfl))
           | (refine absurd hSource ?_; simp; done)
           | (refine absurd hLabel ?_; simp; done)
           | (refine absurd hTarget ?_; simp; done)
           | (injection hSource; subst_vars; contradiction)
           | (injection hSource; subst_vars; simp_all; done)
           | (injection hSource with hAlpha hLeftEq hRightEq
              subst hAlpha
              subst hLeftEq
              subst hRightEq
              have hWFLeft : left.AlphabetWellFormed := by
                simp only [PactType.AlphabetWellFormed] at hWF
                exact hWF.2.2.2.1
              have hLinLeft : left.SameCycleMessageLinear := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.1
              have hMsgLeft : left.ParallelMessageOwnership := by
                simp only [PactType.ParallelMessageOwnership] at hMsg
                exact hMsg.1
              have hProgLeft : left.ParallelProgressOwnership := by
                simp only [PactType.ParallelProgressOwnership] at hProg
                exact hProg.1
              have hFairLeft : left.ParallelFairChoiceOwnership := by
                simp only [PactType.ParallelFairChoiceOwnership] at hFair
                exact hFair.1
              have hScopLeft : left.InterfaceScoped := by
                simp only [PactType.InterfaceScoped] at hScop
                tauto
              have key : ∀ {lt : PactType} {c f : Finset BareMessage},
                  TypeOffers e₂ left l₂ lt c f → left'.shape = lt.shape →
                  hideTypeOffers H current = hideTypeOffers H c := by
                intro lt c f hOff hSh
                exact (ih hWFLeft hLinLeft hMsgLeft hProgLeft hFairLeft hScopLeft H hOff hAgree rfl hLabel).1 hSh
              first
                | (refine key (by assumption) ?_
                   simp only [PactType.shape, PactShape.seq.injEq] at hShape
                   exact hShape.1)
                | (injection hTarget with _ hChildTarget _
                   subst hChildTarget
                   rw [hideTypeOffers_sdiff, hideTypeOffers_sdiff,
                     key (by assumption) rfl])
                | (injection hTarget with _ hChildTarget _
                   subst hChildTarget
                   rw [key (by assumption) rfl]))
           | skip
   | seq_tock env alphabet left left' right current childFuture hChild
       hNotSkip ih =>
       intro hWF hLin hMsg hProg hFair hScop H e₂ s₂ l₂ t₂ c₂ f₂ h₂ hAgree hSource hLabel
       cases h₂ <;>
         (try (first
                 | (exfalso; cases hSource; done)
                 | (injection hSource; subst_vars; contradiction)
                 | (refine absurd hLabel ?_; simp; done))) <;>
         (try refine ⟨fun hShape => ?_, fun hTarget => ?_⟩) <;>
         (try (have hShape := congrArg PactType.shape hTarget)) <;>
         first
           | rfl
           | (subst hTarget; rfl)
           | (injection hSource; subst_vars; rfl)
           | exact absurd hTarget (seq_ne_right _ _ _)
           | exact absurd hTarget.symm (seq_ne_right _ _ _)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget) (by assumption)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget.symm) (by assumption)
           | (exfalso
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              try clear hTarget
              injection hSource
              subst_vars
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              injection hSource with _ hElseEq hBranchEq
              try rw [hElseEq] at hTarget
              try rw [hBranchEq] at hTarget
              first
                | exact absurd hTarget (Ne.symm (xoffer_ne_else _ _ _))
                | exact absurd hTarget (xoffer_ne_else _ _ _)
                | exact absurd hTarget (Ne.symm (offer_ne_else _ _ _))
                | exact absurd hTarget (offer_ne_else _ _ _))
           | (exfalso
              injection hSource with hSA hSL hSR
              try rw [hSA] at hTarget
              try rw [hSL] at hTarget
              try rw [hSR] at hTarget
              first
                | exact absurd hTarget (seq_ne_right _ _ _)
                | exact absurd hTarget.symm (seq_ne_right _ _ _))
           | (obtain rfl := bareMessage_of_message_label hLabel
              first
                | rfl
                | (subst hTarget; rfl)
                | (injection hSource; subst_vars; rfl))
           | (refine absurd hSource ?_; simp; done)
           | (refine absurd hLabel ?_; simp; done)
           | (refine absurd hTarget ?_; simp; done)
           | (injection hSource; subst_vars; contradiction)
           | (injection hSource; subst_vars; simp_all; done)
           | (injection hSource with hAlpha hLeftEq hRightEq
              subst hAlpha
              subst hLeftEq
              subst hRightEq
              have hWFLeft : left.AlphabetWellFormed := by
                simp only [PactType.AlphabetWellFormed] at hWF
                exact hWF.2.2.2.1
              have hLinLeft : left.SameCycleMessageLinear := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.1
              have hMsgLeft : left.ParallelMessageOwnership := by
                simp only [PactType.ParallelMessageOwnership] at hMsg
                exact hMsg.1
              have hProgLeft : left.ParallelProgressOwnership := by
                simp only [PactType.ParallelProgressOwnership] at hProg
                exact hProg.1
              have hFairLeft : left.ParallelFairChoiceOwnership := by
                simp only [PactType.ParallelFairChoiceOwnership] at hFair
                exact hFair.1
              have hScopLeft : left.InterfaceScoped := by
                simp only [PactType.InterfaceScoped] at hScop
                tauto
              have key : ∀ {lt : PactType} {c f : Finset BareMessage},
                  TypeOffers e₂ left l₂ lt c f → left'.shape = lt.shape →
                  hideTypeOffers H current = hideTypeOffers H c := by
                intro lt c f hOff hSh
                exact (ih hWFLeft hLinLeft hMsgLeft hProgLeft hFairLeft hScopLeft H hOff hAgree rfl hLabel).1 hSh
              first
                | (refine key (by assumption) ?_
                   simp only [PactType.shape, PactShape.seq.injEq] at hShape
                   exact hShape.1)
                | (injection hTarget with _ hChildTarget _
                   subst hChildTarget
                   rw [hideTypeOffers_sdiff, hideTypeOffers_sdiff,
                     key (by assumption) rfl])
                | (injection hTarget with _ hChildTarget _
                   subst hChildTarget
                   rw [key (by assumption) rfl]))
           | skip
   | seq_fuse env alphabet skipAlphabet left right label current childFuture
       hChild hNotTock ih =>
       intro hWF hLin hMsg hProg hFair hScop H e₂ s₂ l₂ t₂ c₂ f₂ h₂ hAgree hSource hLabel
       cases h₂ <;>
         (try (first
                 | (exfalso; cases hSource; done)
                 | (injection hSource; subst_vars; contradiction)
                 | (refine absurd hLabel ?_; simp; done))) <;>
         (try refine ⟨fun hShape => ?_, fun hTarget => ?_⟩) <;>
         (try (have hShape := congrArg PactType.shape hTarget)) <;>
         first
           | rfl
           | (subst hTarget; rfl)
           | (injection hSource; subst_vars; rfl)
           | exact absurd hTarget (seq_ne_right _ _ _)
           | exact absurd hTarget.symm (seq_ne_right _ _ _)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget) (by assumption)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget.symm) (by assumption)
           | (exfalso
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              try clear hTarget
              injection hSource
              subst_vars
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              injection hSource with _ hElseEq hBranchEq
              try rw [hElseEq] at hTarget
              try rw [hBranchEq] at hTarget
              first
                | exact absurd hTarget (Ne.symm (xoffer_ne_else _ _ _))
                | exact absurd hTarget (xoffer_ne_else _ _ _)
                | exact absurd hTarget (Ne.symm (offer_ne_else _ _ _))
                | exact absurd hTarget (offer_ne_else _ _ _))
           | (exfalso
              injection hSource with hSA hSL hSR
              try rw [hSA] at hTarget
              try rw [hSL] at hTarget
              try rw [hSR] at hTarget
              first
                | exact absurd hTarget (seq_ne_right _ _ _)
                | exact absurd hTarget.symm (seq_ne_right _ _ _))
           | (obtain rfl := bareMessage_of_message_label hLabel
              first
                | rfl
                | (subst hTarget; rfl)
                | (injection hSource; subst_vars; rfl))
           | (refine absurd hSource ?_; simp; done)
           | (refine absurd hLabel ?_; simp; done)
           | (refine absurd hTarget ?_; simp; done)
           | (injection hSource; subst_vars; contradiction)
           | (injection hSource; subst_vars; simp_all; done)
           | (injection hSource with hAlpha hLeftEq hRightEq
              subst hAlpha
              subst hLeftEq
              subst hRightEq
              have hWFLeft : left.AlphabetWellFormed := by
                simp only [PactType.AlphabetWellFormed] at hWF
                exact hWF.2.2.2.1
              have hLinLeft : left.SameCycleMessageLinear := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.1
              have hMsgLeft : left.ParallelMessageOwnership := by
                simp only [PactType.ParallelMessageOwnership] at hMsg
                exact hMsg.1
              have hProgLeft : left.ParallelProgressOwnership := by
                simp only [PactType.ParallelProgressOwnership] at hProg
                exact hProg.1
              have hFairLeft : left.ParallelFairChoiceOwnership := by
                simp only [PactType.ParallelFairChoiceOwnership] at hFair
                exact hFair.1
              have hScopLeft : left.InterfaceScoped := by
                simp only [PactType.InterfaceScoped] at hScop
                tauto
              have key : ∀ {beta : PactTypeAlphabet} {c f : Finset BareMessage},
                  TypeOffers e₂ left l₂ (PactType.skip beta) c f →
                  hideTypeOffers H current = hideTypeOffers H c := by
                intro beta c f hOff
                exact (ih hWFLeft hLinLeft hMsgLeft hProgLeft hFairLeft hScopLeft H hOff hAgree rfl hLabel).1
                  (by simp [PactType.shape])
              first
                | exact key (by assumption)
                | (rw [hideTypeOffers_sdiff, hideTypeOffers_sdiff,
                     key (by assumption)])
                | rw [key (by assumption)])
           | skip
   | seq_fuse_tock env alphabet skipAlphabet left right current childFuture
       hChild ih =>
       intro hWF hLin hMsg hProg hFair hScop H e₂ s₂ l₂ t₂ c₂ f₂ h₂ hAgree hSource hLabel
       cases h₂ <;>
         (try (first
                 | (exfalso; cases hSource; done)
                 | (injection hSource; subst_vars; contradiction)
                 | (refine absurd hLabel ?_; simp; done))) <;>
         (try refine ⟨fun hShape => ?_, fun hTarget => ?_⟩) <;>
         (try (have hShape := congrArg PactType.shape hTarget)) <;>
         first
           | rfl
           | (subst hTarget; rfl)
           | (injection hSource; subst_vars; rfl)
           | exact absurd hTarget (seq_ne_right _ _ _)
           | exact absurd hTarget.symm (seq_ne_right _ _ _)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget) (by assumption)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget.symm) (by assumption)
           | (exfalso
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              try clear hTarget
              injection hSource
              subst_vars
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              injection hSource with _ hElseEq hBranchEq
              try rw [hElseEq] at hTarget
              try rw [hBranchEq] at hTarget
              first
                | exact absurd hTarget (Ne.symm (xoffer_ne_else _ _ _))
                | exact absurd hTarget (xoffer_ne_else _ _ _)
                | exact absurd hTarget (Ne.symm (offer_ne_else _ _ _))
                | exact absurd hTarget (offer_ne_else _ _ _))
           | (exfalso
              injection hSource with hSA hSL hSR
              try rw [hSA] at hTarget
              try rw [hSL] at hTarget
              try rw [hSR] at hTarget
              first
                | exact absurd hTarget (seq_ne_right _ _ _)
                | exact absurd hTarget.symm (seq_ne_right _ _ _))
           | (obtain rfl := bareMessage_of_message_label hLabel
              first
                | rfl
                | (subst hTarget; rfl)
                | (injection hSource; subst_vars; rfl))
           | (refine absurd hSource ?_; simp; done)
           | (refine absurd hLabel ?_; simp; done)
           | (refine absurd hTarget ?_; simp; done)
           | (injection hSource; subst_vars; contradiction)
           | (injection hSource; subst_vars; simp_all; done)
           | (injection hSource with hAlpha hLeftEq hRightEq
              subst hAlpha
              subst hLeftEq
              subst hRightEq
              have hWFLeft : left.AlphabetWellFormed := by
                simp only [PactType.AlphabetWellFormed] at hWF
                exact hWF.2.2.2.1
              have hLinLeft : left.SameCycleMessageLinear := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.1
              have hMsgLeft : left.ParallelMessageOwnership := by
                simp only [PactType.ParallelMessageOwnership] at hMsg
                exact hMsg.1
              have hProgLeft : left.ParallelProgressOwnership := by
                simp only [PactType.ParallelProgressOwnership] at hProg
                exact hProg.1
              have hFairLeft : left.ParallelFairChoiceOwnership := by
                simp only [PactType.ParallelFairChoiceOwnership] at hFair
                exact hFair.1
              have hScopLeft : left.InterfaceScoped := by
                simp only [PactType.InterfaceScoped] at hScop
                tauto
              have key : ∀ {beta : PactTypeAlphabet} {c f : Finset BareMessage},
                  TypeOffers e₂ left l₂ (PactType.skip beta) c f →
                  hideTypeOffers H current = hideTypeOffers H c := by
                intro beta c f hOff
                exact (ih hWFLeft hLinLeft hMsgLeft hProgLeft hFairLeft hScopLeft H hOff hAgree rfl hLabel).1
                  (by simp [PactType.shape])
              first
                | exact key (by assumption)
                | (rw [hideTypeOffers_sdiff, hideTypeOffers_sdiff,
                     key (by assumption)])
                | rw [key (by assumption)])
           | skip
   | xoffer_wait env alphabet elseType branches hCond hGate =>
       intro hWF hLin hMsg hProg hFair hScop H e₂ s₂ l₂ t₂ c₂ f₂ h₂ hAgree hSource hLabel
       cases h₂ <;>
         (try (first
                 | (exfalso; cases hSource; done)
                 | (injection hSource; subst_vars; contradiction)
                 | (refine absurd hLabel ?_; simp; done))) <;>
         (try refine ⟨fun hShape => ?_, fun hTarget => ?_⟩) <;>
         (try (have hShape := congrArg PactType.shape hTarget)) <;>
         first
           | rfl
           | (subst hTarget; rfl)
           | (injection hSource; subst_vars; rfl)
           | exact absurd hTarget (seq_ne_right _ _ _)
           | exact absurd hTarget.symm (seq_ne_right _ _ _)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget) (by assumption)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget.symm) (by assumption)
           | (exfalso
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              try clear hTarget
              injection hSource
              subst_vars
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              injection hSource with _ hElseEq hBranchEq
              try rw [hElseEq] at hTarget
              try rw [hBranchEq] at hTarget
              first
                | exact absurd hTarget (Ne.symm (xoffer_ne_else _ _ _))
                | exact absurd hTarget (xoffer_ne_else _ _ _)
                | exact absurd hTarget (Ne.symm (offer_ne_else _ _ _))
                | exact absurd hTarget (offer_ne_else _ _ _))
           | (exfalso
              injection hSource with hSA hSL hSR
              try rw [hSA] at hTarget
              try rw [hSL] at hTarget
              try rw [hSR] at hTarget
              first
                | exact absurd hTarget (seq_ne_right _ _ _)
                | exact absurd hTarget.symm (seq_ne_right _ _ _))
           | (obtain rfl := bareMessage_of_message_label hLabel
              first
                | rfl
                | (subst hTarget; rfl)
                | (injection hSource; subst_vars; rfl))
           | (refine absurd hSource ?_; simp; done)
           | (refine absurd hLabel ?_; simp; done)
           | (refine absurd hTarget ?_; simp; done)
           | (injection hSource; subst_vars; contradiction)
           | (injection hSource; subst_vars; simp_all; done)
           | (injection hSource with hAlpha hElse hBranches
              subst hAlpha
              subst hElse
              subst hBranches
              first
                | exact typeWaitingOffers_agree_outside hAgree.future _
                | rw [hideTypeOffers_sdiff, hideTypeOffers_sdiff,
                    typeWaitingOffers_agree_outside hAgree.future branches])
           | skip
   | offer_some env alphabet elseType branches enabled hCond hGate =>
       intro hWF hLin hMsg hProg hFair hScop H e₂ s₂ l₂ t₂ c₂ f₂ h₂ hAgree hSource hLabel
       cases h₂ <;>
         (try (first
                 | (exfalso; cases hSource; done)
                 | (injection hSource; subst_vars; contradiction)
                 | (refine absurd hLabel ?_; simp; done))) <;>
         (try refine ⟨fun hShape => ?_, fun hTarget => ?_⟩) <;>
         (try (have hShape := congrArg PactType.shape hTarget)) <;>
         first
           | rfl
           | (subst hTarget; rfl)
           | (injection hSource; subst_vars; rfl)
           | exact absurd hTarget (seq_ne_right _ _ _)
           | exact absurd hTarget.symm (seq_ne_right _ _ _)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget) (by assumption)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget.symm) (by assumption)
           | (exfalso
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              try clear hTarget
              injection hSource
              subst_vars
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              injection hSource with _ hElseEq hBranchEq
              try rw [hElseEq] at hTarget
              try rw [hBranchEq] at hTarget
              first
                | exact absurd hTarget (Ne.symm (xoffer_ne_else _ _ _))
                | exact absurd hTarget (xoffer_ne_else _ _ _)
                | exact absurd hTarget (Ne.symm (offer_ne_else _ _ _))
                | exact absurd hTarget (offer_ne_else _ _ _))
           | (exfalso
              injection hSource with hSA hSL hSR
              try rw [hSA] at hTarget
              try rw [hSL] at hTarget
              try rw [hSR] at hTarget
              first
                | exact absurd hTarget (seq_ne_right _ _ _)
                | exact absurd hTarget.symm (seq_ne_right _ _ _))
           | (obtain rfl := bareMessage_of_message_label hLabel
              first
                | rfl
                | (subst hTarget; rfl)
                | (injection hSource; subst_vars; rfl))
           | (refine absurd hSource ?_; simp; done)
           | (refine absurd hLabel ?_; simp; done)
           | (refine absurd hTarget ?_; simp; done)
           | (injection hSource; subst_vars; contradiction)
           | (injection hSource; subst_vars; simp_all; done)
           | (injection hSource with hAlpha hElse hBranches
              subst hAlpha
              subst hElse
              subst hBranches
              exfalso
              have hNonempty : branches ≠ [] := branches_ne_nil_of_someEnabled hCond
              have hLinBr : ∀ b ∈ branches,
                  b.1.1 ∉ PactType.PrefixMessageIds elseType := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.2.2
              cases hCons : branches with
              | nil => exact hNonempty hCons
              | cons b r =>
                  subst hCons
                  try simp only [PactType.shape] at hShape
                  first
                    | exact absurd hShape
                        (shape_parallelTypeBranchesSelecting_ne_elseType hLinBr hNonempty)
                    | exact absurd hShape.symm
                        (shape_parallelTypeBranchesSelecting_ne_elseType hLinBr hNonempty)
                    | exact shape_parallelTypeBranchesSelecting_ne_offer _ _ b r _ _ hShape
                    | exact shape_parallelTypeBranchesSelecting_ne_offer _ _ b r _ _ hShape.symm)
           | skip
   | offer_else env alphabet elseType branches hCond hGate =>
       intro hWF hLin hMsg hProg hFair hScop H e₂ s₂ l₂ t₂ c₂ f₂ h₂ hAgree hSource hLabel
       cases h₂ <;>
         (try (first
                 | (exfalso; cases hSource; done)
                 | (injection hSource; subst_vars; contradiction)
                 | (refine absurd hLabel ?_; simp; done))) <;>
         (try refine ⟨fun hShape => ?_, fun hTarget => ?_⟩) <;>
         (try (have hShape := congrArg PactType.shape hTarget)) <;>
         first
           | rfl
           | (subst hTarget; rfl)
           | (injection hSource; subst_vars; rfl)
           | exact absurd hTarget (seq_ne_right _ _ _)
           | exact absurd hTarget.symm (seq_ne_right _ _ _)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget) (by assumption)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget.symm) (by assumption)
           | (exfalso
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              try clear hTarget
              injection hSource
              subst_vars
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              injection hSource with _ hElseEq hBranchEq
              try rw [hElseEq] at hTarget
              try rw [hBranchEq] at hTarget
              first
                | exact absurd hTarget (Ne.symm (xoffer_ne_else _ _ _))
                | exact absurd hTarget (xoffer_ne_else _ _ _)
                | exact absurd hTarget (Ne.symm (offer_ne_else _ _ _))
                | exact absurd hTarget (offer_ne_else _ _ _))
           | (exfalso
              injection hSource with hSA hSL hSR
              try rw [hSA] at hTarget
              try rw [hSL] at hTarget
              try rw [hSR] at hTarget
              first
                | exact absurd hTarget (seq_ne_right _ _ _)
                | exact absurd hTarget.symm (seq_ne_right _ _ _))
           | (obtain rfl := bareMessage_of_message_label hLabel
              first
                | rfl
                | (subst hTarget; rfl)
                | (injection hSource; subst_vars; rfl))
           | (refine absurd hSource ?_; simp; done)
           | (refine absurd hLabel ?_; simp; done)
           | (refine absurd hTarget ?_; simp; done)
           | (injection hSource; subst_vars; contradiction)
           | (injection hSource; subst_vars; simp_all; done)
           | (injection hSource with hAlpha hElse hBranches
              subst hAlpha
              subst hElse
              subst hBranches
              exfalso
              have hNonempty : branches ≠ [] := branches_ne_nil_of_someEnabled (by assumption)
              have hLinBr : ∀ b ∈ branches,
                  b.1.1 ∉ PactType.PrefixMessageIds elseType := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.2.2
              cases hCons : branches with
              | nil => exact hNonempty hCons
              | cons b r =>
                  subst hCons
                  try simp only [PactType.shape] at hShape
                  first
                    | exact absurd hShape
                        (shape_parallelTypeBranchesSelecting_ne_elseType hLinBr hNonempty)
                    | exact absurd hShape.symm
                        (shape_parallelTypeBranchesSelecting_ne_elseType hLinBr hNonempty)
                    | exact shape_parallelTypeBranchesSelecting_ne_offer _ _ b r _ _ hShape
                    | exact shape_parallelTypeBranchesSelecting_ne_offer _ _ b r _ _ hShape.symm)
           | skip
   | offer_wait env alphabet elseType branches hCond hGate =>
       intro hWF hLin hMsg hProg hFair hScop H e₂ s₂ l₂ t₂ c₂ f₂ h₂ hAgree hSource hLabel
       cases h₂ <;>
         (try (first
                 | (exfalso; cases hSource; done)
                 | (injection hSource; subst_vars; contradiction)
                 | (refine absurd hLabel ?_; simp; done))) <;>
         (try refine ⟨fun hShape => ?_, fun hTarget => ?_⟩) <;>
         (try (have hShape := congrArg PactType.shape hTarget)) <;>
         first
           | rfl
           | (subst hTarget; rfl)
           | (injection hSource; subst_vars; rfl)
           | exact absurd hTarget (seq_ne_right _ _ _)
           | exact absurd hTarget.symm (seq_ne_right _ _ _)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget) (by assumption)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget.symm) (by assumption)
           | (exfalso
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              try clear hTarget
              injection hSource
              subst_vars
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              injection hSource with _ hElseEq hBranchEq
              try rw [hElseEq] at hTarget
              try rw [hBranchEq] at hTarget
              first
                | exact absurd hTarget (Ne.symm (xoffer_ne_else _ _ _))
                | exact absurd hTarget (xoffer_ne_else _ _ _)
                | exact absurd hTarget (Ne.symm (offer_ne_else _ _ _))
                | exact absurd hTarget (offer_ne_else _ _ _))
           | (exfalso
              injection hSource with hSA hSL hSR
              try rw [hSA] at hTarget
              try rw [hSL] at hTarget
              try rw [hSR] at hTarget
              first
                | exact absurd hTarget (seq_ne_right _ _ _)
                | exact absurd hTarget.symm (seq_ne_right _ _ _))
           | (obtain rfl := bareMessage_of_message_label hLabel
              first
                | rfl
                | (subst hTarget; rfl)
                | (injection hSource; subst_vars; rfl))
           | (refine absurd hSource ?_; simp; done)
           | (refine absurd hLabel ?_; simp; done)
           | (refine absurd hTarget ?_; simp; done)
           | (injection hSource; subst_vars; contradiction)
           | (injection hSource; subst_vars; simp_all; done)
           | (injection hSource with hAlpha hElse hBranches
              subst hAlpha
              subst hElse
              subst hBranches
              exfalso
              have hNonempty : branches ≠ [] := branches_ne_nil_of_someEnabled (by assumption)
              have hLinBr : ∀ b ∈ branches,
                  b.1.1 ∉ PactType.PrefixMessageIds elseType := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.2.2
              cases hCons : branches with
              | nil => exact hNonempty hCons
              | cons b r =>
                  subst hCons
                  try simp only [PactType.shape] at hShape
                  first
                    | exact absurd hShape
                        (shape_parallelTypeBranchesSelecting_ne_elseType hLinBr hNonempty)
                    | exact absurd hShape.symm
                        (shape_parallelTypeBranchesSelecting_ne_elseType hLinBr hNonempty)
                    | exact shape_parallelTypeBranchesSelecting_ne_offer _ _ b r _ _ hShape
                    | exact shape_parallelTypeBranchesSelecting_ne_offer _ _ b r _ _ hShape.symm)
           | skip
   | left_complete outer rightEnv interface alphabet left right right' rightLabel
       rightCurrent rightFuture hLeftSkip hRightNotSkip hChild hResNotSkip hRestC
       hRestF hLoc hOuterWF hNotTock ih =>
       intro hWF hLin hMsg hProg hFair hScop H e₂ s₂ l₂ t₂ c₂ f₂ h₂ hAgree hSource hLabel
       cases h₂ <;>
         (try (first
                 | (exfalso; cases hSource; done)
                 | (injection hSource; subst_vars; contradiction)
                 | (refine absurd hLabel ?_; simp; done))) <;>
         (try refine ⟨fun hShape => ?_, fun hTarget => ?_⟩) <;>
         (try (have hShape := congrArg PactType.shape hTarget)) <;>
         first
           | rfl
           | (subst hTarget; rfl)
           | (injection hSource; subst_vars; rfl)
           | exact absurd hTarget (seq_ne_right _ _ _)
           | exact absurd hTarget.symm (seq_ne_right _ _ _)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget) (by assumption)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget.symm) (by assumption)
           | (exfalso
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              try clear hTarget
              injection hSource
              subst_vars
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              injection hSource with _ hElseEq hBranchEq
              try rw [hElseEq] at hTarget
              try rw [hBranchEq] at hTarget
              first
                | exact absurd hTarget (Ne.symm (xoffer_ne_else _ _ _))
                | exact absurd hTarget (xoffer_ne_else _ _ _)
                | exact absurd hTarget (Ne.symm (offer_ne_else _ _ _))
                | exact absurd hTarget (offer_ne_else _ _ _))
           | (exfalso
              injection hSource with hSA hSL hSR
              try rw [hSA] at hTarget
              try rw [hSL] at hTarget
              try rw [hSR] at hTarget
              first
                | exact absurd hTarget (seq_ne_right _ _ _)
                | exact absurd hTarget.symm (seq_ne_right _ _ _))
           | (obtain rfl := bareMessage_of_message_label hLabel
              first
                | rfl
                | (subst hTarget; rfl)
                | (injection hSource; subst_vars; rfl))
           | (refine absurd hSource ?_; simp; done)
           | (refine absurd hLabel ?_; simp; done)
           | (refine absurd hTarget ?_; simp; done)
           | (injection hSource; subst_vars; contradiction)
           | (injection hSource; subst_vars; simp_all; done)
           | (injection hSource with hAlpha hLeftEq hRightEq hIfaceEq
              subst hAlpha
              subst hLeftEq
              subst hRightEq
              subst hIfaceEq
              have hWFRight : right.AlphabetWellFormed := by
                simp only [PactType.AlphabetWellFormed] at hWF
                exact hWF.2.2.2
              have hLinRight : right.SameCycleMessageLinear := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.2
              have hMsgRight : right.ParallelMessageOwnership := by
                simp only [PactType.ParallelMessageOwnership] at hMsg
                exact hMsg.2.2
              have hProgRight : right.ParallelProgressOwnership := by
                simp only [PactType.ParallelProgressOwnership] at hProg
                exact hProg.2.2
              have hFairRight : right.ParallelFairChoiceOwnership := by
                simp only [PactType.ParallelFairChoiceOwnership] at hFair
                exact hFair.2.2
              have hScopRight : right.InterfaceScoped := by
                simp only [PactType.InterfaceScoped] at hScop
                tauto
              have key : ∀ {senv : TypeEnvironment} {st : PactType}
                  {sc sf : Finset BareMessage},
                  TypeOffers senv right l₂ st sc sf →
                  LocalTypeOfferEnvironment e₂ interface right senv ∅ ∅ senv →
                  right'.shape = st.shape →
                  hideTypeOffers H (hideTypeOffers interface rightCurrent) =
                    hideTypeOffers H (hideTypeOffers interface sc) := by
                intro senv st sc sf hOff hLoc₂ hSh
                rw [hideTypeOffers_hide_union, hideTypeOffers_hide_union]
                exact (ih hWFRight hLinRight hMsgRight hProgRight hFairRight hScopRight (H ∪ interface) hOff
                  (localTypeOfferEnvironment_agree_of_outer_agree hAgree hLoc hLoc₂)
                  rfl hLabel).1 hSh
              first
                | (exact key (by assumption) (by assumption)
                     (by simpa only [PactType.shape_reannotate] using hShape))
                | (rw [hTarget, hideTypeOffers_sdiff, hideTypeOffers_sdiff]
                   rw [key (by assumption) (by assumption)
                     (by simpa only [PactType.shape_reannotate] using
                       congrArg PactType.shape hTarget)])
                | (rw [key (by assumption) (by assumption)
                     (by simpa only [PactType.shape_reannotate] using
                       congrArg PactType.shape hTarget)]))
           | skip
   | left_complete_tock outer rightEnv interface alphabet left right right' rightLabel
       rightCurrent rightFuture hLeftSkip hRightNotSkip hChild hResNotSkip hRestC
       hRestF hLoc hOuterWF hIsTock ih =>
       intro hWF hLin hMsg hProg hFair hScop H e₂ s₂ l₂ t₂ c₂ f₂ h₂ hAgree hSource hLabel
       cases h₂ <;>
         (try (first
                 | (exfalso; cases hSource; done)
                 | (injection hSource; subst_vars; contradiction)
                 | (refine absurd hLabel ?_; simp; done))) <;>
         (try refine ⟨fun hShape => ?_, fun hTarget => ?_⟩) <;>
         (try (have hShape := congrArg PactType.shape hTarget)) <;>
         first
           | rfl
           | (subst hTarget; rfl)
           | (injection hSource; subst_vars; rfl)
           | exact absurd hTarget (seq_ne_right _ _ _)
           | exact absurd hTarget.symm (seq_ne_right _ _ _)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget) (by assumption)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget.symm) (by assumption)
           | (exfalso
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              try clear hTarget
              injection hSource
              subst_vars
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              injection hSource with _ hElseEq hBranchEq
              try rw [hElseEq] at hTarget
              try rw [hBranchEq] at hTarget
              first
                | exact absurd hTarget (Ne.symm (xoffer_ne_else _ _ _))
                | exact absurd hTarget (xoffer_ne_else _ _ _)
                | exact absurd hTarget (Ne.symm (offer_ne_else _ _ _))
                | exact absurd hTarget (offer_ne_else _ _ _))
           | (exfalso
              injection hSource with hSA hSL hSR
              try rw [hSA] at hTarget
              try rw [hSL] at hTarget
              try rw [hSR] at hTarget
              first
                | exact absurd hTarget (seq_ne_right _ _ _)
                | exact absurd hTarget.symm (seq_ne_right _ _ _))
           | (obtain rfl := bareMessage_of_message_label hLabel
              first
                | rfl
                | (subst hTarget; rfl)
                | (injection hSource; subst_vars; rfl))
           | (refine absurd hSource ?_; simp; done)
           | (refine absurd hLabel ?_; simp; done)
           | (refine absurd hTarget ?_; simp; done)
           | (injection hSource; subst_vars; contradiction)
           | (injection hSource; subst_vars; simp_all; done)
           | (injection hSource with hAlpha hLeftEq hRightEq hIfaceEq
              subst hAlpha
              subst hLeftEq
              subst hRightEq
              subst hIfaceEq
              have hWFRight : right.AlphabetWellFormed := by
                simp only [PactType.AlphabetWellFormed] at hWF
                exact hWF.2.2.2
              have hLinRight : right.SameCycleMessageLinear := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.2
              have hMsgRight : right.ParallelMessageOwnership := by
                simp only [PactType.ParallelMessageOwnership] at hMsg
                exact hMsg.2.2
              have hProgRight : right.ParallelProgressOwnership := by
                simp only [PactType.ParallelProgressOwnership] at hProg
                exact hProg.2.2
              have hFairRight : right.ParallelFairChoiceOwnership := by
                simp only [PactType.ParallelFairChoiceOwnership] at hFair
                exact hFair.2.2
              have hScopRight : right.InterfaceScoped := by
                simp only [PactType.InterfaceScoped] at hScop
                tauto
              have key : ∀ {senv : TypeEnvironment} {st : PactType}
                  {sc sf : Finset BareMessage},
                  TypeOffers senv right l₂ st sc sf →
                  LocalTypeOfferEnvironment e₂ interface right senv ∅ ∅ senv →
                  right'.shape = st.shape →
                  hideTypeOffers H (hideTypeOffers interface rightCurrent) =
                    hideTypeOffers H (hideTypeOffers interface sc) := by
                intro senv st sc sf hOff hLoc₂ hSh
                rw [hideTypeOffers_hide_union, hideTypeOffers_hide_union]
                exact (ih hWFRight hLinRight hMsgRight hProgRight hFairRight hScopRight (H ∪ interface) hOff
                  (localTypeOfferEnvironment_agree_of_outer_agree hAgree hLoc hLoc₂)
                  rfl hLabel).1 hSh
              first
                | (exact key (by assumption) (by assumption)
                     (by simpa only [PactType.shape_reannotate] using hShape))
                | (rw [hTarget, hideTypeOffers_sdiff, hideTypeOffers_sdiff]
                   rw [key (by assumption) (by assumption)
                     (by simpa only [PactType.shape_reannotate] using
                       congrArg PactType.shape hTarget)])
                | (rw [key (by assumption) (by assumption)
                     (by simpa only [PactType.shape_reannotate] using
                       congrArg PactType.shape hTarget)]))
           | skip
   | right_complete outer leftEnv interface alphabet left left' right leftLabel
       leftCurrent leftFuture hRightSkip hLeftNotSkip hChild hResNotSkip hRestC
       hRestF hLoc hOuterWF hNotTock ih =>
       intro hWF hLin hMsg hProg hFair hScop H e₂ s₂ l₂ t₂ c₂ f₂ h₂ hAgree hSource hLabel
       cases h₂ <;>
         (try (first
                 | (exfalso; cases hSource; done)
                 | (injection hSource; subst_vars; contradiction)
                 | (refine absurd hLabel ?_; simp; done))) <;>
         (try refine ⟨fun hShape => ?_, fun hTarget => ?_⟩) <;>
         (try (have hShape := congrArg PactType.shape hTarget)) <;>
         first
           | rfl
           | (subst hTarget; rfl)
           | (injection hSource; subst_vars; rfl)
           | exact absurd hTarget (seq_ne_right _ _ _)
           | exact absurd hTarget.symm (seq_ne_right _ _ _)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget) (by assumption)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget.symm) (by assumption)
           | (exfalso
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              try clear hTarget
              injection hSource
              subst_vars
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              injection hSource with _ hElseEq hBranchEq
              try rw [hElseEq] at hTarget
              try rw [hBranchEq] at hTarget
              first
                | exact absurd hTarget (Ne.symm (xoffer_ne_else _ _ _))
                | exact absurd hTarget (xoffer_ne_else _ _ _)
                | exact absurd hTarget (Ne.symm (offer_ne_else _ _ _))
                | exact absurd hTarget (offer_ne_else _ _ _))
           | (exfalso
              injection hSource with hSA hSL hSR
              try rw [hSA] at hTarget
              try rw [hSL] at hTarget
              try rw [hSR] at hTarget
              first
                | exact absurd hTarget (seq_ne_right _ _ _)
                | exact absurd hTarget.symm (seq_ne_right _ _ _))
           | (obtain rfl := bareMessage_of_message_label hLabel
              first
                | rfl
                | (subst hTarget; rfl)
                | (injection hSource; subst_vars; rfl))
           | (refine absurd hSource ?_; simp; done)
           | (refine absurd hLabel ?_; simp; done)
           | (refine absurd hTarget ?_; simp; done)
           | (injection hSource; subst_vars; contradiction)
           | (injection hSource; subst_vars; simp_all; done)
           | (injection hSource with hAlpha hLeftEq hRightEq hIfaceEq
              subst hAlpha
              subst hLeftEq
              subst hRightEq
              subst hIfaceEq
              have hWFLeft : left.AlphabetWellFormed := by
                simp only [PactType.AlphabetWellFormed] at hWF
                exact hWF.2.2.1
              have hLinLeft : left.SameCycleMessageLinear := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.1
              have hMsgLeft : left.ParallelMessageOwnership := by
                simp only [PactType.ParallelMessageOwnership] at hMsg
                exact hMsg.2.1
              have hProgLeft : left.ParallelProgressOwnership := by
                simp only [PactType.ParallelProgressOwnership] at hProg
                exact hProg.2.1
              have hFairLeft : left.ParallelFairChoiceOwnership := by
                simp only [PactType.ParallelFairChoiceOwnership] at hFair
                exact hFair.2.1
              have hScopLeft : left.InterfaceScoped := by
                simp only [PactType.InterfaceScoped] at hScop
                tauto
              have key : ∀ {senv : TypeEnvironment} {st : PactType}
                  {sc sf : Finset BareMessage},
                  TypeOffers senv left l₂ st sc sf →
                  LocalTypeOfferEnvironment e₂ interface left senv ∅ ∅ senv →
                  left'.shape = st.shape →
                  hideTypeOffers H (hideTypeOffers interface leftCurrent) =
                    hideTypeOffers H (hideTypeOffers interface sc) := by
                intro senv st sc sf hOff hLoc₂ hSh
                rw [hideTypeOffers_hide_union, hideTypeOffers_hide_union]
                exact (ih hWFLeft hLinLeft hMsgLeft hProgLeft hFairLeft hScopLeft (H ∪ interface) hOff
                  (localTypeOfferEnvironment_agree_of_outer_agree hAgree hLoc hLoc₂)
                  rfl hLabel).1 hSh
              first
                | (exact key (by assumption) (by assumption)
                     (by simpa only [PactType.shape_reannotate] using hShape))
                | (rw [hTarget, hideTypeOffers_sdiff, hideTypeOffers_sdiff]
                   rw [key (by assumption) (by assumption)
                     (by simpa only [PactType.shape_reannotate] using
                       congrArg PactType.shape hTarget)])
                | (rw [key (by assumption) (by assumption)
                     (by simpa only [PactType.shape_reannotate] using
                       congrArg PactType.shape hTarget)]))
           | skip
   | right_complete_tock outer leftEnv interface alphabet left left' right leftLabel
       leftCurrent leftFuture hRightSkip hLeftNotSkip hChild hResNotSkip hRestC
       hRestF hLoc hOuterWF hIsTock ih =>
       intro hWF hLin hMsg hProg hFair hScop H e₂ s₂ l₂ t₂ c₂ f₂ h₂ hAgree hSource hLabel
       cases h₂ <;>
         (try (first
                 | (exfalso; cases hSource; done)
                 | (injection hSource; subst_vars; contradiction)
                 | (refine absurd hLabel ?_; simp; done))) <;>
         (try refine ⟨fun hShape => ?_, fun hTarget => ?_⟩) <;>
         (try (have hShape := congrArg PactType.shape hTarget)) <;>
         first
           | rfl
           | (subst hTarget; rfl)
           | (injection hSource; subst_vars; rfl)
           | exact absurd hTarget (seq_ne_right _ _ _)
           | exact absurd hTarget.symm (seq_ne_right _ _ _)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget) (by assumption)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget.symm) (by assumption)
           | (exfalso
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              try clear hTarget
              injection hSource
              subst_vars
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              injection hSource with _ hElseEq hBranchEq
              try rw [hElseEq] at hTarget
              try rw [hBranchEq] at hTarget
              first
                | exact absurd hTarget (Ne.symm (xoffer_ne_else _ _ _))
                | exact absurd hTarget (xoffer_ne_else _ _ _)
                | exact absurd hTarget (Ne.symm (offer_ne_else _ _ _))
                | exact absurd hTarget (offer_ne_else _ _ _))
           | (exfalso
              injection hSource with hSA hSL hSR
              try rw [hSA] at hTarget
              try rw [hSL] at hTarget
              try rw [hSR] at hTarget
              first
                | exact absurd hTarget (seq_ne_right _ _ _)
                | exact absurd hTarget.symm (seq_ne_right _ _ _))
           | (obtain rfl := bareMessage_of_message_label hLabel
              first
                | rfl
                | (subst hTarget; rfl)
                | (injection hSource; subst_vars; rfl))
           | (refine absurd hSource ?_; simp; done)
           | (refine absurd hLabel ?_; simp; done)
           | (refine absurd hTarget ?_; simp; done)
           | (injection hSource; subst_vars; contradiction)
           | (injection hSource; subst_vars; simp_all; done)
           | (injection hSource with hAlpha hLeftEq hRightEq hIfaceEq
              subst hAlpha
              subst hLeftEq
              subst hRightEq
              subst hIfaceEq
              have hWFLeft : left.AlphabetWellFormed := by
                simp only [PactType.AlphabetWellFormed] at hWF
                exact hWF.2.2.1
              have hLinLeft : left.SameCycleMessageLinear := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.1
              have hMsgLeft : left.ParallelMessageOwnership := by
                simp only [PactType.ParallelMessageOwnership] at hMsg
                exact hMsg.2.1
              have hProgLeft : left.ParallelProgressOwnership := by
                simp only [PactType.ParallelProgressOwnership] at hProg
                exact hProg.2.1
              have hFairLeft : left.ParallelFairChoiceOwnership := by
                simp only [PactType.ParallelFairChoiceOwnership] at hFair
                exact hFair.2.1
              have hScopLeft : left.InterfaceScoped := by
                simp only [PactType.InterfaceScoped] at hScop
                tauto
              have key : ∀ {senv : TypeEnvironment} {st : PactType}
                  {sc sf : Finset BareMessage},
                  TypeOffers senv left l₂ st sc sf →
                  LocalTypeOfferEnvironment e₂ interface left senv ∅ ∅ senv →
                  left'.shape = st.shape →
                  hideTypeOffers H (hideTypeOffers interface leftCurrent) =
                    hideTypeOffers H (hideTypeOffers interface sc) := by
                intro senv st sc sf hOff hLoc₂ hSh
                rw [hideTypeOffers_hide_union, hideTypeOffers_hide_union]
                exact (ih hWFLeft hLinLeft hMsgLeft hProgLeft hFairLeft hScopLeft (H ∪ interface) hOff
                  (localTypeOfferEnvironment_agree_of_outer_agree hAgree hLoc hLoc₂)
                  rfl hLabel).1 hSh
              first
                | (exact key (by assumption) (by assumption)
                     (by simpa only [PactType.shape_reannotate] using hShape))
                | (rw [hTarget, hideTypeOffers_sdiff, hideTypeOffers_sdiff]
                   rw [key (by assumption) (by assumption)
                     (by simpa only [PactType.shape_reannotate] using
                       congrArg PactType.shape hTarget)])
                | (rw [key (by assumption) (by assumption)
                     (by simpa only [PactType.shape_reannotate] using
                       congrArg PactType.shape hTarget)]))
           | skip
   | par outer leftEnv rightEnv interface alphabet left left' right right' leftLabel
       rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftNotSkip
       hRightNotSkip hLeftChild hRightChild hNotBothSkip hLeftLoc hRightLoc
       hCond ihLeft ihRight =>
       intro hWF hLin hMsg hProg hFair hScop H e₂ s₂ l₂ t₂ c₂ f₂ h₂ hAgree hSource hLabel
       cases h₂ <;>
         (try (first
                 | (exfalso; cases hSource; done)
                 | (injection hSource; subst_vars; contradiction)
                 | (refine absurd hLabel ?_; simp; done))) <;>
         (try refine ⟨fun hShape => ?_, fun hTarget => ?_⟩) <;>
         (try (have hShape := congrArg PactType.shape hTarget)) <;>
         first
           | rfl
           | (subst hTarget; rfl)
           | (injection hSource; subst_vars; rfl)
           | exact absurd hTarget (seq_ne_right _ _ _)
           | exact absurd hTarget.symm (seq_ne_right _ _ _)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget) (by assumption)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget.symm) (by assumption)
           | (exfalso
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              try clear hTarget
              injection hSource
              subst_vars
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              injection hSource with _ hElseEq hBranchEq
              try rw [hElseEq] at hTarget
              try rw [hBranchEq] at hTarget
              first
                | exact absurd hTarget (Ne.symm (xoffer_ne_else _ _ _))
                | exact absurd hTarget (xoffer_ne_else _ _ _)
                | exact absurd hTarget (Ne.symm (offer_ne_else _ _ _))
                | exact absurd hTarget (offer_ne_else _ _ _))
           | (exfalso
              injection hSource with hSA hSL hSR
              try rw [hSA] at hTarget
              try rw [hSL] at hTarget
              try rw [hSR] at hTarget
              first
                | exact absurd hTarget (seq_ne_right _ _ _)
                | exact absurd hTarget.symm (seq_ne_right _ _ _))
           | (obtain rfl := bareMessage_of_message_label hLabel
              first
                | rfl
                | (subst hTarget; rfl)
                | (injection hSource; subst_vars; rfl))
           | (refine absurd hSource ?_; simp; done)
           | (refine absurd hLabel ?_; simp; done)
           | (refine absurd hTarget ?_; simp; done)
           | (injection hSource; subst_vars; contradiction)
           | (injection hSource; subst_vars; simp_all; done)
           | (injection hSource with hAlpha hLeftEq hRightEq hIfaceEq
              subst hAlpha
              subst hLeftEq
              subst hRightEq
              subst hIfaceEq
              have hWFLeft : left.AlphabetWellFormed := by
                simp only [PactType.AlphabetWellFormed] at hWF
                exact hWF.2.2.1
              have hLinLeft : left.SameCycleMessageLinear := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.1
              have hMsgLeft : left.ParallelMessageOwnership := by
                simp only [PactType.ParallelMessageOwnership] at hMsg
                exact hMsg.2.1
              have hProgLeft : left.ParallelProgressOwnership := by
                simp only [PactType.ParallelProgressOwnership] at hProg
                exact hProg.2.1
              have hFairLeft : left.ParallelFairChoiceOwnership := by
                simp only [PactType.ParallelFairChoiceOwnership] at hFair
                exact hFair.2.1
              have hScopLeft : left.InterfaceScoped := by
                simp only [PactType.InterfaceScoped] at hScop
                tauto
              have hWFRight : right.AlphabetWellFormed := by
                simp only [PactType.AlphabetWellFormed] at hWF
                exact hWF.2.2.2
              have hLinRight : right.SameCycleMessageLinear := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.2
              have hMsgRight : right.ParallelMessageOwnership := by
                simp only [PactType.ParallelMessageOwnership] at hMsg
                exact hMsg.2.2
              have hProgRight : right.ParallelProgressOwnership := by
                simp only [PactType.ParallelProgressOwnership] at hProg
                exact hProg.2.2
              have hFairRight : right.ParallelFairChoiceOwnership := by
                simp only [PactType.ParallelFairChoiceOwnership] at hFair
                exact hFair.2.2
              have hScopRight : right.InterfaceScoped := by
                simp only [PactType.InterfaceScoped] at hScop
                tauto
              have keyC : ∀ {lenv renv : TypeEnvironment} {lt rt : PactType} {ll rl : TypeLabel}
                  {lc lf rc rf : Finset BareMessage},
                  TypeOffers lenv left ll lt lc lf →
                  TypeOffers renv right rl rt rc rf →
                  LocalTypeOfferEnvironment e₂ interface left renv rc rf lenv →
                  LocalTypeOfferEnvironment e₂ interface right lenv lc lf renv →
                  (e₂.WellFormed alphabet ∧ TypeLabel.Sync interface ll rl) →
                  TypeLabel.combine interface leftLabel rightLabel =
                    TypeLabel.combine interface ll rl →
                  PactType.shape left' = PactType.shape lt →
                  PactType.shape right' = PactType.shape rt →
                  hideTypeOffers H (hideTypeOffers interface (leftCurrent ∪ rightCurrent)) =
                    hideTypeOffers H (hideTypeOffers interface (lc ∪ rc)) := by
                intro lenv renv lt rt ll rl lc lf rc rf hL hR hLoc1 hLoc2 hCond₂ hComb hShL hShR
                obtain ⟨hOwnA, hOwnB, hCrossA, hCrossB, hFreshA, hFreshB⟩ :=
                  TypeOffers.par_combine_inj_hypotheses hMsg hWF hProg hFair hScop
                    hLeftChild hRightChild hL hR
                obtain ⟨hLLeq, hRLeq⟩ := TypeLabel.combine_inj hCond.2 hCond₂.2 hOwnA
                  hOwnB hCrossA hCrossB hFreshA hFreshB hComb
                subst hLLeq
                subst hRLeq
                rw [hideTypeOffers_hide_union, hideTypeOffers_hide_union,
                  hideTypeOffers_union, hideTypeOffers_union,
                  (ihLeft hWFLeft hLinLeft hMsgLeft hProgLeft hFairLeft hScopLeft
                    (H ∪ interface) hL
                    (localTypeOfferEnvironment_agree_of_outer_agree hAgree hLeftLoc hLoc1)
                    rfl rfl).1 hShL,
                  (ihRight hWFRight hLinRight hMsgRight hProgRight hFairRight hScopRight
                    (H ∪ interface) hR
                    (localTypeOfferEnvironment_agree_of_outer_agree hAgree hRightLoc hLoc2)
                    rfl rfl).1 hShR]
              first
                | (simp only [PactType.shape, PactShape.par.injEq] at hShape
                   exact keyC (by assumption) (by assumption) (by assumption)
                     (by assumption) (by assumption) hLabel hShape.1 hShape.2.1)
                | (simp only [PactType.shape, PactShape.par.injEq] at hShape
                   have hCur := keyC (by assumption) (by assumption) (by assumption)
                     (by assumption) (by assumption) hLabel hShape.1 hShape.2.1
                   simp only [hLabel, hTarget]
                   try split_ifs with hIfTock
                   all_goals
                     first
                       | rfl
                       | rw [hideTypeOffers_sdiff, hideTypeOffers_sdiff, hCur]))
           | skip
   | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel rightLabel
       leftCurrent leftFuture rightCurrent rightFuture hLeftChild hRightChild
       hLeftLoc hRightLoc hCond hNotTock ihLeft ihRight =>
       intro hWF hLin hMsg hProg hFair hScop H e₂ s₂ l₂ t₂ c₂ f₂ h₂ hAgree hSource hLabel
       cases h₂ <;>
         (try (first
                 | (exfalso; cases hSource; done)
                 | (injection hSource; subst_vars; contradiction)
                 | (refine absurd hLabel ?_; simp; done))) <;>
         (try refine ⟨fun hShape => ?_, fun hTarget => ?_⟩) <;>
         (try (have hShape := congrArg PactType.shape hTarget)) <;>
         first
           | rfl
           | (subst hTarget; rfl)
           | (injection hSource; subst_vars; rfl)
           | exact absurd hTarget (seq_ne_right _ _ _)
           | exact absurd hTarget.symm (seq_ne_right _ _ _)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget) (by assumption)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget.symm) (by assumption)
           | (exfalso
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              try clear hTarget
              injection hSource
              subst_vars
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              injection hSource with _ hElseEq hBranchEq
              try rw [hElseEq] at hTarget
              try rw [hBranchEq] at hTarget
              first
                | exact absurd hTarget (Ne.symm (xoffer_ne_else _ _ _))
                | exact absurd hTarget (xoffer_ne_else _ _ _)
                | exact absurd hTarget (Ne.symm (offer_ne_else _ _ _))
                | exact absurd hTarget (offer_ne_else _ _ _))
           | (exfalso
              injection hSource with hSA hSL hSR
              try rw [hSA] at hTarget
              try rw [hSL] at hTarget
              try rw [hSR] at hTarget
              first
                | exact absurd hTarget (seq_ne_right _ _ _)
                | exact absurd hTarget.symm (seq_ne_right _ _ _))
           | (obtain rfl := bareMessage_of_message_label hLabel
              first
                | rfl
                | (subst hTarget; rfl)
                | (injection hSource; subst_vars; rfl))
           | (refine absurd hSource ?_; simp; done)
           | (refine absurd hLabel ?_; simp; done)
           | (refine absurd hTarget ?_; simp; done)
           | (injection hSource; subst_vars; contradiction)
           | (injection hSource; subst_vars; simp_all; done)
           | (injection hSource with hAlpha hLeftEq hRightEq
              subst hAlpha
              subst hLeftEq
              subst hRightEq
              have hWFLeft : left.AlphabetWellFormed := by
                simp only [PactType.AlphabetWellFormed] at hWF
                exact hWF.2.2.2.1
              have hLinLeft : left.SameCycleMessageLinear := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.1
              have hMsgLeft : left.ParallelMessageOwnership := by
                simp only [PactType.ParallelMessageOwnership] at hMsg
                exact hMsg.1
              have hProgLeft : left.ParallelProgressOwnership := by
                simp only [PactType.ParallelProgressOwnership] at hProg
                exact hProg.1
              have hFairLeft : left.ParallelFairChoiceOwnership := by
                simp only [PactType.ParallelFairChoiceOwnership] at hFair
                exact hFair.1
              have hScopLeft : left.InterfaceScoped := by
                simp only [PactType.InterfaceScoped] at hScop
                tauto
              have key : ∀ {lt : PactType} {c f : Finset BareMessage},
                  TypeOffers e₂ left l₂ lt c f → left'.shape = lt.shape →
                  hideTypeOffers H current = hideTypeOffers H c := by
                intro lt c f hOff hSh
                exact (ih hWFLeft hLinLeft hMsgLeft hProgLeft hFairLeft hScopLeft H hOff hAgree rfl hLabel).1 hSh
              first
                | (refine key (by assumption) ?_
                   simp only [PactType.shape, PactShape.seq.injEq] at hShape
                   exact hShape.1)
                | (injection hTarget with _ hChildTarget _
                   subst hChildTarget
                   rw [hideTypeOffers_sdiff, hideTypeOffers_sdiff,
                     key (by assumption) rfl])
                | (injection hTarget with _ hChildTarget _
                   subst hChildTarget
                   rw [key (by assumption) rfl]))
           | (injection hSource with hAlpha hLeftEq hRightEq hIfaceEq
              subst hAlpha
              subst hLeftEq
              subst hRightEq
              subst hIfaceEq
              have hWFLeft : left.AlphabetWellFormed := by
                simp only [PactType.AlphabetWellFormed] at hWF
                exact hWF.2.2.1
              have hLinLeft : left.SameCycleMessageLinear := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.1
              have hMsgLeft : left.ParallelMessageOwnership := by
                simp only [PactType.ParallelMessageOwnership] at hMsg
                exact hMsg.2.1
              have hProgLeft : left.ParallelProgressOwnership := by
                simp only [PactType.ParallelProgressOwnership] at hProg
                exact hProg.2.1
              have hFairLeft : left.ParallelFairChoiceOwnership := by
                simp only [PactType.ParallelFairChoiceOwnership] at hFair
                exact hFair.2.1
              have hScopLeft : left.InterfaceScoped := by
                simp only [PactType.InterfaceScoped] at hScop
                tauto
              have hWFRight : right.AlphabetWellFormed := by
                simp only [PactType.AlphabetWellFormed] at hWF
                exact hWF.2.2.2
              have hLinRight : right.SameCycleMessageLinear := by
                simp only [PactType.SameCycleMessageLinear] at hLin
                exact hLin.2
              have hMsgRight : right.ParallelMessageOwnership := by
                simp only [PactType.ParallelMessageOwnership] at hMsg
                exact hMsg.2.2
              have hProgRight : right.ParallelProgressOwnership := by
                simp only [PactType.ParallelProgressOwnership] at hProg
                exact hProg.2.2
              have hFairRight : right.ParallelFairChoiceOwnership := by
                simp only [PactType.ParallelFairChoiceOwnership] at hFair
                exact hFair.2.2
              have hScopRight : right.InterfaceScoped := by
                simp only [PactType.InterfaceScoped] at hScop
                tauto
              have keyC : ∀ {lenv renv : TypeEnvironment} {ll rl : TypeLabel}
                  {lc lf rc rf : Finset BareMessage},
                  TypeOffers lenv left ll (PactType.skip left.alphabet) lc lf →
                  TypeOffers renv right rl (PactType.skip right.alphabet) rc rf →
                  LocalTypeOfferEnvironment e₂ interface left renv rc rf lenv →
                  LocalTypeOfferEnvironment e₂ interface right lenv lc lf renv →
                  (e₂.WellFormed alphabet ∧ TypeLabel.Sync interface ll rl) →
                  TypeLabel.combine interface leftLabel rightLabel =
                    TypeLabel.combine interface ll rl →
                  hideTypeOffers H (hideTypeOffers interface (leftCurrent ∪ rightCurrent)) =
                    hideTypeOffers H (hideTypeOffers interface (lc ∪ rc)) := by
                intro lenv renv ll rl lc lf rc rf hL hR hLoc1 hLoc2 hCond₂ hComb
                obtain ⟨hOwnA, hOwnB, hCrossA, hCrossB, hFreshA, hFreshB⟩ :=
                  TypeOffers.par_combine_inj_hypotheses hMsg hWF hProg hFair hScop
                    hLeftChild hRightChild hL hR
                obtain ⟨hLLeq, hRLeq⟩ := TypeLabel.combine_inj hCond.2 hCond₂.2 hOwnA
                  hOwnB hCrossA hCrossB hFreshA hFreshB hComb
                subst hLLeq
                subst hRLeq
                rw [hideTypeOffers_hide_union, hideTypeOffers_hide_union,
                  hideTypeOffers_union, hideTypeOffers_union,
                  (ihLeft hWFLeft hLinLeft hMsgLeft hProgLeft hFairLeft hScopLeft
                    (H ∪ interface) hL
                    (localTypeOfferEnvironment_agree_of_outer_agree hAgree hLeftLoc hLoc1)
                    rfl rfl).1 rfl,
                  (ihRight hWFRight hLinRight hMsgRight hProgRight hFairRight hScopRight
                    (H ∪ interface) hR
                    (localTypeOfferEnvironment_agree_of_outer_agree hAgree hRightLoc hLoc2)
                    rfl rfl).1 rfl]
              have keyF : ∀ {lenv renv : TypeEnvironment} {ll rl : TypeLabel}
                  {lc lf rc rf : Finset BareMessage},
                  TypeOffers lenv left ll (PactType.skip left.alphabet) lc lf →
                  TypeOffers renv right rl (PactType.skip right.alphabet) rc rf →
                  LocalTypeOfferEnvironment e₂ interface left renv rc rf lenv →
                  LocalTypeOfferEnvironment e₂ interface right lenv lc lf renv →
                  (e₂.WellFormed alphabet ∧ TypeLabel.Sync interface ll rl) →
                  TypeLabel.combine interface leftLabel rightLabel =
                    TypeLabel.combine interface ll rl →
                  hideTypeOffers H (hideTypeOffers interface (leftFuture ∪ rightFuture)) =
                    hideTypeOffers H (hideTypeOffers interface (lf ∪ rf)) := by
                intro lenv renv ll rl lc lf rc rf hL hR hLoc1 hLoc2 hCond₂ hComb
                obtain ⟨hOwnA, hOwnB, hCrossA, hCrossB, hFreshA, hFreshB⟩ :=
                  TypeOffers.par_combine_inj_hypotheses hMsg hWF hProg hFair hScop
                    hLeftChild hRightChild hL hR
                obtain ⟨hLLeq, hRLeq⟩ := TypeLabel.combine_inj hCond.2 hCond₂.2 hOwnA
                  hOwnB hCrossA hCrossB hFreshA hFreshB hComb
                subst hLLeq
                subst hRLeq
                rw [hideTypeOffers_hide_union, hideTypeOffers_hide_union,
                  hideTypeOffers_union, hideTypeOffers_union,
                  (ihLeft hWFLeft hLinLeft hMsgLeft hProgLeft hFairLeft hScopLeft
                    (H ∪ interface) hL
                    (localTypeOfferEnvironment_agree_of_outer_agree hAgree hLeftLoc hLoc1)
                    rfl rfl).2 rfl,
                  (ihRight hWFRight hLinRight hMsgRight hProgRight hFairRight hScopRight
                    (H ∪ interface) hR
                    (localTypeOfferEnvironment_agree_of_outer_agree hAgree hRightLoc hLoc2)
                    rfl rfl).2 rfl]
              first
                | (exact keyC (by assumption) (by assumption) (by assumption)
                     (by assumption) (by assumption) hLabel)
                | (exact keyF (by assumption) (by assumption) (by assumption)
                     (by assumption) (by assumption) hLabel))
           | skip
   | _ =>
       intro hWF hLin hMsg hProg hFair hScop H e₂ s₂ l₂ t₂ c₂ f₂ h₂ hAgree hSource hLabel
       cases h₂ <;>
         (try (first
                 | (exfalso; cases hSource; done)
                 | (injection hSource; subst_vars; contradiction)
                 | (refine absurd hLabel ?_; simp; done))) <;>
         (try refine ⟨fun hShape => ?_, fun hTarget => ?_⟩) <;>
         (try (have hShape := congrArg PactType.shape hTarget)) <;>
         first
           | rfl
           | (subst hTarget; rfl)
           | (injection hSource; subst_vars; rfl)
           | exact absurd hTarget (seq_ne_right _ _ _)
           | exact absurd hTarget.symm (seq_ne_right _ _ _)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget) (by assumption)
           | exact absurd (eq_skip_of_reannotate_eq_skip hTarget.symm) (by assumption)
           | (exfalso
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              try clear hTarget
              injection hSource
              subst_vars
              simp only [PactType.shape_reannotate, PactType.shape] at hShape
              first
                | exact absurd hShape (shape_seq_ne_right _ _)
                | exact absurd hShape.symm (shape_seq_ne_right _ _)
                | exact absurd hShape (shape_xoffer_ne_else _ _)
                | exact absurd hShape.symm (shape_xoffer_ne_else _ _)
                | exact absurd hShape (shape_offer_ne_else _ _)
                | exact absurd hShape.symm (shape_offer_ne_else _ _)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape.symm) (by assumption)
                | exact absurd (PactType.eq_skip_of_shape_skip hShape) (by assumption)
                | (simp at hShape; done))
           | (exfalso
              injection hSource with _ hElseEq hBranchEq
              try rw [hElseEq] at hTarget
              try rw [hBranchEq] at hTarget
              first
                | exact absurd hTarget (Ne.symm (xoffer_ne_else _ _ _))
                | exact absurd hTarget (xoffer_ne_else _ _ _)
                | exact absurd hTarget (Ne.symm (offer_ne_else _ _ _))
                | exact absurd hTarget (offer_ne_else _ _ _))
           | (exfalso
              injection hSource with hSA hSL hSR
              try rw [hSA] at hTarget
              try rw [hSL] at hTarget
              try rw [hSR] at hTarget
              first
                | exact absurd hTarget (seq_ne_right _ _ _)
                | exact absurd hTarget.symm (seq_ne_right _ _ _))
           | (obtain rfl := bareMessage_of_message_label hLabel
              first
                | rfl
                | (subst hTarget; rfl)
                | (injection hSource; subst_vars; rfl))
           | (refine absurd hSource ?_; simp; done)
           | (refine absurd hLabel ?_; simp; done)
           | (refine absurd hTarget ?_; simp; done)
           | (injection hSource; subst_vars; contradiction)
           | (injection hSource; subst_vars; simp_all; done)
           | skip

/-- The offer pair is a function of the step. -/
theorem typeOffers_unique
    {e₁ : TypeEnvironment} {s₁ : PactType} {l₁ : TypeLabel} {t₁ : PactType}
    {c₁ f₁ : Finset BareMessage}
    (h₁ : TypeOffers e₁ s₁ l₁ t₁ c₁ f₁) (hWF : s₁.AlphabetWellFormed)
    (hLin : s₁.SameCycleMessageLinear) (hMsg : s₁.ParallelMessageOwnership)
    (hProg : s₁.ParallelProgressOwnership)
    (hFair : s₁.ParallelFairChoiceOwnership) (hScop : s₁.InterfaceScoped)
    {e₂ : TypeEnvironment} {s₂ : PactType} {l₂ : TypeLabel} {t₂ : PactType}
    {c₂ f₂ : Finset BareMessage}
    (h₂ : TypeOffers e₂ s₂ l₂ t₂ c₂ f₂)
    (hEnv : e₁ = e₂) (hSource : s₁ = s₂) (hLabel : l₁ = l₂) (hTarget : t₁ = t₂) :
    c₁ = c₂ ∧ f₁ = f₂ := by
  subst hEnv
  have H := typeOffers_unique_aux h₁ hWF hLin hMsg hProg hFair hScop ∅ h₂ (EnvAgreeOutside.refl _ _)
    hSource hLabel
  constructor
  · simpa using H.1 (by rw [hTarget])
  · simpa using H.2 hTarget


end Pact

#print axioms Pact.typeOffers_unique
#print axioms Pact.typeOffers_unique_aux
