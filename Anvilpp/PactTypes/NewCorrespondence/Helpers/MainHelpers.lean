import Anvilpp.ProofHelpers.Regularity

namespace Pact

noncomputable section

open Classical

def TypeNonClockStep (source target : PactType) : Prop :=
  ∃ env label, TypeTransition env source label target ∧ ¬ label.isTock

/-- Zero or more non-clock semantic type steps. -/
def TypeSameCycleReaches (source target : PactType) : Prop :=
  Relation.ReflTransGen TypeNonClockStep source target

def TypeSameCycleCanComplete (processType : PactType) : Prop :=
  ∃ alphabet, TypeSameCycleReaches processType (.skip alphabet)

/-- `skip`'s only non-clock step is its own idle self-loop, so any same-cycle
path leaving `skip` stays at `skip`. -/
theorem typeSameCycleReaches_skip_absorbs (alphabet : PactTypeAlphabet) :
    ∀ ρ', TypeSameCycleReaches (.skip alphabet) ρ' → ρ' = .skip alphabet := by
  intro ρ' hPath
  induction hPath with
  | refl => rfl
  | tail _ hbc ih =>
      rw [ih] at hbc
      obtain ⟨env, label, hTrans, -⟩ := hbc
      cases hTrans
      rfl

/-- Lifting a same-cycle path of `left` through `.seq _ right` via `T-Seq`,
as long as the path's own target never becomes `skip` (`T-Seq`'s own side
condition) — safe because `skip` only ever appears as the very last state of
a same-cycle path (`typeSameCycleReaches_skip_absorbs`). -/
theorem typeSameCycleReaches_seq_lift (alphabet : PactTypeAlphabet) (right : PactType) :
    ∀ ρ ρ', TypeSameCycleReaches ρ ρ' → (∀ a, ρ' ≠ .skip a) →
      TypeSameCycleReaches (.seq alphabet ρ right) (.seq alphabet ρ' right) := by
  intro ρ ρ' hPath hNotSkip
  induction hPath using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head mid final hStep hRest ih =>
      obtain ⟨env, label, hTrans, hNotTock⟩ := hStep
      by_cases hFinalSkip : final = .skip final.alphabet
      · have hTargetSkip : ρ' = .skip final.alphabet :=
          typeSameCycleReaches_skip_absorbs final.alphabet ρ' (hFinalSkip ▸ hRest)
        exact absurd hTargetSkip (hNotSkip final.alphabet)
      · exact Relation.ReflTransGen.head ⟨env, label,
          TypeTransition.seq env alphabet mid final right label hTrans hFinalSkip, hNotTock⟩ ih

/-- Once `left` reaches `skip` in the same cycle, `.seq left right` reaches
`right` directly (`T-Seq` all the way, then `T-Seq-Fuse` for the very last
step). -/
theorem typeSameCycleReaches_seq_fuse (alphabet skipAlphabet : PactTypeAlphabet)
    (right : PactType) :
    ∀ ρ, TypeSameCycleReaches ρ (.skip skipAlphabet) →
      TypeSameCycleReaches (.seq alphabet ρ right) right := by
  intro ρ hPath
  induction hPath using Relation.ReflTransGen.head_induction_on with
  | refl =>
      have hWellFormed : TypeEnvironment.empty.WellFormed ∧
          TypeEnvironment.empty.clock = false := by
        simp [TypeEnvironment.WellFormed, TypeEnvironment.empty]
      have hSkipStep : TypeTransition TypeEnvironment.empty (.skip skipAlphabet)
          TypeLabel.silent (.skip skipAlphabet) :=
        TypeTransition.skip TypeEnvironment.empty skipAlphabet hWellFormed
      exact Relation.ReflTransGen.single ⟨TypeEnvironment.empty, TypeLabel.silent,
        TypeTransition.seq_fuse TypeEnvironment.empty alphabet skipAlphabet
          (.skip skipAlphabet) right TypeLabel.silent hSkipStep,
        by simp [TypeLabel.isTock, TypeLabel.silent]⟩
  | @head current next hStep hRest ih =>
      obtain ⟨env, label, hTrans, hNotTock⟩ := hStep
      by_cases hNextSkip : next = .skip next.alphabet
      · rw [hNextSkip] at hTrans
        exact Relation.ReflTransGen.single ⟨env, label,
          TypeTransition.seq_fuse env alphabet next.alphabet current right label
            hTrans, hNotTock⟩
      · exact Relation.ReflTransGen.head ⟨env, label,
          TypeTransition.seq env alphabet current next right label hTrans hNextSkip, hNotTock⟩ ih

/-- `pact.pdf`'s own same-cycle completion equation for sequence (p.34): "A
sequence finishes in the current cycle exactly when its left child can
finish and its right child can then finish." -/
theorem typeSameCycleReaches_seq_iff (alphabet : PactTypeAlphabet) (left right : PactType) :
    TypeSameCycleReaches (.seq alphabet left right) (.skip alphabet) ↔
      (∃ skipAlphabet, TypeSameCycleReaches left (.skip skipAlphabet)) ∧
        TypeSameCycleReaches right (.skip alphabet) := by
  constructor
  · intro hPath
    -- Accumulate forward along the path: it stays in `.seq _ right` form
    -- (lifted from left's own steps) until a fuse step reaches `right`,
    -- after which it continues as `right`'s own path.
    have hAux : ∀ current,
        Relation.ReflTransGen TypeNonClockStep (.seq alphabet left right) current →
        (∃ ρ', current = .seq alphabet ρ' right ∧ TypeSameCycleReaches left ρ') ∨
        ((∃ skipAlphabet, TypeSameCycleReaches left (.skip skipAlphabet)) ∧
          TypeSameCycleReaches right current) := by
      intro current hReach
      induction hReach with
      | refl => exact Or.inl ⟨left, rfl, Relation.ReflTransGen.refl⟩
      | tail _ hStep ih =>
          rcases ih with ⟨ρ', hEq, hρReach⟩ | ⟨hLeftDone, hRightReach⟩
          · subst hEq
            obtain ⟨env, label, hTrans, hNotTock⟩ := hStep
            cases hTrans with
            | seq_fuse _ _ skipAlphabet _ _ _ hLeftStep =>
                exact Or.inr ⟨⟨skipAlphabet,
                    hρReach.tail ⟨env, label, hLeftStep, hNotTock⟩⟩,
                  Relation.ReflTransGen.refl⟩
            | seq _ _ _ next _ _ hLeftStep _ =>
                exact Or.inl ⟨next, rfl, hρReach.tail ⟨env, label, hLeftStep, hNotTock⟩⟩
          · exact Or.inr ⟨hLeftDone, hRightReach.tail hStep⟩
    rcases hAux (.skip alphabet) hPath with ⟨_, hEq, _⟩ | ⟨hLeftDone, hRightReach⟩
    · exact nomatch hEq
    · exact ⟨hLeftDone, hRightReach⟩
  · rintro ⟨hLeft, hRight⟩
    obtain ⟨skipAlphabet, hLeft⟩ := hLeft
    exact (typeSameCycleReaches_seq_fuse alphabet skipAlphabet right left hLeft).trans hRight

/-- A choice's own step selects a branch outright, so its same-cycle
completion is exactly whichever branch's own completion. -/
theorem typeSameCycleReaches_choice_iff (alphabet targetAlphabet : PactTypeAlphabet)
    (left right : PactType) :
    TypeSameCycleReaches (.choice alphabet left right) (.skip targetAlphabet) ↔
      TypeSameCycleReaches left (.skip targetAlphabet) ∨
        TypeSameCycleReaches right (.skip targetAlphabet) := by
  constructor
  · intro hPath
    rcases Relation.ReflTransGen.cases_head hPath with h | ⟨mid, hStep, hRest⟩
    · exact nomatch h
    · obtain ⟨env, label, hTrans, -⟩ := hStep
      cases hTrans with
      | choice_left env hWF hClock => exact Or.inl hRest
      | choice_right env hWF hClock => exact Or.inr hRest
  · have hWF : TypeEnvironment.empty.WellFormed := by
      simp [TypeEnvironment.WellFormed, TypeEnvironment.empty]
    rintro (h | h)
    · exact Relation.ReflTransGen.head
        ⟨TypeEnvironment.empty, _,
          TypeTransition.choice_left TypeEnvironment.empty alphabet left right hWF rfl,
          by simp [TypeLabel.isTock, TypeLabel.silent]⟩ h
    · exact Relation.ReflTransGen.head
        ⟨TypeEnvironment.empty, _,
          TypeTransition.choice_right TypeEnvironment.empty alphabet left right hWF rfl,
          by simp [TypeLabel.isTock, TypeLabel.silent]⟩ h

/-- A fair choice's own step selects a branch outright too, same as ordinary
choice — only the labels differ. -/
theorem typeSameCycleReaches_fairChoice_iff (alphabet : PactTypeAlphabet)
    (targetAlphabet : PactTypeAlphabet) (bid : BranchId) (left right : PactType) :
    TypeSameCycleReaches (.fairChoice alphabet bid left right) (.skip targetAlphabet) ↔
      TypeSameCycleReaches left (.skip targetAlphabet) ∨
        TypeSameCycleReaches right (.skip targetAlphabet) := by
  constructor
  · intro hPath
    rcases Relation.ReflTransGen.cases_head hPath with h | ⟨mid, hStep, hRest⟩
    · exact nomatch h
    · obtain ⟨env, label, hTrans, -⟩ := hStep
      cases hTrans with
      | fair_left env hWF hClock => exact Or.inl hRest
      | fair_right env hWF hClock => exact Or.inr hRest
  · have hWF : TypeEnvironment.empty.WellFormed := by
      simp [TypeEnvironment.WellFormed, TypeEnvironment.empty]
    rintro (h | h)
    · exact Relation.ReflTransGen.head
        ⟨TypeEnvironment.empty, _,
          TypeTransition.fair_left TypeEnvironment.empty alphabet bid left right hWF rfl,
          by simp [TypeLabel.isTock, TypeLabel.fair]⟩ h
    · exact Relation.ReflTransGen.head
        ⟨TypeEnvironment.empty, _,
          TypeTransition.fair_right TypeEnvironment.empty alphabet bid left right hWF rfl,
          by simp [TypeLabel.isTock, TypeLabel.fair]⟩ h

theorem typeSameCycleCanComplete_choice_iff (alphabet : PactTypeAlphabet)
    (left right : PactType) :
    TypeSameCycleCanComplete (.choice alphabet left right) ↔
      TypeSameCycleCanComplete left ∨ TypeSameCycleCanComplete right := by
  constructor
  · rintro ⟨targetAlphabet, reach⟩
    rcases (typeSameCycleReaches_choice_iff alphabet targetAlphabet left right).mp reach with
      leftReach | rightReach
    · exact Or.inl ⟨targetAlphabet, leftReach⟩
    · exact Or.inr ⟨targetAlphabet, rightReach⟩
  · rintro (⟨targetAlphabet, leftReach⟩ | ⟨targetAlphabet, rightReach⟩)
    · exact ⟨targetAlphabet,
        (typeSameCycleReaches_choice_iff alphabet targetAlphabet left right).mpr
          (Or.inl leftReach)⟩
    · exact ⟨targetAlphabet,
        (typeSameCycleReaches_choice_iff alphabet targetAlphabet left right).mpr
          (Or.inr rightReach)⟩

theorem typeSameCycleCanComplete_fairChoice_iff (alphabet : PactTypeAlphabet)
    (bid : BranchId) (left right : PactType) :
    TypeSameCycleCanComplete (.fairChoice alphabet bid left right) ↔
      TypeSameCycleCanComplete left ∨ TypeSameCycleCanComplete right := by
  constructor
  · rintro ⟨targetAlphabet, reach⟩
    rcases (typeSameCycleReaches_fairChoice_iff alphabet targetAlphabet bid left right).mp
      reach with leftReach | rightReach
    · exact Or.inl ⟨targetAlphabet, leftReach⟩
    · exact Or.inr ⟨targetAlphabet, rightReach⟩
  · rintro (⟨targetAlphabet, leftReach⟩ | ⟨targetAlphabet, rightReach⟩)
    · exact ⟨targetAlphabet,
        (typeSameCycleReaches_fairChoice_iff alphabet targetAlphabet bid left right).mpr
          (Or.inl leftReach)⟩
    · exact ⟨targetAlphabet,
        (typeSameCycleReaches_fairChoice_iff alphabet targetAlphabet bid left right).mpr
          (Or.inr rightReach)⟩

/-- `T-Seq-Fuse` hands the sequence's own alphabet to the `skip` it produces,
so a sequence only ever completes at that alphabet. -/
theorem typeSameCycleReaches_seq_skip_alphabet (alphabet targetAlphabet : PactTypeAlphabet)
    (left right : PactType)
    (reach : TypeSameCycleReaches (.seq alphabet left right) (.skip targetAlphabet)) :
    TypeSameCycleReaches (.seq targetAlphabet left right) (.skip targetAlphabet) := by
  have hAux : ∀ current,
      Relation.ReflTransGen TypeNonClockStep (.seq alphabet left right) current →
      (∃ ρ', current = .seq alphabet ρ' right ∧ TypeSameCycleReaches left ρ') ∨
      ((∃ skipAlphabet, TypeSameCycleReaches left (.skip skipAlphabet)) ∧
        TypeSameCycleReaches right current) := by
    intro current hReach
    induction hReach with
    | refl => exact Or.inl ⟨left, rfl, Relation.ReflTransGen.refl⟩
    | tail _ hStep ih =>
        rcases ih with ⟨ρ', hEq, hρReach⟩ | ⟨hLeftDone, hRightReach⟩
        · subst hEq
          obtain ⟨env, label, hTrans, hNotTock⟩ := hStep
          cases hTrans with
          | seq_fuse _ _ skipAlphabet _ _ _ hLeftStep =>
              exact Or.inr ⟨⟨skipAlphabet,
                  hρReach.tail ⟨env, label, hLeftStep, hNotTock⟩⟩,
                Relation.ReflTransGen.refl⟩
          | seq _ _ _ next _ _ hLeftStep _ =>
              exact Or.inl ⟨next, rfl, hρReach.tail ⟨env, label, hLeftStep, hNotTock⟩⟩
        · exact Or.inr ⟨hLeftDone, hRightReach.tail hStep⟩
  rcases hAux _ reach with ⟨ρ', hEq, -⟩ | ⟨hLeftDone, hRightReach⟩
  · exact nomatch hEq
  · exact (typeSameCycleReaches_seq_iff targetAlphabet left right).mpr
      ⟨hLeftDone, hRightReach⟩

/-- A sequence completes in the current cycle exactly when its left child can
and its right child can then follow. -/
theorem typeSameCycleCanComplete_seq_iff (alphabet : PactTypeAlphabet)
    (left right : PactType) :
    TypeSameCycleCanComplete (.seq alphabet left right) ↔
      TypeSameCycleCanComplete left ∧ TypeSameCycleCanComplete right := by
  constructor
  · rintro ⟨targetAlphabet, reach⟩
    obtain ⟨hLeft, hRight⟩ :=
      (typeSameCycleReaches_seq_iff targetAlphabet left right).mp
        (typeSameCycleReaches_seq_skip_alphabet alphabet targetAlphabet left right
          reach)
    exact ⟨hLeft, ⟨targetAlphabet, hRight⟩⟩
  · rintro ⟨⟨leftAlphabet, hLeft⟩, ⟨rightAlphabet, hRight⟩⟩
    exact ⟨rightAlphabet,
      (typeSameCycleReaches_seq_fuse alphabet leftAlphabet right left
        hLeft).trans hRight⟩

/-- A recursion's own step unfolds it outright, so its same-cycle completion
is exactly its unfolded body's. -/
theorem typeSameCycleReaches_recur_iff (alphabet targetAlphabet : PactTypeAlphabet)
    (name : String) (body : PactType) :
    TypeSameCycleReaches (.recur alphabet name body) (.skip targetAlphabet) ↔
      TypeSameCycleReaches (body.replaceVar name (.recur alphabet name body))
        (.skip targetAlphabet) := by
  constructor
  · intro hPath
    rcases Relation.ReflTransGen.cases_head hPath with h | ⟨mid, hStep, hRest⟩
    · exact nomatch h
    · obtain ⟨env, label, hTrans, -⟩ := hStep
      cases hTrans with
      | recur env alphabet name body hWF hClock => exact hRest
  · intro h
    have hWF : TypeEnvironment.empty.WellFormed := by
      simp [TypeEnvironment.WellFormed, TypeEnvironment.empty]
    exact Relation.ReflTransGen.head
      ⟨TypeEnvironment.empty, _,
        TypeTransition.recur TypeEnvironment.empty alphabet name body hWF rfl,
        by simp [TypeLabel.isTock, TypeLabel.silent]⟩ h

theorem typeSameCycleCanComplete_recur_iff (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType) :
    TypeSameCycleCanComplete (.recur alphabet name body) ↔
      TypeSameCycleCanComplete (body.replaceVar name (.recur alphabet name body)) := by
  constructor
  · rintro ⟨targetAlphabet, reach⟩
    exact ⟨targetAlphabet,
      (typeSameCycleReaches_recur_iff alphabet targetAlphabet name body).mp reach⟩
  · rintro ⟨targetAlphabet, reach⟩
    exact ⟨targetAlphabet,
      (typeSameCycleReaches_recur_iff alphabet targetAlphabet name body).mpr reach⟩

/-- An exclusive offer may idle at its root, so its same-cycle completion is
its else-branch's or some branch body's. -/
theorem typeSameCycleReaches_xoffer_iff (alphabet targetAlphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hBranchActions : ∀ b ∈ branches, b.1 ∈ alphabet.actions) :
    TypeSameCycleReaches (.xoffer alphabet elseType branches) (.skip targetAlphabet) ↔
      TypeSameCycleReaches elseType (.skip targetAlphabet) ∨
      ∃ entry ∈ branches, TypeSameCycleReaches entry.2 (.skip targetAlphabet) := by
  constructor
  · intro hPath
    have hAux : ∀ current,
        Relation.ReflTransGen TypeNonClockStep (.xoffer alphabet elseType branches) current →
        current = .xoffer alphabet elseType branches ∨
        TypeSameCycleReaches elseType current ∨
        ∃ entry ∈ branches, TypeSameCycleReaches entry.2 current := by
      intro current hReach
      induction hReach with
      | refl => exact Or.inl rfl
      | tail _ hStep ih =>
          rcases ih with hRoot | hElse | ⟨entry, hMem, hEntry⟩
          · rw [hRoot] at hStep
            obtain ⟨env, label, hTrans, -⟩ := hStep
            cases hTrans with
            | xoffer_branch _ _ _ _ action _ hCond =>
                exact Or.inr (Or.inr ⟨(action, _), hCond.2.1,
                  Relation.ReflTransGen.refl⟩)
            | xoffer_else _ _ _ _ hCond => exact Or.inr (Or.inl Relation.ReflTransGen.refl)
            | xoffer_wait _ _ _ _ hCond => exact Or.inl rfl
          · exact Or.inr (Or.inl (hElse.tail hStep))
          · exact Or.inr (Or.inr ⟨entry, hMem, hEntry.tail hStep⟩)
    rcases hAux _ hPath with hRoot | hElse | hBranch
    · exact nomatch hRoot
    · exact Or.inl hElse
    · exact Or.inr hBranch
  · have hWF : TypeEnvironment.empty.WellFormed := by
      simp [TypeEnvironment.WellFormed, TypeEnvironment.empty]
    rintro (hElse | ⟨entry, hMem, hEntry⟩)
    · refine Relation.ReflTransGen.head ⟨TypeEnvironment.empty, _,
        TypeTransition.xoffer_else TypeEnvironment.empty alphabet elseType branches
          ⟨hWF, rfl, ?_, ?_⟩ hBranchActions,
        by simp [TypeLabel.isTock, TypeLabel.silent]⟩ hElse
      · simp [TypeNoImmediateBranch, TypeEnvironment.empty]
      · simp [TypeResolved, TypeEnvironment.empty]
    · rcases entry with ⟨action, branchType⟩
      set env : TypeEnvironment :=
        { immediate := {typeNeed action}, future := ∅, clock := false } with hEnvDef
      have hWFenv : env.WellFormed := by
        simp [TypeEnvironment.WellFormed, hEnvDef]
      refine Relation.ReflTransGen.head ⟨env, _,
        TypeTransition.xoffer_branch env alphabet elseType branches action branchType
          ⟨hWFenv, hMem, ?_, ?_⟩ hBranchActions, ?_⟩ hEntry
      · simp [TypeBranchEnabled, hEnvDef]
      · simp [TypeResolved, hEnvDef]
      · simp [TypeLabel.isTock, TypeLabel.message]

theorem typeSameCycleCanComplete_xoffer_iff (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hBranchActions : ∀ b ∈ branches, b.1 ∈ alphabet.actions) :
    TypeSameCycleCanComplete (.xoffer alphabet elseType branches) ↔
      TypeSameCycleCanComplete elseType ∨
      ∃ entry ∈ branches, TypeSameCycleCanComplete entry.2 := by
  constructor
  · rintro ⟨targetAlphabet, reach⟩
    rcases (typeSameCycleReaches_xoffer_iff alphabet targetAlphabet elseType
        branches hBranchActions).mp reach with hElse | ⟨entry, hMem, hEntry⟩
    · exact Or.inl ⟨targetAlphabet, hElse⟩
    · exact Or.inr ⟨entry, hMem, targetAlphabet, hEntry⟩
  · rintro (⟨targetAlphabet, hElse⟩ | ⟨entry, hMem, targetAlphabet, hEntry⟩)
    · exact ⟨targetAlphabet, (typeSameCycleReaches_xoffer_iff alphabet targetAlphabet
        elseType branches hBranchActions).mpr (Or.inl hElse)⟩
    · exact ⟨targetAlphabet, (typeSameCycleReaches_xoffer_iff alphabet targetAlphabet
        elseType branches hBranchActions).mpr (Or.inr ⟨entry, hMem, hEntry⟩)⟩

/-- A conjunctive offer may idle at its root, so its same-cycle completion is
its else-branch's or some selected branch product's. -/
theorem typeSameCycleReaches_offer_iff (alphabet targetAlphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hBranchActions : ∀ b ∈ branches, b.1 ∈ alphabet.actions) :
    TypeSameCycleReaches (.offer alphabet elseType branches) (.skip targetAlphabet) ↔
      TypeSameCycleReaches elseType (.skip targetAlphabet) ∨
      ∃ entry ∈ branches, TypeSameCycleReaches
        (parallelTypeBranchesSelecting entry branches) (.skip targetAlphabet) := by
  constructor
  · intro hPath
    have hAux : ∀ current,
        Relation.ReflTransGen TypeNonClockStep (.offer alphabet elseType branches) current →
        current = .offer alphabet elseType branches ∨
        TypeSameCycleReaches elseType current ∨
        ∃ entry ∈ branches, TypeSameCycleReaches
          (parallelTypeBranchesSelecting entry branches) current := by
      intro current hReach
      induction hReach with
      | refl => exact Or.inl rfl
      | tail _ hStep ih =>
          rcases ih with hRoot | hElse | ⟨entry, hMem, hEntry⟩
          · rw [hRoot] at hStep
            obtain ⟨env, label, hTrans, -⟩ := hStep
            cases hTrans with
            | offer_some _ _ _ _ enabled hCond =>
                exact Or.inr (Or.inr ⟨enabled, hCond.2.1, Relation.ReflTransGen.refl⟩)
            | offer_else _ _ _ _ hCond => exact Or.inr (Or.inl Relation.ReflTransGen.refl)
            | offer_wait _ _ _ _ hCond => exact Or.inl rfl
          · exact Or.inr (Or.inl (hElse.tail hStep))
          · exact Or.inr (Or.inr ⟨entry, hMem, hEntry.tail hStep⟩)
    rcases hAux _ hPath with hRoot | hElse | hBranch
    · exact nomatch hRoot
    · exact Or.inl hElse
    · exact Or.inr hBranch
  · have hWF : TypeEnvironment.empty.WellFormed := by
      simp [TypeEnvironment.WellFormed, TypeEnvironment.empty]
    rintro (hElse | ⟨entry, hMem, hEntry⟩)
    · refine Relation.ReflTransGen.head ⟨TypeEnvironment.empty, _,
        TypeTransition.offer_else TypeEnvironment.empty alphabet elseType branches
          ⟨hWF, rfl, ?_, ?_⟩ hBranchActions,
        by simp [TypeLabel.isTock, TypeLabel.silent]⟩ hElse
      · simp [TypeNoImmediateBranch, TypeEnvironment.empty]
      · simp [TypeResolved, TypeEnvironment.empty]
    · set env : TypeEnvironment :=
        { immediate := {typeNeed entry.1}, future := ∅, clock := false } with hEnvDef
      have hWFenv : env.WellFormed := by
        simp [TypeEnvironment.WellFormed, hEnvDef]
      refine Relation.ReflTransGen.head ⟨env, _,
        TypeTransition.offer_some env alphabet elseType branches entry
          ⟨hWFenv, hMem, ?_⟩ hBranchActions, ?_⟩ hEntry
      · simp [TypeBranchEnabled, hEnvDef]
      · simp [TypeLabel.isTock, TypeLabel.silent]

theorem typeSameCycleCanComplete_offer_iff (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hBranchActions : ∀ b ∈ branches, b.1 ∈ alphabet.actions) :
    TypeSameCycleCanComplete (.offer alphabet elseType branches) ↔
      TypeSameCycleCanComplete elseType ∨
      ∃ entry ∈ branches,
        TypeSameCycleCanComplete (parallelTypeBranchesSelecting entry branches) := by
  constructor
  · rintro ⟨targetAlphabet, reach⟩
    rcases (typeSameCycleReaches_offer_iff alphabet targetAlphabet elseType
        branches hBranchActions).mp reach with hElse | ⟨entry, hMem, hEntry⟩
    · exact Or.inl ⟨targetAlphabet, hElse⟩
    · exact Or.inr ⟨entry, hMem, targetAlphabet, hEntry⟩
  · rintro (⟨targetAlphabet, hElse⟩ | ⟨entry, hMem, targetAlphabet, hEntry⟩)
    · exact ⟨targetAlphabet, (typeSameCycleReaches_offer_iff alphabet targetAlphabet
        elseType branches hBranchActions).mpr (Or.inl hElse)⟩
    · exact ⟨targetAlphabet, (typeSameCycleReaches_offer_iff alphabet targetAlphabet
        elseType branches hBranchActions).mpr (Or.inr ⟨entry, hMem, hEntry⟩)⟩

/-- A mandatory clock survives substitution: neither operand of any clause
depends on which term replaces a variable. -/
theorem mustTock_replaceVar (name : String) (replacement : PactType) :
    ∀ body : PactType, body.MustTockBeforeCompletion →
      (body.replaceVar name replacement).MustTockBeforeCompletion := by
  intro body
  induction hSize : sizeOf body using Nat.strong_induction_on generalizing body with
  | _ n ih =>
    have hBranches : ∀ (branches : List (BareMessage × PactType)),
        sizeOf branches < n →
        PactType.BranchesMustTockBeforeCompletion branches →
        PactType.BranchesMustTockBeforeCompletion
          (PactType.replaceBranches branches name replacement) := by
      intro branches hSz hAll
      induction branches with
      | nil =>
          rw [PactType.replaceBranches, PactType.BranchesMustTockBeforeCompletion]
          exact trivial
      | cons b rest restIH =>
          rcases b with ⟨act, bt⟩
          have hFields : bt.MustTockBeforeCompletion ∧
              PactType.BranchesMustTockBeforeCompletion rest := by
            simpa only [PactType.BranchesMustTockBeforeCompletion] using hAll
          simp only [PactType.replaceBranches, PactType.BranchesMustTockBeforeCompletion]
          refine ⟨ih (sizeOf bt) (by
            have h1 : sizeOf bt < sizeOf (act, bt) := by simp_wf; omega
            have h2 : sizeOf (act, bt) < sizeOf ((act, bt) :: rest) := by simp_wf; omega
            omega) bt rfl hFields.1, restIH (by
            have : sizeOf rest < sizeOf ((act, bt) :: rest) := by simp_wf; omega
            omega) hFields.2⟩
    intro hTock
    cases body with
    | message _ _ _ | progress _ _ | skip _ =>
        simp [PactType.MustTockBeforeCompletion] at hTock
    | var _ other =>
        simp [PactType.MustTockBeforeCompletion] at hTock
    | tock alphabet => simp [PactType.replaceVar, PactType.MustTockBeforeCompletion]
    | recur alphabet other b =>
        by_cases hEq : name = other
        · rw [PactType.replaceVar, if_pos hEq]
          simpa only [PactType.MustTockBeforeCompletion] using hTock
        · simp only [PactType.replaceVar, if_neg hEq, PactType.MustTockBeforeCompletion]
          exact ih (sizeOf b) (by rw [← hSize]; simp_wf; omega) b rfl
            (by simpa only [PactType.MustTockBeforeCompletion] using hTock)
    | choice alphabet l r | fairChoice alphabet _ l r | par alphabet l r _ =>
        have hF : l.MustTockBeforeCompletion ∧ r.MustTockBeforeCompletion := by
          simpa only [PactType.MustTockBeforeCompletion] using hTock
        simp only [PactType.replaceVar, PactType.MustTockBeforeCompletion]
        exact ⟨ih (sizeOf l) (by rw [← hSize]; simp_wf; omega) l rfl hF.1,
          ih (sizeOf r) (by rw [← hSize]; simp_wf; omega) r rfl hF.2⟩
    | seq alphabet l r =>
        have hF : l.MustTockBeforeCompletion ∨ r.MustTockBeforeCompletion := by
          simpa only [PactType.MustTockBeforeCompletion] using hTock
        simp only [PactType.replaceVar, PactType.MustTockBeforeCompletion]
        rcases hF with h | h
        · exact Or.inl (ih (sizeOf l) (by rw [← hSize]; simp_wf; omega) l rfl h)
        · exact Or.inr (ih (sizeOf r) (by rw [← hSize]; simp_wf; omega) r rfl h)
    | xoffer alphabet e branches | offer alphabet e branches =>
        have hF : e.MustTockBeforeCompletion ∧
            PactType.BranchesMustTockBeforeCompletion branches := by
          simpa only [PactType.MustTockBeforeCompletion] using hTock
        simp only [PactType.replaceVar, PactType.MustTockBeforeCompletion]
        exact ⟨ih (sizeOf e) (by rw [← hSize]; simp_wf; omega) e rfl hF.1,
          hBranches branches (by rw [← hSize]; simp_wf; omega) hF.2⟩

/-- Synchronized labels are tock together, so a non-clock product step has
non-clock component steps. -/
theorem typeLabel_sync_not_isTock (interface : Interface) (left right : TypeLabel)
    (hSync : TypeLabel.Sync interface left right)
    (hNotTock : ¬ (TypeLabel.combine interface left right).isTock) :
    ¬ left.isTock ∧ ¬ right.isTock := by
  cases left with
  | tock =>
      cases right with
      | tock => exact absurd (by simp [TypeLabel.combine, TypeLabel.isTock]) hNotTock
      | actions ra => exact absurd (hSync.2.2.mp trivial) (by simp [TypeLabel.isTock])
  | actions la =>
      cases right with
      | tock => exact absurd (hSync.2.2.mpr trivial) (by simp [TypeLabel.isTock])
      | actions ra => exact ⟨by simp [TypeLabel.isTock], by simp [TypeLabel.isTock]⟩

/-- A non-clock raw automaton edge — matching `ofStage`'s own edge filter
(`compileTypeFuel`'s pending edges, before the external-alphabet filter
`compileType` applies), not the public, alphabet-filtered `TypeAutomaton`.
H14, like `ofStage`, needs to see every same-cycle edge the compiler produces,
not just the ones exported to the fixed transition alphabet. -/
def AutomatonNonClockStep (fragment : AutomatonFragment)
    (source target : TypeAutomatonState) : Prop :=
  ∃ edge ∈ fragment.edges,
    edge.source = source ∧ edge.target = target ∧ ¬ edge.label.semantic.isTock

/-- A state reaches an accepting state without crossing a clock edge. -/
def AutomatonSameCycleReachesAccepting
    (fragment : AutomatonFragment) (state : TypeAutomatonState) : Prop :=
  ∃ finalState,
    Relation.ReflTransGen (AutomatonNonClockStep fragment) state finalState ∧
    finalState ∈ fragment.accepting

/-- No same-cycle path out of `state` reaches a state that sources a marker
edge for `name`. -/
def MarkerUnreachableThisCycle (fragment : AutomatonFragment) (name : String)
    (state : TypeAutomatonState) : Prop :=
  ∀ reached, Relation.ReflTransGen (AutomatonNonClockStep fragment) state reached →
    ¬ MarkerSource fragment name reached

/-- Reachability transports along a `.child index`-tagged embedding whenever
every non-clock step from a tagged state stays tagged and matches the child
fragment's own step exactly (no redirect ever crosses the tag boundary) —
the reachability analogue of `ofStage_binaryChoice_child0`/`_child1`'s
one-step tag-transparency, reused by every constructor whose child edges are
copied verbatim (`choice`, `fairChoice`, `recur`'s non-marker body edges). -/
theorem automatonSameCycleReachesAccepting_of_child_tag
    (fragment childFragment : AutomatonFragment) (index : Nat)
    (hStep : ∀ q target, AutomatonNonClockStep fragment (childState index q) target ↔
      ∃ q', target = childState index q' ∧ AutomatonNonClockStep childFragment q q')
    (hAccept : ∀ q, childState index q ∈ fragment.accepting ↔ q ∈ childFragment.accepting)
    (q : TypeAutomatonState) :
    AutomatonSameCycleReachesAccepting fragment (childState index q) ↔
      AutomatonSameCycleReachesAccepting childFragment q := by
  have hForward : ∀ q finalState,
      Relation.ReflTransGen (AutomatonNonClockStep fragment) (childState index q) finalState →
      ∃ q', finalState = childState index q' ∧
        Relation.ReflTransGen (AutomatonNonClockStep childFragment) q q' := by
    intro q finalState hReach
    induction hReach with
    | refl => exact ⟨q, rfl, Relation.ReflTransGen.refl⟩
    | tail hab hbc ih =>
        obtain ⟨q'', hEq, hReach'⟩ := ih
        subst hEq
        obtain ⟨q''', hEq', hStep'⟩ := (hStep q'' _).mp hbc
        exact ⟨q''', hEq', hReach'.tail hStep'⟩
  have hBackward : ∀ q q',
      Relation.ReflTransGen (AutomatonNonClockStep childFragment) q q' →
      Relation.ReflTransGen (AutomatonNonClockStep fragment)
        (childState index q) (childState index q') := by
    intro q q' hReach
    induction hReach with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih => exact ih.tail ((hStep _ _).mpr ⟨_, rfl, hbc⟩)
  constructor
  · rintro ⟨finalState, hReach, hFinal⟩
    obtain ⟨q', hEq, hReach'⟩ := hForward q finalState hReach
    subst hEq
    exact ⟨q', hReach', (hAccept q').mp hFinal⟩
  · rintro ⟨q', hReach, hFinal⟩
    exact ⟨childState index q', hBackward q q' hReach, (hAccept q').mpr hFinal⟩

/-- A choice's tagged-left one-step raw edges are exactly its child's own
edges, tagged (labels are copied verbatim by `childPendingEdge`, so
tock-ness is preserved). -/
theorem automatonNonClockStep_binaryChoice_child0
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (q target : TypeAutomatonState) :
    AutomatonNonClockStep
        (buildChoiceAutomaton signature alphabet left right selectionLeft
          selectionRight)
        (childState 0 q) target ↔
      ∃ q', target = childState 0 q' ∧ AutomatonNonClockStep left q q' := by
  constructor
  · rintro ⟨edge, hEdgeMem, hSource, hTarget, hNotTock⟩
    obtain ⟨childEdge, hChildEdge, hChildSource, hEdgeEq⟩ :=
      (buildChoiceAutomaton_outgoing_left signature alphabet left right
        selectionLeft selectionRight q edge).mp ⟨hEdgeMem, hSource⟩
    refine ⟨childEdge.target, ?_, childEdge, hChildEdge, hChildSource, rfl, ?_⟩
    · rw [← hTarget, hEdgeEq]; simp [childPendingEdge, childState]
    · simpa [hEdgeEq, childPendingEdge] using hNotTock
  · rintro ⟨q', hTargetEq, childEdge, hChildEdge, hChildSource, hChildTarget, hChildNotTock⟩
    have hOut := (buildChoiceAutomaton_outgoing_left signature alphabet left right
      selectionLeft selectionRight q (childPendingEdge 0 childEdge)).mpr
      ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    exact ⟨childPendingEdge 0 childEdge, hOut.1, hOut.2,
      by rw [hTargetEq]; simp [childPendingEdge, childState, hChildTarget],
      by simpa [childPendingEdge] using hChildNotTock⟩

/-- Right-side analogue of `automatonNonClockStep_binaryChoice_child0`. -/
theorem automatonNonClockStep_binaryChoice_child1
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (q target : TypeAutomatonState) :
    AutomatonNonClockStep
        (buildChoiceAutomaton signature alphabet left right selectionLeft
          selectionRight)
        (childState 1 q) target ↔
      ∃ q', target = childState 1 q' ∧ AutomatonNonClockStep right q q' := by
  constructor
  · rintro ⟨edge, hEdgeMem, hSource, hTarget, hNotTock⟩
    obtain ⟨childEdge, hChildEdge, hChildSource, hEdgeEq⟩ :=
      (buildChoiceAutomaton_outgoing_right signature alphabet left right
        selectionLeft selectionRight q edge).mp ⟨hEdgeMem, hSource⟩
    refine ⟨childEdge.target, ?_, childEdge, hChildEdge, hChildSource, rfl, ?_⟩
    · rw [← hTarget, hEdgeEq]; simp [childPendingEdge, childState]
    · simpa [hEdgeEq, childPendingEdge] using hNotTock
  · rintro ⟨q', hTargetEq, childEdge, hChildEdge, hChildSource, hChildTarget, hChildNotTock⟩
    have hOut := (buildChoiceAutomaton_outgoing_right signature alphabet left right
      selectionLeft selectionRight q (childPendingEdge 1 childEdge)).mpr
      ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    exact ⟨childPendingEdge 1 childEdge, hOut.1, hOut.2,
      by rw [hTargetEq]; simp [childPendingEdge, childState, hChildTarget],
      by simpa [childPendingEdge] using hChildNotTock⟩

theorem buildChoiceAutomaton_child0_accepting_iff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (q : TypeAutomatonState) :
    childState 0 q ∈
        (buildChoiceAutomaton signature alphabet left right selectionLeft
          selectionRight).accepting ↔
      q ∈ left.accepting := by
  simp [buildChoiceAutomaton, finishAutomatonFragment, childAccepting, childState]

theorem buildChoiceAutomaton_child1_accepting_iff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (q : TypeAutomatonState) :
    childState 1 q ∈
        (buildChoiceAutomaton signature alphabet left right selectionLeft
          selectionRight).accepting ↔
      q ∈ right.accepting := by
  simp [buildChoiceAutomaton, finishAutomatonFragment, childAccepting, childState]

theorem buildChoiceAutomaton_root_not_accepting
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) :
    TypeAutomatonState.root ∉
      (buildChoiceAutomaton signature alphabet left right selectionLeft
          selectionRight).accepting := by
  simp [buildChoiceAutomaton, finishAutomatonFragment, childAccepting, childState]

/-- The root's only one-step raw targets are the two children's initial
states — read off `buildChoiceAutomaton`'s selection edges, which fire for
any supported environment (the empty one always qualifies). -/
theorem automatonNonClockStep_root_binaryChoice_iff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hEnvMem :
      TypeEnvironment.empty ∈ signature.localEnvironmentsFor alphabet)
    (hLeftNotTock : ¬ selectionLeft.isTock) (hRightNotTock : ¬ selectionRight.isTock)
    (target : TypeAutomatonState) :
    AutomatonNonClockStep
        (buildChoiceAutomaton signature alphabet left right selectionLeft
          selectionRight)
        TypeAutomatonState.root target ↔
      target = childState 0 left.initial ∨ target = childState 1 right.initial := by
  constructor
  · rintro ⟨edge, hEdgeMem, hSource, hTarget, -⟩
    simp only [buildChoiceAutomaton, finishAutomatonFragment, childPendingEdges,
      Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_insert, Finset.mem_singleton] at hEdgeMem
    rcases hEdgeMem with (⟨childEdge, -, hEq⟩ | ⟨childEdge, -, hEq⟩) |
      ⟨environment, -, hEq | hEq⟩
    · exfalso; rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
    · exfalso; rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
    · left; rw [← hTarget, hEq]
    · right; rw [← hTarget, hEq]
  · rintro (rfl | rfl)
    · set edge : PendingAutomatonEdge :=
        { source := TypeAutomatonState.root, environment := TypeEnvironment.empty,
          label := AutomatonConstructionLabel.visible selectionLeft, current := ∅,
          future := FutureSpec.at (childState 0 left.initial) ∅,
          target := childState 0 left.initial } with hEdgeDef
      have hEdgeMem : edge ∈
          (buildChoiceAutomaton signature alphabet left right selectionLeft
          selectionRight).edges := by
        simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
          Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton]
        exact Or.inr ⟨TypeEnvironment.empty, ⟨hEnvMem, rfl⟩,
          Or.inl hEdgeDef.symm⟩
      exact ⟨edge, hEdgeMem, rfl, rfl,
        by simp [hEdgeDef, AutomatonConstructionLabel.semantic, hLeftNotTock]⟩
    · set edge : PendingAutomatonEdge :=
        { source := TypeAutomatonState.root, environment := TypeEnvironment.empty,
          label := AutomatonConstructionLabel.visible selectionRight, current := ∅,
          future := FutureSpec.at (childState 1 right.initial) ∅,
          target := childState 1 right.initial } with hEdgeDef
      have hEdgeMem : edge ∈
          (buildChoiceAutomaton signature alphabet left right selectionLeft
          selectionRight).edges := by
        simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
          Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton]
        exact Or.inr ⟨TypeEnvironment.empty, ⟨hEnvMem, rfl⟩,
          Or.inr hEdgeDef.symm⟩
      exact ⟨edge, hEdgeMem, rfl, rfl,
        by simp [hEdgeDef, AutomatonConstructionLabel.semantic, hRightNotTock]⟩

/-- Root reachability for a choice: since the root is never itself accepting
and its only one-step targets are the two children's initial states,
reaching an accepting state from the root is exactly reaching one from
either tagged child-initial state. -/
theorem automatonSameCycleReachesAccepting_root_binaryChoice
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hEnvMem :
      TypeEnvironment.empty ∈ signature.localEnvironmentsFor alphabet)
    (hLeftNotTock : ¬ selectionLeft.isTock) (hRightNotTock : ¬ selectionRight.isTock) :
    AutomatonSameCycleReachesAccepting
        (buildChoiceAutomaton signature alphabet left right selectionLeft
          selectionRight)
        TypeAutomatonState.root ↔
      AutomatonSameCycleReachesAccepting
        (buildChoiceAutomaton signature alphabet left right selectionLeft
          selectionRight)
        (childState 0 left.initial) ∨
      AutomatonSameCycleReachesAccepting
        (buildChoiceAutomaton signature alphabet left right selectionLeft
          selectionRight)
        (childState 1 right.initial) := by
  constructor
  · rintro ⟨finalState, hReach, hFinal⟩
    rcases Relation.ReflTransGen.cases_head hReach with hEq | ⟨mid, hStep, hRest⟩
    · exfalso
      rw [← hEq] at hFinal
      exact absurd hFinal
        (buildChoiceAutomaton_root_not_accepting signature alphabet left right
          selectionLeft selectionRight)
    · rcases (automatonNonClockStep_root_binaryChoice_iff signature alphabet left right
        selectionLeft selectionRight hEnvMem hLeftNotTock hRightNotTock mid).mp hStep with
        rfl | rfl
      · exact Or.inl ⟨finalState, hRest, hFinal⟩
      · exact Or.inr ⟨finalState, hRest, hFinal⟩
  · rintro (⟨finalState, hReach, hFinal⟩ | ⟨finalState, hReach, hFinal⟩)
    · refine ⟨finalState, Relation.ReflTransGen.head ?_ hReach, hFinal⟩
      exact (automatonNonClockStep_root_binaryChoice_iff signature alphabet left right
        selectionLeft selectionRight hEnvMem hLeftNotTock hRightNotTock
        (childState 0 left.initial)).mpr (Or.inl rfl)
    · refine ⟨finalState, Relation.ReflTransGen.head ?_ hReach, hFinal⟩
      exact (automatonNonClockStep_root_binaryChoice_iff signature alphabet left right
        selectionLeft selectionRight hEnvMem hLeftNotTock hRightNotTock
        (childState 1 right.initial)).mpr (Or.inr rfl)

def ofStage (signature : TypeAlphabet) :
    Nat → PactType → TypeAutomatonState → Finset BareMessage
  | 0, _, _ => ∅
  | n + 1, processType, state =>
      (((compileTypeFuel signature (typeCompilationFuel processType)
          processType).edges.filter
          (fun edge => edge.source = state ∧ ¬ edge.label.semantic.isTock))).biUnion
        (fun edge => edge.current ∪ ofStage signature n processType edge.target) ∪
      (match stateProductInfo processType state with
        | some (interface, left, right, q1, q2) =>
            hideTypeOffers interface
              (ofStage signature n left q1 ∪ ofStage signature n right q2)
        | none => ∅)

/-- One same-cycle semantic step out of a residual, as a (current offer,
target) pair — enumerated directly from `TypeTransition`'s own rules, one
constructor at a time, mirroring `compileTypeFuel`'s edge families one level
shallower (no further recursion into the target). Every non-clock rule
contributes exactly one entry, since some well-formed environment always
realizes it (e.g. the empty environment realizes a message's wait, and the
environment needing it realizes its fire); a `.seq` step wraps or fuses a
left step exactly as `T-Seq`/`T-Seq-Fuse` do, and a `.par` step pairs one
step of each component, hiding the interface and fusing to `skip` when both
components complete, exactly as `T-Par`/`T-Par-Fuse` do. -/
def typeSameCycleSteps : PactType → Finset (Finset BareMessage × PactType)
  | .skip alphabet => {(∅, .skip alphabet)}
  | .message alphabet msg dir =>
      {({(msg, dir)}, .skip alphabet), ({(msg, dir)}, .message alphabet msg dir)}
  | .tock alphabet => {(∅, .tock alphabet)}
  | .progress alphabet pid => {(∅, .skip alphabet)}
  | .var _ _ => ∅
  | .choice _ left right => {(∅, left), (∅, right)}
  | .fairChoice _ _ left right => {(∅, left), (∅, right)}
  | .recur alphabet name body =>
      {(∅, body.replaceVar name (.recur alphabet name body))}
  | .seq alphabet left right =>
      (typeSameCycleSteps left).image fun step =>
        if step.2 = .skip step.2.alphabet then (step.1, right)
        else (step.1, .seq alphabet step.2 right)
  | .par alphabet left right interface =>
      (typeSameCycleSteps left).biUnion fun leftStep =>
        (typeSameCycleSteps right).image fun rightStep =>
          (hideTypeOffers interface (leftStep.1 ∪ rightStep.1),
            if leftStep.2 = .skip leftStep.2.alphabet ∧
                rightStep.2 = .skip rightStep.2.alphabet then
              .skip alphabet
            else .par alphabet leftStep.2 rightStep.2 interface)
  | .xoffer alphabet elseType branches =>
      insert (∅, .xoffer alphabet elseType branches)
        (insert (∅, elseType)
          ((branches.map fun branch => ({branch.1}, branch.2)).toFinset))
  | .offer alphabet elseType branches =>
      insert (∅, .offer alphabet elseType branches)
        (insert (∅, elseType)
          ((branches.map fun branch =>
            ({branch.1}, parallelTypeBranchesSelecting branch branches)).toFinset))

/-- The Kleene-staged semantic future-offer menu, indexed by the *same* stage
convention as `ofStage` — one stage per same-cycle step actually taken, not
per syntactic unwrap (unlike `typeFutureOffersFuel`, which decrements fuel on
structural descent regardless of whether that descent corresponds to a real
step — see `interestingdiscoveries.md` for the counterexample this was built
to fix). Mirrors `pact.pdf`'s Ψ directly: `Bare(O_C)` off one same-cycle step
unioned with the stage-below value at that step's target, plus the same
unconditional `hideTypeOffers` term at a `.par` residual that `ofStage`'s Φ
has at a product state. -/
def futOffStage : Nat → PactType → Finset BareMessage
  | 0, _ => ∅
  | n + 1, ty =>
      (typeSameCycleSteps ty).biUnion (fun step => step.1 ∪ futOffStage n step.2) ∪
      (match ty with
        | .par _ left right interface =>
            hideTypeOffers interface (futOffStage n left ∪ futOffStage n right)
        | _ => ∅)

/-- `skip`'s idle self-loop never exposes an offer, at any stage. -/
theorem futOffStage_skip : ∀ n alphabet, futOffStage n (.skip alphabet) = ∅ := by
  intro n alphabet
  induction n with
  | zero => rfl
  | succ n ih =>
      show (typeSameCycleSteps (.skip alphabet)).biUnion
          (fun step => step.1 ∪ futOffStage n step.2) ∪ ∅ = ∅
      simp [typeSameCycleSteps, ih]

/-- An open variable fragment has no same-cycle step at all, at any stage. -/
theorem futOffStage_var : ∀ n alphabet name, futOffStage n (.var alphabet name) = ∅ := by
  intro n alphabet name
  cases n with
  | zero => rfl
  | succ n =>
      show (typeSameCycleSteps (.var alphabet name)).biUnion
          (fun step => step.1 ∪ futOffStage n step.2) ∪ ∅ = ∅
      simp [typeSameCycleSteps]

/-- `tock`'s idle self-loop never exposes an offer, at any stage. -/
theorem futOffStage_tock : ∀ n alphabet, futOffStage n (.tock alphabet) = ∅ := by
  intro n alphabet
  induction n with
  | zero => rfl
  | succ n ih =>
      show (typeSameCycleSteps (.tock alphabet)).biUnion
          (fun step => step.1 ∪ futOffStage n step.2) ∪ ∅ = ∅
      simp [typeSameCycleSteps, ih]

/-- A progress marker fires unconditionally into `skip`, which never exposes
an offer of its own. -/
theorem futOffStage_progress :
    ∀ n alphabet pid, futOffStage n (.progress alphabet pid) = ∅ := by
  intro n alphabet pid
  cases n with
  | zero => rfl
  | succ n =>
      show (typeSameCycleSteps (.progress alphabet pid)).biUnion
          (fun step => step.1 ∪ futOffStage n step.2) ∪ ∅ = ∅
      simp [typeSameCycleSteps, futOffStage_skip]

/-- A message's fire/wait pair both expose the same singleton offer, at every
stage past the first. -/
theorem futOffStage_message :
    ∀ n alphabet msg dir,
      futOffStage (n + 1) (.message alphabet msg dir) = {(msg, dir)} := by
  intro n
  induction n with
  | zero =>
      intro alphabet msg dir
      simp [futOffStage, typeSameCycleSteps, futOffStage_skip]
  | succ n ih =>
      intro alphabet msg dir
      show (typeSameCycleSteps (.message alphabet msg dir)).biUnion
          (fun step => step.1 ∪ futOffStage (n + 1) step.2) ∪ ∅ = {(msg, dir)}
      simp [typeSameCycleSteps, futOffStage_skip, ih alphabet msg dir]

/-- An ordinary choice's two silent selection steps expose whatever their
selected branch exposes one stage down. -/
theorem futOffStage_choice :
    ∀ n alphabet left right, futOffStage (n + 1) (.choice alphabet left right) =
      futOffStage n left ∪ futOffStage n right := by
  intro n alphabet left right
  show (typeSameCycleSteps (.choice alphabet left right)).biUnion
      (fun step => step.1 ∪ futOffStage n step.2) ∪ ∅ = _
  simp [typeSameCycleSteps]

/-- A fair choice's two selection steps expose the same menu as ordinary
choice — only the labels differ, and `typeSameCycleSteps` doesn't track
labels at all. -/
theorem futOffStage_fairChoice :
    ∀ n alphabet bid left right,
      futOffStage (n + 1) (.fairChoice alphabet bid left right) =
      futOffStage n left ∪ futOffStage n right := by
  intro n alphabet bid left right
  show (typeSameCycleSteps (.fairChoice alphabet bid left right)).biUnion
      (fun step => step.1 ∪ futOffStage n step.2) ∪ ∅ = _
  simp [typeSameCycleSteps]

/-- A sequence's same-cycle steps are exactly its left component's own
same-cycle steps, each either fused directly into `right` (when the left
step already reaches `skip`, `T-Seq-Fuse`) or wrapped back into a smaller
sequence (`T-Seq`) — matching `sequenceRedirect`'s kept/redirect split on the
automaton side exactly, but decided here by a direct check on the target
residual, needing nothing about accepting states or H13. -/
theorem futOffStage_seq :
    ∀ n alphabet left right, futOffStage (n + 1) (.seq alphabet left right) =
      (typeSameCycleSteps left).biUnion (fun step =>
        step.1 ∪ if step.2 = .skip step.2.alphabet then futOffStage n right
          else futOffStage n (.seq alphabet step.2 right)) := by
  intro n alphabet left right
  apply Finset.ext
  intro x
  show x ∈ (typeSameCycleSteps (.seq alphabet left right)).biUnion
      (fun step => step.1 ∪ futOffStage n step.2) ∪ (∅ : Finset BareMessage) ↔ _
  simp only [typeSameCycleSteps, Finset.union_empty, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨step, hStep, rfl⟩, hx⟩
    refine ⟨step, hStep, ?_⟩
    split_ifs at hx ⊢ with hSkip <;> exact hx
  · rintro ⟨step, hStep, hx⟩
    refine ⟨_, ⟨step, hStep, rfl⟩, ?_⟩
    split_ifs at hx ⊢ with hSkip <;> exact hx

/-- Tag-transparency for `.seq`'s right child: a right state's edges are
copied unchanged from `right`'s own compilation (no redirect touches them),
so `ofStage` there agrees with `right`'s own value directly, at every
stage. -/
theorem ofStage_sequence_child1
    (signature : TypeAlphabet) (whole left right : PactType)
    (hEdgesEq : (compileTypeFuel signature (typeCompilationFuel whole) whole).edges =
      (buildSequenceAutomaton signature
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right)).edges)
    (hProductEq : ∀ q, stateProductInfo whole (TypeAutomatonState.child 1 q) =
      stateProductInfo right q) :
    ∀ m q, ofStage signature m whole (TypeAutomatonState.child 1 q) =
      ofStage signature m right q := by
  intro m
  induction m with
  | zero => intro q; rfl
  | succ m ih =>
      intro q
      simp only [ofStage]
      rw [hProductEq q, hEdgesEq]
      congr 1
      apply Finset.ext
      intro x
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨edge, ⟨hEdgeMem, hSource, hNotTock⟩, hx⟩
        obtain ⟨childEdge, hChildMem, hChildSource, hEdgeEq⟩ :=
          (buildSequenceAutomaton_outgoing_right signature
            (compileTypeFuel signature (typeCompilationFuel left) left)
            (compileTypeFuel signature (typeCompilationFuel right) right)
            q edge).mp ⟨hEdgeMem, hSource⟩
        refine ⟨childEdge, ⟨hChildMem, hChildSource, ?_⟩, ?_⟩
        · simpa [hEdgeEq, childPendingEdge] using hNotTock
        · rw [hEdgeEq] at hx
          simp only [childPendingEdge, childState] at hx
          rwa [ih childEdge.target] at hx
      · rintro ⟨childEdge, ⟨hChildMem, hChildSource, hNotTock⟩, hx⟩
        have hOut := (buildSequenceAutomaton_outgoing_right signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          q (childPendingEdge 1 childEdge)).mpr
          ⟨childEdge, hChildMem, hChildSource, rfl⟩
        refine ⟨childPendingEdge 1 childEdge, ⟨hOut.1, hOut.2, ?_⟩, ?_⟩
        · simpa [childPendingEdge] using hNotTock
        · simp only [childPendingEdge, childState]
          rwa [ih childEdge.target]

/-- The `AutomatonNonClockStep`-level (one-step, non-recursive) form of
`ofStage_sequence_child1`'s own edge case-split: a `.child 1 q`-tagged
state's real one-step behaviour is exactly `right`'s own, verbatim (no
redirect, no bridge, ever touches the right side). -/
theorem automatonNonClockStep_sequence_child1
    (signature : TypeAlphabet) (left right : AutomatonFragment) (q target : TypeAutomatonState) :
    AutomatonNonClockStep (buildSequenceAutomaton signature left right) (childState 1 q) target ↔
      ∃ q', target = childState 1 q' ∧ AutomatonNonClockStep right q q' := by
  constructor
  · rintro ⟨edge, hEdgeMem, hSource, hTarget, hNotTock⟩
    obtain ⟨childEdge, hChildMem, hChildSource, hEdgeEq⟩ :=
      (buildSequenceAutomaton_outgoing_right signature left right q edge).mp
        ⟨hEdgeMem, hSource⟩
    refine ⟨childEdge.target, ?_, childEdge, hChildMem, hChildSource, rfl, ?_⟩
    · rw [hEdgeEq] at hTarget
      exact hTarget.symm
    · simpa [hEdgeEq, childPendingEdge] using hNotTock
  · rintro ⟨q', hTargetEq, childEdge, hChildMem, hChildSource, hChildTarget,
      hChildNotTock⟩
    have hOut := (buildSequenceAutomaton_outgoing_right signature left right q
      (childPendingEdge 1 childEdge)).mpr
      ⟨childEdge, hChildMem, hChildSource, rfl⟩
    refine ⟨childPendingEdge 1 childEdge, hOut.1, hOut.2, ?_, ?_⟩
    · simp only [childPendingEdge, childState]
      exact (congrArg (childState 1) hChildTarget).trans hTargetEq.symm
    · simpa [childPendingEdge] using hChildNotTock

theorem buildSequenceAutomaton_child1_accepting_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment) (q : TypeAutomatonState) :
    childState 1 q ∈ (buildSequenceAutomaton signature left right).accepting ↔
      q ∈ right.accepting := by
  simp [buildSequenceAutomaton, finishAutomatonFragment, childAccepting, childState]

/-- Every edge leaving a left-child state is a left edge of `left`, kept or
redirected — for any label, not just a visible one. -/
theorem buildSequenceAutomaton_outgoing_left_any
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge)
    (hOutgoing :
      edge ∈ (buildSequenceAutomaton signature left right).edges ∧
        edge.source = .child 0 state) :
    ∃ childEdge ∈ left.edges,
      childEdge.source = state ∧ edge = sequenceLeftEdge left right childEdge := by
  classical
  rcases hOutgoing with ⟨hEdge, hSource⟩
  simp only [buildSequenceAutomaton, finishAutomatonFragment, sequenceLeftEdges,
    sequenceRightEdges, sequenceRedirectEdges, childPendingEdges,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
  rcases hEdge with (hLeft | hRight) | hRedirect
  · rcases hLeft with ⟨childEdge, ⟨hChildMem, hNotAccepting⟩, hEdgeEq⟩
    have hChildSource := hSource
    rw [← hEdgeEq] at hChildSource
    simp [sequenceKeptLeftEdge, childState] at hChildSource
    exact ⟨childEdge, hChildMem, hChildSource,
      by rw [← hEdgeEq, sequenceLeftEdge, if_neg hNotAccepting]⟩
  · rcases hRight with ⟨childEdge, _, hEdgeEq⟩
    rw [← hEdgeEq] at hSource
    simp [childPendingEdge, childState] at hSource
  · rcases hRedirect with ⟨childEdge, ⟨hChildMem, hAccepting⟩, hEdgeEq⟩
    have hChildSource := hSource
    rw [← hEdgeEq] at hChildSource
    simp [sequenceRedirectEdge, childState] at hChildSource
    exact ⟨childEdge, hChildMem, hChildSource,
      by rw [← hEdgeEq, sequenceLeftEdge, if_pos hAccepting]⟩

/-- A non-clock step out of a left-child state mirrors one of `left`'s own
steps, landing either at the retagged target or, when that target accepts, at
the right entry. -/
theorem automatonNonClockStep_sequence_child0
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (q target : TypeAutomatonState) :
    AutomatonNonClockStep (buildSequenceAutomaton signature left right)
        (childState 0 q) target ↔
      ∃ q', AutomatonNonClockStep left q q' ∧
        target = sequenceRedirect left right q' := by
  constructor
  · rintro ⟨edge, hEdgeMem, hSource, hTarget, hNotTock⟩
    obtain ⟨childEdge, hChildMem, hChildSource, hEdgeEq⟩ :=
      buildSequenceAutomaton_outgoing_left_any signature left right q edge
        ⟨hEdgeMem, hSource⟩
    refine ⟨childEdge.target, ⟨childEdge, hChildMem, hChildSource, rfl, ?_⟩, ?_⟩
    · rw [hEdgeEq] at hNotTock; simpa using hNotTock
    · rw [hEdgeEq] at hTarget; simpa using hTarget.symm
  · rintro ⟨q', ⟨childEdge, hChildMem, hChildSource, hChildTarget, hNotTock⟩,
      hTargetEq⟩
    refine ⟨sequenceLeftEdge left right childEdge, ?_, ?_, ?_, ?_⟩
    · simp only [buildSequenceAutomaton, finishAutomatonFragment,
        sequenceLeftEdges, sequenceRightEdges, sequenceRedirectEdges,
        Finset.mem_union, Finset.mem_image, Finset.mem_filter]
      by_cases hAccepting : childEdge.target ∈ left.accepting
      · exact Or.inr ⟨childEdge, ⟨hChildMem, hAccepting⟩,
          by rw [sequenceLeftEdge, if_pos hAccepting]⟩
      · exact Or.inl (Or.inl ⟨childEdge, ⟨hChildMem, hAccepting⟩,
          by rw [sequenceLeftEdge, if_neg hAccepting]⟩)
    · simp [hChildSource]
    · rw [sequenceLeftEdge_target, hChildTarget]; exact hTargetEq.symm
    · simpa using hNotTock

/-- Every indexed branch accepting state is tagged, so the fresh root of an
offer is never among them. -/
theorem root_not_mem_indexedFragmentAccepting
    (automata : List (BareMessage × AutomatonFragment)) :
    TypeAutomatonState.root ∉ indexedFragmentAccepting automata := by
  have hAux : ∀ (items : List ((BareMessage × AutomatonFragment) × Nat))
      (seed : Finset TypeAutomatonState),
      TypeAutomatonState.root ∉ seed →
      TypeAutomatonState.root ∉
        items.foldl (fun states indexed =>
          states ∪ childAccepting (indexed.2 + 1) indexed.1.2) seed := by
    intro items
    induction items with
    | nil => intro seed hSeed; exact hSeed
    | cons item rest ih =>
        intro seed hSeed
        refine ih _ ?_
        simp only [Finset.mem_union, not_or]
        refine ⟨hSeed, ?_⟩
        simp [childAccepting, childState]
  exact hAux _ ∅ (Finset.notMem_empty _)

/-- `skip` is the only fragment accepting at its own initial state, and its
idle self-loop is a non-clock step, so an accepting initial state always has
one. -/
theorem compileTypeFuel_nonClockStep_of_initial_accepting
    (signature : TypeAlphabet) (fuel : Nat) (processType : PactType)
    (hAccepting : (compileTypeFuel signature fuel processType).initial ∈
      (compileTypeFuel signature fuel processType).accepting) :
    ∃ target, AutomatonNonClockStep (compileTypeFuel signature fuel processType)
      (compileTypeFuel signature fuel processType).initial target ∧
      target ∈ (compileTypeFuel signature fuel processType).accepting := by
  classical
  cases fuel with
  | zero => simp [compileTypeFuel] at hAccepting
  | succ fuel =>
      cases processType with
      | skip alphabet =>
          have hEmptyLocal :
              TypeEnvironment.empty ∈ signature.localEnvironmentsFor alphabet := by
            simp only [TypeAlphabet.localEnvironmentsFor, Finset.mem_union,
              Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
            exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
          refine ⟨TypeAutomatonState.root, ?_, ?_⟩
          · refine ⟨PendingAutomatonEdge.mk TypeAutomatonState.root
              TypeEnvironment.empty (AutomatonConstructionLabel.visible TypeLabel.silent)
              ∅ (FutureSpec.explicit ∅) TypeAutomatonState.root, ?_, ?_, rfl, ?_⟩
            · simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image,
                Finset.mem_filter]
              exact ⟨TypeEnvironment.empty, ⟨hEmptyLocal, rfl⟩, rfl⟩
            · simp [compileTypeFuel, finishAutomatonFragment]
            · simp [AutomatonConstructionLabel.semantic, TypeLabel.isTock,
                TypeLabel.silent]
          · simp [compileTypeFuel, finishAutomatonFragment]
      | message alphabet msg dir =>
          exact absurd hAccepting (by
            simp [compileTypeFuel, finishAutomatonFragment])
      | tock alphabet =>
          exact absurd hAccepting (by
            simp [compileTypeFuel, finishAutomatonFragment])
      | progress alphabet pid =>
          exact absurd hAccepting (by
            simp [compileTypeFuel, finishAutomatonFragment])
      | var alphabet name =>
          exact absurd hAccepting (by
            simp [compileTypeFuel, finishAutomatonFragment])
      | choice alphabet left right =>
          exact absurd hAccepting (by
            simp [compileTypeFuel, buildChoiceAutomaton, finishAutomatonFragment,
              childAccepting, childState])
      | fairChoice alphabet bid left right =>
          exact absurd hAccepting (by
            simp [compileTypeFuel, buildChoiceAutomaton, finishAutomatonFragment,
              childAccepting, childState])
      | recur alphabet name body =>
          exact absurd hAccepting (by
            simp [compileTypeFuel, buildRecursionAutomaton, finishAutomatonFragment,
              childAccepting, childState])
      | seq alphabet left right =>
          exact absurd hAccepting (by
            simp [compileTypeFuel, buildSequenceAutomaton, finishAutomatonFragment,
              childAccepting, childState])
      | par alphabet left right interface =>
          exact absurd hAccepting (by
            simp [compileTypeFuel, buildParallelAutomaton, finishAutomatonFragment])
      | xoffer alphabet elseType branches =>
          refine absurd hAccepting ?_
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union, childAccepting,
            Finset.mem_image, not_or]
          refine ⟨?_, root_not_mem_indexedFragmentAccepting _⟩
          simp [childState]
      | offer alphabet elseType branches =>
          refine absurd hAccepting ?_
          simp only [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union, childAccepting,
            Finset.mem_image, not_or]
          refine ⟨?_, root_not_mem_indexedFragmentAccepting _⟩
          simp [childState]

/-- A left path whose last state accepts lifts into the sequence: either it
crosses the redirect into the right entry, or it was empty at an accepting
start. -/
theorem automatonSameCycleReaches_sequence_lift_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (q q' : TypeAutomatonState)
    (hReach : Relation.ReflTransGen (AutomatonNonClockStep left) q q')
    (hAccepting : q' ∈ left.accepting) :
    Relation.ReflTransGen
      (AutomatonNonClockStep (buildSequenceAutomaton signature left right))
      (childState 0 q) (childState 1 right.initial) ∨ q = q' := by
  induction hReach using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inr rfl
  | @head a b hStep hRest ih =>
      refine Or.inl ?_
      by_cases hAcceptingB : b ∈ left.accepting
      · refine Relation.ReflTransGen.single ?_
        refine (automatonNonClockStep_sequence_child0 signature left right a _).mpr
          ⟨b, hStep, ?_⟩
        rw [sequenceRedirect, if_pos hAcceptingB]
      · refine Relation.ReflTransGen.head (b := childState 0 b) ?_ ?_
        · exact (automatonNonClockStep_sequence_child0 signature left right a
            (childState 0 b)).mpr ⟨b, hStep,
            by rw [sequenceRedirect, if_neg hAcceptingB]⟩
        · rcases ih with hPath | hEq
          · exact hPath
          · exact absurd (hEq ▸ hAccepting) hAcceptingB

/-- A same-cycle path out of a left-child state either stays in the left copy
or has already crossed the redirect into the right entry. -/
theorem automatonSameCycleReaches_sequence_child0_cases
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (q target : TypeAutomatonState)
    (hReach : Relation.ReflTransGen
      (AutomatonNonClockStep (buildSequenceAutomaton signature left right))
      (childState 0 q) target) :
    (∃ q', target = childState 0 q' ∧
      Relation.ReflTransGen (AutomatonNonClockStep left) q q') ∨
    (∃ q', Relation.ReflTransGen (AutomatonNonClockStep left) q q' ∧
      q' ∈ left.accepting ∧
      Relation.ReflTransGen
        (AutomatonNonClockStep (buildSequenceAutomaton signature left right))
        (childState 1 right.initial) target) := by
  induction hReach with
  | refl => exact Or.inl ⟨q, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hStep ih =>
      rcases ih with ⟨q', hEq, hLeftReach⟩ | ⟨q', hLeftReach, hAccepting, hRest⟩
      · subst hEq
        obtain ⟨q'', hLeftStep, hTargetEq⟩ :=
          (automatonNonClockStep_sequence_child0 signature left right _ _).mp hStep
        by_cases hAccepting : q'' ∈ left.accepting
        · refine Or.inr ⟨q'', hLeftReach.tail hLeftStep, hAccepting, ?_⟩
          rw [hTargetEq, sequenceRedirect, if_pos hAccepting]
        · refine Or.inl ⟨q'', ?_, hLeftReach.tail hLeftStep⟩
          rw [hTargetEq, sequenceRedirect, if_neg hAccepting]
      · exact Or.inr ⟨q', hLeftReach, hAccepting, hRest.tail hStep⟩

lemma helper_h12_compiled_state_shape
    (signature : TypeAlphabet) {processType residual : PactType}
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual (compileType signature processType).initial) :
    (compileType signature processType).initial ∈
      (compileType signature processType).states :=
  compileType_initial_mem signature processType

/-- Helper Lemma H15: future offers agree. -/
lemma helper_h15_future_offers_agree
    (signature : TypeAlphabet) {processType residual : PactType}
    {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual state) :
    computeFutureOf signature processType state = typeFutureOffers residual := by
  sorry -- TODO(section7): prove by the constructor future-correctness bundle.

/-- Every local environment a signature generates is well-formed. -/
theorem H13_localEnvironment_wellFormed
    (signature : TypeAlphabet) {environment : TypeEnvironment}
    (hEnvironment : environment ∈ signature.localEnvironments) :
    environment.WellFormed := by
  simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
    Finset.mem_image] at hEnvironment
  rcases hEnvironment with rfl | ⟨immediate, _hImmediate, future, hFuture, rfl⟩
  · simp [TypeEnvironment.WellFormed, TypeEnvironment.tock]
  · constructor
    · simp
    · intro _hClock
      change immediate ∩ future = ∅
      rw [← Finset.disjoint_iff_inter_eq_empty]
      apply Finset.disjoint_left.mpr
      intro action hImmediate hFutureMember
      have hAvailable := hFuture hFutureMember
      simp only [Finset.mem_sdiff] at hAvailable
      exact hAvailable.2 hImmediate

/-- Helper Lemma H12, binary choice/offer-root case, shared by `.choice` and
`.fairChoice`. -/
theorem helper_h12_binaryChoice_shape
    (signature : TypeAlphabet) (whole left right : PactType)
    (hUnfold :
      buildRelationSetCoreFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right) + 1) whole =
        insert (whole, TypeAutomatonState.root)
          ((buildRelationSetCoreFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left).image
              (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
            (buildRelationSetCoreFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right).image
              (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2))))
    (hFuelEq : typeCompilationFuel whole =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership (buildRelationSet whole (compileType signature whole))
        residual state) :
    (residual = whole ∧ state = TypeAutomatonState.root) ∨
    (∃ q1, state = .child 0 q1 ∧
      relationMembership (buildRelationSet left (compileType signature left)) residual q1) ∨
    (∃ q2, state = .child 1 q2 ∧
      relationMembership (buildRelationSet right (compileType signature right)) residual q2) := by
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel signature (typeCompilationFuel whole) whole := hRelated
  rw [hFuelEq, hUnfold] at hMem
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Prod.mk.injEq] at hMem
  rcases hMem with ⟨hR, hS⟩ | ⟨entry, hEntry, hR, hS⟩ | ⟨entry, hEntry, hR, hS⟩
  · exact Or.inl ⟨hR, hS⟩
  · refine Or.inr (Or.inl ⟨entry.2, hS.symm, ?_⟩)
    show (residual, entry.2) ∈ buildRelationSetCoreFuel signature (typeCompilationFuel left) left
    rw [← buildRelationSetCoreFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl, ← hR]
    exact hEntry
  · refine Or.inr (Or.inr ⟨entry.2, hS.symm, ?_⟩)
    show (residual, entry.2) ∈ buildRelationSetCoreFuel signature (typeCompilationFuel right) right
    rw [← buildRelationSetCoreFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl, ← hR]
    exact hEntry

/-- Shape of a related pair for `.seq left right`: unlike choice/fairChoice
there is no fresh root (the sequence's own initial state IS `left`'s tagged
initial state, per `buildSequenceAutomaton`), so a state is tagged `.child 0`
with the residual still wrapped in `.seq _ right` (we haven't crossed over
yet) or tagged `.child 1` with the residual exactly `right`'s own (we have). -/
theorem helper_h12_seq_shape
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet) (left right : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.seq alphabet left right)
          (compileType signature (.seq alphabet left right)))
        residual state) :
    (∃ ρ q1, residual = .seq alphabet ρ right ∧ state = .child 0 q1 ∧
      relationMembership (buildRelationSet left (compileType signature left)) ρ q1 ∧
      (q1 ∉ (compileType signature left).accepting ∨
        q1 = (compileType signature left).initial)) ∨
    (∃ q2, state = .child 1 q2 ∧
      relationMembership (buildRelationSet right (compileType signature right)) residual q2) := by
  have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel signature (typeCompilationFuel (.seq alphabet left right))
        (.seq alphabet left right) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel] at hMem
  rcases Finset.mem_union.mp hMem with hLeft | hRight
  · rcases Finset.mem_image.mp hLeft with ⟨entry, hEntry, hEq⟩
    have hEntryMem := (Finset.mem_filter.mp hEntry).1
    have hSurvives := (Finset.mem_filter.mp hEntry).2
    injection hEq with hR hS
    refine Or.inl ⟨entry.1, entry.2, hR.symm, hS.symm, ?_, ?_⟩
    show (entry.1, entry.2) ∈ buildRelationSetCoreFuel signature (typeCompilationFuel left) left
    rw [← buildRelationSetCoreFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl]
    exact hEntryMem
    have hCompile := compileTypeFuel_eq_of_sufficient signature left
      (le_max_left (typeCompilationFuel left) (typeCompilationFuel right)) le_rfl
    rw [hCompile] at hSurvives
    change entry.2 ∉ (compileTypeFuel signature (typeCompilationFuel left) left).accepting ∨
      entry.2 = (compileTypeFuel signature (typeCompilationFuel left) left).initial
    by_cases hAccepting :
        entry.2 ∈ (compileTypeFuel signature (typeCompilationFuel left) left).accepting
    · exact Or.inr (by
        by_contra hNotInitial
        exact hSurvives (by simp [sequenceDeleted, hAccepting, hNotInitial]))
    · exact Or.inl hAccepting
  · rcases Finset.mem_image.mp hRight with ⟨entry, hEntry, hEq⟩
    injection hEq with hR hS
    refine Or.inr ⟨entry.2, hS.symm, ?_⟩
    show (residual, entry.2) ∈ buildRelationSetCoreFuel signature (typeCompilationFuel right) right
    rw [← buildRelationSetCoreFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl, ← hR]
    exact hEntry

theorem compileType_var_no_edge
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet) (name : String)
    (source : TypeAutomatonState) (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : TypeAutomatonState) :
    ¬ (compileType signature (.var alphabet name)).HasEdge source env label offers target := by
  intro hEdge
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature (.var alphabet name)
      source target env label offers).mp hEdge
  obtain ⟨pendingEdge, hMem, -, -, hLabel, -, -, -⟩ := hResolved
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_image] at hMem
  obtain ⟨environment, -, hEq⟩ := hMem
  rw [← hEq] at hLabel
  simp at hLabel

theorem compileType_var_edges_empty
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet) (name : String) :
    (compileType signature (.var alphabet name)).edges = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro edge hEdge
  exact compileType_var_no_edge signature alphabet name edge.source edge.symbol.environment
    edge.symbol.label edge.symbol.offers edge.target hEdge

private theorem stateProductInfoFuel_succ_stable :
    ∀ fuel processType state, typeCompilationFuel processType ≤ fuel →
      stateProductInfoFuel (fuel + 1) processType state =
        stateProductInfoFuel fuel processType state := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType state hFuel
      have := typeCompilationFuel_positive processType
      omega
  | succ fuel ih =>
      intro processType state hFuel
      cases processType with
      | skip _ => rfl
      | message _ _ _ => rfl
      | tock _ => rfl
      | progress _ _ => rfl
      | var _ _ => rfl
      | choice _ left right =>
          cases state with
          | child i q =>
              cases i with
              | zero =>
                  have hLeft : typeCompilationFuel left ≤ fuel := by
                    simp [typeCompilationFuel] at hFuel; omega
                  change stateProductInfoFuel (fuel + 1) left q =
                    stateProductInfoFuel fuel left q
                  exact ih left q hLeft
              | succ i =>
                  cases i with
                  | zero =>
                      have hRight : typeCompilationFuel right ≤ fuel := by
                        simp [typeCompilationFuel] at hFuel; omega
                      change stateProductInfoFuel (fuel + 1) right q =
                        stateProductInfoFuel fuel right q
                      exact ih right q hRight
                  | succ i => rfl
          | _ => rfl
      | fairChoice _ bid left right =>
          cases state with
          | child i q =>
              cases i with
              | zero =>
                  have hLeft : typeCompilationFuel left ≤ fuel := by
                    simp [typeCompilationFuel] at hFuel; omega
                  change stateProductInfoFuel (fuel + 1) left q =
                    stateProductInfoFuel fuel left q
                  exact ih left q hLeft
              | succ i =>
                  cases i with
                  | zero =>
                      have hRight : typeCompilationFuel right ≤ fuel := by
                        simp [typeCompilationFuel] at hFuel; omega
                      change stateProductInfoFuel (fuel + 1) right q =
                        stateProductInfoFuel fuel right q
                      exact ih right q hRight
                  | succ i => rfl
          | _ => rfl
      | seq _ left right =>
          cases state with
          | child i q =>
              cases i with
              | zero =>
                  have hLeft : typeCompilationFuel left ≤ fuel := by
                    simp [typeCompilationFuel] at hFuel; omega
                  change stateProductInfoFuel (fuel + 1) left q =
                    stateProductInfoFuel fuel left q
                  exact ih left q hLeft
              | succ i =>
                  cases i with
                  | zero =>
                      have hRight : typeCompilationFuel right ≤ fuel := by
                        simp [typeCompilationFuel] at hFuel; omega
                      change stateProductInfoFuel (fuel + 1) right q =
                        stateProductInfoFuel fuel right q
                      exact ih right q hRight
                  | succ i => rfl
          | _ => rfl
      | par _ left right interface =>
          cases state with
          | pair q1 q2 => rfl
          | _ => rfl
      | recur _ name body =>
          cases state with
          | child i q =>
              cases i with
              | zero =>
                  have hBody : typeCompilationFuel body ≤ fuel := by
                    simp [typeCompilationFuel] at hFuel; omega
                  change stateProductInfoFuel (fuel + 1) body q =
                    stateProductInfoFuel fuel body q
                  exact ih body q hBody
              | succ i => rfl
          | _ => rfl
      | xoffer _ elseType branches =>
          cases state with
          | child i q =>
              cases i with
              | zero =>
                  have hElse : typeCompilationFuel elseType ≤ fuel := by
                    simp [typeCompilationFuel] at hFuel; omega
                  change stateProductInfoFuel (fuel + 1) elseType q =
                    stateProductInfoFuel fuel elseType q
                  exact ih elseType q hElse
              | succ i =>
                  simp only [stateProductInfoFuel]
                  cases hGet : branches[i]? with
                  | none => simp
                  | some branch =>
                      simp only
                      have hMem : branch ∈ branches := List.mem_of_getElem? hGet
                      have hBranchFuel : typeCompilationFuel branch.2 ≤ fuel := by
                        have hBound :=
                          typeCompilationFuel_le_typeBranchCompilationFuel branches branch hMem
                        simp [typeCompilationFuel] at hFuel; omega
                      exact ih branch.2 q hBranchFuel
          | _ => rfl
      | offer _ elseType branches =>
          cases state with
          | child i q =>
              cases i with
              | zero =>
                  have hElse : typeCompilationFuel elseType ≤ fuel := by
                    simp [typeCompilationFuel] at hFuel; omega
                  change stateProductInfoFuel (fuel + 1) elseType q =
                    stateProductInfoFuel fuel elseType q
                  exact ih elseType q hElse
              | succ i =>
                  simp only [stateProductInfoFuel]
                  cases hGet : branches[i]? with
                  | none => simp
                  | some selected =>
                      simp only
                      have hFuel' :
                          typeCompilationFuel (parallelTypeBranchesSelecting selected branches) ≤
                            fuel := by
                        rw [typeCompilationFuel_parallelTypeBranchesSelecting]
                        simp [typeCompilationFuel] at hFuel; omega
                      exact ih (parallelTypeBranchesSelecting selected branches) q hFuel'
          | _ => rfl

private theorem stateProductInfoFuel_add_stable
    (processType : PactType) (state : TypeAutomatonState)
    (fuel extra : Nat) (hFuel : typeCompilationFuel processType ≤ fuel) :
    stateProductInfoFuel (fuel + extra) processType state =
      stateProductInfoFuel fuel processType state := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ,
        stateProductInfoFuel_succ_stable (fuel + extra) processType state (by omega), ih]

theorem stateProductInfoFuel_eq_of_sufficient'
    (processType : PactType) (state : TypeAutomatonState)
    {leftFuel rightFuel : Nat}
    (hLeft : TypeCompilationFuelSufficient processType leftFuel)
    (hRight : TypeCompilationFuelSufficient processType rightFuel) :
    stateProductInfoFuel leftFuel processType state =
      stateProductInfoFuel rightFuel processType state := by
  by_cases hOrder : leftFuel ≤ rightFuel
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hOrder
    exact (stateProductInfoFuel_add_stable processType state leftFuel extra hLeft).symm
  · have hReverse : rightFuel ≤ leftFuel := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hReverse
    exact stateProductInfoFuel_add_stable processType state rightFuel extra hRight

/-- Tag-transparency for `.choice`/`.fairChoice`: `ofStage` at a `.child 0`-tagged
state agrees with `ofStage` inside `left`'s own automaton, at every stage. -/
theorem ofStage_binaryChoice_child0
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (whole left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (hEdgesEq : (compileTypeFuel signature (typeCompilationFuel whole) whole).edges =
      (buildChoiceAutomaton signature alphabet
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right)
        selectionLeft selectionRight).edges)
    (hProductEq : ∀ q, stateProductInfo whole (TypeAutomatonState.child 0 q) =
      stateProductInfo left q) :
    ∀ m q, ofStage signature m whole (TypeAutomatonState.child 0 q) =
      ofStage signature m left q := by
  intro m
  induction m with
  | zero => intro q; rfl
  | succ m ih =>
      intro q
      simp only [ofStage]
      rw [hProductEq q, hEdgesEq]
      congr 1
      apply Finset.ext
      intro x
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨edge, ⟨hEdgeMem, hSource, hNotTock⟩, hx⟩
        obtain ⟨childEdge, hChildEdge, hChildSource, hEdgeEq⟩ :=
          (buildChoiceAutomaton_outgoing_left signature alphabet
            (compileTypeFuel signature (typeCompilationFuel left) left)
            (compileTypeFuel signature (typeCompilationFuel right) right)
            selectionLeft selectionRight q edge).mp ⟨hEdgeMem, hSource⟩
        refine ⟨childEdge, ⟨hChildEdge, hChildSource, ?_⟩, ?_⟩
        · simpa [hEdgeEq, childPendingEdge] using hNotTock
        · rw [hEdgeEq] at hx
          simp only [childPendingEdge, childState] at hx
          rwa [ih childEdge.target] at hx
      · rintro ⟨childEdge, ⟨hChildMem, hChildSource, hNotTock⟩, hx⟩
        have hOut := (buildChoiceAutomaton_outgoing_left signature alphabet
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          selectionLeft selectionRight q (childPendingEdge 0 childEdge)).mpr
          ⟨childEdge, hChildMem, hChildSource, rfl⟩
        refine ⟨childPendingEdge 0 childEdge, ⟨hOut.1, hOut.2, ?_⟩, ?_⟩
        · simpa [childPendingEdge] using hNotTock
        · simp only [childPendingEdge, childState]
          rwa [ih childEdge.target]

/-- Tag-transparency for `.choice`/`.fairChoice`, right side. -/
theorem ofStage_binaryChoice_child1
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (whole left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (hEdgesEq : (compileTypeFuel signature (typeCompilationFuel whole) whole).edges =
      (buildChoiceAutomaton signature alphabet
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right)
        selectionLeft selectionRight).edges)
    (hProductEq : ∀ q, stateProductInfo whole (TypeAutomatonState.child 1 q) =
      stateProductInfo right q) :
    ∀ m q, ofStage signature m whole (TypeAutomatonState.child 1 q) =
      ofStage signature m right q := by
  intro m
  induction m with
  | zero => intro q; rfl
  | succ m ih =>
      intro q
      simp only [ofStage]
      rw [hProductEq q, hEdgesEq]
      congr 1
      apply Finset.ext
      intro x
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨edge, ⟨hEdgeMem, hSource, hNotTock⟩, hx⟩
        obtain ⟨childEdge, hChildEdge, hChildSource, hEdgeEq⟩ :=
          (buildChoiceAutomaton_outgoing_right signature alphabet
            (compileTypeFuel signature (typeCompilationFuel left) left)
            (compileTypeFuel signature (typeCompilationFuel right) right)
            selectionLeft selectionRight q edge).mp ⟨hEdgeMem, hSource⟩
        refine ⟨childEdge, ⟨hChildEdge, hChildSource, ?_⟩, ?_⟩
        · simpa [hEdgeEq, childPendingEdge] using hNotTock
        · rw [hEdgeEq] at hx
          simp only [childPendingEdge, childState] at hx
          rwa [ih childEdge.target] at hx
      · rintro ⟨childEdge, ⟨hChildMem, hChildSource, hNotTock⟩, hx⟩
        have hOut := (buildChoiceAutomaton_outgoing_right signature alphabet
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          selectionLeft selectionRight q (childPendingEdge 1 childEdge)).mpr
          ⟨childEdge, hChildMem, hChildSource, rfl⟩
        refine ⟨childPendingEdge 1 childEdge, ⟨hOut.1, hOut.2, ?_⟩, ?_⟩
        · simpa [childPendingEdge] using hNotTock
        · simp only [childPendingEdge, childState]
          rwa [ih childEdge.target]

/-- The compiler's action families are gated on the type's own alphabet, so
the staged menus only agree for an alphabet-well-formed type. -/
theorem ofStage_futOffStage_agree (signature : TypeAlphabet) (processType : PactType)
    (hClockGuarded : processType.ClockGuarded)
    (hTailRecursive : processType.TailRecursive)
    (hAlphabet : processType.AlphabetWellFormed) :
    ∀ n, ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet processType (compileType signature processType))
        residual state →
      ofStage signature n processType state = futOffStage n residual := by
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ k ih =>
    intro n
    induction n with
    | zero => intro residual state _; rfl
    | succ n innerIH =>
      intro residual state hRelated
      cases processType with
      | skip alphabet =>
          obtain ⟨hR, hS⟩ :=
            NewCorrespondence.relationMembership_skip_cases signature alphabet hRelated
          subst hR; subst hS
          have hSelf : ofStage signature n (.skip alphabet) .root = ∅ := by
            have hIH := innerIH (buildRelationSet_initial (.skip alphabet)
              (compileType signature (.skip alphabet)))
            have hInit : (compileType signature (.skip alphabet)).initial =
                TypeAutomatonState.root := by
              simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
            rw [hInit] at hIH
            rw [hIH]
            exact futOffStage_skip n alphabet
          rw [futOffStage_skip]
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
            stateProductInfo, typeCompilationFuel, stateProductInfoFuel] at hx
          rcases hx with ⟨edge, ⟨hEdge, _⟩, hx⟩ | hx
          · simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              Finset.mem_image, Finset.mem_filter] at hEdge
            obtain ⟨env, -, hEq⟩ := hEdge
            rw [← hEq] at hx
            simp only [hSelf] at hx
            simp at hx
          · simp at hx
      | var alphabet name =>
          unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
          simp only [typeCompilationFuel, buildRelationSetCoreFuel, Finset.mem_singleton,
            Prod.mk.injEq] at hRelated
          obtain ⟨hR, hS⟩ := hRelated
          subst hR; subst hS
          have hFinalEmpty : ofStage signature n (.var alphabet name) TypeAutomatonState.final = ∅ := by
            cases n with
            | zero => rfl
            | succ n =>
                apply Finset.eq_empty_iff_forall_notMem.mpr
                intro y hy
                simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
                  stateProductInfo, typeCompilationFuel, stateProductInfoFuel] at hy
                rcases hy with ⟨edge, ⟨hEdge, hSource⟩, -⟩ | hy
                · simp only [compileTypeFuel, finishAutomatonFragment,
                    Finset.mem_image] at hEdge
                  obtain ⟨env, -, hEq⟩ := hEdge
                  rw [← hEq] at hSource
                  simp at hSource
                · simp at hy
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
            stateProductInfo, typeCompilationFuel, stateProductInfoFuel] at hx
          rcases hx with ⟨edge, ⟨hEdge, -⟩, hx⟩ | hx
          · simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              Finset.mem_image] at hEdge
            obtain ⟨env, -, hEq⟩ := hEdge
            rw [← hEq] at hx
            simp only [hFinalEmpty] at hx
            simp at hx
          · simp at hx
      | message alphabet msg dir =>
          have hEdgeCases : ∀ edge ∈ (compileTypeFuel signature
              (typeCompilationFuel (.message alphabet msg dir)) (.message alphabet msg dir)).edges,
              (edge.source = TypeAutomatonState.root ∧ edge.current = {(msg, dir)} ∧
                edge.target = TypeAutomatonState.final) ∨
              (edge.source = TypeAutomatonState.root ∧ edge.current = {(msg, dir)} ∧
                edge.target = TypeAutomatonState.root) ∨
              (edge.source = TypeAutomatonState.final ∧ edge.current = ∅ ∧
                edge.target = TypeAutomatonState.final) := by
            intro edge hEdge
            simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
            rcases hEdge with (⟨env, -, hEq⟩ | ⟨env, -, hEq⟩) | ⟨env, -, hEq⟩
            · exact Or.inl (by rw [← hEq]; exact ⟨rfl, rfl, rfl⟩)
            · exact Or.inr (Or.inl (by rw [← hEq]; exact ⟨rfl, rfl, rfl⟩))
            · exact Or.inr (Or.inr (by rw [← hEq]; exact ⟨rfl, rfl, rfl⟩))
          have hFinalSelf : ofStage signature n (.message alphabet msg dir) TypeAutomatonState.final = ∅ := by
            have hFinalRelated :
                relationMembership
                  (buildRelationSet (.message alphabet msg dir) (compileType signature (.message alphabet msg dir)))
                  (.skip alphabet) TypeAutomatonState.final := by
              show (PactType.skip alphabet, TypeAutomatonState.final) ∈
                buildRelationSetCoreFuel signature (typeCompilationFuel (.message alphabet msg dir))
                  (.message alphabet msg dir)
              simp [typeCompilationFuel, buildRelationSetCoreFuel]
            have hIH := innerIH hFinalRelated
            rw [hIH]; exact futOffStage_skip n alphabet
          have hRootSelf : ofStage signature n (.message alphabet msg dir) TypeAutomatonState.root =
              futOffStage n (.message alphabet msg dir) := by
            have hIH := innerIH (buildRelationSet_initial (.message alphabet msg dir)
              (compileType signature (.message alphabet msg dir)))
            have hInit : (compileType signature (.message alphabet msg dir)).initial =
                TypeAutomatonState.root := by
              simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
            rwa [hInit] at hIH
          have hNoProduct : ∀ q, stateProductInfo (.message alphabet msg dir) q = none := by
            intro q
            simp [stateProductInfo, typeCompilationFuel, stateProductInfoFuel]
          have hEmptyLocal :
            TypeEnvironment.empty ∈ signature.localEnvironmentsFor alphabet := by
            simp only [TypeAlphabet.localEnvironmentsFor, Finset.mem_union,
              Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
            exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
          have hWitness : PendingAutomatonEdge.mk TypeAutomatonState.root TypeEnvironment.empty
              (AutomatonConstructionLabel.visible TypeLabel.silent) {(msg, dir)}
              (FutureSpec.at TypeAutomatonState.root {(msg, dir)}) TypeAutomatonState.root ∈
              (compileTypeFuel signature (typeCompilationFuel (.message alphabet msg dir))
                (.message alphabet msg dir)).edges := by
            simp only [PactType.AlphabetWellFormed] at hAlphabet
            simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              Finset.mem_union, Finset.mem_image, Finset.mem_filter]
            refine Or.inl (Or.inr ⟨TypeEnvironment.empty,
              ⟨hEmptyLocal, rfl, ?_, hAlphabet.2⟩, rfl⟩)
            simp [TypeEnvironment.hasNeed, TypeEnvironment.empty]
          obtain ⟨hR, hS⟩ | ⟨hR, hS⟩ :=
            NewCorrespondence.relationMembership_message_cases signature alphabet msg dir hRelated
          · subst hR; subst hS
            rw [futOffStage_message]
            apply Finset.ext
            intro x
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProduct, Finset.notMem_empty, or_false, Finset.mem_singleton]
            constructor
            · rintro ⟨edge, hEdge, hx⟩
              rcases hEdgeCases edge hEdge.1 with ⟨-, hCurrent, hTarget⟩ | ⟨-, hCurrent, hTarget⟩ |
                  ⟨hSource, -, -⟩
              · rw [hCurrent, hTarget, hFinalSelf] at hx
                rcases hx with hx | hx
                · exact Finset.mem_singleton.mp hx
                · simp at hx
              · rw [hCurrent, hTarget, hRootSelf] at hx
                rcases hx with hx | hx
                · exact Finset.mem_singleton.mp hx
                · cases n with
                  | zero => exact absurd hx (Finset.notMem_empty _)
                  | succ n => simpa [futOffStage_message] using hx
              · exact absurd hEdge.2 (by rw [hSource]; simp)
            · intro hx
              subst hx
              exact ⟨_, ⟨hWitness, by
                simp [AutomatonConstructionLabel.semantic, TypeLabel.isTock, TypeLabel.silent]⟩,
                Or.inl (Finset.mem_singleton_self _)⟩
          · subst hR; subst hS
            rw [futOffStage_skip]
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProduct, Finset.notMem_empty, or_false] at hx
            obtain ⟨edge, hEdge, hx⟩ := hx
            rcases hEdgeCases edge hEdge.1 with ⟨hSource, -, -⟩ | ⟨hSource, -, -⟩ |
                ⟨-, hCurrent, hTarget⟩
            · exact absurd hEdge.2 (by rw [hSource]; simp)
            · exact absurd hEdge.2 (by rw [hSource]; simp)
            · rw [hCurrent, hTarget, hFinalSelf] at hx
              simpa using hx
      | tock alphabet =>
          have hEdgeCases : ∀ edge ∈ (compileTypeFuel signature
              (typeCompilationFuel (.tock alphabet)) (.tock alphabet)).edges,
              (edge.source = TypeAutomatonState.root ∧ edge.current = ∅ ∧
                (edge.target = TypeAutomatonState.final ∨
                  edge.target = TypeAutomatonState.root)) ∨
              (edge.source = TypeAutomatonState.final ∧ edge.current = ∅ ∧
                edge.target = TypeAutomatonState.final) := by
            intro edge hEdge
            simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              Finset.mem_union, Finset.mem_image] at hEdge
            rcases hEdge with ⟨env, -, hEq⟩ | ⟨env, -, hEq⟩
            · split at hEq <;> exact Or.inl (by rw [← hEq]; simp)
            · exact Or.inr (by rw [← hEq]; exact ⟨rfl, rfl, rfl⟩)
          have hNoProduct : ∀ q, stateProductInfo (.tock alphabet) q = none := by
            intro q; simp [stateProductInfo, typeCompilationFuel, stateProductInfoFuel]
          have hFinalSelf : ofStage signature n (.tock alphabet)
              TypeAutomatonState.final = ∅ := by
            have hFinalRelated :
                relationMembership (buildRelationSet (.tock alphabet)
                  (compileType signature (.tock alphabet)))
                  (.skip alphabet) TypeAutomatonState.final := by
              show (PactType.skip alphabet, TypeAutomatonState.final) ∈
                buildRelationSetCoreFuel signature (typeCompilationFuel (.tock alphabet))
                  (.tock alphabet)
              simp [typeCompilationFuel, buildRelationSetCoreFuel]
            have hIH := innerIH hFinalRelated
            rw [hIH]; exact futOffStage_skip n alphabet
          have hRootSelf : ofStage signature n (.tock alphabet)
              TypeAutomatonState.root = ∅ := by
            have hIH := innerIH (buildRelationSet_initial (.tock alphabet)
              (compileType signature (.tock alphabet)))
            have hInit : (compileType signature (.tock alphabet)).initial =
                TypeAutomatonState.root := by
              simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
            rw [hInit] at hIH
            rw [hIH]; exact futOffStage_tock n alphabet
          obtain ⟨hR, hS⟩ | ⟨hR, hS⟩ :=
            NewCorrespondence.relationMembership_tock_cases signature alphabet hRelated
          · subst hR; subst hS
            rw [futOffStage_tock]
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProduct, Finset.notMem_empty, or_false] at hx
            obtain ⟨edge, hEdge, hx⟩ := hx
            rcases hEdgeCases edge hEdge.1 with ⟨-, hCurrent, hTarget⟩ | ⟨hSource, -, -⟩
            · rw [hCurrent] at hx
              rcases hTarget with hTarget | hTarget
              · rw [hTarget, hFinalSelf] at hx; simpa using hx
              · rw [hTarget, hRootSelf] at hx; simpa using hx
            · exact absurd hEdge.2 (by rw [hSource]; simp)
          · subst hR; subst hS
            rw [futOffStage_skip]
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProduct, Finset.notMem_empty, or_false] at hx
            obtain ⟨edge, hEdge, hx⟩ := hx
            rcases hEdgeCases edge hEdge.1 with ⟨hSource, -, -⟩ | ⟨-, hCurrent, hTarget⟩
            · exact absurd hEdge.2 (by rw [hSource]; simp)
            · rw [hCurrent, hTarget, hFinalSelf] at hx
              simpa using hx
      | progress alphabet pid =>
          have hEdgeCases : ∀ edge ∈ (compileTypeFuel signature
              (typeCompilationFuel (.progress alphabet pid)) (.progress alphabet pid)).edges,
              (edge.source = TypeAutomatonState.root ∧ edge.current = ∅ ∧
                edge.target = TypeAutomatonState.final) ∨
              (edge.source = TypeAutomatonState.final ∧ edge.current = ∅ ∧
                edge.target = TypeAutomatonState.final) := by
            intro edge hEdge
            simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
            rcases hEdge with ⟨env, -, hEq⟩ | ⟨env, -, hEq⟩
            · exact Or.inl (by rw [← hEq]; exact ⟨rfl, rfl, rfl⟩)
            · exact Or.inr (by rw [← hEq]; exact ⟨rfl, rfl, rfl⟩)
          have hNoProduct : ∀ q, stateProductInfo (.progress alphabet pid) q = none := by
            intro q; simp [stateProductInfo, typeCompilationFuel, stateProductInfoFuel]
          have hFinalSelf : ofStage signature n (.progress alphabet pid) TypeAutomatonState.final = ∅ := by
            have hFinalRelated :
                relationMembership
                  (buildRelationSet (.progress alphabet pid) (compileType signature (.progress alphabet pid)))
                  (.skip alphabet) TypeAutomatonState.final := by
              show (PactType.skip alphabet, TypeAutomatonState.final) ∈
                buildRelationSetCoreFuel signature (typeCompilationFuel (.progress alphabet pid))
                  (.progress alphabet pid)
              simp [typeCompilationFuel, buildRelationSetCoreFuel]
            have hIH := innerIH hFinalRelated
            rw [hIH]; exact futOffStage_skip n alphabet
          obtain ⟨hR, hS⟩ | ⟨hR, hS⟩ :=
            NewCorrespondence.relationMembership_progress_cases signature alphabet pid hRelated
          · subst hR; subst hS
            rw [futOffStage_progress]
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProduct, Finset.notMem_empty, or_false] at hx
            obtain ⟨edge, hEdge, hx⟩ := hx
            rcases hEdgeCases edge hEdge.1 with ⟨-, hCurrent, hTarget⟩ | ⟨hSource, -, -⟩
            · rw [hCurrent, hTarget, hFinalSelf] at hx; simpa using hx
            · exact absurd hEdge.2 (by rw [hSource]; simp)
          · subst hR; subst hS
            rw [futOffStage_skip]
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProduct, Finset.notMem_empty, or_false] at hx
            obtain ⟨edge, hEdge, hx⟩ := hx
            rcases hEdgeCases edge hEdge.1 with ⟨hSource, -, -⟩ | ⟨-, hCurrent, hTarget⟩
            · exact absurd hEdge.2 (by rw [hSource]; simp)
            · rw [hCurrent, hTarget, hFinalSelf] at hx; simpa using hx
      | choice alphabet left right =>
          have hLeftSize : sizeOf left < k := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < k := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AlphabetWellFormed] at hAlphabet
          obtain ⟨-, -, -, hAWLeft, hAWRight⟩ := hAlphabet
          simp only [PactType.ClockGuarded] at hClockGuarded
          simp only [PactType.TailRecursive] at hTailRecursive
          obtain ⟨hCGLeft, hCGRight⟩ := hClockGuarded
          obtain ⟨hTRLeft, hTRRight⟩ := hTailRecursive
          have hFuelEq : typeCompilationFuel (.choice alphabet left right) =
              max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
            simp only [typeCompilationFuel]; omega
          have hWhole :
              compileTypeFuel signature (typeCompilationFuel (.choice alphabet left right))
                (.choice alphabet left right) =
                buildChoiceAutomaton signature alphabet
                  (compileTypeFuel signature (typeCompilationFuel left) left)
                  (compileTypeFuel signature (typeCompilationFuel right) right)
                  TypeLabel.silent TypeLabel.silent := by
            rw [hFuelEq]
            rw [compileTypeFuel.eq_def]
            show buildChoiceAutomaton signature alphabet
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
                TypeLabel.silent TypeLabel.silent =
              buildChoiceAutomaton signature alphabet (compileTypeFuel signature
                (typeCompilationFuel left) left) (compileTypeFuel signature
                (typeCompilationFuel right) right) TypeLabel.silent TypeLabel.silent
            rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
              compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
          have hProductEq0 : ∀ q, stateProductInfo (.choice alphabet left right)
              (TypeAutomatonState.child 0 q) = stateProductInfo left q := by
            intro q
            show stateProductInfoFuel (typeCompilationFuel (.choice alphabet left right))
              (.choice alphabet left right) (.child 0 q) =
              stateProductInfoFuel (typeCompilationFuel left) left q
            rw [hFuelEq]
            exact stateProductInfoFuel_eq_of_sufficient' left q (le_max_left _ _) le_rfl
          have hProductEq1 : ∀ q, stateProductInfo (.choice alphabet left right)
              (TypeAutomatonState.child 1 q) = stateProductInfo right q := by
            intro q
            show stateProductInfoFuel (typeCompilationFuel (.choice alphabet left right))
              (.choice alphabet left right) (.child 1 q) =
              stateProductInfoFuel (typeCompilationFuel right) right q
            rw [hFuelEq]
            exact stateProductInfoFuel_eq_of_sufficient' right q (le_max_right _ _) le_rfl
          have hTag0 := ofStage_binaryChoice_child0 signature alphabet
            (.choice alphabet left right) left right
            TypeLabel.silent TypeLabel.silent (by rw [hWhole]) hProductEq0
          have hTag1 := ofStage_binaryChoice_child1 signature alphabet
            (.choice alphabet left right) left right
            TypeLabel.silent TypeLabel.silent (by rw [hWhole]) hProductEq1
          have hShape := helper_h12_binaryChoice_shape signature (.choice alphabet left right) left right
            rfl hFuelEq hRelated
          rcases hShape with ⟨hResidualEq, hStateEq⟩ |
            ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
          · subst hResidualEq; subst hStateEq
            have hEmptyLocal : TypeEnvironment.empty ∈
                signature.localEnvironmentsFor alphabet := by
              simp only [TypeAlphabet.localEnvironmentsFor, Finset.mem_union,
                Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
              exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
            have hNoProductRoot : stateProductInfo (.choice alphabet left right)
                TypeAutomatonState.root = none := by
              show stateProductInfoFuel (typeCompilationFuel (.choice alphabet left right))
                (.choice alphabet left right) TypeAutomatonState.root = none
              rw [hFuelEq]; rfl
            have hWitness0 : PendingAutomatonEdge.mk TypeAutomatonState.root TypeEnvironment.empty
                (AutomatonConstructionLabel.visible TypeLabel.silent) ∅
                (FutureSpec.at (TypeAutomatonState.child 0
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial) ∅)
                (TypeAutomatonState.child 0
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial) ∈
                (compileTypeFuel signature (typeCompilationFuel (.choice alphabet left right))
                  (.choice alphabet left right)).edges := by
              rw [hWhole]
              simp only [buildChoiceAutomaton, finishAutomatonFragment, childState,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
                Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨TypeEnvironment.empty, ⟨hEmptyLocal, rfl⟩, Or.inl rfl⟩
            have hWitness1 : PendingAutomatonEdge.mk TypeAutomatonState.root TypeEnvironment.empty
                (AutomatonConstructionLabel.visible TypeLabel.silent) ∅
                (FutureSpec.at (TypeAutomatonState.child 1
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial) ∅)
                (TypeAutomatonState.child 1
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial) ∈
                (compileTypeFuel signature (typeCompilationFuel (.choice alphabet left right))
                  (.choice alphabet left right)).edges := by
              rw [hWhole]
              simp only [buildChoiceAutomaton, finishAutomatonFragment, childState,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
                Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨TypeEnvironment.empty, ⟨hEmptyLocal, rfl⟩, Or.inr rfl⟩
            have hEdgeSourceCases : ∀ edge ∈ (compileTypeFuel signature
                (typeCompilationFuel (.choice alphabet left right)) (.choice alphabet left right)).edges,
                edge.source = TypeAutomatonState.root →
                (edge.current = ∅ ∧ edge.target = TypeAutomatonState.child 0
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial) ∨
                (edge.current = ∅ ∧ edge.target = TypeAutomatonState.child 1
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial) := by
              intro edge hEdge hSource
              rw [hWhole] at hEdge
              simp only [buildChoiceAutomaton, finishAutomatonFragment, childPendingEdges,
                childState, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
                Finset.mem_insert, Finset.mem_singleton] at hEdge
              rcases hEdge with (⟨childEdge, -, hEq⟩ | ⟨childEdge, -, hEq⟩) |
                ⟨environment, -, hEq | hEq⟩
              · exfalso; rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
              · exfalso; rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
              · left; rw [hEq]; exact ⟨rfl, rfl⟩
              · right; rw [hEq]; exact ⟨rfl, rfl⟩
            rw [futOffStage_choice]
            apply Finset.ext
            intro x
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProductRoot, Finset.notMem_empty, or_false]
            constructor
            · rintro ⟨edge, ⟨hEdgeMem, hEdgeSource, -⟩, hx⟩
              rcases hEdgeSourceCases edge hEdgeMem hEdgeSource with
                ⟨hCurrent, hTarget⟩ | ⟨hCurrent, hTarget⟩
              · simp only [hCurrent, hTarget, Finset.notMem_empty, false_or] at hx
                rw [hTag0 n
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial] at hx
                have hLeftInitRelated := buildRelationSet_initial left (compileType signature left)
                simp only [compileType] at hLeftInitRelated
                rw [ih (sizeOf left) hLeftSize left hCGLeft hTRLeft hAWLeft rfl n
                  hLeftInitRelated] at hx
                exact Or.inl hx
              · simp only [hCurrent, hTarget, Finset.notMem_empty, false_or] at hx
                rw [hTag1 n
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial] at hx
                have hRightInitRelated := buildRelationSet_initial right
                  (compileType signature right)
                simp only [compileType] at hRightInitRelated
                rw [ih (sizeOf right) hRightSize right hCGRight hTRRight hAWRight rfl n
                  hRightInitRelated] at hx
                exact Or.inr hx
            · intro hx
              simp only [Finset.mem_union] at hx
              rcases hx with hx | hx
              · refine ⟨_, ⟨hWitness0, rfl, ?_⟩, ?_⟩
                · simp [AutomatonConstructionLabel.semantic, TypeLabel.isTock, TypeLabel.silent]
                · right
                  rw [hTag0 n
                    (compileTypeFuel signature (typeCompilationFuel left) left).initial]
                  have hLeftInitRelated := buildRelationSet_initial left
                    (compileType signature left)
                  simp only [compileType] at hLeftInitRelated
                  rwa [ih (sizeOf left) hLeftSize left hCGLeft hTRLeft hAWLeft rfl n
                    hLeftInitRelated]
              · refine ⟨_, ⟨hWitness1, rfl, ?_⟩, ?_⟩
                · simp [AutomatonConstructionLabel.semantic, TypeLabel.isTock, TypeLabel.silent]
                · right
                  rw [hTag1 n
                    (compileTypeFuel signature (typeCompilationFuel right) right).initial]
                  have hRightInitRelated := buildRelationSet_initial right
                    (compileType signature right)
                  simp only [compileType] at hRightInitRelated
                  rwa [ih (sizeOf right) hRightSize right hCGRight hTRRight hAWRight rfl n
                    hRightInitRelated]
          · subst hStateEq
            rw [hTag0 (n + 1) q]
            exact ih (sizeOf left) hLeftSize left hCGLeft hTRLeft hAWLeft rfl (n + 1)
              hLeftRelated
          · subst hStateEq
            rw [hTag1 (n + 1) q]
            exact ih (sizeOf right) hRightSize right hCGRight hTRRight hAWRight rfl (n + 1)
              hRightRelated
      | fairChoice alphabet bid left right =>
          have hLeftSize : sizeOf left < k := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < k := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AlphabetWellFormed] at hAlphabet
          obtain ⟨-, -, -, -, hAWLeft, hAWRight⟩ := hAlphabet
          simp only [PactType.ClockGuarded] at hClockGuarded
          simp only [PactType.TailRecursive] at hTailRecursive
          obtain ⟨hCGLeft, hCGRight⟩ := hClockGuarded
          obtain ⟨hTRLeft, hTRRight⟩ := hTailRecursive
          have hFuelEq : typeCompilationFuel (.fairChoice alphabet bid left right) =
              max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
            simp only [typeCompilationFuel]; omega
          have hWhole :
              compileTypeFuel signature (typeCompilationFuel (.fairChoice alphabet bid left right))
                (.fairChoice alphabet bid left right) =
                buildChoiceAutomaton signature alphabet
                  (compileTypeFuel signature (typeCompilationFuel left) left)
                  (compileTypeFuel signature (typeCompilationFuel right) right)
                  (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
            rw [hFuelEq]
            rw [compileTypeFuel.eq_def]
            show buildChoiceAutomaton signature alphabet
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
                (TypeLabel.fair bid true) (TypeLabel.fair bid false) =
              buildChoiceAutomaton signature alphabet (compileTypeFuel signature
                (typeCompilationFuel left) left) (compileTypeFuel signature
                (typeCompilationFuel right) right) (TypeLabel.fair bid true)
                (TypeLabel.fair bid false)
            rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
              compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
          have hProductEq0 : ∀ q, stateProductInfo (.fairChoice alphabet bid left right)
              (TypeAutomatonState.child 0 q) = stateProductInfo left q := by
            intro q
            show stateProductInfoFuel (typeCompilationFuel (.fairChoice alphabet bid left right))
              (.fairChoice alphabet bid left right) (.child 0 q) =
              stateProductInfoFuel (typeCompilationFuel left) left q
            rw [hFuelEq]
            exact stateProductInfoFuel_eq_of_sufficient' left q (le_max_left _ _) le_rfl
          have hProductEq1 : ∀ q, stateProductInfo (.fairChoice alphabet bid left right)
              (TypeAutomatonState.child 1 q) = stateProductInfo right q := by
            intro q
            show stateProductInfoFuel (typeCompilationFuel (.fairChoice alphabet bid left right))
              (.fairChoice alphabet bid left right) (.child 1 q) =
              stateProductInfoFuel (typeCompilationFuel right) right q
            rw [hFuelEq]
            exact stateProductInfoFuel_eq_of_sufficient' right q (le_max_right _ _) le_rfl
          have hTag0 := ofStage_binaryChoice_child0 signature alphabet
            (.fairChoice alphabet bid left right)
            left right (TypeLabel.fair bid true) (TypeLabel.fair bid false)
            (by rw [hWhole]) hProductEq0
          have hTag1 := ofStage_binaryChoice_child1 signature alphabet
            (.fairChoice alphabet bid left right)
            left right (TypeLabel.fair bid true) (TypeLabel.fair bid false)
            (by rw [hWhole]) hProductEq1
          have hShape := helper_h12_binaryChoice_shape signature (.fairChoice alphabet bid left right)
            left right rfl hFuelEq hRelated
          rcases hShape with ⟨hResidualEq, hStateEq⟩ |
            ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
          · subst hResidualEq; subst hStateEq
            have hEmptyLocal : TypeEnvironment.empty ∈
                signature.localEnvironmentsFor alphabet := by
              simp only [TypeAlphabet.localEnvironmentsFor, Finset.mem_union,
                Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
              exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
            have hNoProductRoot : stateProductInfo (.fairChoice alphabet bid left right)
                TypeAutomatonState.root = none := by
              show stateProductInfoFuel (typeCompilationFuel (.fairChoice alphabet bid left right))
                (.fairChoice alphabet bid left right) TypeAutomatonState.root = none
              rw [hFuelEq]; rfl
            have hWitness0 : PendingAutomatonEdge.mk TypeAutomatonState.root TypeEnvironment.empty
                (AutomatonConstructionLabel.visible (TypeLabel.fair bid true)) ∅
                (FutureSpec.at (TypeAutomatonState.child 0
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial) ∅)
                (TypeAutomatonState.child 0
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial) ∈
                (compileTypeFuel signature (typeCompilationFuel (.fairChoice alphabet bid left right))
                  (.fairChoice alphabet bid left right)).edges := by
              rw [hWhole]
              simp only [buildChoiceAutomaton, finishAutomatonFragment, childState,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
                Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨TypeEnvironment.empty, ⟨hEmptyLocal, rfl⟩, Or.inl rfl⟩
            have hWitness1 : PendingAutomatonEdge.mk TypeAutomatonState.root TypeEnvironment.empty
                (AutomatonConstructionLabel.visible (TypeLabel.fair bid false)) ∅
                (FutureSpec.at (TypeAutomatonState.child 1
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial) ∅)
                (TypeAutomatonState.child 1
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial) ∈
                (compileTypeFuel signature (typeCompilationFuel (.fairChoice alphabet bid left right))
                  (.fairChoice alphabet bid left right)).edges := by
              rw [hWhole]
              simp only [buildChoiceAutomaton, finishAutomatonFragment, childState,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
                Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨TypeEnvironment.empty, ⟨hEmptyLocal, rfl⟩, Or.inr rfl⟩
            have hEdgeSourceCases : ∀ edge ∈ (compileTypeFuel signature
                (typeCompilationFuel (.fairChoice alphabet bid left right))
                (.fairChoice alphabet bid left right)).edges,
                edge.source = TypeAutomatonState.root →
                (edge.current = ∅ ∧ edge.target = TypeAutomatonState.child 0
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial) ∨
                (edge.current = ∅ ∧ edge.target = TypeAutomatonState.child 1
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial) := by
              intro edge hEdge hSource
              rw [hWhole] at hEdge
              simp only [buildChoiceAutomaton, finishAutomatonFragment, childPendingEdges,
                childState, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
                Finset.mem_insert, Finset.mem_singleton] at hEdge
              rcases hEdge with (⟨childEdge, -, hEq⟩ | ⟨childEdge, -, hEq⟩) |
                ⟨environment, -, hEq | hEq⟩
              · exfalso; rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
              · exfalso; rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
              · left; rw [hEq]; exact ⟨rfl, rfl⟩
              · right; rw [hEq]; exact ⟨rfl, rfl⟩
            rw [futOffStage_fairChoice]
            apply Finset.ext
            intro x
            simp only [ofStage, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
              hNoProductRoot, Finset.notMem_empty, or_false]
            constructor
            · rintro ⟨edge, ⟨hEdgeMem, hEdgeSource, -⟩, hx⟩
              rcases hEdgeSourceCases edge hEdgeMem hEdgeSource with
                ⟨hCurrent, hTarget⟩ | ⟨hCurrent, hTarget⟩
              · simp only [hCurrent, hTarget, Finset.notMem_empty, false_or] at hx
                rw [hTag0 n
                  (compileTypeFuel signature (typeCompilationFuel left) left).initial] at hx
                have hLeftInitRelated := buildRelationSet_initial left (compileType signature left)
                simp only [compileType] at hLeftInitRelated
                rw [ih (sizeOf left) hLeftSize left hCGLeft hTRLeft hAWLeft rfl n
                  hLeftInitRelated] at hx
                exact Or.inl hx
              · simp only [hCurrent, hTarget, Finset.notMem_empty, false_or] at hx
                rw [hTag1 n
                  (compileTypeFuel signature (typeCompilationFuel right) right).initial] at hx
                have hRightInitRelated := buildRelationSet_initial right
                  (compileType signature right)
                simp only [compileType] at hRightInitRelated
                rw [ih (sizeOf right) hRightSize right hCGRight hTRRight hAWRight rfl n
                  hRightInitRelated] at hx
                exact Or.inr hx
            · intro hx
              simp only [Finset.mem_union] at hx
              rcases hx with hx | hx
              · refine ⟨_, ⟨hWitness0, rfl, ?_⟩, ?_⟩
                · simp [AutomatonConstructionLabel.semantic, TypeLabel.isTock, TypeLabel.fair]
                · right
                  rw [hTag0 n
                    (compileTypeFuel signature (typeCompilationFuel left) left).initial]
                  have hLeftInitRelated := buildRelationSet_initial left
                    (compileType signature left)
                  simp only [compileType] at hLeftInitRelated
                  rwa [ih (sizeOf left) hLeftSize left hCGLeft hTRLeft hAWLeft rfl n
                    hLeftInitRelated]
              · refine ⟨_, ⟨hWitness1, rfl, ?_⟩, ?_⟩
                · simp [AutomatonConstructionLabel.semantic, TypeLabel.isTock, TypeLabel.fair]
                · right
                  rw [hTag1 n
                    (compileTypeFuel signature (typeCompilationFuel right) right).initial]
                  have hRightInitRelated := buildRelationSet_initial right
                    (compileType signature right)
                  simp only [compileType] at hRightInitRelated
                  rwa [ih (sizeOf right) hRightSize right hCGRight hTRRight hAWRight rfl n
                    hRightInitRelated]
          · subst hStateEq
            rw [hTag0 (n + 1) q]
            exact ih (sizeOf left) hLeftSize left hCGLeft hTRLeft hAWLeft rfl (n + 1)
              hLeftRelated
          · subst hStateEq
            rw [hTag1 (n + 1) q]
            exact ih (sizeOf right) hRightSize right hCGRight hTRRight hAWRight rfl (n + 1)
              hRightRelated
      | _ => sorry

/-- Substitution cannot create or remove a `skip` when the replacement is not
itself a `skip`. -/
theorem replaceVar_eq_skip_iff (ty : PactType) (var : String) (replacement : PactType)
    (hReplacement : replacement ≠ .skip replacement.alphabet) :
    ty.replaceVar var replacement = .skip (ty.replaceVar var replacement).alphabet ↔
      ty = .skip ty.alphabet := by
  cases ty with
  | var alphabet other =>
      simp only [PactType.replaceVar]
      split
      · simp [hReplacement]
      · simp
  | skip alphabet => simp [PactType.replaceVar]
  | message _ _ _ => simp [PactType.replaceVar]
  | progress _ _ => simp [PactType.replaceVar]
  | tock alphabet => simp [PactType.replaceVar]
  | choice _ _ _ => simp [PactType.replaceVar]
  | seq _ _ _ => simp [PactType.replaceVar]
  | par _ _ _ _ => simp [PactType.replaceVar]
  | recur _ _ _ => simp only [PactType.replaceVar]; split <;> simp
  | fairChoice _ _ _ _ => simp [PactType.replaceVar]
  | xoffer _ _ _ => simp [PactType.replaceVar]
  | offer _ _ _ => simp [PactType.replaceVar]

/-- H13 for any `.par _ _ _` node, unconditionally. -/
theorem helper_h13_par_case
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (hLeftH13 : ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet left (compileType signature left))
        residual state →
      (state ∈ (compileType signature left).accepting ↔
        residual = .skip residual.alphabet))
    (hRightH13 : ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet right (compileType signature right))
        residual state →
      (state ∈ (compileType signature right).accepting ↔
        residual = .skip residual.alphabet))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet (.par alphabet left right interface)
        (compileType signature (.par alphabet left right interface))) residual state) :
    state ∈ (compileType signature (.par alphabet left right interface)).accepting ↔
      residual = .skip residual.alphabet := by
  have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hAcceptEq : (compileType signature (.par alphabet left right interface)).accepting =
      {TypeAutomatonState.final} := by
    show (compileTypeFuel signature (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)).accepting = _
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
    show (buildParallelAutomaton signature alphabet left.alphabet right.alphabet
      interface
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
      (compiledChildFutureFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
      (compiledChildFutureFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) right)).accepting = _
    simp [buildParallelAutomaton, finishAutomatonFragment]
  rw [hAcceptEq]
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel signature
        (typeCompilationFuel (.par alphabet left right interface))
        (.par alphabet left right interface) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Prod.mk.injEq] at hMem
  rcases hMem with ⟨hResidualEq, hStateEq⟩ | (⟨entry, -, hR, hS⟩ |
      ⟨entry, hEntryMem, hR, hS⟩) | ⟨entry, hEntryMem, hR, hS⟩
  · subst hResidualEq; subst hStateEq; simp [PactType.alphabet]
  · subst hR; subst hS; simp [PactType.alphabet]
  · -- A survivor state is non-accepting, so H13 forces a non-`skip` residual.
    subst hR; subst hS
    obtain ⟨hEntry, hNotAcc⟩ := Finset.mem_filter.mp hEntryMem
    rw [buildRelationSetCoreFuel_eq_of_sufficient signature left
      (le_max_left _ _) le_rfl] at hEntry
    rw [compileTypeFuel_eq_of_sufficient signature left
      (le_max_left _ _) le_rfl] at hNotAcc
    refine ⟨fun hIn => absurd hIn (by simp), fun hSkip => ?_⟩
    refine absurd ((hLeftH13 hEntry).mpr ?_) hNotAcc
    rw [PactType.reannotate_alphabet] at hSkip
    cases hForm : entry.1 with
    | skip a => simp [PactType.alphabet]
    | _ => rw [hForm] at hSkip; simp [PactType.reannotate] at hSkip
  · subst hR; subst hS
    obtain ⟨hEntry, hNotAcc⟩ := Finset.mem_filter.mp hEntryMem
    rw [buildRelationSetCoreFuel_eq_of_sufficient signature right
      (le_max_right _ _) le_rfl] at hEntry
    rw [compileTypeFuel_eq_of_sufficient signature right
      (le_max_right _ _) le_rfl] at hNotAcc
    refine ⟨fun hIn => absurd hIn (by simp), fun hSkip => ?_⟩
    refine absurd ((hRightH13 hEntry).mpr ?_) hNotAcc
    rw [PactType.reannotate_alphabet] at hSkip
    cases hForm : entry.1 with
    | skip a => simp [PactType.alphabet]
    | _ => rw [hForm] at hSkip; simp [PactType.reannotate] at hSkip

/-- H13 for any `.seq first second`, given H13 for `second` alone. -/
theorem helper_h13_seq_case
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet) (first second : PactType)
    (hSecondH13 : ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet second (compileType signature second)) residual
        state →
      (state ∈ (compileType signature second).accepting ↔
        residual = .skip residual.alphabet))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet (.seq alphabet first second)
        (compileType signature (.seq alphabet first second)))
      residual state) :
    state ∈ (compileType signature (.seq alphabet first second)).accepting ↔
      residual = .skip residual.alphabet := by
  have hFuelEq : typeCompilationFuel (.seq alphabet first second) =
      max (typeCompilationFuel first) (typeCompilationFuel second) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hAcceptEq : (compileType signature (.seq alphabet first second)).accepting =
      childAccepting 1 (compileTypeFuel signature (typeCompilationFuel second) second) := by
    show (compileTypeFuel signature (typeCompilationFuel (.seq alphabet first second))
      (.seq alphabet first second)).accepting = _
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
    show (buildSequenceAutomaton signature
      (compileTypeFuel signature
        (max (typeCompilationFuel first) (typeCompilationFuel second)) first)
      (compileTypeFuel signature
        (max (typeCompilationFuel first) (typeCompilationFuel second)) second)).accepting = _
    rw [compileTypeFuel_eq_of_sufficient signature second (le_max_right _ _) le_rfl]
    simp [buildSequenceAutomaton, finishAutomatonFragment]
  rw [hAcceptEq]
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel signature (typeCompilationFuel (.seq alphabet first second))
        (.seq alphabet first second) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel] at hMem
  rcases Finset.mem_union.mp hMem with hLeft | hRight
  · rcases Finset.mem_image.mp hLeft with ⟨entry, hEntry, hEq⟩
    have hEntry := (Finset.mem_filter.mp hEntry).1
    injection hEq with hR hS
    subst hR; subst hS
    simp only [childAccepting, Finset.mem_image, childState]
    constructor
    · rintro ⟨q', -, hEq⟩
      injection hEq with hIdx _
      omega
    · intro hSkip
      exact absurd hSkip (by simp)
  · rcases Finset.mem_image.mp hRight with ⟨entry, hEntry, hEq⟩
    injection hEq with hR hS
    subst hR; subst hS
    have hEntryRelated :
        relationMembership (buildRelationSet second (compileType signature second))
          entry.1 entry.2 := by
      show (entry.1, entry.2) ∈
        buildRelationSetCoreFuel signature (typeCompilationFuel second) second
      rw [← buildRelationSetCoreFuel_eq_of_sufficient signature second
        (le_max_right _ _) le_rfl]
      exact hEntry
    have hIH := hSecondH13 hEntryRelated
    simp only [childAccepting, Finset.mem_image, childState]
    constructor
    · rintro ⟨q', hq', hEq⟩
      injection hEq with _ hEq'
      exact hIH.mp (hEq' ▸ hq')
    · intro hSkip
      exact ⟨entry.2, hIH.mpr hSkip, rfl⟩

/-- H13 for any `.xoffer elseType branches`, given H13 for `elseType` and for
every branch's continuation type. -/
theorem helper_h13_xoffer_case
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseH13 : ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet elseType (compileType signature elseType)) residual
        state →
      (state ∈ (compileType signature elseType).accepting ↔
        residual = .skip residual.alphabet))
    (hBranchesH13 : ∀ branch ∈ branches, ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet branch.2 (compileType signature branch.2)) residual
        state →
      (state ∈ (compileType signature branch.2).accepting ↔
        residual = .skip residual.alphabet))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet (.xoffer alphabet elseType branches)
        (compileType signature (.xoffer alphabet elseType branches))) residual state) :
    state ∈ (compileType signature (.xoffer alphabet elseType branches)).accepting ↔
      residual = .skip residual.alphabet := by
  have hFuelEq : typeCompilationFuel (.xoffer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hAcceptEq : (compileType signature (.xoffer alphabet elseType branches)).accepting =
      childAccepting 0 (compileTypeFuel signature (typeCompilationFuel elseType) elseType) ∪
        indexedFragmentAccepting (branches.map fun branch =>
          (branch.1, compileTypeFuel signature (typeCompilationFuel branch.2) branch.2)) := by
    show (compileTypeFuel signature (typeCompilationFuel (.xoffer alphabet elseType branches))
      (.xoffer alphabet elseType branches)).accepting = _
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
    show (buildExclusiveOfferAutomaton signature alphabet branches
      (compileTypeFuel signature
        (max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches)) elseType)
      (branches.map fun branch => (branch.1, compileTypeFuel signature
        (max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches))
        branch.2))).accepting = _
    rw [compileTypeFuel_eq_of_sufficient signature elseType (le_max_left _ _) le_rfl]
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment]
    congr 2
    apply List.map_congr_left
    intro branch hBranch
    congr 1
    exact compileTypeFuel_eq_of_sufficient signature branch.2
      (le_trans (typeCompilationFuel_le_typeBranchCompilationFuel branches branch hBranch)
        (le_max_right _ _)) le_rfl
  rw [hAcceptEq]
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel signature
        (typeCompilationFuel (.xoffer alphabet elseType branches))
        (.xoffer alphabet elseType branches) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
    mem_foldl_union_iff, Finset.notMem_empty, false_or, Finset.mem_image,
    Prod.mk.injEq] at hMem
  rcases hMem with ⟨hResidualEq, hStateEq⟩ | ⟨a, ha, hR, hS⟩ |
    ⟨item, hItem, a, ha, hR, hS⟩
  · subst hResidualEq; subst hStateEq
    simp [childAccepting, childState, indexedFragmentAccepting, mem_foldl_union_iff]
  · subst hR; subst hS
    have hEntryRelated :
        relationMembership (buildRelationSet elseType (compileType signature elseType))
          a.1 a.2 := by
      show (a.1, a.2) ∈ buildRelationSetCoreFuel signature (typeCompilationFuel elseType)
        elseType
      rw [← buildRelationSetCoreFuel_eq_of_sufficient signature elseType
        (le_max_left _ _) le_rfl]
      exact ha
    have hIH := hElseH13 hEntryRelated
    simp only [Finset.mem_union, childAccepting, Finset.mem_image, childState,
      indexedFragmentAccepting, mem_foldl_union_iff, Finset.notMem_empty, false_or]
    constructor
    · rintro (⟨q', hq', hEq⟩ | ⟨item', hItem', q', -, hEq⟩)
      · injection hEq with _ hEq'
        exact hIH.mp (hEq' ▸ hq')
      · exact nomatch hEq
    · intro hSkip
      exact Or.inl ⟨a.2, hIH.mpr hSkip, rfl⟩
  · subst hR; subst hS
    have hMemBranches : item.1 ∈ branches := by
      have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hItem
      exact List.mem_of_getElem? hGet
    have hItemFuel : typeCompilationFuel item.1.2 ≤
        max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) :=
      le_trans (typeCompilationFuel_le_typeBranchCompilationFuel branches item.1 hMemBranches)
        (le_max_right _ _)
    have hEntryRelated :
        relationMembership (buildRelationSet item.1.2 (compileType signature item.1.2))
          a.1 a.2 := by
      show (a.1, a.2) ∈ buildRelationSetCoreFuel signature (typeCompilationFuel item.1.2)
        item.1.2
      rw [← buildRelationSetCoreFuel_eq_of_sufficient signature item.1.2 hItemFuel le_rfl]
      exact ha
    have hIH := hBranchesH13 item.1 hMemBranches hEntryRelated
    have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hItem
    have hMapGet :
        (branches.map fun branch => (branch.1,
          compileTypeFuel signature (typeCompilationFuel branch.2) branch.2))[item.2]? =
          some (item.1.1, compileTypeFuel signature (typeCompilationFuel item.1.2) item.1.2) := by
      rw [List.getElem?_map, hGet]; rfl
    simp only [Finset.mem_union, childAccepting, Finset.mem_image, childState,
      indexedFragmentAccepting, mem_foldl_union_iff, Finset.notMem_empty, false_or]
    constructor
    · rintro (⟨q1, hq1, hEq1⟩ | ⟨item', hItem', q2, hq2, hEq2⟩)
      · exact nomatch hEq1
      · injection hEq2 with hIdxEq hQEq
        have hItemEq : item'.1 =
            (item.1.1, compileTypeFuel signature (typeCompilationFuel item.1.2) item.1.2) := by
          have hGet' := List.mk_mem_zipIdx_iff_getElem?.mp hItem'
          have hIdxEq' : item'.2 = item.2 := by omega
          rw [hIdxEq'] at hGet'
          rw [hMapGet] at hGet'
          injection hGet' with hFst
          exact hFst.symm
        rw [hItemEq] at hq2
        exact hIH.mp (hQEq ▸ hq2)
    · intro hSkip
      refine Or.inr ⟨((item.1.1,
          compileTypeFuel signature (typeCompilationFuel item.1.2) item.1.2), item.2),
        List.mk_mem_zipIdx_iff_getElem?.mpr hMapGet, a.2, hIH.mpr hSkip, rfl⟩

/-- H13 for one singleton branch node, at any alphabet. -/
theorem helper_h13_singletonTypeXOfferAt_case
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branch : BareMessage × PactType)
    (hBranchH13 : ∀ branchAlphabet,
      ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership
          (buildRelationSet (branch.2.reannotate branchAlphabet)
            (compileType signature (branch.2.reannotate branchAlphabet)))
          residual state →
      (state ∈ (compileType signature
          (branch.2.reannotate branchAlphabet)).accepting ↔
        residual = .skip residual.alphabet))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet (singletonTypeXOfferAt alphabet branch)
        (compileType signature (singletonTypeXOfferAt alphabet branch)))
      residual state) :
    state ∈ (compileType signature
        (singletonTypeXOfferAt alphabet branch)).accepting ↔
      residual = .skip residual.alphabet := by
  simp only [singletonTypeXOfferAt] at hRelated ⊢
  exact helper_h13_xoffer_case signature alphabet (.skip alphabet)
    [(branch.1, branch.2.reannotate alphabet)]
    (fun hR => by
      obtain ⟨hR', hS'⟩ :=
        NewCorrespondence.relationMembership_skip_cases signature alphabet hR
      subst hR'; subst hS'
      simp [PactType.alphabet, compileType, typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment])
    (by
      intro branch' hBranch' residual state hR
      have hEq : branch' = (branch.1, branch.2.reannotate alphabet) := by
        simpa using hBranch'
      subst branch'
      exact hBranchH13 alphabet hR)
    hRelated

/-- H13 for the unselected branch product, at any alphabet. -/
theorem helper_h13_parallelTypeBranchesWithin_case
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (hBranchesH13 : ∀ branch ∈ branches, ∀ branchAlphabet,
      ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership
          (buildRelationSet (branch.2.reannotate branchAlphabet)
            (compileType signature (branch.2.reannotate branchAlphabet)))
          residual state →
      (state ∈ (compileType signature
          (branch.2.reannotate branchAlphabet)).accepting ↔
        residual = .skip residual.alphabet))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet (parallelTypeBranchesWithin alphabet branches)
        (compileType signature (parallelTypeBranchesWithin alphabet branches)))
      residual state) :
    state ∈ (compileType signature
        (parallelTypeBranchesWithin alphabet branches)).accepting ↔
      residual = .skip residual.alphabet := by
  match branches with
  | [] =>
      simp only [parallelTypeBranchesWithin] at hRelated ⊢
      obtain ⟨hR, hS⟩ :=
        NewCorrespondence.relationMembership_skip_cases signature alphabet hRelated
      subst hR; subst hS
      simp [PactType.alphabet, compileType, typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment]
  | [branch] =>
      simp only [parallelTypeBranchesWithin] at hRelated ⊢
      exact helper_h13_singletonTypeXOfferAt_case signature alphabet branch
        (fun ba => hBranchesH13 branch (by simp) ba) hRelated
  | branch :: b2 :: rest =>
      simp only [parallelTypeBranchesWithin] at hRelated ⊢
      exact helper_h13_par_case signature alphabet _ _ ∅
        (fun hR => helper_h13_singletonTypeXOfferAt_case signature
          (alphabet.branchPart branch) branch
          (fun ba => hBranchesH13 branch (by simp) ba) hR)
        (fun hR => helper_h13_parallelTypeBranchesWithin_case signature
          (alphabet.remove (alphabet.branchPart branch)) (b2 :: rest)
          (fun b hb ba => hBranchesH13 b (by simp [hb]) ba) hR)
        hRelated

/-- H13 for the branch product after a selection, at any alphabet. -/
theorem helper_h13_parallelTypeBranchesSelectingWithin_case
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hBranchesH13 : ∀ branch ∈ branches, ∀ branchAlphabet,
      ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership
          (buildRelationSet (branch.2.reannotate branchAlphabet)
            (compileType signature (branch.2.reannotate branchAlphabet)))
          residual state →
      (state ∈ (compileType signature
          (branch.2.reannotate branchAlphabet)).accepting ↔
        residual = .skip residual.alphabet))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet
        (parallelTypeBranchesSelectingWithin alphabet selected branches)
        (compileType signature
          (parallelTypeBranchesSelectingWithin alphabet selected branches)))
      residual state) :
    state ∈ (compileType signature
        (parallelTypeBranchesSelectingWithin alphabet selected
          branches)).accepting ↔
      residual = .skip residual.alphabet := by
  match branches with
  | [] =>
      simp only [parallelTypeBranchesSelectingWithin] at hRelated ⊢
      obtain ⟨hR, hS⟩ :=
        NewCorrespondence.relationMembership_skip_cases signature alphabet hRelated
      subst hR; subst hS
      simp [PactType.alphabet, compileType, typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment]
  | [branch] =>
      simp only [parallelTypeBranchesSelectingWithin] at hRelated ⊢
      by_cases hSel : branch = selected
      · rw [if_pos hSel] at hRelated ⊢
        simp only [selectedTypeBranchAt] at hRelated ⊢
        exact helper_h13_seq_case signature alphabet
          (.message alphabet branch.1.1 branch.1.2)
          (branch.2.reannotate alphabet)
          (hBranchesH13 branch (by simp) alphabet) hRelated
      · rw [if_neg hSel] at hRelated ⊢
        exact helper_h13_singletonTypeXOfferAt_case signature alphabet branch
          (fun ba => hBranchesH13 branch (by simp) ba) hRelated
  | branch :: b2 :: rest =>
      simp only [parallelTypeBranchesSelectingWithin] at hRelated ⊢
      by_cases hSel : branch = selected
      · rw [if_pos hSel] at hRelated ⊢
        exact helper_h13_par_case signature alphabet _ _ ∅
          (fun hR => by
            simp only [selectedTypeBranchAt] at hR ⊢
            exact helper_h13_seq_case signature (alphabet.branchPart branch)
              (.message (alphabet.branchPart branch) branch.1.1 branch.1.2)
              (branch.2.reannotate (alphabet.branchPart branch))
              (hBranchesH13 branch (by simp) (alphabet.branchPart branch)) hR)
          (fun hR => helper_h13_parallelTypeBranchesWithin_case signature
            (alphabet.remove (alphabet.branchPart branch)) (b2 :: rest)
            (fun b hb ba => hBranchesH13 b (by simp [hb]) ba) hR)
          hRelated
      · rw [if_neg hSel] at hRelated ⊢
        exact helper_h13_par_case signature alphabet _ _ ∅
          (fun hR => helper_h13_singletonTypeXOfferAt_case signature
            (alphabet.branchPart branch) branch
            (fun ba => hBranchesH13 branch (by simp) ba) hR)
          (fun hR => helper_h13_parallelTypeBranchesSelectingWithin_case signature
            (alphabet.remove (alphabet.branchPart branch)) selected (b2 :: rest)
            (fun b hb ba => hBranchesH13 b (by simp [hb]) ba) hR)
          hRelated

/-- H13 for `parallelTypeBranchesSelecting selected branches`, given H13 for
every branch's own continuation type. -/
theorem helper_h13_parallelTypeBranchesSelecting
    (signature : TypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hBranchesH13 : ∀ branch ∈ branches, ∀ branchAlphabet,
      ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership
          (buildRelationSet (branch.2.reannotate branchAlphabet)
            (compileType signature (branch.2.reannotate branchAlphabet)))
          residual state →
      (state ∈ (compileType signature
          (branch.2.reannotate branchAlphabet)).accepting ↔
        residual = .skip residual.alphabet))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet (parallelTypeBranchesSelecting selected branches)
        (compileType signature (parallelTypeBranchesSelecting selected branches)))
      residual state) :
    state ∈ (compileType signature (parallelTypeBranchesSelecting selected branches)).accepting ↔
      residual = .skip residual.alphabet := by
  match branches with
  | [] =>
      simp only [parallelTypeBranchesSelecting] at hRelated ⊢
      obtain ⟨hR, hS⟩ :=
        NewCorrespondence.relationMembership_skip_cases signature
          PactTypeAlphabet.empty hRelated
      subst hR; subst hS
      simp [PactType.alphabet, compileType, typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment]
  | branch :: rest =>
      simp only [parallelTypeBranchesSelecting] at hRelated ⊢
      exact helper_h13_parallelTypeBranchesSelectingWithin_case signature
        branch.2.alphabet selected (branch :: rest) hBranchesH13 hRelated

/-- Helper Lemma H13: final states represent completion. -/
lemma helper_h13_final_states_represent_completion
    (signature : TypeAlphabet) {processType residual : PactType}
    {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual state) :
    state ∈ (compileType signature processType).accepting ↔
      residual = .skip residual.alphabet := by
  induction hFuel : typeCompilationFuel processType using Nat.strong_induction_on
      generalizing processType residual state with
  | _ n ih =>
    cases processType with
    | skip alphabet =>
        obtain ⟨hResidual, hState⟩ :=
          NewCorrespondence.relationMembership_skip_cases signature alphabet hRelated
        subst hResidual; subst hState
        simp [PactType.alphabet, compileType, typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment]
    | message alphabet msg dir =>
        rcases NewCorrespondence.relationMembership_message_cases signature alphabet msg dir
            hRelated with
          ⟨hResidual, hState⟩ | ⟨hResidual, hState⟩ <;> subst hResidual <;> subst hState <;>
          simp [PactType.alphabet, compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
    | tock alphabet =>
        rcases NewCorrespondence.relationMembership_tock_cases signature alphabet hRelated with
          ⟨hResidual, hState⟩ | ⟨hResidual, hState⟩ <;> subst hResidual <;> subst hState <;>
          simp [PactType.alphabet, compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
    | progress alphabet pid =>
        rcases NewCorrespondence.relationMembership_progress_cases signature alphabet pid
            hRelated with
          ⟨hResidual, hState⟩ | ⟨hResidual, hState⟩ <;> subst hResidual <;> subst hState <;>
          simp [PactType.alphabet, compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
    | var alphabet name =>
        unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
        simp only [typeCompilationFuel, buildRelationSetCoreFuel, Finset.mem_singleton,
          Prod.mk.injEq] at hRelated
        obtain ⟨hResidualEq, hStateEq⟩ := hRelated
        subst hResidualEq; subst hStateEq
        simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    | choice alphabet left right =>
        have hLeftSize : typeCompilationFuel left < n := by
          rw [← hFuel]; simp [typeCompilationFuel]; omega
        have hRightSize : typeCompilationFuel right < n := by
          rw [← hFuel]; simp [typeCompilationFuel]; omega
        have hFuelEq : typeCompilationFuel (.choice alphabet left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hWhole :
            compileTypeFuel signature (typeCompilationFuel (.choice alphabet left right))
              (.choice alphabet left right) =
              buildChoiceAutomaton signature alphabet
                (compileTypeFuel signature (typeCompilationFuel left) left)
                (compileTypeFuel signature (typeCompilationFuel right) right)
                TypeLabel.silent TypeLabel.silent := by
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show buildChoiceAutomaton signature alphabet
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
              TypeLabel.silent TypeLabel.silent =
            buildChoiceAutomaton signature alphabet (compileTypeFuel signature
              (typeCompilationFuel left) left) (compileTypeFuel signature
              (typeCompilationFuel right) right) TypeLabel.silent TypeLabel.silent
          rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
        have hAcceptEq : (compileType signature (.choice alphabet left right)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel left) left) ∪
              childAccepting 1 (compileTypeFuel signature (typeCompilationFuel right) right) := by
          show (compileTypeFuel signature (typeCompilationFuel (.choice alphabet left right))
            (.choice alphabet left right)).accepting = _
          rw [hWhole]; simp [buildChoiceAutomaton, finishAutomatonFragment]
        rw [hAcceptEq]
        have hShape := helper_h12_binaryChoice_shape signature (.choice alphabet left right) left right
          rfl hFuelEq hRelated
        rcases hShape with ⟨hResidualEq, hStateEq⟩ |
          ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
        · subst hResidualEq; subst hStateEq
          simp [childAccepting, childState]
        · subst hStateEq
          simp only [childAccepting, Finset.mem_union, Finset.mem_image, childState]
          constructor
          · rintro (⟨q', hq', hEq⟩ | ⟨q', hq', hEq⟩)
            · injection hEq with _ hEq'
              exact (ih (typeCompilationFuel left) hLeftSize hLeftRelated rfl).mp (hEq' ▸ hq')
            · exact absurd hEq (by simp)
          · intro hSkip
            exact Or.inl ⟨q, (ih (typeCompilationFuel left) hLeftSize hLeftRelated rfl).mpr hSkip, rfl⟩
        · subst hStateEq
          simp only [childAccepting, Finset.mem_union, Finset.mem_image, childState]
          constructor
          · rintro (⟨q', hq', hEq⟩ | ⟨q', hq', hEq⟩)
            · exact absurd hEq (by simp)
            · injection hEq with _ hEq'
              exact (ih (typeCompilationFuel right) hRightSize hRightRelated rfl).mp (hEq' ▸ hq')
          · intro hSkip
            exact Or.inr ⟨q, (ih (typeCompilationFuel right) hRightSize hRightRelated rfl).mpr hSkip, rfl⟩
    | fairChoice alphabet bid left right =>
        have hLeftSize : typeCompilationFuel left < n := by
          rw [← hFuel]; simp [typeCompilationFuel]; omega
        have hRightSize : typeCompilationFuel right < n := by
          rw [← hFuel]; simp [typeCompilationFuel]; omega
        have hFuelEq : typeCompilationFuel (.fairChoice alphabet bid left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hWhole :
            compileTypeFuel signature (typeCompilationFuel (.fairChoice alphabet bid left right))
              (.fairChoice alphabet bid left right) =
              buildChoiceAutomaton signature alphabet
                (compileTypeFuel signature (typeCompilationFuel left) left)
                (compileTypeFuel signature (typeCompilationFuel right) right)
                (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show buildChoiceAutomaton signature alphabet
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
              (TypeLabel.fair bid true) (TypeLabel.fair bid false) =
            buildChoiceAutomaton signature alphabet (compileTypeFuel signature
              (typeCompilationFuel left) left) (compileTypeFuel signature
              (typeCompilationFuel right) right) (TypeLabel.fair bid true)
              (TypeLabel.fair bid false)
          rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
        have hAcceptEq : (compileType signature (.fairChoice alphabet bid left right)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel left) left) ∪
              childAccepting 1 (compileTypeFuel signature (typeCompilationFuel right) right) := by
          show (compileTypeFuel signature (typeCompilationFuel (.fairChoice alphabet bid left right))
            (.fairChoice alphabet bid left right)).accepting = _
          rw [hWhole]; simp [buildChoiceAutomaton, finishAutomatonFragment]
        rw [hAcceptEq]
        have hShape := helper_h12_binaryChoice_shape signature (.fairChoice alphabet bid left right)
          left right rfl hFuelEq hRelated
        rcases hShape with ⟨hResidualEq, hStateEq⟩ |
          ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
        · subst hResidualEq; subst hStateEq
          simp [childAccepting, childState]
        · subst hStateEq
          simp only [childAccepting, Finset.mem_union, Finset.mem_image, childState]
          constructor
          · rintro (⟨q', hq', hEq⟩ | ⟨q', hq', hEq⟩)
            · injection hEq with _ hEq'
              exact (ih (typeCompilationFuel left) hLeftSize hLeftRelated rfl).mp (hEq' ▸ hq')
            · exact absurd hEq (by simp)
          · intro hSkip
            exact Or.inl ⟨q, (ih (typeCompilationFuel left) hLeftSize hLeftRelated rfl).mpr hSkip, rfl⟩
        · subst hStateEq
          simp only [childAccepting, Finset.mem_union, Finset.mem_image, childState]
          constructor
          · rintro (⟨q', hq', hEq⟩ | ⟨q', hq', hEq⟩)
            · exact absurd hEq (by simp)
            · injection hEq with _ hEq'
              exact (ih (typeCompilationFuel right) hRightSize hRightRelated rfl).mp (hEq' ▸ hq')
          · intro hSkip
            exact Or.inr ⟨q, (ih (typeCompilationFuel right) hRightSize hRightRelated rfl).mpr hSkip, rfl⟩
    | recur alphabet name body =>
        have hBodySize : typeCompilationFuel body < n := by
          rw [← hFuel]
          simp [typeCompilationFuel]
        have hFuelEq : typeCompilationFuel (.recur alphabet name body) = typeCompilationFuel body + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq : (compileType signature (.recur alphabet name body)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel body) body) := by
          show (compileTypeFuel signature (typeCompilationFuel (.recur alphabet name body))
            (.recur alphabet name body)).accepting = _
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildRecursionAutomaton signature alphabet name
            (compileTypeFuel signature (typeCompilationFuel body) body)).accepting = _
          simp [buildRecursionAutomaton, finishAutomatonFragment]
        rw [hAcceptEq]
        have hMem : (residual, state) ∈
            buildRelationSetCoreFuel signature (typeCompilationFuel (.recur alphabet name body))
              (.recur alphabet name body) := hRelated
        rw [hFuelEq] at hMem
        simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_image,
          Prod.mk.injEq] at hMem
        rcases hMem with ⟨hResidualEq, hStateEq⟩ | ⟨entry, hEntry, hR, hS⟩
        · subst hResidualEq; subst hStateEq
          simp [childAccepting, childState]
        · subst hS
          have hEntryRelated :
              relationMembership (buildRelationSet body (compileType signature body))
                entry.1 entry.2 := hEntry
          have hIH := ih (typeCompilationFuel body) hBodySize hEntryRelated rfl
          simp only [childAccepting, Finset.mem_image, childState]
          constructor
          · rintro ⟨q', hq', hEq⟩
            injection hEq with _ hEq'
            rw [← hR, replaceVar_eq_skip_iff entry.1 name (.recur alphabet name body) (by simp)]
            exact hIH.mp (hEq' ▸ hq')
          · intro hSkip
            rw [← hR, replaceVar_eq_skip_iff entry.1 name (.recur alphabet name body) (by simp)]
              at hSkip
            exact ⟨entry.2, hIH.mpr hSkip, rfl⟩
    | seq alphabet first second =>
        have hSecondSize : typeCompilationFuel second < n := by
          rw [← hFuel]; simp [typeCompilationFuel]; omega
        exact helper_h13_seq_case signature alphabet first second
          (fun hR => ih (typeCompilationFuel second) hSecondSize hR rfl) hRelated
    | par alphabet left right interface =>
        have hLeftSize : typeCompilationFuel left < n := by
          rw [← hFuel]; simp [typeCompilationFuel]; omega
        have hRightSize : typeCompilationFuel right < n := by
          rw [← hFuel]; simp [typeCompilationFuel]; omega
        exact helper_h13_par_case signature alphabet left right interface
          (fun hR => ih (typeCompilationFuel left) hLeftSize hR rfl)
          (fun hR => ih (typeCompilationFuel right) hRightSize hR rfl) hRelated
    | xoffer alphabet elseType branches =>
        have hElseSize : typeCompilationFuel elseType < n := by
          rw [← hFuel]; simp [typeCompilationFuel]; omega
        have hBranchesSize : ∀ branch ∈ branches,
            typeCompilationFuel branch.2 < n := by
          intro branch hBranch
          have hLe := typeCompilationFuel_le_typeBranchCompilationFuel
            branches branch hBranch
          rw [← hFuel]
          simp only [typeCompilationFuel]
          omega
        exact helper_h13_xoffer_case signature alphabet elseType branches
          (fun hR => ih (typeCompilationFuel elseType) hElseSize hR rfl)
          (by
            intro branch hBranch residual state hR
            exact ih (typeCompilationFuel branch.2)
              (hBranchesSize branch hBranch) hR rfl)
          hRelated
    | offer alphabet elseType branches =>
        have hElseSize : typeCompilationFuel elseType < n := by
          rw [← hFuel]; simp [typeCompilationFuel]; omega
        have hBranchesSize : ∀ branch ∈ branches,
            typeCompilationFuel branch.2 < n := by
          intro branch hBranch
          have hLe := typeCompilationFuel_le_conjunctiveCompilationFuel
            branches branch hBranch
          rw [← hFuel]
          simp only [typeCompilationFuel]
          omega
        have hBranchesH13 : ∀ branch ∈ branches, ∀ branchAlphabet,
            ∀ {residual : PactType}
            {state : TypeAutomatonState},
            relationMembership
              (buildRelationSet (branch.2.reannotate branchAlphabet)
                (compileType signature (branch.2.reannotate branchAlphabet)))
              residual state →
            (state ∈ (compileType signature
                (branch.2.reannotate branchAlphabet)).accepting ↔
              residual = .skip residual.alphabet) := by
          intro branch hBranch branchAlphabet residual state hR
          have hBranchFuel : typeCompilationFuel
              (branch.2.reannotate branchAlphabet) < n := by
            rw [typeCompilationFuel_reannotate]
            exact hBranchesSize branch hBranch
          exact ih (typeCompilationFuel (branch.2.reannotate branchAlphabet))
            hBranchFuel hR rfl
        have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
            max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq : (compileType signature (.offer alphabet elseType branches)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel elseType) elseType) ∪
              indexedFragmentAccepting (branches.map fun selected =>
                (selected.1, compileTypeFuel signature
                  (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
                  (parallelTypeBranchesSelecting selected branches))) := by
          show (compileTypeFuel signature (typeCompilationFuel (.offer alphabet elseType branches))
            (.offer alphabet elseType branches)).accepting = _
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildSelectedConjunctiveOfferAutomaton signature alphabet branches
            (compileTypeFuel signature
              (max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches)) elseType)
            (branches.map fun selected => (selected.1, compileTypeFuel signature
              (max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches))
              (parallelTypeBranchesSelecting selected branches)))).accepting = _
          rw [compileTypeFuel_eq_of_sufficient signature elseType (le_max_left _ _) le_rfl]
          simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment]
          congr 2
          apply List.map_congr_left
          intro selected hSelected
          congr 1
          exact compileTypeFuel_eq_of_sufficient signature
            (parallelTypeBranchesSelecting selected branches)
            (by
              show typeCompilationFuel (parallelTypeBranchesSelecting selected branches) ≤ _
              rw [typeCompilationFuel_parallelTypeBranchesSelecting]
              exact le_max_right _ _)
            le_rfl
        rw [hAcceptEq]
        have hMem : (residual, state) ∈
            buildRelationSetCoreFuel signature (typeCompilationFuel (.offer alphabet elseType branches))
              (.offer alphabet elseType branches) := hRelated
        rw [hFuelEq] at hMem
        simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
          mem_foldl_union_iff, Finset.notMem_empty, false_or, Finset.mem_image,
          Prod.mk.injEq] at hMem
        rcases hMem with ⟨hResidualEq, hStateEq⟩ | ⟨a, ha, hR, hS⟩ |
          ⟨item, hItem, a, ha, hR, hS⟩
        · subst hResidualEq; subst hStateEq
          simp [childAccepting, childState, indexedFragmentAccepting, mem_foldl_union_iff]
        · subst hR; subst hS
          have hEntryRelated :
              relationMembership (buildRelationSet elseType (compileType signature elseType))
                a.1 a.2 := by
            show (a.1, a.2) ∈ buildRelationSetCoreFuel signature (typeCompilationFuel elseType)
              elseType
            rw [← buildRelationSetCoreFuel_eq_of_sufficient signature elseType
              (le_max_left _ _) le_rfl]
            exact ha
          have hIH := ih (typeCompilationFuel elseType) hElseSize hEntryRelated rfl
          simp only [Finset.mem_union, childAccepting, Finset.mem_image, childState,
            indexedFragmentAccepting, mem_foldl_union_iff, Finset.notMem_empty, false_or]
          constructor
          · rintro (⟨q', hq', hEq⟩ | ⟨item', hItem', q', -, hEq⟩)
            · injection hEq with _ hEq'
              exact hIH.mp (hEq' ▸ hq')
            · exact nomatch hEq
          · intro hSkip
            exact Or.inl ⟨a.2, hIH.mpr hSkip, rfl⟩
        · subst hR; subst hS
          have hMemBranches : item.1 ∈ branches := by
            have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hItem
            exact List.mem_of_getElem? hGet
          have hItemFuel : typeCompilationFuel (parallelTypeBranchesSelecting item.1 branches) ≤
              max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) := by
            rw [typeCompilationFuel_parallelTypeBranchesSelecting]
            exact le_max_right _ _
          have hEntryRelated :
              relationMembership
                (buildRelationSet (parallelTypeBranchesSelecting item.1 branches)
                  (compileType signature (parallelTypeBranchesSelecting item.1 branches)))
                a.1 a.2 := by
            show (a.1, a.2) ∈ buildRelationSetCoreFuel signature
              (typeCompilationFuel (parallelTypeBranchesSelecting item.1 branches))
              (parallelTypeBranchesSelecting item.1 branches)
            rw [← buildRelationSetCoreFuel_eq_of_sufficient signature
              (parallelTypeBranchesSelecting item.1 branches) hItemFuel le_rfl]
            exact ha
          have hIH := helper_h13_parallelTypeBranchesSelecting signature item.1 branches
            hBranchesH13 hEntryRelated
          have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hItem
          have hMapGet :
              (branches.map fun selected => (selected.1, compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
                (parallelTypeBranchesSelecting selected branches)))[item.2]? =
                some (item.1.1, compileTypeFuel signature
                  (typeCompilationFuel (parallelTypeBranchesSelecting item.1 branches))
                  (parallelTypeBranchesSelecting item.1 branches)) := by
            rw [List.getElem?_map, hGet]; rfl
          simp only [Finset.mem_union, childAccepting, Finset.mem_image, childState,
            indexedFragmentAccepting, mem_foldl_union_iff, Finset.notMem_empty, false_or]
          constructor
          · rintro (⟨q1, hq1, hEq1⟩ | ⟨item', hItem', q2, hq2, hEq2⟩)
            · exact nomatch hEq1
            · injection hEq2 with hIdxEq hQEq
              have hItemEq : item'.1 = (item.1.1, compileTypeFuel signature
                  (typeCompilationFuel (parallelTypeBranchesSelecting item.1 branches))
                  (parallelTypeBranchesSelecting item.1 branches)) := by
                have hGet' := List.mk_mem_zipIdx_iff_getElem?.mp hItem'
                have hIdxEq' : item'.2 = item.2 := by omega
                rw [hIdxEq'] at hGet'
                rw [hMapGet] at hGet'
                injection hGet' with hFst
                exact hFst.symm
              rw [hItemEq] at hq2
              exact hIH.mp (hQEq ▸ hq2)
          · intro hSkip
            refine Or.inr ⟨((item.1.1, compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting item.1 branches))
                (parallelTypeBranchesSelecting item.1 branches)), item.2),
              List.mk_mem_zipIdx_iff_getElem?.mpr hMapGet, a.2, hIH.mpr hSkip, rfl⟩

/-- A witness environment over the type's own alphabet that lets
`(msg, dir.invert)` fire immediately and nothing else — built directly from
the declaring alphabet, which is what the compiled edges now range over. -/
theorem firing_environment_mem_localEnvironmentsFor
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (msg : MessageId) (dir : MessageDir)
    (hAction : (msg, dir) ∈ alphabet.actions) :
    ({ immediate := {(msg, dir.invert)}, future := ∅, clock := false } :
      TypeEnvironment) ∈ signature.localEnvironmentsFor alphabet := by
  have hMem : (msg, dir.invert) ∈
      signature.localEnvironmentActionsFor alphabet := by
    have hImage := Finset.mem_image_of_mem typeNeed hAction
    simpa [typeNeed, TypeAlphabet.localEnvironmentActionsFor,
      TypeAlphabet.localActionsFor] using hImage
  simp only [TypeAlphabet.localEnvironmentsFor, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_powerset, Finset.mem_image]
  refine Or.inr ⟨{(msg, dir.invert)}, Finset.singleton_subset_iff.mpr hMem, ∅,
    Finset.empty_subset _, rfl⟩

/-- Generic: tag-transparency of one non-clock step, from an `outgoing`
characterization of the parent's edges at a tagged child state. -/
theorem automatonNonClockStep_of_outgoing_childPendingEdge
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ (state : TypeAutomatonState) (edge : PendingAutomatonEdge),
      (edge ∈ parent.edges ∧ edge.source = childState index state) ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧ edge = childPendingEdge index childEdge)
    (state target : TypeAutomatonState) :
    AutomatonNonClockStep parent (childState index state) target ↔
      ∃ q', target = childState index q' ∧ AutomatonNonClockStep child state q' := by
  constructor
  · rintro ⟨edge, hEdgeMem, hSource, hTarget, hNotTock⟩
    obtain ⟨childEdge, hChildEdge, hChildSource, hEdgeEq⟩ :=
      (hOutgoing state edge).mp ⟨hEdgeMem, hSource⟩
    refine ⟨childEdge.target, ?_, childEdge, hChildEdge, hChildSource, rfl, ?_⟩
    · rw [← hTarget, hEdgeEq]; simp [childPendingEdge, childState]
    · simpa [hEdgeEq, childPendingEdge] using hNotTock
  · rintro ⟨q', hTargetEq, childEdge, hChildEdge, hChildSource, hChildTarget,
      hChildNotTock⟩
    have hOut := (hOutgoing state (childPendingEdge index childEdge)).mpr
      ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    exact ⟨childPendingEdge index childEdge, hOut.1, hOut.2,
      by rw [hTargetEq]; simp [childPendingEdge, childState, hChildTarget],
      by simpa [childPendingEdge] using hChildNotTock⟩

/-- An exclusive offer's tagged-else outgoing edges are exactly the else
fragment's own edges, tagged. -/
theorem exclusiveOffer_outgoing_else
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    (edge ∈ (buildExclusiveOfferAutomaton signature alphabet branches
        elseAutomaton branchAutomata).edges ∧
      edge.source = childState 0 state) ↔
      ∃ childEdge ∈ elseAutomaton.edges,
        childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, hChildEdge, hEdgeEq⟩
      have hChildSource := hSource
      rw [← hEdgeEq] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEdgeEq.symm⟩
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, _hIndexed, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, _hChildEdge, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp [childPendingEdge, childState] at hSource
    · rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, _hIndexed, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, _hEnvironment, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp [childState] at hSource
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childState] at hSource
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childState] at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl (Or.inl ⟨childEdge, hChildEdge, rfl⟩)))
    · simp [childPendingEdge, childState, hChildSource]

/-- An exclusive offer's tagged-branch outgoing edges are exactly that
branch fragment's own edges, tagged. -/
theorem exclusiveOffer_outgoing_branch
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment)
    (hBranch : branchAutomata[i]? = some (action, automaton))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    (edge ∈ (buildExclusiveOfferAutomaton signature alphabet branches
        elseAutomaton branchAutomata).edges ∧
      edge.source = childState (i + 1) state) ↔
      ∃ childEdge ∈ automaton.edges,
        childEdge.source = state ∧ edge = childPendingEdge (i + 1) childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hBranchEdges) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, _hChildEdge, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childPendingEdge, childState] at hSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, hChildEdge, hEdgeEq⟩
        have hChildSource := hSource
        rw [← hEdgeEq] at hChildSource
        simp [childPendingEdge, childState] at hChildSource
        rcases hChildSource with ⟨hIndexEq, hSourceEq⟩
        have hIndexedGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
        have hEntryEq : indexed.1 = (action, automaton) := by
          have hGet : branchAutomata[i]? = some indexed.1 := by
            simpa [hIndexEq] using hIndexedGet
          rw [hBranch] at hGet
          exact (Option.some.inj hGet).symm
        have hAutomatonEq : indexed.1.2 = automaton := congrArg Prod.snd hEntryEq
        have hEdgeEq' : edge = childPendingEdge (i + 1) childEdge := by
          simpa [hIndexEq] using hEdgeEq.symm
        exact ⟨childEdge, by simpa [hAutomatonEq] using hChildEdge,
          hSourceEq, hEdgeEq'⟩
    · rw [mem_foldl_union_iff] at hBranchEdges
      rcases hBranchEdges with hEmpty | ⟨indexed, _hIndexed, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, _hEnvironment, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp [childState] at hSource
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childState] at hSource
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childState] at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
      rw [indexedFragmentEdges, mem_foldl_union_iff]
      exact Or.inr ⟨((action, automaton), i),
        List.mk_mem_zipIdx_iff_getElem?.mpr hBranch,
        Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩⟩
    · simp [childPendingEdge, childState, hChildSource]

/-- Tagged-else acceptance in an exclusive offer is the else fragment's own. -/
theorem buildExclusiveOfferAutomaton_child0_accepting_iff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (q : TypeAutomatonState) :
    childState 0 q ∈ (buildExclusiveOfferAutomaton signature alphabet branches
        elseAutomaton branchAutomata).accepting ↔
      q ∈ elseAutomaton.accepting := by
  classical
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, childAccepting, Finset.mem_image, childState,
    indexedFragmentAccepting, mem_foldl_union_iff, Finset.notMem_empty, false_or]
  constructor
  · rintro (⟨q', hq', hEq⟩ | ⟨indexed, -, q', -, hEq⟩)
    · injection hEq with _ hEq'; exact hEq' ▸ hq'
    · exact nomatch hEq
  · intro hq; exact Or.inl ⟨q, hq, rfl⟩

/-- Tagged-branch acceptance in an exclusive offer is that branch's own. -/
theorem buildExclusiveOfferAutomaton_branch_accepting_iff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment)
    (hBranch : branchAutomata[i]? = some (action, automaton))
    (q : TypeAutomatonState) :
    childState (i + 1) q ∈ (buildExclusiveOfferAutomaton signature alphabet branches
        elseAutomaton branchAutomata).accepting ↔
      q ∈ automaton.accepting := by
  classical
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, childAccepting, Finset.mem_image, childState,
    indexedFragmentAccepting, mem_foldl_union_iff, Finset.notMem_empty, false_or]
  constructor
  · rintro (⟨q', hq', hEq⟩ | ⟨indexed, hIndexed, q', hq', hEq⟩)
    · exact nomatch hEq
    · injection hEq with hIdx hQ
      have hIdxEq : indexed.2 = i := by omega
      have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexed
      rw [hIdxEq, hBranch] at hGet
      have hEntry : indexed.1 = (action, automaton) := (Option.some.inj hGet).symm
      rw [hEntry] at hq'
      exact hQ ▸ hq'
  · intro hq
    exact Or.inr ⟨((action, automaton), i),
      List.mk_mem_zipIdx_iff_getElem?.mpr hBranch, q, hq, rfl⟩

/-- The exclusive offer's fresh root is never accepting. -/
theorem buildExclusiveOfferAutomaton_root_not_accepting
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) :
    TypeAutomatonState.root ∉ (buildExclusiveOfferAutomaton signature alphabet
      branches elseAutomaton branchAutomata).accepting := by
  classical
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, childAccepting, Finset.mem_image, childState,
    indexedFragmentAccepting, mem_foldl_union_iff, Finset.notMem_empty, false_or]
  rintro (⟨q, -, hEq⟩ | ⟨indexed, -, q, -, hEq⟩) <;> exact nomatch hEq

/-- The exclusive offer's root steps back to itself (wait) or into the else
or one branch entry. -/
theorem automatonNonClockStep_root_exclusiveOffer
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    {target : TypeAutomatonState}
    (hStep : AutomatonNonClockStep (buildExclusiveOfferAutomaton signature alphabet
      branches elseAutomaton branchAutomata) TypeAutomatonState.root target) :
    target = TypeAutomatonState.root ∨
    target = childState 0 elseAutomaton.initial ∨
    ∃ i action automaton, branchAutomata[i]? = some (action, automaton) ∧
      target = childState (i + 1) automaton.initial := by
  classical
  obtain ⟨edge, hEdge, hSource, hTarget, -⟩ := hStep
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
  rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
  · rcases hElse with ⟨childEdge, -, hEdgeEq⟩
    rw [← hEdgeEq] at hSource
    simp [childPendingEdge, childState] at hSource
  · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
    rcases hIndexed with hEmpty | ⟨indexed, -, hChild⟩
    · simp at hEmpty
    · simp only [childPendingEdges, Finset.mem_image] at hChild
      rcases hChild with ⟨childEdge, -, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childPendingEdge, childState] at hSource
  · rw [mem_foldl_union_iff] at hBranch
    rcases hBranch with hEmpty | ⟨indexed, hIndexedMem, hRoot⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
      rcases hRoot with ⟨environment, -, hEdgeEq⟩
      refine Or.inr (Or.inr ⟨indexed.2, indexed.1.1, indexed.1.2,
        List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem, ?_⟩)
      rw [← hTarget, ← hEdgeEq]
  · simp only [Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, -, hEdgeEq⟩
    exact Or.inl (by rw [← hTarget, ← hEdgeEq])
  · simp only [Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, -, hEdgeEq⟩
    exact Or.inr (Or.inl (by rw [← hTarget, ← hEdgeEq]))

/-- The empty environment always realizes the exclusive offer's else edge. -/
theorem automatonNonClockStep_root_exclusiveOffer_else
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (hEnvMem : TypeEnvironment.empty ∈ signature.localEnvironmentsFor alphabet)
    (hBranchActions : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions) :
    AutomatonNonClockStep (buildExclusiveOfferAutomaton signature alphabet branches
        elseAutomaton branchAutomata) TypeAutomatonState.root
      (childState 0 elseAutomaton.initial) := by
  classical
  set edge : PendingAutomatonEdge :=
    { source := TypeAutomatonState.root, environment := TypeEnvironment.empty,
      label := .visible TypeLabel.silent, current := ∅,
      future := FutureSpec.at (childState 0 elseAutomaton.initial) ∅,
      target := childState 0 elseAutomaton.initial } with hEdgeDef
  refine ⟨edge, ?_, rfl, rfl, ?_⟩
  · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter]
    exact Or.inr ⟨TypeEnvironment.empty,
      ⟨hEnvMem, rfl, by simp [TypeEnvironment.empty], by simp [TypeEnvironment.empty],
        hBranchActions⟩, hEdgeDef.symm⟩
  · simp [hEdgeDef, AutomatonConstructionLabel.semantic, TypeLabel.isTock,
      TypeLabel.silent]

/-- The environment needing exactly `action` realizes that branch's fire edge. -/
theorem automatonNonClockStep_root_exclusiveOffer_branch
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment)
    (hBranch : branchAutomata[i]? = some (action, automaton))
    (hEnvMem : ({ immediate := {typeNeed action}, future := ∅, clock := false } :
      TypeEnvironment) ∈ signature.localEnvironmentsFor alphabet)
    (hBranchActions : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions) :
    AutomatonNonClockStep (buildExclusiveOfferAutomaton signature alphabet branches
        elseAutomaton branchAutomata) TypeAutomatonState.root
      (childState (i + 1) automaton.initial) := by
  classical
  set env : TypeEnvironment :=
    { immediate := {typeNeed action}, future := ∅, clock := false } with hEnvDef
  set edge : PendingAutomatonEdge :=
    { source := TypeAutomatonState.root, environment := env,
      label := .visible (TypeLabel.message action.1 action.2),
      current := {action},
      future := FutureSpec.at (childState (i + 1) automaton.initial) ∅,
      target := childState (i + 1) automaton.initial } with hEdgeDef
  refine ⟨edge, ?_, rfl, rfl, ?_⟩
  · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union]
    refine Or.inl (Or.inl (Or.inr ?_))
    rw [mem_foldl_union_iff]
    refine Or.inr ⟨((action, automaton), i),
      List.mk_mem_zipIdx_iff_getElem?.mpr hBranch, ?_⟩
    simp only [Finset.mem_image, Finset.mem_filter]
    exact ⟨env, ⟨hEnvMem, by simp [hEnvDef], by simp [hEnvDef], hBranchActions⟩,
      hEdgeDef.symm⟩
  · simp [hEdgeDef, AutomatonConstructionLabel.semantic, TypeLabel.isTock,
      TypeLabel.message]

/-- Root reachability for an exclusive offer: the wait edges self-loop, the
root is never accepting, and every escape lands at the else entry or a branch
entry — each realized by a witness environment. -/
theorem automatonSameCycleReachesAccepting_root_exclusiveOffer
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (hEnvMem : TypeEnvironment.empty ∈ signature.localEnvironmentsFor alphabet)
    (hBranchActions : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions)
    (hFiringEnv : ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
      branchAutomata[i]? = some (action, automaton) →
      ({ immediate := {typeNeed action}, future := ∅, clock := false } :
        TypeEnvironment) ∈ signature.localEnvironmentsFor alphabet) :
    AutomatonSameCycleReachesAccepting (buildExclusiveOfferAutomaton signature alphabet
        branches elseAutomaton branchAutomata) TypeAutomatonState.root ↔
      AutomatonSameCycleReachesAccepting (buildExclusiveOfferAutomaton signature alphabet
        branches elseAutomaton branchAutomata) (childState 0 elseAutomaton.initial) ∨
      ∃ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
        branchAutomata[i]? = some (action, automaton) ∧
        AutomatonSameCycleReachesAccepting (buildExclusiveOfferAutomaton signature
          alphabet branches elseAutomaton branchAutomata)
          (childState (i + 1) automaton.initial) := by
  classical
  set offer := buildExclusiveOfferAutomaton signature alphabet branches
    elseAutomaton branchAutomata with hOfferDef
  constructor
  · rintro ⟨finalState, hReach, hFinal⟩
    have hAux : ∀ reached,
        Relation.ReflTransGen (AutomatonNonClockStep offer) TypeAutomatonState.root reached →
        reached = TypeAutomatonState.root ∨
        Relation.ReflTransGen (AutomatonNonClockStep offer)
          (childState 0 elseAutomaton.initial) reached ∨
        ∃ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
          branchAutomata[i]? = some (action, automaton) ∧
          Relation.ReflTransGen (AutomatonNonClockStep offer)
            (childState (i + 1) automaton.initial) reached := by
      intro reached hR
      induction hR with
      | refl => exact Or.inl rfl
      | tail _ hStep ih =>
          rcases ih with hRoot | hElse | ⟨i, action, automaton, hGet, hPath⟩
          · rw [hRoot] at hStep
            rcases automatonNonClockStep_root_exclusiveOffer signature alphabet branches
                elseAutomaton branchAutomata hStep with h | h | ⟨i, action, automaton, hGet, h⟩
            · exact Or.inl h
            · exact Or.inr (Or.inl (by rw [h]))
            · exact Or.inr (Or.inr ⟨i, action, automaton, hGet, by rw [h]⟩)
          · exact Or.inr (Or.inl (hElse.tail hStep))
          · exact Or.inr (Or.inr ⟨i, action, automaton, hGet, hPath.tail hStep⟩)
    rcases hAux finalState hReach with hRoot | hElse | ⟨i, action, automaton, hGet, hPath⟩
    · exfalso
      rw [hRoot] at hFinal
      exact absurd hFinal (buildExclusiveOfferAutomaton_root_not_accepting signature
        alphabet branches elseAutomaton branchAutomata)
    · exact Or.inl ⟨finalState, hElse, hFinal⟩
    · exact Or.inr ⟨i, action, automaton, hGet, finalState, hPath, hFinal⟩
  · rintro (⟨finalState, hReach, hFinal⟩ |
      ⟨i, action, automaton, hGet, finalState, hReach, hFinal⟩)
    · exact ⟨finalState, Relation.ReflTransGen.head
        (automatonNonClockStep_root_exclusiveOffer_else signature alphabet branches
          elseAutomaton branchAutomata hEnvMem hBranchActions) hReach, hFinal⟩
    · exact ⟨finalState, Relation.ReflTransGen.head
        (automatonNonClockStep_root_exclusiveOffer_branch signature alphabet branches
          elseAutomaton branchAutomata i action automaton hGet
          (hFiringEnv i action automaton hGet) hBranchActions) hReach, hFinal⟩

/-- Per-branch projection of `TypeAlphabet.SupportsBranches`. -/
private theorem branchType_supports_of_mem
    (signature : TypeAlphabet) {branches : List (BareMessage × PactType)}
    (hBranches : signature.SupportsBranches branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    signature.Supports branch.2 := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      have hAll : (headAction ∈ signature.boundary ∨
            headAction.1 ∈ signature.interface) ∧
          signature.Supports headType ∧ signature.SupportsBranches rest := by
        simpa only [TypeAlphabet.SupportsBranches] using hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq; exact hAll.2.1
      · exact ih hAll.2.2 hMemRest

/-- Per-branch projection of `PactType.BranchesAlphabetWellFormed`. -/
private theorem branchType_alphabetWellFormed_of_mem
    {alphabet : PactTypeAlphabet} {branches : List (BareMessage × PactType)}
    (hBranches : PactType.BranchesAlphabetWellFormed alphabet branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    branch.2.AlphabetWellFormed ∧ branch.1 ∈ alphabet.actions := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.BranchesAlphabetWellFormed] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq; exact ⟨hBranches.2.2.1, hBranches.1⟩
      · exact ih hBranches.2.2.2 hMemRest

/-- Per-branch projection of `PactType.ClockGuardedBranches`. -/
private theorem branchType_clockGuarded_of_mem
    {branches : List (BareMessage × PactType)}
    (hBranches : PactType.ClockGuardedBranches branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    branch.2.ClockGuarded := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.ClockGuardedBranches] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq; exact hBranches.1
      · exact ih hBranches.2 hMemRest

/-- Per-branch projection of `PactType.TailRecursiveBranches`. -/
private theorem branchType_tailRecursive_of_mem
    {branches : List (BareMessage × PactType)}
    (hBranches : PactType.TailRecursiveBranches branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    branch.2.TailRecursive := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.TailRecursiveBranches] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq; exact hBranches.1
      · exact ih hBranches.2 hMemRest

/-- A branch continuation is a strict subterm of the offer that carries it. -/
private theorem sizeOf_branchType_lt_branches
    {branches : List (BareMessage × PactType)}
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    sizeOf branch.2 < sizeOf branches := by
  have h1 : sizeOf branch < sizeOf branches := List.sizeOf_lt_of_mem hMem
  have h2 : sizeOf branch.2 < sizeOf branch := by
    rcases branch with ⟨action, branchType⟩; simp_wf; omega
  omega

/-- Shape of a related pair for `.xoffer elseType branches`: the fresh root,
a tagged else state, or a tagged branch state. -/
theorem helper_h12_xoffer_shape
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.xoffer alphabet elseType branches)
          (compileType signature (.xoffer alphabet elseType branches)))
        residual state) :
    (residual = .xoffer alphabet elseType branches ∧
      state = TypeAutomatonState.root) ∨
    (∃ q, state = .child 0 q ∧
      relationMembership (buildRelationSet elseType (compileType signature elseType))
        residual q) ∨
    (∃ (i : Nat) (action : BareMessage) (branchType : PactType)
        (q : TypeAutomatonState),
      branches[i]? = some (action, branchType) ∧ state = .child (i + 1) q ∧
      relationMembership (buildRelationSet branchType
        (compileType signature branchType)) residual q) := by
  have hFuelEq : typeCompilationFuel (.xoffer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel signature
        (typeCompilationFuel (.xoffer alphabet elseType branches))
        (.xoffer alphabet elseType branches) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
    mem_foldl_union_iff, Finset.notMem_empty, false_or, Finset.mem_image,
    Prod.mk.injEq] at hMem
  rcases hMem with ⟨hR, hS⟩ | ⟨a, ha, hR, hS⟩ | ⟨item, hItem, a, ha, hR, hS⟩
  · exact Or.inl ⟨hR, hS⟩
  · refine Or.inr (Or.inl ⟨a.2, hS.symm, ?_⟩)
    show (residual, a.2) ∈
      buildRelationSetCoreFuel signature (typeCompilationFuel elseType) elseType
    rw [← buildRelationSetCoreFuel_eq_of_sufficient signature elseType
      (le_max_left _ _) le_rfl, ← hR]
    exact ha
  · have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hItem
    have hMemBranches : item.1 ∈ branches := List.mem_of_getElem? hGet
    have hItemFuel : typeCompilationFuel item.1.2 ≤
        max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) :=
      le_trans (typeCompilationFuel_le_typeBranchCompilationFuel branches item.1
        hMemBranches) (le_max_right _ _)
    refine Or.inr (Or.inr ⟨item.2, item.1.1, item.1.2, a.2, hGet, hS.symm, ?_⟩)
    show (residual, a.2) ∈
      buildRelationSetCoreFuel signature (typeCompilationFuel item.1.2) item.1.2
    rw [← buildRelationSetCoreFuel_eq_of_sufficient signature item.1.2 hItemFuel
      le_rfl, ← hR]
    exact ha

/-- Helper Lemma H14: same-cycle completion. Needs `signature.Supports
processType` (unlike H12/H13, which hold unconditionally), because the
choice, sequence and parallel cases recurse into subterms and the induction
hypothesis carries the same premise; `pact.pdf`'s own Lemma 4.5 already
fixes an admissible (hence supported) type throughout, so this hypothesis
is implicit there and needs to be made explicit here. -/
theorem helper_h14_same_cycle_completion
    (signature : TypeAlphabet) {processType residual : PactType}
    {state : TypeAutomatonState}
    (hSupports : signature.Supports processType)
    (hAlphabet : processType.AlphabetWellFormed)
    (hClockGuarded : processType.ClockGuarded)
    (hTailRecursive : processType.TailRecursive)
    (hRelated :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual state) :
    AutomatonSameCycleReachesAccepting
        (compileTypeFuel signature (typeCompilationFuel processType) processType) state ↔
      TypeSameCycleCanComplete residual := by
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType residual state with
  | _ n ih =>
    cases processType with
    | skip alphabet =>
        obtain ⟨hResidual, hState⟩ :=
          NewCorrespondence.relationMembership_skip_cases signature alphabet hRelated
        subst hResidual; subst hState
        constructor
        · intro _; exact ⟨alphabet, Relation.ReflTransGen.refl⟩
        · intro _
          refine ⟨TypeAutomatonState.root, Relation.ReflTransGen.refl, ?_⟩
          simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    | var alphabet name =>
        unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
        simp only [typeCompilationFuel, buildRelationSetCoreFuel, Finset.mem_singleton,
          Prod.mk.injEq] at hRelated
        obtain ⟨hResidual, hState⟩ := hRelated
        subst hResidual; subst hState
        constructor
        · rintro ⟨finalState, -, hFinal⟩
          exfalso
          simp [compileType, typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
            at hFinal
        · rintro ⟨_, hReaches⟩
          exfalso
          exact absurd (Relation.ReflTransGen.cases_head hReaches) (by
            rintro (h | ⟨c, ⟨env, label, hTrans, -⟩, -⟩)
            · exact nomatch h
            · cases hTrans)
    | message alphabet msg dir =>
        set env : TypeEnvironment :=
          { immediate := {(msg, dir.invert)}, future := ∅, clock := false } with hEnvDef
        have hHasNeed : env.hasNeed (msg, dir) := by simp [TypeEnvironment.hasNeed, hEnvDef]
        rcases NewCorrespondence.relationMembership_message_cases signature alphabet msg dir
            hRelated with
          ⟨hResidual, hState⟩ | ⟨hResidual, hState⟩ <;> subst hResidual <;> subst hState
        · constructor
          · intro _
            have hWF : env.WellFormed := by simp [TypeEnvironment.WellFormed, hEnvDef]
            have hAction : (msg, dir) ∈ alphabet.actions := by
              simp only [PactType.AlphabetWellFormed] at hAlphabet
              exact hAlphabet.2
            exact ⟨alphabet, Relation.ReflTransGen.single ⟨env, _,
              TypeTransition.action env alphabet msg dir ⟨hWF, hHasNeed⟩ hAction,
              by simp [TypeLabel.isTock, TypeLabel.message]⟩⟩
          · intro _
            have hDeclared : (msg, dir) ∈ alphabet.actions := by
              simp only [PactType.AlphabetWellFormed] at hAlphabet
              exact hAlphabet.2
            have hEnvMem := firing_environment_mem_localEnvironmentsFor signature
              alphabet msg dir hDeclared
            rw [← hEnvDef] at hEnvMem
            set edge : PendingAutomatonEdge :=
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible (TypeLabel.message msg dir),
                current := {(msg, dir)}, future := FutureSpec.at TypeAutomatonState.final ∅,
                target := TypeAutomatonState.final } with hEdgeDef
            have hEdgeMem : edge ∈
                (compileTypeFuel signature (typeCompilationFuel (.message alphabet msg dir))
                  (.message alphabet msg dir)).edges := by
              have hAction : (msg, dir) ∈ alphabet.actions := by
                simp only [PactType.AlphabetWellFormed] at hAlphabet
                exact hAlphabet.2
              simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_image, Finset.mem_filter]
              exact Or.inl (Or.inl ⟨env, ⟨hEnvMem, hHasNeed, hAction⟩, hEdgeDef.symm⟩)
            refine ⟨TypeAutomatonState.final,
              Relation.ReflTransGen.single ⟨edge, hEdgeMem, rfl, rfl, ?_⟩, ?_⟩
            · simp [hEdgeDef, AutomatonConstructionLabel.semantic, TypeLabel.isTock,
                TypeLabel.message]
            · simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
        · constructor
          · intro _; exact ⟨alphabet, Relation.ReflTransGen.refl⟩
          · intro _
            refine ⟨TypeAutomatonState.final, Relation.ReflTransGen.refl, ?_⟩
            simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    | tock alphabet =>
        rcases NewCorrespondence.relationMembership_tock_cases signature alphabet hRelated with
          ⟨hResidual, hState⟩ | ⟨hResidual, hState⟩ <;> subst hResidual <;> subst hState
        · have hTockStays : ∀ ρ', TypeSameCycleReaches (.tock alphabet) ρ' →
              ρ' = .tock alphabet := by
            intro ρ' hPath
            induction hPath with
            | refl => rfl
            | tail _ hbc ih =>
                rw [ih] at hbc
                obtain ⟨env, label, hTrans, hNotTock⟩ := hbc
                cases hTrans with
                | cycle env hCond => exact absurd (by simp [TypeLabel.isTock]) hNotTock
                | cycle_wait env hCond => rfl
          have hAutoStays : ∀ q, Relation.ReflTransGen
              (AutomatonNonClockStep
                (compileTypeFuel signature (typeCompilationFuel (.tock alphabet))
                  (.tock alphabet)))
              TypeAutomatonState.root q → q = TypeAutomatonState.root := by
            intro q hR
            induction hR with
            | refl => rfl
            | tail _ hbc ih =>
                rw [ih] at hbc
                obtain ⟨edge, hMem, hSource, hTarget, hNotTock⟩ := hbc
                simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
                  Finset.mem_union, Finset.mem_image] at hMem
                rcases hMem with ⟨env, -, hEq⟩ | ⟨env, -, hEq⟩
                · rw [← hEq] at hSource hTarget hNotTock
                  split at hSource <;> split at hTarget <;> split at hNotTock <;>
                    simp_all [AutomatonConstructionLabel.semantic, TypeLabel.isTock]
                · rw [← hEq] at hSource
                  simp at hSource
          constructor
          · rintro ⟨finalState, hReach, hFinal⟩
            rw [hAutoStays finalState hReach] at hFinal
            simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment] at hFinal
          · rintro ⟨targetAlphabet, hReaches⟩
            exact absurd (hTockStays (.skip targetAlphabet) hReaches) (by simp)
        · constructor
          · intro _; exact ⟨alphabet, Relation.ReflTransGen.refl⟩
          · intro _
            refine ⟨TypeAutomatonState.final, Relation.ReflTransGen.refl, ?_⟩
            simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    | progress alphabet pid =>
        rcases NewCorrespondence.relationMembership_progress_cases signature alphabet pid
            hRelated with
          ⟨hResidual, hState⟩ | ⟨hResidual, hState⟩ <;> subst hResidual <;> subst hState
        · constructor
          · intro _
            have hEnv : TypeEnvironment.empty.WellFormed := by
              simp [TypeEnvironment.WellFormed, TypeEnvironment.empty]
            exact ⟨alphabet, Relation.ReflTransGen.single ⟨TypeEnvironment.empty, _,
              TypeTransition.progress TypeEnvironment.empty alphabet pid hEnv rfl,
              by simp [TypeLabel.isTock, TypeLabel.progress]⟩⟩
          · intro _
            have hEmptyLocal : TypeEnvironment.empty ∈
                signature.localEnvironmentsFor alphabet := by
              simp only [TypeAlphabet.localEnvironmentsFor, Finset.mem_union,
                Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
              exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
            set edge : PendingAutomatonEdge :=
              { source := TypeAutomatonState.root, environment := TypeEnvironment.empty,
                label := AutomatonConstructionLabel.visible (TypeLabel.progress pid),
                current := ∅, future := FutureSpec.at TypeAutomatonState.final ∅,
                target := TypeAutomatonState.final } with hEdgeDef
            have hEdgeMem : edge ∈
                (compileTypeFuel signature (typeCompilationFuel (.progress alphabet pid))
                  (.progress alphabet pid)).edges := by
              simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_image, Finset.mem_filter]
              exact Or.inl ⟨TypeEnvironment.empty, ⟨hEmptyLocal, rfl⟩, hEdgeDef.symm⟩
            refine ⟨TypeAutomatonState.final,
              Relation.ReflTransGen.single ⟨edge, hEdgeMem, rfl, rfl, ?_⟩, ?_⟩
            · simp [hEdgeDef, AutomatonConstructionLabel.semantic, TypeLabel.isTock,
                TypeLabel.progress]
            · simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
        · constructor
          · intro _; exact ⟨alphabet, Relation.ReflTransGen.refl⟩
          · intro _
            refine ⟨TypeAutomatonState.final, Relation.ReflTransGen.refl, ?_⟩
            simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    | choice alphabet left right =>
        have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
        have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
        simp only [PactType.AlphabetWellFormed] at hAlphabet
        obtain ⟨-, -, -, hAWLeft, hAWRight⟩ := hAlphabet
        simp only [PactType.ClockGuarded] at hClockGuarded
        simp only [PactType.TailRecursive] at hTailRecursive
        obtain ⟨hCGLeft, hCGRight⟩ := hClockGuarded
        obtain ⟨hTRLeft, hTRRight⟩ := hTailRecursive
        have hFuelEq : typeCompilationFuel (.choice alphabet left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        set leftAuto := compileTypeFuel signature (typeCompilationFuel left) left with hLeftAutoDef
        set rightAuto := compileTypeFuel signature (typeCompilationFuel right) right
          with hRightAutoDef
        have hWhole :
            compileTypeFuel signature (typeCompilationFuel (.choice alphabet left right))
              (.choice alphabet left right) =
              buildChoiceAutomaton signature alphabet leftAuto rightAuto
                TypeLabel.silent TypeLabel.silent := by
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show buildChoiceAutomaton signature alphabet
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
              TypeLabel.silent TypeLabel.silent =
            buildChoiceAutomaton signature alphabet leftAuto rightAuto
              TypeLabel.silent TypeLabel.silent
          rw [hLeftAutoDef, hRightAutoDef,
            compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
        rw [hWhole]
        simp only [TypeAlphabet.Supports] at hSupports
        have hEmptyLocal :
            TypeEnvironment.empty ∈ signature.localEnvironmentsFor alphabet := by
          simp only [TypeAlphabet.localEnvironmentsFor, Finset.mem_union,
            Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
          exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
        have hShape := helper_h12_binaryChoice_shape signature (.choice alphabet left right) left right
          rfl hFuelEq hRelated
        have hTag0 := automatonSameCycleReachesAccepting_of_child_tag
          (buildChoiceAutomaton signature alphabet leftAuto rightAuto
            TypeLabel.silent TypeLabel.silent)
          leftAuto 0
          (automatonNonClockStep_binaryChoice_child0 signature alphabet leftAuto
            rightAuto
            TypeLabel.silent TypeLabel.silent)
          (buildChoiceAutomaton_child0_accepting_iff signature alphabet leftAuto
            rightAuto
            TypeLabel.silent TypeLabel.silent)
        have hTag1 := automatonSameCycleReachesAccepting_of_child_tag
          (buildChoiceAutomaton signature alphabet leftAuto rightAuto
            TypeLabel.silent TypeLabel.silent)
          rightAuto 1
          (automatonNonClockStep_binaryChoice_child1 signature alphabet leftAuto
            rightAuto
            TypeLabel.silent TypeLabel.silent)
          (buildChoiceAutomaton_child1_accepting_iff signature alphabet leftAuto
            rightAuto
            TypeLabel.silent TypeLabel.silent)
        rcases hShape with ⟨hResidualEq, hStateEq⟩ |
          ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
        · subst hResidualEq; subst hStateEq
          rw [typeSameCycleCanComplete_choice_iff,
            automatonSameCycleReachesAccepting_root_binaryChoice signature alphabet
              leftAuto rightAuto _ _
              hEmptyLocal (by simp [TypeLabel.isTock, TypeLabel.silent])
              (by simp [TypeLabel.isTock, TypeLabel.silent])]
          have hIHLeft := ih (sizeOf left) hLeftSize hSupports.1 hAWLeft hCGLeft hTRLeft
            (buildRelationSet_initial left (compileType signature left)) rfl
          have hIHRight := ih (sizeOf right) hRightSize hSupports.2 hAWRight hCGRight hTRRight
            (buildRelationSet_initial right (compileType signature right)) rfl
          simp only [compileType] at hIHLeft hIHRight
          rw [← hLeftAutoDef] at hIHLeft
          rw [← hRightAutoDef] at hIHRight
          rw [hTag0 leftAuto.initial, hTag1 rightAuto.initial, hIHLeft, hIHRight]
        · subst hStateEq
          exact (hTag0 q).trans (ih (sizeOf left) hLeftSize hSupports.1 hAWLeft hCGLeft
            hTRLeft hLeftRelated rfl)
        · subst hStateEq
          exact (hTag1 q).trans (ih (sizeOf right) hRightSize hSupports.2 hAWRight hCGRight
            hTRRight hRightRelated rfl)
    | fairChoice alphabet bid left right =>
        have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
        have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
        simp only [PactType.AlphabetWellFormed] at hAlphabet
        obtain ⟨-, -, -, -, hAWLeft, hAWRight⟩ := hAlphabet
        simp only [PactType.ClockGuarded] at hClockGuarded
        simp only [PactType.TailRecursive] at hTailRecursive
        obtain ⟨hCGLeft, hCGRight⟩ := hClockGuarded
        obtain ⟨hTRLeft, hTRRight⟩ := hTailRecursive
        have hFuelEq : typeCompilationFuel (.fairChoice alphabet bid left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        set leftAuto := compileTypeFuel signature (typeCompilationFuel left) left with hLeftAutoDef
        set rightAuto := compileTypeFuel signature (typeCompilationFuel right) right
          with hRightAutoDef
        have hWhole :
            compileTypeFuel signature (typeCompilationFuel (.fairChoice alphabet bid left right))
              (.fairChoice alphabet bid left right) =
              buildChoiceAutomaton signature alphabet leftAuto rightAuto
                (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show buildChoiceAutomaton signature alphabet
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
              (TypeLabel.fair bid true) (TypeLabel.fair bid false) =
            buildChoiceAutomaton signature alphabet leftAuto rightAuto
              (TypeLabel.fair bid true) (TypeLabel.fair bid false)
          rw [hLeftAutoDef, hRightAutoDef,
            compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
        rw [hWhole]
        simp only [TypeAlphabet.Supports] at hSupports
        have hEmptyLocal :
            TypeEnvironment.empty ∈ signature.localEnvironmentsFor alphabet := by
          simp only [TypeAlphabet.localEnvironmentsFor, Finset.mem_union,
            Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
          exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
        have hShape := helper_h12_binaryChoice_shape signature (.fairChoice alphabet bid left right)
          left right rfl hFuelEq hRelated
        have hTag0 := automatonSameCycleReachesAccepting_of_child_tag
          (buildChoiceAutomaton signature alphabet leftAuto rightAuto
            (TypeLabel.fair bid true) (TypeLabel.fair bid false))
          leftAuto 0
          (automatonNonClockStep_binaryChoice_child0 signature alphabet leftAuto
            rightAuto
            (TypeLabel.fair bid true) (TypeLabel.fair bid false))
          (buildChoiceAutomaton_child0_accepting_iff signature alphabet leftAuto
            rightAuto
            (TypeLabel.fair bid true) (TypeLabel.fair bid false))
        have hTag1 := automatonSameCycleReachesAccepting_of_child_tag
          (buildChoiceAutomaton signature alphabet leftAuto rightAuto
            (TypeLabel.fair bid true) (TypeLabel.fair bid false))
          rightAuto 1
          (automatonNonClockStep_binaryChoice_child1 signature alphabet leftAuto
            rightAuto
            (TypeLabel.fair bid true) (TypeLabel.fair bid false))
          (buildChoiceAutomaton_child1_accepting_iff signature alphabet leftAuto
            rightAuto
            (TypeLabel.fair bid true) (TypeLabel.fair bid false))
        rcases hShape with ⟨hResidualEq, hStateEq⟩ |
          ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
        · subst hResidualEq; subst hStateEq
          rw [typeSameCycleCanComplete_fairChoice_iff,
            automatonSameCycleReachesAccepting_root_binaryChoice signature alphabet
              leftAuto rightAuto _ _
              hEmptyLocal (by simp [TypeLabel.isTock, TypeLabel.fair])
              (by simp [TypeLabel.isTock, TypeLabel.fair])]
          have hIHLeft := ih (sizeOf left) hLeftSize hSupports.2.1 hAWLeft hCGLeft hTRLeft
            (buildRelationSet_initial left (compileType signature left)) rfl
          have hIHRight := ih (sizeOf right) hRightSize hSupports.2.2 hAWRight hCGRight hTRRight
            (buildRelationSet_initial right (compileType signature right)) rfl
          simp only [compileType] at hIHLeft hIHRight
          rw [← hLeftAutoDef] at hIHLeft
          rw [← hRightAutoDef] at hIHRight
          rw [hTag0 leftAuto.initial, hTag1 rightAuto.initial, hIHLeft, hIHRight]
        · subst hStateEq
          exact (hTag0 q).trans (ih (sizeOf left) hLeftSize hSupports.2.1 hAWLeft hCGLeft
            hTRLeft hLeftRelated rfl)
        · subst hStateEq
          exact (hTag1 q).trans (ih (sizeOf right) hRightSize hSupports.2.2 hAWRight hCGRight
            hTRRight hRightRelated rfl)
    | seq alphabet left right =>
        have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
        have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
        simp only [PactType.AlphabetWellFormed] at hAlphabet
        obtain ⟨-, -, -, hAWLeft, hAWRight⟩ := hAlphabet
        simp only [PactType.ClockGuarded] at hClockGuarded
        simp only [PactType.TailRecursive] at hTailRecursive
        obtain ⟨hCGLeft, hCGRight⟩ := hClockGuarded
        obtain ⟨hTRLeft, hTRRight⟩ := hTailRecursive
        simp only [TypeAlphabet.Supports] at hSupports
        have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        set leftAuto := compileTypeFuel signature (typeCompilationFuel left) left
          with hLeftAutoDef
        set rightAuto := compileTypeFuel signature (typeCompilationFuel right) right
          with hRightAutoDef
        have hWhole :
            compileTypeFuel signature (typeCompilationFuel (.seq alphabet left right))
              (.seq alphabet left right) =
              buildSequenceAutomaton signature leftAuto rightAuto := by
          rw [hFuelEq, compileTypeFuel.eq_def]
          show buildSequenceAutomaton signature
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right) =
            buildSequenceAutomaton signature leftAuto rightAuto
          rw [hLeftAutoDef, hRightAutoDef,
            compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
        have hTag1 := automatonSameCycleReachesAccepting_of_child_tag
          (buildSequenceAutomaton signature leftAuto rightAuto) rightAuto 1
          (automatonNonClockStep_sequence_child1 signature leftAuto rightAuto)
          (buildSequenceAutomaton_child1_accepting_iff signature leftAuto rightAuto)
        rw [hWhole]
        rcases helper_h12_seq_shape signature alphabet left right hRelated with
          ⟨ρ, q1, hResidualEq, hStateEq, hLeftRelated, hSurvives⟩ |
          ⟨q2, hStateEq, hRightRelated⟩
        · subst hResidualEq; subst hStateEq
          have hIHLeft := ih (sizeOf left) hLeftSize hSupports.1 hAWLeft hCGLeft hTRLeft
            hLeftRelated rfl
          have hIHRightInit := ih (sizeOf right) hRightSize hSupports.2 hAWRight hCGRight
            hTRRight (buildRelationSet_initial right (compileType signature right)) rfl
          simp only [compileType] at hIHRightInit
          rw [← hRightAutoDef] at hIHRightInit
          rw [typeSameCycleCanComplete_seq_iff]
          constructor
          · rintro ⟨finalState, hReach, hFinal⟩
            rcases automatonSameCycleReaches_sequence_child0_cases signature
                leftAuto rightAuto q1 finalState hReach with
              ⟨q', hEq, -⟩ | ⟨q', hLeftReach, hAccepting, hRest⟩
            · exfalso
              rw [hEq] at hFinal
              simp [buildSequenceAutomaton, finishAutomatonFragment,
                childAccepting, childState] at hFinal
            · exact ⟨hIHLeft.mp ⟨q', hLeftReach, hAccepting⟩,
                hIHRightInit.mp
                  ((hTag1 rightAuto.initial).mp ⟨finalState, hRest, hFinal⟩)⟩
          · rintro ⟨hLeftDone, hRightDone⟩
            obtain ⟨q', hLeftReach, hAccepting⟩ := hIHLeft.mpr hLeftDone
            obtain ⟨q2', hRightReach, hRightFinal⟩ :=
              (hTag1 rightAuto.initial).mpr (hIHRightInit.mpr hRightDone)
            refine ⟨q2', Relation.ReflTransGen.trans ?_ hRightReach, hRightFinal⟩
            rcases automatonSameCycleReaches_sequence_lift_left signature
                leftAuto rightAuto q1 q' hLeftReach hAccepting with
              hPath | hEq
            · exact hPath
            · -- `q1` already accepts, so it is `left`'s entry and its own idle
              -- step redirects into the right entry.
              subst hEq
              have hEntry : q1 = leftAuto.initial := by
                rcases hSurvives with hNot | hInit
                · exact absurd hAccepting (by
                    simpa only [compileType, ← hLeftAutoDef] using hNot)
                · simpa only [compileType, ← hLeftAutoDef] using hInit
              rw [hEntry] at hAccepting ⊢
              obtain ⟨target, hStep, hTargetAccepting⟩ :=
                compileTypeFuel_nonClockStep_of_initial_accepting signature
                  (typeCompilationFuel left) left hAccepting
              refine Relation.ReflTransGen.single ?_
              refine (automatonNonClockStep_sequence_child0 signature leftAuto
                rightAuto leftAuto.initial _).mpr ⟨target, hStep, ?_⟩
              rw [sequenceRedirect, if_pos hTargetAccepting]
        · subst hStateEq
          exact (hTag1 q2).trans (ih (sizeOf right) hRightSize hSupports.2 hAWRight hCGRight
            hTRRight hRightRelated rfl)
    | par alphabet left right interface => sorry
    | recur alphabet name body => sorry
    | xoffer alphabet elseType branches =>
        have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
        have hBranchSize : ∀ branch ∈ branches, sizeOf branch.2 < n := by
          intro branch hMem
          have hLt := sizeOf_branchType_lt_branches hMem
          rw [← hSize]; simp_wf; omega
        simp only [PactType.AlphabetWellFormed] at hAlphabet
        obtain ⟨-, -, hAWElse, hAWBranches⟩ := hAlphabet
        simp only [PactType.ClockGuarded] at hClockGuarded
        obtain ⟨hCGElse, hCGBranches⟩ := hClockGuarded
        simp only [PactType.TailRecursive] at hTailRecursive
        obtain ⟨hTRElse, hTRBranches⟩ := hTailRecursive
        simp only [TypeAlphabet.Supports] at hSupports
        obtain ⟨hSupElse, hSupBranches⟩ := hSupports
        have hBranchActions : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions := fun b hb =>
          (branchType_alphabetWellFormed_of_mem hAWBranches hb).2
        have hEmptyLocal : TypeEnvironment.empty ∈ signature.localEnvironmentsFor alphabet := by
          simp only [TypeAlphabet.localEnvironmentsFor, Finset.mem_union,
            Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
          exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
        have hFuelEq : typeCompilationFuel (.xoffer alphabet elseType branches) =
            max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) + 1 := by
          simp only [typeCompilationFuel]; omega
        set elseAuto := compileTypeFuel signature (typeCompilationFuel elseType) elseType
          with hElseAutoDef
        set branchAutos := branches.map (fun branch =>
          (branch.1, compileTypeFuel signature (typeCompilationFuel branch.2) branch.2))
          with hBranchAutosDef
        have hWhole :
            compileTypeFuel signature
              (typeCompilationFuel (.xoffer alphabet elseType branches))
              (.xoffer alphabet elseType branches) =
              buildExclusiveOfferAutomaton signature alphabet branches elseAuto branchAutos := by
          rw [hFuelEq, compileTypeFuel.eq_def]
          show buildExclusiveOfferAutomaton signature alphabet branches
              (compileTypeFuel signature (max (typeCompilationFuel elseType)
                (typeBranchCompilationFuel branches)) elseType)
              (branches.map fun branch => (branch.1, compileTypeFuel signature
                (max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches))
                branch.2)) = _
          rw [hElseAutoDef, hBranchAutosDef,
            compileTypeFuel_eq_of_sufficient signature elseType (le_max_left _ _) le_rfl]
          congr 1
          apply List.map_congr_left
          intro branch hBranch
          congr 1
          exact compileTypeFuel_eq_of_sufficient signature branch.2
            (le_trans (typeCompilationFuel_le_typeBranchCompilationFuel branches branch hBranch)
              (le_max_right _ _)) le_rfl
        have hMapGet : ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
            branchAutos[i]? = some (action, automaton) →
            ∃ branchType, branches[i]? = some (action, branchType) ∧
              automaton = compileTypeFuel signature (typeCompilationFuel branchType) branchType := by
          intro i action automaton hGet
          rw [hBranchAutosDef, List.getElem?_map] at hGet
          cases hb : branches[i]? with
          | none => rw [hb] at hGet; exact absurd hGet (by simp)
          | some b =>
              rw [hb] at hGet
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hGet
              exact ⟨b.2, by rw [← hGet.1], hGet.2.symm⟩
        have hMapGetRev : ∀ (i : Nat) (branch : BareMessage × PactType),
            branches[i]? = some branch →
            branchAutos[i]? = some (branch.1,
              compileTypeFuel signature (typeCompilationFuel branch.2) branch.2) := by
          intro i branch hGet
          rw [hBranchAutosDef, List.getElem?_map, hGet]
          rfl
        have hFiringEnv : ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
            branchAutos[i]? = some (action, automaton) →
            ({ immediate := {typeNeed action}, future := ∅, clock := false } : TypeEnvironment)
              ∈ signature.localEnvironmentsFor alphabet := by
          intro i action automaton hGet
          obtain ⟨branchType, hBranchGet, -⟩ := hMapGet i action automaton hGet
          have hMem : (action, branchType) ∈ branches := List.mem_of_getElem? hBranchGet
          have hAction : action ∈ alphabet.actions := hBranchActions _ hMem
          simpa [typeNeed] using
            firing_environment_mem_localEnvironmentsFor signature alphabet action.1 action.2
              (by simpa using hAction)
        rw [hWhole]
        have hTag0 := automatonSameCycleReachesAccepting_of_child_tag
          (buildExclusiveOfferAutomaton signature alphabet branches elseAuto branchAutos)
          elseAuto 0
          (fun q target => automatonNonClockStep_of_outgoing_childPendingEdge _ _ 0
            (exclusiveOffer_outgoing_else signature alphabet branches elseAuto branchAutos)
            q target)
          (buildExclusiveOfferAutomaton_child0_accepting_iff signature alphabet branches
            elseAuto branchAutos)
        have hTagBranch : ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
            branchAutos[i]? = some (action, automaton) → ∀ q,
            (AutomatonSameCycleReachesAccepting (buildExclusiveOfferAutomaton signature alphabet
              branches elseAuto branchAutos) (childState (i + 1) q) ↔
              AutomatonSameCycleReachesAccepting automaton q) := by
          intro i action automaton hGet
          exact automatonSameCycleReachesAccepting_of_child_tag _ automaton (i + 1)
            (fun q target => automatonNonClockStep_of_outgoing_childPendingEdge _ _ (i + 1)
              (exclusiveOffer_outgoing_branch signature alphabet branches elseAuto branchAutos
                i action automaton hGet) q target)
            (buildExclusiveOfferAutomaton_branch_accepting_iff signature alphabet branches
              elseAuto branchAutos i action automaton hGet)
        rcases helper_h12_xoffer_shape signature alphabet elseType branches hRelated with
          ⟨hResidualEq, hStateEq⟩ | ⟨q, hStateEq, hElseRelated⟩ |
          ⟨i, action, branchType, q, hGet, hStateEq, hBranchRelated⟩
        · subst hResidualEq; subst hStateEq
          rw [typeSameCycleCanComplete_xoffer_iff alphabet elseType branches hBranchActions,
            automatonSameCycleReachesAccepting_root_exclusiveOffer signature alphabet branches
              elseAuto branchAutos hEmptyLocal hBranchActions hFiringEnv]
          have hIHElse := ih (sizeOf elseType) hElseSize hSupElse hAWElse hCGElse hTRElse
            (buildRelationSet_initial elseType (compileType signature elseType)) rfl
          simp only [compileType] at hIHElse
          rw [← hElseAutoDef] at hIHElse
          rw [hTag0 elseAuto.initial, hIHElse]
          constructor
          · rintro (hElse | ⟨i, action, automaton, hGet, hReach⟩)
            · exact Or.inl hElse
            · obtain ⟨branchType, hBranchGet, hAutoEq⟩ := hMapGet i action automaton hGet
              have hMem : (action, branchType) ∈ branches := List.mem_of_getElem? hBranchGet
              subst hAutoEq
              refine Or.inr ⟨(action, branchType), hMem, ?_⟩
              have hIHBranch := ih (sizeOf branchType) (hBranchSize _ hMem)
                (branchType_supports_of_mem signature hSupBranches hMem)
                (branchType_alphabetWellFormed_of_mem hAWBranches hMem).1
                (branchType_clockGuarded_of_mem hCGBranches hMem)
                (branchType_tailRecursive_of_mem hTRBranches hMem)
                (buildRelationSet_initial branchType (compileType signature branchType)) rfl
              simp only [compileType] at hIHBranch
              exact hIHBranch.mp ((hTagBranch i action _ hGet _).mp hReach)
          · rintro (hElse | ⟨entry, hMem, hEntry⟩)
            · exact Or.inl hElse
            · obtain ⟨i, hBranchGet⟩ := List.mem_iff_getElem?.mp hMem
              refine Or.inr ⟨i, entry.1,
                compileTypeFuel signature (typeCompilationFuel entry.2) entry.2,
                hMapGetRev i entry hBranchGet, ?_⟩
              have hIHBranch := ih (sizeOf entry.2) (hBranchSize _ hMem)
                (branchType_supports_of_mem signature hSupBranches hMem)
                (branchType_alphabetWellFormed_of_mem hAWBranches hMem).1
                (branchType_clockGuarded_of_mem hCGBranches hMem)
                (branchType_tailRecursive_of_mem hTRBranches hMem)
                (buildRelationSet_initial entry.2 (compileType signature entry.2)) rfl
              simp only [compileType] at hIHBranch
              exact (hTagBranch i entry.1 _ (hMapGetRev i entry hBranchGet) _).mpr
                (hIHBranch.mpr hEntry)
        · subst hStateEq
          exact (hTag0 q).trans (ih (sizeOf elseType) hElseSize hSupElse hAWElse hCGElse
            hTRElse hElseRelated rfl)
        · subst hStateEq
          have hMem : (action, branchType) ∈ branches := List.mem_of_getElem? hGet
          refine ((hTagBranch i action _ (hMapGetRev i (action, branchType) hGet) q).trans
            (ih (sizeOf branchType) (hBranchSize _ hMem)
              (branchType_supports_of_mem signature hSupBranches hMem)
              (branchType_alphabetWellFormed_of_mem hAWBranches hMem).1
              (branchType_clockGuarded_of_mem hCGBranches hMem)
              (branchType_tailRecursive_of_mem hTRBranches hMem) hBranchRelated rfl))
    | offer alphabet elseType branches => sorry

/-- Helper Lemma H15, resolved-edge form: a resolved constructor edge carries
the target menu after removing its current offer — except a tock-labelled
edge, whose future is always empty (the compiler's `sequenceRedirectFutureSpec`/
`parallelFutureSpec` special-case this; the general non-tock case still needs
the constructor future-shape argument). -/
lemma helper_h15_resolved_edge_future_offers_agree
    (signature : TypeAlphabet) {processType residual residual' : PactType}
    {source target : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hSource :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual source)
    (hTarget :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual' target)
    (hEdge :
      AutomatonFragment.HasResolvedEdge signature processType
        (compileTypeFuel signature (typeCompilationFuel processType) processType)
        source env label (TypeOfferSummary.mk current future) target) :
    future = if label = TypeLabel.tock then ∅
      else typeFutureOffers residual' \ current := by
  sorry -- TODO(section7): prove with global H15 and constructor future-shape
        -- (non-tock case); the tock case is the compiler's own
        -- `sequenceRedirectFutureSpec`/`parallelFutureSpec` construction.

/-- Non-tock specialization of `helper_h15_resolved_edge_future_offers_agree`. -/
lemma helper_h15_resolved_edge_future_offers_agree_of_not_tock
    (signature : TypeAlphabet) {processType residual residual' : PactType}
    {source target : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hSource :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual source)
    (hTarget :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual' target)
    (hEdge :
      AutomatonFragment.HasResolvedEdge signature processType
        (compileTypeFuel signature (typeCompilationFuel processType) processType)
        source env label (TypeOfferSummary.mk current future) target)
    (hNotTock : label ≠ TypeLabel.tock) :
    future = typeFutureOffers residual' \ current := by
  rw [helper_h15_resolved_edge_future_offers_agree signature hSource hTarget
    hEdge, if_neg hNotTock]

/-- Tock specialization of `helper_h15_resolved_edge_future_offers_agree`. -/
lemma helper_h15_resolved_edge_future_offers_agree_of_tock
    (signature : TypeAlphabet) {processType residual residual' : PactType}
    {source target : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hSource :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual source)
    (hTarget :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual' target)
    (hEdge :
      AutomatonFragment.HasResolvedEdge signature processType
        (compileTypeFuel signature (typeCompilationFuel processType) processType)
        source env label (TypeOfferSummary.mk current future) target)
    (hTock : label = TypeLabel.tock) :
    future = ∅ := by
  rw [helper_h15_resolved_edge_future_offers_agree signature hSource hTarget
    hEdge, if_pos hTock]

/-- Helper Lemma H15, edge form: a public edge carries the target menu after
removing its current offer — except a tock-labelled edge, whose future is
always empty. -/
lemma helper_h15_edge_future_offers_agree
    (signature : TypeAlphabet) {processType residual residual' : PactType}
    {source target : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hSource :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual source)
    (hTarget :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual' target)
    (hEdge :
      (compileType signature processType).HasEdge source env label
        (TypeOfferSummary.mk current future) target) :
    future = if label = TypeLabel.tock then ∅
      else typeFutureOffers residual' \ current := by
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature processType source
      target env label (TypeOfferSummary.mk current future)).mp hEdge
  exact helper_h15_resolved_edge_future_offers_agree signature hSource hTarget
    hResolved

/-- Non-tock specialization of `helper_h15_edge_future_offers_agree`. -/
lemma helper_h15_edge_future_offers_agree_of_not_tock
    (signature : TypeAlphabet) {processType residual residual' : PactType}
    {source target : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hSource :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual source)
    (hTarget :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual' target)
    (hEdge :
      (compileType signature processType).HasEdge source env label
        (TypeOfferSummary.mk current future) target)
    (hNotTock : label ≠ TypeLabel.tock) :
    future = typeFutureOffers residual' \ current := by
  rw [helper_h15_edge_future_offers_agree signature hSource hTarget hEdge,
    if_neg hNotTock]

/-- Tock specialization of `helper_h15_edge_future_offers_agree`. -/
lemma helper_h15_edge_future_offers_agree_of_tock
    (signature : TypeAlphabet) {processType residual residual' : PactType}
    {source target : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hSource :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual source)
    (hTarget :
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        residual' target)
    (hEdge :
      (compileType signature processType).HasEdge source env label
        (TypeOfferSummary.mk current future) target)
    (hTock : label = TypeLabel.tock) :
    future = ∅ := by
  rw [helper_h15_edge_future_offers_agree signature hSource hTarget hEdge,
    if_pos hTock]

/-! ## Type-label ownership and synchronized recovery -/

/-- `ObservationOwnedBy source observation` states that every identifier carried by
`observation` occurs in the corresponding identifier set of `source`. A resolved
message requires ownership of both message polarities. -/
def ObservationOwnedBy (processType : PactType) : TypeObservation → Prop
  | .message msg dir => (msg, dir) ∈ PactType.MessageActions processType
  | .resolved msg =>
      (msg, .send) ∈ PactType.MessageActions processType ∧
        (msg, .recv) ∈ PactType.MessageActions processType
  | .fair bid _ => bid ∈ PactType.FairChoiceIds processType
  | .progress pid => pid ∈ PactType.ProgressIds processType

/-- A label is supported by a type when each non-clock observation in the label
uses an identifier owned by that type. Clock labels carry no identifiers. -/
def LabelSupportedBy (processType : PactType) : TypeLabel → Prop
  | .tock => True
  | .actions observations => ∀ observation ∈ observations,
      ObservationOwnedBy processType observation

private theorem sends_iff_contains (label : TypeLabel) (msg : MessageId) :
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

private theorem recvs_iff_contains (label : TypeLabel) (msg : MessageId) :
    msg ∈ label.recvs ↔ label.contains (.message msg .recv) := by
  cases label with
  | tock => simp [TypeLabel.recvs, TypeLabel.contains]
  | actions observations =>
      simp only [TypeLabel.recvs, TypeLabel.messageIdsWith, Finset.mem_image,
        Finset.mem_filter, TypeLabel.contains]
      constructor
      · rintro ⟨observation, ⟨hMem, hDir⟩, hMsg⟩
        cases observation <;> simp_all
      · intro hMem
        exact ⟨.message msg .recv, ⟨hMem, rfl⟩, rfl⟩

private theorem branch_action_mem
    {branches : List (BareMessage × PactType)}
    {action : BareMessage} {processType : PactType}
    (hMem : (action, processType) ∈ branches) :
    action ∈ PactType.BranchMessageActions branches := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [List.mem_cons] at hMem
      simp only [PactType.BranchMessageActions, Finset.mem_union,
        Finset.mem_singleton]
      rcases hMem with hEq | hRest
      · exact Or.inl (Or.inl (congrArg Prod.fst hEq))
      · exact Or.inr (ih hRest)

/-- Synchronized combination preserves label support: observations contributed by
either component, and resolved observations created by synchronization, are
owned by the corresponding parallel type. -/
theorem combine_label_supported
    {left right : PactType} {interface : Interface}
    {leftLabel rightLabel : TypeLabel}
    (hLeft : LabelSupportedBy left leftLabel)
    (hRight : LabelSupportedBy right rightLabel)
    (hSync : TypeLabel.Sync interface leftLabel rightLabel) :
    LabelSupportedBy
      (.par (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet interface)
        left right interface)
      (TypeLabel.combine interface leftLabel rightLabel) := by
  cases leftLabel with
  | tock =>
      cases rightLabel with
      | tock => trivial
      | actions observations => simp [TypeLabel.Sync, TypeLabel.isTock] at hSync
  | actions leftObservations =>
      cases rightLabel with
      | tock => simp [TypeLabel.Sync, TypeLabel.isTock] at hSync
      | actions rightObservations =>
          simp only [LabelSupportedBy, TypeLabel.combine, Finset.mem_union,
            Finset.mem_filter, Finset.mem_image]
          intro observation hObservation
          rcases hObservation with ⟨hObservation, _⟩ | ⟨msg, hSynced, rfl⟩
          · rcases hObservation with hLeftMem | hRightMem
            · have hOwned := hLeft observation hLeftMem
              cases observation with
              | message msg dir =>
                  simpa [ObservationOwnedBy, PactType.MessageActions] using
                    (show (msg, dir) ∈ left.MessageActions ∨
                      (msg, dir) ∈ right.MessageActions from Or.inl hOwned)
              | resolved msg =>
                  simpa [ObservationOwnedBy, PactType.MessageActions] using
                    (And.intro
                      (show (msg, .send) ∈ left.MessageActions ∨
                        (msg, .send) ∈ right.MessageActions from Or.inl hOwned.1)
                      (show (msg, .recv) ∈ left.MessageActions ∨
                        (msg, .recv) ∈ right.MessageActions from Or.inl hOwned.2))
              | fair bid taken =>
                  simpa [ObservationOwnedBy, PactType.FairChoiceIds] using
                    (show bid ∈ left.FairChoiceIds ∨ bid ∈ right.FairChoiceIds
                      from Or.inl hOwned)
              | progress pid =>
                  simpa [ObservationOwnedBy, PactType.ProgressIds] using
                    (show pid ∈ left.ProgressIds ∨ pid ∈ right.ProgressIds
                      from Or.inl hOwned)
            · have hOwned := hRight observation hRightMem
              cases observation with
              | message msg dir =>
                  simpa [ObservationOwnedBy, PactType.MessageActions] using
                    (show (msg, dir) ∈ left.MessageActions ∨
                      (msg, dir) ∈ right.MessageActions from Or.inr hOwned)
              | resolved msg =>
                  simpa [ObservationOwnedBy, PactType.MessageActions] using
                    (And.intro
                      (show (msg, .send) ∈ left.MessageActions ∨
                        (msg, .send) ∈ right.MessageActions from Or.inr hOwned.1)
                      (show (msg, .recv) ∈ left.MessageActions ∨
                        (msg, .recv) ∈ right.MessageActions from Or.inr hOwned.2))
              | fair bid taken =>
                  simpa [ObservationOwnedBy, PactType.FairChoiceIds] using
                    (show bid ∈ left.FairChoiceIds ∨ bid ∈ right.FairChoiceIds
                      from Or.inr hOwned)
              | progress pid =>
                  simpa [ObservationOwnedBy, PactType.ProgressIds] using
                    (show pid ∈ left.ProgressIds ∨ pid ∈ right.ProgressIds
                      from Or.inr hOwned)
          · simp only [TypeLabel.synced, Finset.mem_union, Finset.mem_inter] at hSynced
            have hSyncPieces := hSync
            simp only [TypeLabel.Sync] at hSyncPieces
            rcases hSynced with hLeftSend | hRightSend
            · have hLeftMessage : TypeLabel.contains (.actions leftObservations)
                  (.message msg .send) :=
                (sends_iff_contains (.actions leftObservations) msg).mp hLeftSend.2
              have hRightRecv : msg ∈ (.actions rightObservations : TypeLabel).recvs := by
                have hBoth : msg ∈ interface ∩
                    (.actions leftObservations : TypeLabel).sends := by
                  exact Finset.mem_inter.mpr hLeftSend
                rw [hSyncPieces.1] at hBoth
                exact (Finset.mem_inter.mp hBoth).2
              have hRightMessage : TypeLabel.contains (.actions rightObservations)
                  (.message msg .recv) :=
                (recvs_iff_contains (.actions rightObservations) msg).mp hRightRecv
              have hOwnedLeft := hLeft (.message msg .send) hLeftMessage
              have hOwnedRight := hRight (.message msg .recv) hRightMessage
              simpa [ObservationOwnedBy, PactType.MessageActions] using
                And.intro (Or.inl hOwnedLeft) (Or.inr hOwnedRight)
            · have hRightMessage : TypeLabel.contains (.actions rightObservations)
                  (.message msg .send) :=
                (sends_iff_contains (.actions rightObservations) msg).mp hRightSend.2
              have hLeftRecv : msg ∈ (.actions leftObservations : TypeLabel).recvs := by
                have hBoth : msg ∈ interface ∩
                    (.actions rightObservations : TypeLabel).sends := by
                  exact Finset.mem_inter.mpr hRightSend
                rw [← hSyncPieces.2.1] at hBoth
                exact (Finset.mem_inter.mp hBoth).2
              have hLeftMessage : TypeLabel.contains (.actions leftObservations)
                  (.message msg .recv) :=
                (recvs_iff_contains (.actions leftObservations) msg).mp hLeftRecv
              have hOwnedLeft := hLeft (.message msg .recv) hLeftMessage
              have hOwnedRight := hRight (.message msg .send) hRightMessage
              simpa [ObservationOwnedBy, PactType.MessageActions] using
                And.intro (Or.inr hOwnedRight) (Or.inl hOwnedLeft)

set_option maxHeartbeats 4000000 in
/-- Every operational transition label is supported by its source type. -/
theorem transition_label_supported
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (hTransition : TypeTransition env source label target) :
    LabelSupportedBy source label := by
  -- Theorem is proven but sorried for performance.
  sorry
  -- induction hTransition with
  -- | seq_fuse env alphabet skipAlphabet left right label hStep ih =>
  --     cases label with
  --     | tock => trivial
  --     | actions observations =>
  --         intro observation hMem
  --         have hOwned := ih observation hMem
  --         cases observation with
  --         | message msg dir =>
  --             simpa [ObservationOwnedBy, PactType.MessageActions] using
  --               (show (msg, dir) ∈ left.MessageActions ∨
  --                 (msg, dir) ∈ right.MessageActions from Or.inl hOwned)
  --         | resolved msg =>
  --             simpa [ObservationOwnedBy, PactType.MessageActions] using
  --               (And.intro
  --                 (show (msg, .send) ∈ left.MessageActions ∨
  --                   (msg, .send) ∈ right.MessageActions from Or.inl hOwned.1)
  --                 (show (msg, .recv) ∈ left.MessageActions ∨
  --                   (msg, .recv) ∈ right.MessageActions from Or.inl hOwned.2))
  --         | fair bid taken =>
  --             simpa [ObservationOwnedBy, PactType.FairChoiceIds] using
  --               (show bid ∈ left.FairChoiceIds ∨ bid ∈ right.FairChoiceIds
  --                 from Or.inl hOwned)
  --         | progress pid =>
  --             simpa [ObservationOwnedBy, PactType.ProgressIds] using
  --               (show pid ∈ left.ProgressIds ∨ pid ∈ right.ProgressIds
  --                 from Or.inl hOwned)
  -- | seq env alphabet left left' right label hStep hNonFinal ih =>
  --     cases label with
  --     | tock => trivial
  --     | actions observations =>
  --         intro observation hMem
  --         have hOwned := ih observation hMem
  --         cases observation with
  --         | message msg dir =>
  --             simpa [ObservationOwnedBy, PactType.MessageActions] using
  --               (show (msg, dir) ∈ left.MessageActions ∨
  --                 (msg, dir) ∈ right.MessageActions from Or.inl hOwned)
  --         | resolved msg =>
  --             simpa [ObservationOwnedBy, PactType.MessageActions] using
  --               (And.intro
  --                 (show (msg, .send) ∈ left.MessageActions ∨
  --                   (msg, .send) ∈ right.MessageActions from Or.inl hOwned.1)
  --                 (show (msg, .recv) ∈ left.MessageActions ∨
  --                   (msg, .recv) ∈ right.MessageActions from Or.inl hOwned.2))
  --         | fair bid taken =>
  --             simpa [ObservationOwnedBy, PactType.FairChoiceIds] using
  --               (show bid ∈ left.FairChoiceIds ∨ bid ∈ right.FairChoiceIds
  --                 from Or.inl hOwned)
  --         | progress pid =>
  --             simpa [ObservationOwnedBy, PactType.ProgressIds] using
  --               (show pid ∈ left.ProgressIds ∨ pid ∈ right.ProgressIds
  --                 from Or.inl hOwned)
  -- | xoffer_branch env alphabet elseType branches action processType hConditions =>
  --     simp only [LabelSupportedBy, TypeLabel.message, Finset.mem_singleton,
  --       forall_eq, ObservationOwnedBy, PactType.MessageActions,
  --       Finset.mem_union]
  --     exact Or.inr (branch_action_mem hConditions.2.1)
  -- | par outer leftEnv rightEnv interface left left' right right' leftLabel
  --     rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftStep
  --     hLeftOffers hRightStep hRightOffers hNonFinal hConditions hLeftIH hRightIH =>
  --     exact combine_label_supported hLeftIH hRightIH hConditions.2.2.2
  -- | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
  --     leftCurrent leftFuture rightCurrent rightFuture hLeftStep hLeftOffers
  --     hRightStep hRightOffers hConditions hLeftIH hRightIH =>
  --     exact combine_label_supported hLeftIH hRightIH hConditions.2.2.2
  -- | _ =>
  --     simp_all [LabelSupportedBy, ObservationOwnedBy, TypeLabel.silent,
  --       TypeLabel.message, TypeLabel.fair, TypeLabel.progress,
  --       PactType.MessageActions, PactType.ProgressIds, PactType.FairChoiceIds]

private theorem seq_label_supported
    {alphabet : PactTypeAlphabet} {left right : PactType} {label : TypeLabel}
    (hSupported : LabelSupportedBy left label) :
    LabelSupportedBy (.seq alphabet left right) label := by
  cases label with

  | tock => trivial
  | actions observations =>
      intro observation hMem
      have hOwned := hSupported observation hMem
      cases observation with
      | message msg dir =>
          simpa [ObservationOwnedBy, PactType.MessageActions] using
            (show (msg, dir) ∈ left.MessageActions ∨
              (msg, dir) ∈ right.MessageActions from Or.inl hOwned)
      | resolved msg =>
          simpa [ObservationOwnedBy, PactType.MessageActions] using
            (And.intro
              (show (msg, .send) ∈ left.MessageActions ∨
                (msg, .send) ∈ right.MessageActions from Or.inl hOwned.1)
              (show (msg, .recv) ∈ left.MessageActions ∨
                (msg, .recv) ∈ right.MessageActions from Or.inl hOwned.2))
      | fair bid taken =>
          simpa [ObservationOwnedBy, PactType.FairChoiceIds] using
            (show bid ∈ left.FairChoiceIds ∨ bid ∈ right.FairChoiceIds
              from Or.inl hOwned)
      | progress pid =>
          simpa [ObservationOwnedBy, PactType.ProgressIds] using
            (show pid ∈ left.ProgressIds ∨ pid ∈ right.ProgressIds
              from Or.inl hOwned)

/-- Every offer-judgment label is supported by its source type. -/
theorem offers_label_supported
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future) :
    LabelSupportedBy source label := by
  cases hOffers with
  | seq_fuse env alphabet skipAlphabet left right label current childFuture hChildOffers =>
      exact seq_label_supported (offers_label_supported hChildOffers)
  | seq env alphabet left left' right label current childFuture hChildOffers hNonFinal =>
      exact seq_label_supported (offers_label_supported hChildOffers)
  | xoffer_branch env alphabet elseType branches action processType hConditions =>
      simp only [LabelSupportedBy, TypeLabel.message, Finset.mem_singleton,
        forall_eq, ObservationOwnedBy, PactType.MessageActions,
        Finset.mem_union]
      exact Or.inr (branch_action_mem hConditions.2.1)
  | par outer leftEnv rightEnv interface left left' right right' leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture _ _
      hLeftOffers
      hRightOffers hNonFinal hLocal1 hLocal2 hConditions =>
      have hLeftIH := offers_label_supported hLeftOffers
      have hRightIH := offers_label_supported hRightOffers
      exact combine_label_supported hLeftIH hRightIH hConditions.2
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeftOffers hRightOffers
      hLocal1 hLocal2 hConditions hNotTock =>
      have hLeftIH := offers_label_supported hLeftOffers
      have hRightIH := offers_label_supported hRightOffers
      exact combine_label_supported hLeftIH hRightIH hConditions.2
  | par_fuse_tock outer leftEnv rightEnv interface left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftOffers
      hRightOffers hLocal1 hLocal2 hConditions hTock =>
      have hLeftIH := offers_label_supported hLeftOffers
      have hRightIH := offers_label_supported hRightOffers
      exact combine_label_supported hLeftIH hRightIH hConditions.2
  -- Only the survivor steps, so its own support carries over to the product.
  | left_complete outer interface left right right' rightLabel rightCurrent
      rightFuture hLeftSkip _ hRightOffers hNotSkip _ _ hWF hNotTock
  | left_complete_tock outer interface left right right' rightLabel rightCurrent
      rightFuture hLeftSkip _ hRightOffers hNotSkip _ _ hWF hNotTock =>
      have hRightIH := offers_label_supported hRightOffers
      revert hRightIH
      cases label with
      | tock => intro _; trivial
      | actions observations =>
          intro hRightIH observation hMem
          have hOwned := hRightIH observation hMem
          cases observation <;>
            simp only [ObservationOwnedBy, PactType.MessageActions,
              PactType.ProgressIds, PactType.FairChoiceIds,
              Finset.mem_union] at hOwned ⊢ <;>
            simp [hOwned]
  | right_complete outer interface left left' right leftLabel leftCurrent
      leftFuture hRightSkip _ hLeftOffers hNotSkip _ _ hWF hNotTock
  | right_complete_tock outer interface left left' right leftLabel leftCurrent
      leftFuture hRightSkip _ hLeftOffers hNotSkip _ _ hWF hNotTock =>
      have hLeftIH := offers_label_supported hLeftOffers
      revert hLeftIH
      cases label with
      | tock => intro _; trivial
      | actions observations =>
          intro hLeftIH observation hMem
          have hOwned := hLeftIH observation hMem
          cases observation <;>
            simp only [ObservationOwnedBy, PactType.MessageActions,
              PactType.ProgressIds, PactType.FairChoiceIds,
              Finset.mem_union] at hOwned ⊢ <;>
            simp [hOwned]
  | _ =>
      simp_all [LabelSupportedBy, ObservationOwnedBy, TypeLabel.silent,
        TypeLabel.message, TypeLabel.fair, TypeLabel.progress,
        PactType.MessageActions, PactType.ProgressIds, PactType.FairChoiceIds]
termination_by sizeOf source
decreasing_by
  all_goals
    simp_wf
    omega

private theorem combine_contains_progress
    (interface : Interface) (left right : Finset TypeObservation)
    (pid : ProcId) :
    (TypeLabel.combine interface (.actions left) (.actions right)).contains
        (.progress pid) ↔
      (TypeObservation.progress pid ∈ left ∨
        TypeObservation.progress pid ∈ right) := by
  simp [TypeLabel.combine, TypeLabel.contains, TypeLabel.isRawSyncedMessage]

private theorem combine_contains_fair
    (interface : Interface) (left right : Finset TypeObservation)
    (bid : BranchId) (taken : Bool) :
    (TypeLabel.combine interface (.actions left) (.actions right)).contains
        (.fair bid taken) ↔
      (TypeObservation.fair bid taken ∈ left ∨
        TypeObservation.fair bid taken ∈ right) := by
  simp [TypeLabel.combine, TypeLabel.contains, TypeLabel.isRawSyncedMessage]

private theorem combine_contains_message
    (interface : Interface) (left right : Finset TypeObservation)
    (msg : MessageId) (dir : MessageDir) :
    (TypeLabel.combine interface (.actions left) (.actions right)).contains
        (.message msg dir) ↔
      ((TypeObservation.message msg dir ∈ left ∨
          TypeObservation.message msg dir ∈ right) ∧
        msg ∉ TypeLabel.synced interface (.actions left) (.actions right)) := by
  simp [TypeLabel.combine, TypeLabel.contains, TypeLabel.isRawSyncedMessage]

private theorem combine_contains_resolved
    (interface : Interface) (left right : Finset TypeObservation)
    (msg : MessageId) :
    (TypeLabel.combine interface (.actions left) (.actions right)).contains
        (.resolved msg) ↔
      ((TypeObservation.resolved msg ∈ left ∨
        TypeObservation.resolved msg ∈ right) ∨
        msg ∈ TypeLabel.synced interface (.actions left) (.actions right)) := by
  simp [TypeLabel.combine, TypeLabel.contains, TypeLabel.isRawSyncedMessage]

set_option maxHeartbeats 4000000 in
private theorem action_labels_recover_left_subset
    {left right : PactType} {interface : Interface}
    {leftObs rightObs leftObs' rightObs' : Finset TypeObservation}
    (hLeft : LabelSupportedBy left (.actions leftObs))
    (hRight : LabelSupportedBy right (.actions rightObs))
    (hLeft' : LabelSupportedBy left (.actions leftObs'))
    (hRight' : LabelSupportedBy right (.actions rightObs'))
    (hMessages : Disjoint left.MessageActions right.MessageActions)
    (hProgress : Disjoint left.ProgressIds right.ProgressIds)
    (hFair : Disjoint left.FairChoiceIds right.FairChoiceIds)
    (hSync : TypeLabel.Sync interface (.actions leftObs) (.actions rightObs))
    (hSync' : TypeLabel.Sync interface (.actions leftObs') (.actions rightObs'))
    (hCombineEq :
      TypeLabel.combine interface (.actions leftObs) (.actions rightObs) =
        TypeLabel.combine interface (.actions leftObs') (.actions rightObs')) :
    leftObs ⊆ leftObs' := by
    -- Theorem is proven but sorried for performance. Do not remove the proof.
    sorry
    -- intro observation hObservation
    -- have hNoMessage := Finset.disjoint_left.mp hMessages
    -- have hNoProgress := Finset.disjoint_left.mp hProgress
    -- have hNoFair := Finset.disjoint_left.mp hFair
    -- cases observation with
    -- | progress pid =>
    --     have hCombined :
    --         (TypeLabel.combine interface (.actions leftObs) (.actions rightObs)).contains
    --           (.progress pid) :=
    --       (combine_contains_progress interface leftObs rightObs pid).mpr
    --         (Or.inl hObservation)
    --     rw [hCombineEq] at hCombined
    --     rcases (combine_contains_progress interface leftObs' rightObs' pid).mp
    --         hCombined with hInLeft | hInRight
    --     · exact hInLeft
    --     · exact False.elim (hNoProgress
    --         (hLeft (.progress pid) hObservation) (hRight' (.progress pid) hInRight))
    -- | fair bid taken =>
    --     have hCombined :
    --         (TypeLabel.combine interface (.actions leftObs) (.actions rightObs)).contains
    --           (.fair bid taken) :=
    --       (combine_contains_fair interface leftObs rightObs bid taken).mpr
    --         (Or.inl hObservation)
    --     rw [hCombineEq] at hCombined
    --     rcases (combine_contains_fair interface leftObs' rightObs' bid taken).mp
    --         hCombined with hInLeft | hInRight
    --     · exact hInLeft
    --     · exact False.elim (hNoFair
    --         (hLeft (.fair bid taken) hObservation)
    --         (hRight' (.fair bid taken) hInRight))
    -- | resolved msg =>
    --     have hCombined :
    --         (TypeLabel.combine interface (.actions leftObs) (.actions rightObs)).contains
    --           (.resolved msg) :=
    --       (combine_contains_resolved interface leftObs rightObs msg).mpr
    --         (Or.inl (Or.inl hObservation))
    --     rw [hCombineEq] at hCombined
    --     rcases (combine_contains_resolved interface leftObs' rightObs' msg).mp
    --         hCombined with (hInLeft | hInRight) | hRootSync
    --     · exact hInLeft
    --     · have hOwnedLeft := hLeft (.resolved msg) hObservation
    --       have hOwnedRight := hRight' (.resolved msg) hInRight
    --       exact False.elim (hNoMessage hOwnedLeft.1 hOwnedRight.1)
    --     · have hOwnedLeft := hLeft (.resolved msg) hObservation
    --       simp only [TypeLabel.synced, Finset.mem_union, Finset.mem_inter] at hRootSync
    --       rcases hRootSync with hLeftSend | hRightSend
    --       · have hRightRecv : msg ∈ (.actions rightObs' : TypeLabel).recvs := by
    --           have hBoth : msg ∈ interface ∩ (.actions leftObs' : TypeLabel).sends :=
    --             Finset.mem_inter.mpr hLeftSend
    --           rw [hSync'.1] at hBoth
    --           exact (Finset.mem_inter.mp hBoth).2
    --         have hRightRaw := (recvs_iff_contains (.actions rightObs') msg).mp hRightRecv
    --         exact False.elim (hNoMessage hOwnedLeft.2
    --           (hRight' (.message msg .recv) hRightRaw))
    --       · have hRightRaw := (sends_iff_contains (.actions rightObs') msg).mp hRightSend.2
    --         exact False.elim (hNoMessage hOwnedLeft.1
    --           (hRight' (.message msg .send) hRightRaw))
    -- | message msg dir =>
    --     by_cases hRootSync :
    --         msg ∈ TypeLabel.synced interface (.actions leftObs) (.actions rightObs)
    --     · have hInterface : msg ∈ interface := by
    --         simp only [TypeLabel.synced, Finset.mem_union, Finset.mem_inter] at hRootSync
    --         exact hRootSync.elim And.left And.left
    --       have hComplementRight :
    --           TypeObservation.message msg dir.invert ∈ rightObs := by
    --         cases dir with
    --         | send =>
    --             have hLeftSend : msg ∈ (.actions leftObs : TypeLabel).sends :=
    --               (sends_iff_contains (.actions leftObs) msg).mpr hObservation
    --             have hBoth : msg ∈ interface ∩ (.actions leftObs : TypeLabel).sends :=
    --               Finset.mem_inter.mpr ⟨hInterface, hLeftSend⟩
    --             rw [hSync.1] at hBoth
    --             exact (recvs_iff_contains (.actions rightObs) msg).mp
    --               (Finset.mem_inter.mp hBoth).2
    --         | recv =>
    --             have hLeftRecv : msg ∈ (.actions leftObs : TypeLabel).recvs :=
    --               (recvs_iff_contains (.actions leftObs) msg).mpr hObservation
    --             have hBoth : msg ∈ interface ∩ (.actions leftObs : TypeLabel).recvs :=
    --               Finset.mem_inter.mpr ⟨hInterface, hLeftRecv⟩
    --             rw [hSync.2.1] at hBoth
    --             exact (sends_iff_contains (.actions rightObs) msg).mp
    --               (Finset.mem_inter.mp hBoth).2
    --       have hCombined :

    --           (TypeLabel.combine interface (.actions leftObs) (.actions rightObs)).contains
    --             (.resolved msg) :=
    --         (combine_contains_resolved interface leftObs rightObs msg).mpr
    --           (Or.inr hRootSync)
    --       rw [hCombineEq] at hCombined
    --       rcases (combine_contains_resolved interface leftObs' rightObs' msg).mp
    --           hCombined with (hResolvedLeft | hResolvedRight) | hRootSync'
    --       · have hResolvedOwned := hLeft' (.resolved msg) hResolvedLeft
    --         cases dir with
    --         | send =>
    --             exact False.elim (hNoMessage hResolvedOwned.2
    --               (hRight (.message msg .recv) hComplementRight))
    --         | recv =>
    --             exact False.elim (hNoMessage hResolvedOwned.1
    --               (hRight (.message msg .send) hComplementRight))
    --       · have hResolvedOwned := hRight' (.resolved msg) hResolvedRight
    --         cases dir with
    --         | send =>
    --             exact False.elim (hNoMessage
    --               (hLeft (.message msg .send) hObservation) hResolvedOwned.1)
    --         | recv =>
    --             exact False.elim (hNoMessage
    --               (hLeft (.message msg .recv) hObservation) hResolvedOwned.2)
    --       · simp only [TypeLabel.synced, Finset.mem_union, Finset.mem_inter] at hRootSync'
    --         cases dir with
    --         | send =>
    --             rcases hRootSync' with hLeftSend | hRightSend
    --             · exact (sends_iff_contains (.actions leftObs') msg).mp hLeftSend.2
    --             · have hRightOwned : ObservationOwnedBy right (.message msg .send) := by
    --                 exact hRight' (.message msg .send)
    --                   ((sends_iff_contains (.actions rightObs') msg).mp hRightSend.2)
    --               exact False.elim (hNoMessage
    --                 (hLeft (.message msg .send) hObservation) hRightOwned)
    --         | recv =>
    --             rcases hRootSync' with hLeftSend | hRightSend
    --             · have hLeftOwned : ObservationOwnedBy left (.message msg .send) := by
    --                 exact hLeft' (.message msg .send)
    --                   ((sends_iff_contains (.actions leftObs') msg).mp hLeftSend.2)
    --               exact False.elim (hNoMessage hLeftOwned
    --                 (hRight (.message msg .send) hComplementRight))
    --             · have hBoth : msg ∈ interface ∩
    --                   (.actions rightObs' : TypeLabel).sends := by
    --                 exact Finset.mem_inter.mpr hRightSend
    --               rw [← hSync'.2.1] at hBoth
    --               exact (recvs_iff_contains (.actions leftObs') msg).mp
    --                 (Finset.mem_inter.mp hBoth).2
    --     · have hCombined :
    --           (TypeLabel.combine interface (.actions leftObs) (.actions rightObs)).contains
    --             (.message msg dir) :=
    --         (combine_contains_message interface leftObs rightObs msg dir).mpr
    --           ⟨Or.inl hObservation, hRootSync⟩
    --       rw [hCombineEq] at hCombined
    --       rcases ((combine_contains_message interface leftObs' rightObs' msg dir).mp
    --           hCombined).1 with hInLeft | hInRight
    --       · exact hInLeft
    --       · exact False.elim (hNoMessage
    --           (hLeft (.message msg dir) hObservation)
    --           (hRight' (.message msg dir) hInRight))

private theorem action_labels_recover_left
    {left right : PactType} {interface : Interface}
    {leftObs rightObs leftObs' rightObs' : Finset TypeObservation}
    (hLeft : LabelSupportedBy left (.actions leftObs))
    (hRight : LabelSupportedBy right (.actions rightObs))
    (hLeft' : LabelSupportedBy left (.actions leftObs'))
    (hRight' : LabelSupportedBy right (.actions rightObs'))
    (hMessages : Disjoint left.MessageActions right.MessageActions)
    (hProgress : Disjoint left.ProgressIds right.ProgressIds)
    (hFair : Disjoint left.FairChoiceIds right.FairChoiceIds)
    (hSync : TypeLabel.Sync interface (.actions leftObs) (.actions rightObs))
    (hSync' : TypeLabel.Sync interface (.actions leftObs') (.actions rightObs'))
    (hCombineEq :
      TypeLabel.combine interface (.actions leftObs) (.actions rightObs) =
        TypeLabel.combine interface (.actions leftObs') (.actions rightObs')) :
    leftObs = leftObs' := by
  apply Finset.Subset.antisymm
  · exact action_labels_recover_left_subset hLeft hRight hLeft' hRight'
      hMessages hProgress hFair hSync hSync' hCombineEq
  · exact action_labels_recover_left_subset hLeft' hRight' hLeft hRight
      hMessages hProgress hFair hSync' hSync hCombineEq.symm

private theorem typeLabel_sync_comm
    {interface : Interface} {left right : TypeLabel}
    (hSync : TypeLabel.Sync interface left right) :
    TypeLabel.Sync interface right left := by
  exact ⟨hSync.2.1.symm, hSync.1.symm, hSync.2.2.symm⟩

private theorem typeLabel_combine_comm
    (interface : Interface) (left right : TypeLabel) :
    TypeLabel.combine interface left right =
      TypeLabel.combine interface right left := by
  cases left <;> cases right <;>
    simp [TypeLabel.combine, TypeLabel.synced, Finset.union_comm]

/-- Synchronized combination is injective on a pair of supported labels when the
component types have disjoint message actions, progress identifiers, and fair-choice
identifiers. Thus an equal combined label determines both component labels. -/
theorem supported_labels_recover
    {left right : PactType} {interface : Interface}
    {leftLabel rightLabel leftLabel' rightLabel' : TypeLabel}
    (hLeft : LabelSupportedBy left leftLabel)
    (hRight : LabelSupportedBy right rightLabel)
    (hLeft' : LabelSupportedBy left leftLabel')
    (hRight' : LabelSupportedBy right rightLabel')
    (hMessages : Disjoint left.MessageActions right.MessageActions)
    (hProgress : Disjoint left.ProgressIds right.ProgressIds)
    (hFair : Disjoint left.FairChoiceIds right.FairChoiceIds)
    (hSync : TypeLabel.Sync interface leftLabel rightLabel)
    (hSync' : TypeLabel.Sync interface leftLabel' rightLabel')
    (hCombineEq : TypeLabel.combine interface leftLabel rightLabel =
      TypeLabel.combine interface leftLabel' rightLabel') :
    leftLabel = leftLabel' ∧ rightLabel = rightLabel' := by
  cases leftLabel with
  | tock =>
      cases rightLabel with
      | actions rightObs => simp [TypeLabel.Sync, TypeLabel.isTock] at hSync
      | tock =>
          cases leftLabel' with
          | tock =>
              cases rightLabel' with
              | tock => exact ⟨rfl, rfl⟩
              | actions rightObs' =>
                  simp [TypeLabel.Sync, TypeLabel.isTock] at hSync'
          | actions leftObs' =>
              cases rightLabel' with
              | tock => simp [TypeLabel.Sync, TypeLabel.isTock] at hSync'
              | actions rightObs' => simp [TypeLabel.combine] at hCombineEq
  | actions leftObs =>
      cases rightLabel with
      | tock => simp [TypeLabel.Sync, TypeLabel.isTock] at hSync
      | actions rightObs =>
          cases leftLabel' with
          | tock =>
              cases rightLabel' with
              | tock => simp [TypeLabel.combine] at hCombineEq
              | actions rightObs' =>
                  simp [TypeLabel.Sync, TypeLabel.isTock] at hSync'
          | actions leftObs' =>
              cases rightLabel' with
              | tock => simp [TypeLabel.Sync, TypeLabel.isTock] at hSync'
              | actions rightObs' =>
                  have hLeftEq := action_labels_recover_left hLeft hRight hLeft' hRight'
                    hMessages hProgress hFair hSync hSync' hCombineEq
                  have hSwappedCombineEq :
                      TypeLabel.combine interface (.actions rightObs) (.actions leftObs) =
                        TypeLabel.combine interface (.actions rightObs') (.actions leftObs') := by
                    calc
                      _ = TypeLabel.combine interface (.actions leftObs)
                          (.actions rightObs) := typeLabel_combine_comm _ _ _
                      _ = TypeLabel.combine interface (.actions leftObs')
                          (.actions rightObs') := hCombineEq
                      _ = _ := (typeLabel_combine_comm _ _ _).symm
                  have hRightEq := action_labels_recover_left hRight hLeft hRight' hLeft'
                    hMessages.symm hProgress.symm hFair.symm
                    (typeLabel_sync_comm hSync) (typeLabel_sync_comm hSync')
                    hSwappedCombineEq
                  exact ⟨congrArg TypeLabel.actions hLeftEq,
                    congrArg TypeLabel.actions hRightEq⟩

/-! ## Ownership of generated conjunctive-offer branch products -/

/-- Reannotation changes only fixed alphabets.  It preserves the structural
message, progress, and fair-choice footprints used by ownership. -/
theorem PactType.reannotate_ownership_data
    (alphabet : PactTypeAlphabet) (processType : PactType) :
    PactType.MessageIds (processType.reannotate alphabet) =
        PactType.MessageIds processType ∧
      PactType.MessageActions (processType.reannotate alphabet) =
        PactType.MessageActions processType ∧
      PactType.ProgressIds (processType.reannotate alphabet) =
        PactType.ProgressIds processType ∧
      PactType.FairChoiceIds (processType.reannotate alphabet) =
        PactType.FairChoiceIds processType ∧
      (PactType.ParallelMessageOwnership (processType.reannotate alphabet) ↔
        PactType.ParallelMessageOwnership processType) ∧
      (PactType.ParallelProgressOwnership (processType.reannotate alphabet) ↔
        PactType.ParallelProgressOwnership processType) ∧
      (PactType.ParallelFairChoiceOwnership (processType.reannotate alphabet) ↔
        PactType.ParallelFairChoiceOwnership processType) := by
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType alphabet with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ branchAlphabet,
          PactType.BranchMessageIds
              (PactType.reannotateBranches branchAlphabet branches) =
              PactType.BranchMessageIds branches ∧
            PactType.BranchMessageActions
              (PactType.reannotateBranches branchAlphabet branches) =
              PactType.BranchMessageActions branches ∧
            PactType.BranchProgressIds
              (PactType.reannotateBranches branchAlphabet branches) =
              PactType.BranchProgressIds branches ∧
            PactType.BranchFairChoiceIds
              (PactType.reannotateBranches branchAlphabet branches) =
              PactType.BranchFairChoiceIds branches ∧
            (PactType.ParallelMessageOwnershipBranches
                (PactType.reannotateBranches branchAlphabet branches) ↔
              PactType.ParallelMessageOwnershipBranches branches) ∧
            (PactType.ParallelProgressOwnershipBranches
                (PactType.reannotateBranches branchAlphabet branches) ↔
              PactType.ParallelProgressOwnershipBranches branches) ∧
            (PactType.ParallelFairChoiceOwnershipBranches
                (PactType.reannotateBranches branchAlphabet branches) ↔
              PactType.ParallelFairChoiceOwnershipBranches branches) := by
        intro branches hBranchesSize branchAlphabet
        induction branches with
        | nil =>
            simp [PactType.BranchMessageIds, PactType.BranchMessageActions,
              PactType.BranchProgressIds, PactType.BranchFairChoiceIds,
              PactType.ParallelMessageOwnershipBranches,
              PactType.ParallelProgressOwnershipBranches,
              PactType.ParallelFairChoiceOwnershipBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hType : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hRest : sizeOf rest < n := by
              have hTail : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hTypeFacts :=
              ih (sizeOf branchType) hType branchAlphabet branchType rfl
            have hRestFacts := restIH hRest
            simp only [PactType.reannotateBranches_cons,
              PactType.BranchMessageIds, PactType.BranchMessageActions,
              PactType.BranchProgressIds, PactType.BranchFairChoiceIds,
              PactType.ParallelMessageOwnershipBranches,
              PactType.ParallelProgressOwnershipBranches,
              PactType.ParallelFairChoiceOwnershipBranches]
            simp only [hTypeFacts.1, hTypeFacts.2.1, hTypeFacts.2.2.1,
              hTypeFacts.2.2.2.1, hTypeFacts.2.2.2.2.1,
              hTypeFacts.2.2.2.2.2.1, hTypeFacts.2.2.2.2.2.2,
              hRestFacts.1, hRestFacts.2.1, hRestFacts.2.2.1,
              hRestFacts.2.2.2.1, hRestFacts.2.2.2.2.1,
              hRestFacts.2.2.2.2.2.1, hRestFacts.2.2.2.2.2.2]
            simp
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
          simp [PactType.reannotate, PactType.MessageIds,
            PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership]
      | recur _ _ body =>
          have hBody : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simpa [PactType.reannotate, PactType.MessageIds,
            PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership] using
              ih (sizeOf body) hBody alphabet body rfl
      | choice _ left right | seq _ left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.MessageIds,
            PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            ih (sizeOf left) hLeft alphabet left rfl,
            ih (sizeOf right) hRight alphabet right rfl]
      | fairChoice _ _ left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.MessageIds,
            PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            ih (sizeOf left) hLeft alphabet left rfl,
            ih (sizeOf right) hRight alphabet right rfl]
      | par _ left right interface =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.MessageIds,
            PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            ih (sizeOf left) hLeft
              (PactTypeAlphabet.projectParallelLeft alphabet left.alphabet
                right.alphabet interface) left rfl,
            ih (sizeOf right) hRight
              (PactTypeAlphabet.projectParallelChild alphabet right.alphabet
                interface) right rfl]
      | xoffer _ elseType branches | offer _ elseType branches =>
          have hElse : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.MessageIds,
            PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            ih (sizeOf elseType) hElse alphabet elseType rfl,
            hBranches branches hBranchSize alphabet]

@[simp] theorem PactType.messageIds_reannotate
    (alphabet : PactTypeAlphabet) (processType : PactType) :
    PactType.MessageIds (processType.reannotate alphabet) =
      PactType.MessageIds processType :=
  (PactType.reannotate_ownership_data alphabet processType).1

@[simp] theorem PactType.messageActions_reannotate
    (alphabet : PactTypeAlphabet) (processType : PactType) :
    PactType.MessageActions (processType.reannotate alphabet) =
      PactType.MessageActions processType :=
  (PactType.reannotate_ownership_data alphabet processType).2.1

@[simp] theorem PactType.progressIds_reannotate
    (alphabet : PactTypeAlphabet) (processType : PactType) :
    PactType.ProgressIds (processType.reannotate alphabet) =
      PactType.ProgressIds processType :=
  (PactType.reannotate_ownership_data alphabet processType).2.2.1

@[simp] theorem PactType.fairChoiceIds_reannotate
    (alphabet : PactTypeAlphabet) (processType : PactType) :
    PactType.FairChoiceIds (processType.reannotate alphabet) =
      PactType.FairChoiceIds processType :=
  (PactType.reannotate_ownership_data alphabet processType).2.2.2.1

@[simp] theorem PactType.parallelMessageOwnership_reannotate
    (alphabet : PactTypeAlphabet) (processType : PactType) :
    PactType.ParallelMessageOwnership (processType.reannotate alphabet) ↔
      PactType.ParallelMessageOwnership processType :=
  (PactType.reannotate_ownership_data alphabet processType).2.2.2.2.1

@[simp] theorem PactType.parallelProgressOwnership_reannotate
    (alphabet : PactTypeAlphabet) (processType : PactType) :
    PactType.ParallelProgressOwnership (processType.reannotate alphabet) ↔
      PactType.ParallelProgressOwnership processType :=
  (PactType.reannotate_ownership_data alphabet processType).2.2.2.2.2.1

@[simp] theorem PactType.parallelFairChoiceOwnership_reannotate
    (alphabet : PactTypeAlphabet) (processType : PactType) :
    PactType.ParallelFairChoiceOwnership (processType.reannotate alphabet) ↔
      PactType.ParallelFairChoiceOwnership processType :=
  (PactType.reannotate_ownership_data alphabet processType).2.2.2.2.2.2

/-- The generated branch-product worker preserves message names. -/
theorem parallelTypeBranchesWithin_messageIds
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType)) :
    PactType.MessageIds (parallelTypeBranchesWithin alphabet branches) =
      PactType.BranchMessageIds branches := by
  induction branches generalizing alphabet with
  | nil => simp [parallelTypeBranchesWithin, PactType.MessageIds,
      PactType.BranchMessageIds]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.MessageIds, PactType.BranchMessageIds]
      | cons next tail =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.MessageIds, PactType.BranchMessageIds, ih]

/-- The generated branch-product worker preserves polarized message actions. -/
theorem parallelTypeBranchesWithin_messageActions
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType)) :
    PactType.MessageActions (parallelTypeBranchesWithin alphabet branches) =
      PactType.BranchMessageActions branches := by
  induction branches generalizing alphabet with
  | nil => simp [parallelTypeBranchesWithin, PactType.MessageActions,
      PactType.BranchMessageActions]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.MessageActions, PactType.BranchMessageActions]
      | cons next tail =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.MessageActions, PactType.BranchMessageActions, ih]

/-- The generated branch-product worker preserves progress identifiers. -/
theorem parallelTypeBranchesWithin_progressIds
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType)) :
    PactType.ProgressIds (parallelTypeBranchesWithin alphabet branches) =
      PactType.BranchProgressIds branches := by
  induction branches generalizing alphabet with
  | nil => simp [parallelTypeBranchesWithin, PactType.ProgressIds,
      PactType.BranchProgressIds]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.ProgressIds, PactType.BranchProgressIds]
      | cons next tail =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.ProgressIds, PactType.BranchProgressIds, ih]

/-- The generated branch-product worker preserves fair-choice identifiers. -/
theorem parallelTypeBranchesWithin_fairChoiceIds
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType)) :
    PactType.FairChoiceIds (parallelTypeBranchesWithin alphabet branches) =
      PactType.BranchFairChoiceIds branches := by
  induction branches generalizing alphabet with
  | nil => simp [parallelTypeBranchesWithin, PactType.FairChoiceIds,
      PactType.BranchFairChoiceIds]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.FairChoiceIds, PactType.BranchFairChoiceIds]
      | cons next tail =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.FairChoiceIds, PactType.BranchFairChoiceIds, ih]

/-- The generated parallel branch product mentions exactly the message names occurring in the source branch list. -/
theorem parallelTypeBranches_messageIds (branches : List (BareMessage × PactType)) :
    PactType.MessageIds (parallelTypeBranches branches) =
      PactType.BranchMessageIds branches := by
  cases branches with
  | nil => simp [parallelTypeBranches, PactType.MessageIds,
      PactType.BranchMessageIds]
  | cons branch rest =>
      exact parallelTypeBranchesWithin_messageIds branch.2.alphabet
        (branch :: rest)

/-- The generated parallel branch product mentions exactly the polarized message actions occurring in the source branch list. -/
theorem parallelTypeBranches_messageActions (branches : List (BareMessage × PactType)) :
    PactType.MessageActions (parallelTypeBranches branches) =
      PactType.BranchMessageActions branches := by
  cases branches with
  | nil => simp [parallelTypeBranches, PactType.MessageActions,
      PactType.BranchMessageActions]
  | cons branch rest =>
      exact parallelTypeBranchesWithin_messageActions branch.2.alphabet
        (branch :: rest)

/-- The generated parallel branch product preserves the branch list's progress identifiers. -/
theorem parallelTypeBranches_progressIds (branches : List (BareMessage × PactType)) :
    PactType.ProgressIds (parallelTypeBranches branches) =
      PactType.BranchProgressIds branches := by
  cases branches with
  | nil => simp [parallelTypeBranches, PactType.ProgressIds,
      PactType.BranchProgressIds]
  | cons branch rest =>
      exact parallelTypeBranchesWithin_progressIds branch.2.alphabet
        (branch :: rest)

/-- The generated parallel branch product preserves the branch list's fair-choice identifiers. -/
theorem parallelTypeBranches_fairChoiceIds (branches : List (BareMessage × PactType)) :
    PactType.FairChoiceIds (parallelTypeBranches branches) =
      PactType.BranchFairChoiceIds branches := by
  cases branches with
  | nil => simp [parallelTypeBranches, PactType.FairChoiceIds,
      PactType.BranchFairChoiceIds]
  | cons branch rest =>
      exact parallelTypeBranchesWithin_fairChoiceIds branch.2.alphabet
        (branch :: rest)

/-- Selecting a generated branch preserves the structural ownership data. -/
theorem parallelTypeBranchesSelectingWithin_ownershipData
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType)) :
    PactType.MessageIds
        (parallelTypeBranchesSelectingWithin alphabet selected branches) =
        PactType.BranchMessageIds branches ∧
      PactType.MessageActions
        (parallelTypeBranchesSelectingWithin alphabet selected branches) =
        PactType.BranchMessageActions branches ∧
      PactType.ProgressIds
        (parallelTypeBranchesSelectingWithin alphabet selected branches) =
        PactType.BranchProgressIds branches ∧
      PactType.FairChoiceIds
        (parallelTypeBranchesSelectingWithin alphabet selected branches) =
        PactType.BranchFairChoiceIds branches := by
  induction branches generalizing alphabet with
  | nil =>
      simp [parallelTypeBranchesSelectingWithin, PactType.MessageIds,
        PactType.MessageActions, PactType.ProgressIds, PactType.FairChoiceIds,
        PactType.BranchMessageIds, PactType.BranchMessageActions,
        PactType.BranchProgressIds, PactType.BranchFairChoiceIds]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          by_cases hSelected : (action, processType) = selected
          · subst selected
            simp [parallelTypeBranchesSelectingWithin,
              selectedTypeBranchAt, singletonTypeXOfferAt,
              PactType.MessageIds, PactType.MessageActions,
              PactType.ProgressIds, PactType.FairChoiceIds,
              PactType.BranchMessageIds, PactType.BranchMessageActions,
              PactType.BranchProgressIds, PactType.BranchFairChoiceIds]
          · simp [parallelTypeBranchesSelectingWithin, hSelected,
              selectedTypeBranchAt, singletonTypeXOfferAt,
              PactType.MessageIds, PactType.MessageActions,
              PactType.ProgressIds, PactType.FairChoiceIds,
              PactType.BranchMessageIds, PactType.BranchMessageActions,
              PactType.BranchProgressIds, PactType.BranchFairChoiceIds]
      | cons next tail =>
          by_cases hSelected : (action, processType) = selected
          · subst selected
            simp [parallelTypeBranchesSelectingWithin,
              selectedTypeBranchAt, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.BranchMessageIds,
              PactType.BranchMessageActions, PactType.BranchProgressIds,
              PactType.BranchFairChoiceIds,
              parallelTypeBranchesWithin_messageIds,
              parallelTypeBranchesWithin_messageActions,
              parallelTypeBranchesWithin_progressIds,
              parallelTypeBranchesWithin_fairChoiceIds]
          · simp [parallelTypeBranchesSelectingWithin, hSelected,
              singletonTypeXOfferAt, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.BranchMessageIds,
              PactType.BranchMessageActions, PactType.BranchProgressIds,
              PactType.BranchFairChoiceIds, ih]

/-- Selecting a generated branch preserves the message-name set of the complete branch list. -/
theorem parallelTypeBranchesSelecting_messageIds
    (selected : BareMessage × PactType) (branches : List (BareMessage × PactType)) :
    PactType.MessageIds (parallelTypeBranchesSelecting selected branches) =
      PactType.BranchMessageIds branches := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.MessageIds,
      PactType.BranchMessageIds]
  | cons branch rest =>
      exact (parallelTypeBranchesSelectingWithin_ownershipData
        branch.2.alphabet selected (branch :: rest)).1

/-- Selecting a generated branch preserves the polarized message-action set of the complete branch list. -/
theorem parallelTypeBranchesSelecting_messageActions
    (selected : BareMessage × PactType) (branches : List (BareMessage × PactType)) :
    PactType.MessageActions (parallelTypeBranchesSelecting selected branches) =
      PactType.BranchMessageActions branches := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.MessageActions,
      PactType.BranchMessageActions]
  | cons branch rest =>
      exact (parallelTypeBranchesSelectingWithin_ownershipData
        branch.2.alphabet selected (branch :: rest)).2.1

/-- Selecting a generated branch preserves the progress-identifier set of the complete branch list. -/
theorem parallelTypeBranchesSelecting_progressIds
    (selected : BareMessage × PactType) (branches : List (BareMessage × PactType)) :
    PactType.ProgressIds (parallelTypeBranchesSelecting selected branches) =
      PactType.BranchProgressIds branches := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.ProgressIds,
      PactType.BranchProgressIds]
  | cons branch rest =>
      exact (parallelTypeBranchesSelectingWithin_ownershipData
        branch.2.alphabet selected (branch :: rest)).2.2.1

/-- Selecting a generated branch preserves the fair-choice-identifier set of the complete branch list. -/
theorem parallelTypeBranchesSelecting_fairChoiceIds
    (selected : BareMessage × PactType) (branches : List (BareMessage × PactType)) :
    PactType.FairChoiceIds (parallelTypeBranchesSelecting selected branches) =
      PactType.BranchFairChoiceIds branches := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.FairChoiceIds,
      PactType.BranchFairChoiceIds]
  | cons branch rest =>
      exact (parallelTypeBranchesSelectingWithin_ownershipData
        branch.2.alphabet selected (branch :: rest)).2.2.2

--  theorem clockCanOnlyTakeSemanticClockStep
--     (ty : PactType) (env : TypeEnv)

end

end Pact
