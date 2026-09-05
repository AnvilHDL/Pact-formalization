import Anvilpp.PactTypes.Automata.CompileTypeLemmas
import Mathlib.Data.Finset.Prod

namespace Pact

open Classical

noncomputable section


/- The canonical relation definition now lives with the compiler metadata in
CompileTypeDefs.lean. Its previous location is retained during the migration.

/-- Relates each residual of `ty` to the compiled state that represents it.
A rebuilt node carries `ty`'s alphabet; a residual copied from a child keeps
the child's. -/
def buildRelationSetCoreFuel :
    Nat → PactType → Finset (PactType × TypeAutomatonState)
  | 0, ty => {(ty, .root)}
  | fuel + 1, ty =>
      match ty with
      | .skip alphabet => {(.skip alphabet, .root)}
      | .message alphabet msg dir =>
          {(.message alphabet msg dir, .root), (.skip alphabet, .final)}
      | .tock alphabet => {(.tock alphabet, .root), (.skip alphabet, .final)}
      | .progress alphabet pid =>
          {(.progress alphabet pid, .root), (.skip alphabet, .final)}
      | .var alphabet name => {(.var alphabet name, .root)}
      | .choice _ left right =>
          insert (ty, TypeAutomatonState.root)
            ((buildRelationSetCoreFuel fuel
                  left).image
                (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
              (buildRelationSetCoreFuel fuel
                  right).image
                (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2)))
      | .fairChoice _ _ left right =>
          insert (ty, TypeAutomatonState.root)
            ((buildRelationSetCoreFuel fuel
                  left).image
                (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
              (buildRelationSetCoreFuel fuel
                  right).image
                (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2)))
      | .seq alphabet left right =>
          ((buildRelationSetCoreFuel fuel
              left).filter (fun entry =>
              entry.2 ∉ sequenceDeleted
                (compileTypeFuel fuel left))).image
              (fun entry =>
                (.seq alphabet entry.1 right,
                  TypeAutomatonState.child 0 entry.2)) ∪
            (buildRelationSetCoreFuel fuel
                right).image
              (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2))
      | .par alphabet left right interface =>
          insert (PactType.skip alphabet, TypeAutomatonState.final)
            ((Finset.product
                (buildRelationSetCoreFuel fuel left)
                (buildRelationSetCoreFuel fuel right)).image
              (fun entry =>
                (.par alphabet entry.1.1 entry.2.1 interface,
                  TypeAutomatonState.pair entry.1.2 entry.2.2)) ∪
              ((buildRelationSetCoreFuel fuel
                  (left.reannotate alphabet)).filter fun entry =>
                  entry.2 ∉
                    (compileTypeFuel fuel
                      (left.reannotate alphabet)).accepting).image
                (fun entry =>
                  (entry.1, TypeAutomatonState.survivor 0 entry.2)) ∪
              ((buildRelationSetCoreFuel fuel
                  (right.reannotate alphabet)).filter fun entry =>
                  entry.2 ∉
                    (compileTypeFuel fuel
                      (right.reannotate alphabet)).accepting).image
                (fun entry =>
                  (entry.1, TypeAutomatonState.survivor 1 entry.2)))
      | .recur alphabet name body =>
          insert (ty, TypeAutomatonState.root)
            ((buildRelationSetCoreFuel fuel
                body).image
              (fun entry =>
                (entry.1.replaceVar name (.recur alphabet name body),
                  TypeAutomatonState.child 0 entry.2)))
      | .xoffer _ elseType branches =>
          insert (ty, TypeAutomatonState.root)
            ((buildRelationSetCoreFuel fuel
                elseType).image
                (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
              branches.zipIdx.foldl (fun acc indexed =>
                acc ∪ (buildRelationSetCoreFuel
                    fuel indexed.1.2).image
                  (fun entry => (entry.1, TypeAutomatonState.child (indexed.2 + 1) entry.2)))
                ∅)
      | .offer alphabet elseType branches =>
          insert (ty, TypeAutomatonState.root)
            ((buildRelationSetCoreFuel fuel
                elseType).image
                (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
              branches.zipIdx.foldl (fun acc indexed =>
                acc ∪ (buildRelationSetCoreFuel
                    fuel
                    (parallelTypeBranchesSelecting alphabet indexed.1 branches)).image
                  (fun entry => (entry.1, TypeAutomatonState.child (indexed.2 + 1) entry.2)))
                ∅)
-/

/-- Public, provenance-directed relation: `buildRelationSetCoreFuel` at
`typeCompilationFuel`'s own budget. -/
def buildRelationSetCore  (ty : PactType) :
    Finset (PactType × TypeAutomatonState) :=
  buildRelationSetCoreFuel (typeCompilationFuel ty) ty

/-- The seed pair is always in the fuel-indexed relation, for sufficient fuel. -/
theorem buildRelationSetCoreFuel_initial_mem  :
    ∀ fuel processType, TypeCompilationFuelSufficient processType fuel →
      (processType, (compileTypeFuel fuel processType).initial) ∈
        buildRelationSetCoreFuel fuel processType := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message alphabet msg dir =>
          simp [compileTypeFuel, finishAutomatonFragment,
            buildRelationSetCoreFuel]
      | progress alphabet pid =>
          simp [compileTypeFuel, finishAutomatonFragment,
            buildRelationSetCoreFuel]
      | tock alphabet =>
          simp [compileTypeFuel, finishAutomatonFragment,
            buildRelationSetCoreFuel]
      | skip alphabet =>
          simp [compileTypeFuel, finishAutomatonFragment,
            buildRelationSetCoreFuel]
      | var alphabet name =>
          simp [compileTypeFuel, finishAutomatonFragment,
            buildRelationSetCoreFuel]
      | choice alphabet left right =>
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, buildRelationSetCoreFuel,
            Finset.mem_insert]
          exact Or.inl trivial
      | fairChoice alphabet bid left right =>
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, buildRelationSetCoreFuel,
            Finset.mem_insert]
          exact Or.inl trivial
      | recur alphabet name body =>
          simp only [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, buildRelationSetCoreFuel,
            Finset.mem_insert]
          exact Or.inl trivial
      | xoffer alphabet elseType branches =>
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, buildRelationSetCoreFuel,
            Finset.mem_insert]
          exact Or.inl trivial
      | offer alphabet elseType branches =>
          simp only [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, buildRelationSetCoreFuel,
            Finset.mem_insert]
          exact Or.inl trivial
      | seq alphabet left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hLeftMem := ih left hLeft
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childState, buildRelationSetCoreFuel,
            Finset.mem_union]
          exact Or.inl (Finset.mem_image.mpr ⟨_,
            Finset.mem_filter.mpr ⟨hLeftMem, initial_not_mem_sequenceDeleted _⟩,
            rfl⟩)
      | par alphabet left right interface =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hLeftMem := ih left hLeft
          have hRightMem := ih right hRight
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, buildRelationSetCoreFuel,
            Finset.mem_insert]
          right
          refine Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨
              ((left, (compileTypeFuel fuel left).initial),
                (right, (compileTypeFuel fuel right).initial)),
              Finset.mem_product.mpr ⟨hLeftMem, hRightMem⟩,
              rfl⟩))

/-- The seed pair for the public compiler's own fuel choice. -/
theorem buildRelationSetCore_initial_mem
     (processType : PactType) :
    (processType, (compileType processType).initial) ∈
      buildRelationSetCore
        processType := by
  simp only [compileType, buildRelationSetCore]
  exact buildRelationSetCoreFuel_initial_mem
   
    (typeCompilationFuel processType) processType
    (typeCompilationFuel_sufficient processType)

/-- Every compiled state relates to at most one residual, unconditionally. -/
theorem buildRelationSetCoreFuel_functional  :
    ∀ fuel (ty : PactType) {residual residual' : PactType}
      {state : TypeAutomatonState},
      (residual, state) ∈ buildRelationSetCoreFuel fuel ty →
      (residual', state) ∈ buildRelationSetCoreFuel fuel ty →
      residual = residual' := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty residual residual' state h h'
      simp only [buildRelationSetCoreFuel, Finset.mem_singleton,
        Prod.mk.injEq] at h h'
      rw [h.1, h'.1]
  | succ fuel ih =>
      intro ty residual residual' state h h'
      cases ty with
      | skip alphabet =>
          simp only [buildRelationSetCoreFuel, Finset.mem_singleton,
            Prod.mk.injEq] at h h'
          rw [h.1, h'.1]
      | message alphabet msg dir =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_singleton, Prod.mk.injEq] at h h'
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            rcases h' with ⟨rfl, hEq⟩ | ⟨rfl, hEq⟩ <;>
            first | rfl | exact absurd hEq (by decide)
      | tock alphabet =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_singleton, Prod.mk.injEq] at h h'
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            rcases h' with ⟨rfl, hEq⟩ | ⟨rfl, hEq⟩ <;>
            first | rfl | exact absurd hEq (by decide)
      | progress alphabet pid =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_singleton, Prod.mk.injEq] at h h'
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            rcases h' with ⟨rfl, hEq⟩ | ⟨rfl, hEq⟩ <;>
            first | rfl | exact absurd hEq (by decide)
      | var alphabet name =>
          simp only [buildRelationSetCoreFuel, Finset.mem_singleton,
            Prod.mk.injEq] at h h'
          rw [h.1, h'.1]
      | choice alphabet left right =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image, Prod.mk.injEq] at h h'
          rcases h with ⟨rfl, rfl⟩ | ⟨a, ha, rfl, ha2⟩ | ⟨a, ha, rfl, ha2⟩
          · rcases h' with ⟨rfl, -⟩ | ⟨a', ha', rfl, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩
            · rfl
            · exact nomatch ha2'
            · exact nomatch ha2'
          · rcases h' with ⟨-, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩
            · exact nomatch (ha2.trans ha2')
            · have hStateEq : a.2 = a'.2 := by injection ha2.trans ha2'.symm
              exact ih left ha (hStateEq ▸ ha')
            · exact nomatch (ha2.trans ha2'.symm)
          · rcases h' with ⟨-, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩
            · exact nomatch (ha2.trans ha2')
            · exact nomatch (ha2.trans ha2'.symm)
            · have hStateEq : a.2 = a'.2 := by injection ha2.trans ha2'.symm
              exact ih right ha (hStateEq ▸ ha')
      | fairChoice alphabet bid left right =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image, Prod.mk.injEq] at h h'
          rcases h with ⟨rfl, rfl⟩ | ⟨a, ha, rfl, ha2⟩ | ⟨a, ha, rfl, ha2⟩
          · rcases h' with ⟨rfl, -⟩ | ⟨a', ha', rfl, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩
            · rfl
            · exact nomatch ha2'
            · exact nomatch ha2'
          · rcases h' with ⟨-, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩
            · exact nomatch (ha2.trans ha2')
            · have hStateEq : a.2 = a'.2 := by injection ha2.trans ha2'.symm
              exact ih left ha (hStateEq ▸ ha')
            · exact nomatch (ha2.trans ha2'.symm)
          · rcases h' with ⟨-, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩
            · exact nomatch (ha2.trans ha2')
            · exact nomatch (ha2.trans ha2'.symm)
            · have hStateEq : a.2 = a'.2 := by injection ha2.trans ha2'.symm
              exact ih right ha (hStateEq ▸ ha')
      | seq alphabet left right =>
          simp only [buildRelationSetCoreFuel, Finset.mem_union,
            Finset.mem_image, Finset.mem_filter, Prod.mk.injEq] at h h'
          rcases h with ⟨a, ⟨ha, _⟩, rfl, ha2⟩ | ⟨a, ha, rfl, ha2⟩ <;>
            rcases h' with ⟨a', ⟨ha', _⟩, rfl, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩
          · have hStateEq : a.2 = a'.2 := by injection ha2.trans ha2'.symm
            have ha'' : (a'.1, a.2) ∈ buildRelationSetCoreFuel fuel left :=
              hStateEq ▸ ha'
            rw [ih left ha ha'']
          · exact nomatch (ha2.trans ha2'.symm)
          · exact nomatch (ha2.trans ha2'.symm)
          · have hStateEq : a.2 = a'.2 := by injection ha2.trans ha2'.symm
            have ha'' : (a'.1, a.2) ∈ buildRelationSetCoreFuel fuel right :=
              hStateEq ▸ ha'
            exact ih right ha ha''
      | par alphabet left right interface =>
          -- The four families are distinguished by the state's own shape:
          -- `.final`, `.pair`, `.survivor 0` and `.survivor 1` are pairwise
          -- distinct, so at most one family can supply any given state.
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at h h'
          rcases h with hDone | (hProd | hS0) | hS1 <;>
            rcases h' with hDone' | (hProd' | hS0') | hS1'
          · exact (congrArg Prod.fst hDone).trans (congrArg Prod.fst hDone').symm
          · obtain ⟨a', -, hEq'⟩ := hProd'
            have h1 : _ = state := congrArg Prod.snd hEq'
            have h2 : state = _ := congrArg Prod.snd hDone
            exact absurd (h1.trans h2) (by simp)
          · obtain ⟨a', -, hEq'⟩ := hS0'
            have h1 : _ = state := congrArg Prod.snd hEq'
            have h2 : state = _ := congrArg Prod.snd hDone
            exact absurd (h1.trans h2) (by simp)
          · obtain ⟨a', -, hEq'⟩ := hS1'
            have h1 : _ = state := congrArg Prod.snd hEq'
            have h2 : state = _ := congrArg Prod.snd hDone
            exact absurd (h1.trans h2) (by simp)
          · obtain ⟨a, -, hEq⟩ := hProd
            have h1 : _ = state := congrArg Prod.snd hEq
            have h2 : state = _ := congrArg Prod.snd hDone'
            exact absurd (h1.trans h2) (by simp)
          · obtain ⟨a, haMem, hEq⟩ := hProd
            obtain ⟨a', ha'Mem, hEq'⟩ := hProd'
            obtain ⟨haLeft, haRight⟩ := Finset.mem_product.mp haMem
            obtain ⟨ha'Left, ha'Right⟩ := Finset.mem_product.mp ha'Mem
            have hState := (congrArg Prod.snd hEq).trans (congrArg Prod.snd hEq').symm
            have hL : a.1.2 = a'.1.2 := by injection hState
            have hR : a.2.2 = a'.2.2 := by injection hState
            refine (congrArg Prod.fst hEq).symm.trans
              (Eq.trans ?_ (congrArg Prod.fst hEq'))
            have hLm : (a'.1.1, a.1.2) ∈ buildRelationSetCoreFuel fuel left := by
              rw [hL]; exact (Prod.mk.eta (p := a'.1)) ▸ ha'Left
            have hRm : (a'.2.1, a.2.2) ∈ buildRelationSetCoreFuel fuel right := by
              rw [hR]; exact (Prod.mk.eta (p := a'.2)) ▸ ha'Right
            rw [ih left haLeft hLm, ih right haRight hRm]
          · obtain ⟨a, -, hEq⟩ := hProd
            obtain ⟨a', -, hEq'⟩ := hS0'
            have h1 : _ = state := congrArg Prod.snd hEq
            have h2 : _ = state := congrArg Prod.snd hEq'
            exact absurd (h1.trans h2.symm) (by simp)
          · obtain ⟨a, -, hEq⟩ := hProd
            obtain ⟨a', -, hEq'⟩ := hS1'
            have h1 : _ = state := congrArg Prod.snd hEq
            have h2 : _ = state := congrArg Prod.snd hEq'
            exact absurd (h1.trans h2.symm) (by simp)
          · obtain ⟨a, -, hEq⟩ := hS0
            have h1 : _ = state := congrArg Prod.snd hEq
            have h2 : state = _ := congrArg Prod.snd hDone'
            exact absurd (h1.trans h2) (by simp)
          · obtain ⟨a, -, hEq⟩ := hS0
            obtain ⟨a', -, hEq'⟩ := hProd'
            have h1 : _ = state := congrArg Prod.snd hEq
            have h2 : _ = state := congrArg Prod.snd hEq'
            exact absurd (h1.trans h2.symm) (by simp)
          · obtain ⟨a, ha, hEq⟩ := hS0
            obtain ⟨a', ⟨ha', -⟩, hEq'⟩ := hS0'
            have hState := (congrArg Prod.snd hEq).trans (congrArg Prod.snd hEq').symm
            have hInner : a.2 = a'.2 := by injection hState
            refine (congrArg Prod.fst hEq).symm.trans
              (Eq.trans ?_ (congrArg Prod.fst hEq'))
            have hm : (a'.1, a.2) ∈ buildRelationSetCoreFuel fuel
                (left.reannotate alphabet) := by
              rw [hInner]; exact (Prod.mk.eta (p := a')) ▸ ha'
            rw [ih (left.reannotate alphabet) ha.1 hm]
          · obtain ⟨a, -, hEq⟩ := hS0
            obtain ⟨a', -, hEq'⟩ := hS1'
            have h1 : _ = state := congrArg Prod.snd hEq
            have h2 : _ = state := congrArg Prod.snd hEq'
            exact absurd (h1.trans h2.symm) (by simp)
          · obtain ⟨a, -, hEq⟩ := hS1
            have h1 : _ = state := congrArg Prod.snd hEq
            have h2 : state = _ := congrArg Prod.snd hDone'
            exact absurd (h1.trans h2) (by simp)
          · obtain ⟨a, -, hEq⟩ := hS1
            obtain ⟨a', -, hEq'⟩ := hProd'
            have h1 : _ = state := congrArg Prod.snd hEq
            have h2 : _ = state := congrArg Prod.snd hEq'
            exact absurd (h1.trans h2.symm) (by simp)
          · obtain ⟨a, -, hEq⟩ := hS1
            obtain ⟨a', -, hEq'⟩ := hS0'
            have h1 : _ = state := congrArg Prod.snd hEq
            have h2 : _ = state := congrArg Prod.snd hEq'
            exact absurd (h1.trans h2.symm) (by simp)
          · obtain ⟨a, ha, hEq⟩ := hS1
            obtain ⟨a', ⟨ha', -⟩, hEq'⟩ := hS1'
            have hState := (congrArg Prod.snd hEq).trans (congrArg Prod.snd hEq').symm
            have hInner : a.2 = a'.2 := by injection hState
            refine (congrArg Prod.fst hEq).symm.trans
              (Eq.trans ?_ (congrArg Prod.fst hEq'))
            have hm : (a'.1, a.2) ∈ buildRelationSetCoreFuel fuel
                (right.reannotate alphabet) := by
              rw [hInner]; exact (Prod.mk.eta (p := a')) ▸ ha'
            rw [ih (right.reannotate alphabet) ha.1 hm]
      | recur alphabet name body =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_image, Prod.mk.injEq] at h h'
          rcases h with ⟨rfl, rfl⟩ | ⟨a, ha, rfl, ha2⟩
          · rcases h' with ⟨rfl, -⟩ | ⟨a', ha', rfl, ha2'⟩
            · rfl
            · exact nomatch ha2'
          · rcases h' with ⟨-, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩
            · exact nomatch (ha2.trans ha2')
            · have hStateEq : a.2 = a'.2 := by injection ha2.trans ha2'.symm
              have ha'' : (a'.1, a.2) ∈ buildRelationSetCoreFuel fuel body :=
                hStateEq ▸ ha'
              rw [ih body ha ha'']
      | xoffer alphabet elseType branches =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, mem_foldl_union_iff, Finset.notMem_empty,
            false_or, Finset.mem_image, Prod.mk.injEq] at h h'
          rcases h with ⟨rfl, rfl⟩ | ⟨a, ha, rfl, ha2⟩ |
            ⟨item, hItem, a, ha, rfl, ha2⟩
          · rcases h' with ⟨rfl, -⟩ | ⟨a', ha', rfl, ha2'⟩ |
              ⟨item', hItem', a', ha', rfl, ha2'⟩
            · rfl
            · exact nomatch ha2'
            · exact nomatch ha2'
          · rcases h' with ⟨-, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩ |
              ⟨item', hItem', a', ha', rfl, ha2'⟩
            · exact nomatch (ha2.trans ha2')
            · have hStateEq : a.2 = a'.2 := by injection ha2.trans ha2'.symm
              have ha'' : (a'.1, a.2) ∈
                  buildRelationSetCoreFuel fuel elseType :=
                hStateEq ▸ ha'
              rw [ih elseType ha ha'']
            · exact nomatch (ha2.trans ha2'.symm)
          · rcases h' with ⟨-, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩ |
              ⟨item', hItem', a', ha', rfl, ha2'⟩
            · exact nomatch (ha2.trans ha2')
            · exact nomatch (ha2.trans ha2'.symm)
            · have hIdxEq : item.2 = item'.2 := by
                injection ha2.trans ha2'.symm with hIdxEq
                omega
              have hItemEq : item = item' := by
                have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hItem
                have hGet' := List.mk_mem_zipIdx_iff_getElem?.mp hItem'
                rw [hIdxEq] at hGet
                rw [hGet'] at hGet
                have hFst : item.1 = item'.1 := by injection hGet with hFst; exact hFst.symm
                exact Prod.ext hFst hIdxEq
              have hStateEq : a.2 = a'.2 := by injection ha2.trans ha2'.symm
              have ha'' : (a'.1, a.2) ∈
                  buildRelationSetCoreFuel
                    fuel item.1.2 :=
                hItemEq ▸ hStateEq ▸ ha'
              rw [ih item.1.2 ha ha'']
      | offer alphabet elseType branches =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, mem_foldl_union_iff, Finset.notMem_empty,
            false_or, Finset.mem_image, Prod.mk.injEq] at h h'
          rcases h with ⟨rfl, rfl⟩ | ⟨a, ha, rfl, ha2⟩ |
            ⟨item, hItem, a, ha, rfl, ha2⟩
          · rcases h' with ⟨rfl, -⟩ | ⟨a', ha', rfl, ha2'⟩ |
              ⟨item', hItem', a', ha', rfl, ha2'⟩
            · rfl
            · exact nomatch ha2'
            · exact nomatch ha2'
          · rcases h' with ⟨-, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩ |
              ⟨item', hItem', a', ha', rfl, ha2'⟩
            · exact nomatch (ha2.trans ha2')
            · have hStateEq : a.2 = a'.2 := by injection ha2.trans ha2'.symm
              have ha'' : (a'.1, a.2) ∈
                  buildRelationSetCoreFuel fuel elseType :=
                hStateEq ▸ ha'
              rw [ih elseType ha ha'']
            · exact nomatch (ha2.trans ha2'.symm)
          · rcases h' with ⟨-, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩ |
              ⟨item', hItem', a', ha', rfl, ha2'⟩
            · exact nomatch (ha2.trans ha2')
            · exact nomatch (ha2.trans ha2'.symm)
            · have hIdxEq : item.2 = item'.2 := by
                injection ha2.trans ha2'.symm with hIdxEq
                omega
              have hItemEq : item = item' := by
                have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hItem
                have hGet' := List.mk_mem_zipIdx_iff_getElem?.mp hItem'
                rw [hIdxEq] at hGet
                rw [hGet'] at hGet
                have hFst : item.1 = item'.1 := by injection hGet with hFst; exact hFst.symm
                exact Prod.ext hFst hIdxEq
              have hStateEq : a.2 = a'.2 := by injection ha2.trans ha2'.symm
              have ha'' : (a'.1, a.2) ∈
                  buildRelationSetCoreFuel
                    fuel
                    (parallelTypeBranchesSelecting alphabet item.1 branches) :=
                hItemEq ▸ hStateEq ▸ ha'
              rw [ih
                (parallelTypeBranchesSelecting alphabet item.1 branches) ha ha'']

/-- The public-fuel relation is functional: each compiled state relates to at
most one residual. Unconditional — no fuel-sufficiency side condition needed,
unlike `buildRelationSetCoreFuel_initial_mem`, since `buildRelationSetCoreFuel_functional`
holds for *every* fuel value, not just sufficient ones. -/
theorem buildRelationSetCore_functional
     (processType : PactType)
    {residual residual' : PactType} {state : TypeAutomatonState}
    (hRelated : (residual, state) ∈ buildRelationSetCore processType)
    (hRelated' : (residual', state) ∈ buildRelationSetCore processType) :
    residual = residual' :=
  buildRelationSetCoreFuel_functional (typeCompilationFuel processType)
    processType hRelated hRelated'

/-! ### Fuel-sufficiency stability (needed to reconcile a shared parent fuel,
e.g. `max (typeCompilationFuel left) (typeCompilationFuel right)`, with each
child's own minimal fuel `typeCompilationFuel left`/`right` — the same
reconciliation `compileTypeFuel_eq_of_sufficient` provides for `compileType`,
needed here for the same reason: `buildRelationSetCoreFuel` mirrors
`compileTypeFuel`'s exact fuel-passing convention.) -/

private theorem buildRelationSetCoreFuel_succ_stable  :
    ∀ fuel processType, typeCompilationFuel processType ≤ fuel →
      buildRelationSetCoreFuel (fuel + 1) processType =
        buildRelationSetCoreFuel fuel processType := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      have hPositive := typeCompilationFuel_positive processType
      omega
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message alphabet msg dir => simp only [buildRelationSetCoreFuel]
      | progress alphabet pid => simp only [buildRelationSetCoreFuel]
      | tock alphabet => simp only [buildRelationSetCoreFuel]
      | skip alphabet => simp only [buildRelationSetCoreFuel]
      | var alphabet name => simp only [buildRelationSetCoreFuel]
      | choice alphabet left right =>
          have hLeft : typeCompilationFuel left ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel right ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          conv_lhs => rw [buildRelationSetCoreFuel.eq_def]
          conv_rhs => rw [buildRelationSetCoreFuel.eq_def]
          change insert (PactType.choice alphabet left right, TypeAutomatonState.root)
              ((buildRelationSetCoreFuel (fuel+1) left).image
                  (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
                (buildRelationSetCoreFuel (fuel+1) right).image
                  (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2))) =
            insert (PactType.choice alphabet left right, TypeAutomatonState.root)
              ((buildRelationSetCoreFuel fuel left).image
                  (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
                (buildRelationSetCoreFuel fuel right).image
                  (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2)))
          rw [ih left hLeft, ih right hRight]
      | fairChoice alphabet bid left right =>
          have hLeft : typeCompilationFuel left ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel right ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          conv_lhs => rw [buildRelationSetCoreFuel.eq_def]
          conv_rhs => rw [buildRelationSetCoreFuel.eq_def]
          change insert (PactType.fairChoice alphabet bid left right,
              TypeAutomatonState.root)
              ((buildRelationSetCoreFuel (fuel+1) left).image
                  (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
                (buildRelationSetCoreFuel (fuel+1) right).image
                  (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2))) =
            insert (PactType.fairChoice alphabet bid left right,
              TypeAutomatonState.root)
              ((buildRelationSetCoreFuel fuel left).image
                  (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
                (buildRelationSetCoreFuel fuel right).image
                  (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2)))
          rw [ih left hLeft, ih right hRight]
      | seq alphabet left right =>
          have hLeft : typeCompilationFuel left ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel right ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hCompileLeft :
              compileTypeFuel (fuel + 1) left =
                compileTypeFuel fuel left :=
            compileTypeFuel_eq_of_sufficient left
              (leftFuel := fuel + 1) (rightFuel := fuel)
              (Nat.le.step hLeft) hLeft
          conv_lhs => rw [buildRelationSetCoreFuel.eq_def]
          conv_rhs => rw [buildRelationSetCoreFuel.eq_def]
          change
              ((buildRelationSetCoreFuel (fuel+1) left).filter (fun entry =>
                  entry.2 ∉ sequenceDeleted
                    (compileTypeFuel (fuel+1) left))).image
                  (fun entry =>
                    (PactType.seq alphabet entry.1 right,
                      TypeAutomatonState.child 0 entry.2)) ∪
                (buildRelationSetCoreFuel (fuel+1) right).image
                  (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2)) =
              ((buildRelationSetCoreFuel fuel left).filter (fun entry =>
                  entry.2 ∉ sequenceDeleted
                    (compileTypeFuel fuel left))).image
                  (fun entry =>
                    (PactType.seq alphabet entry.1 right,
                      TypeAutomatonState.child 0 entry.2)) ∪
                (buildRelationSetCoreFuel fuel right).image
                  (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2))
          rw [ih left hLeft, ih right hRight, hCompileLeft]
      | par alphabet left right interface =>
          have hLeft : typeCompilationFuel left ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel right ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hCompileLeft :
              compileTypeFuel (fuel + 1) left =
                compileTypeFuel fuel left :=
            compileTypeFuel_eq_of_sufficient left
              (leftFuel := fuel + 1) (rightFuel := fuel)
              (Nat.le.step hLeft) hLeft
          have hCompileRight :
              compileTypeFuel (fuel + 1) right =
                compileTypeFuel fuel right :=
            compileTypeFuel_eq_of_sufficient right
              (leftFuel := fuel + 1) (rightFuel := fuel)
              (Nat.le.step hRight) hRight
          have hLeftR : typeCompilationFuel (left.reannotate alphabet) ≤ fuel := by
            rw [typeCompilationFuel_reannotate]; exact hLeft
          have hRightR : typeCompilationFuel (right.reannotate alphabet) ≤ fuel := by
            rw [typeCompilationFuel_reannotate]; exact hRight
          have hCompileLeftR :
              compileTypeFuel (fuel + 1) (left.reannotate alphabet) =
                compileTypeFuel fuel (left.reannotate alphabet) :=
            compileTypeFuel_eq_of_sufficient (left.reannotate alphabet)
              (leftFuel := fuel + 1) (rightFuel := fuel)
              (Nat.le.step hLeftR) hLeftR
          have hCompileRightR :
              compileTypeFuel (fuel + 1) (right.reannotate alphabet) =
                compileTypeFuel fuel (right.reannotate alphabet) :=
            compileTypeFuel_eq_of_sufficient (right.reannotate alphabet)
              (leftFuel := fuel + 1) (rightFuel := fuel)
              (Nat.le.step hRightR) hRightR
          conv_lhs => rw [buildRelationSetCoreFuel.eq_def]
          conv_rhs => rw [buildRelationSetCoreFuel.eq_def]
          change insert (PactType.skip alphabet, TypeAutomatonState.final)
              ((Finset.product (buildRelationSetCoreFuel (fuel+1) left)
                  (buildRelationSetCoreFuel (fuel+1) right)).image
                (fun entry =>
                  (PactType.par alphabet entry.1.1 entry.2.1 interface,
                    TypeAutomatonState.pair entry.1.2 entry.2.2)) ∪
                ((buildRelationSetCoreFuel (fuel+1)
                      (left.reannotate alphabet)).filter
                    fun entry => entry.2 ∉
                      (compileTypeFuel (fuel+1)
                        (left.reannotate alphabet)).accepting).image
                  (fun entry =>
                    (entry.1, TypeAutomatonState.survivor 0 entry.2)) ∪
                ((buildRelationSetCoreFuel (fuel+1)
                      (right.reannotate alphabet)).filter
                    fun entry => entry.2 ∉
                      (compileTypeFuel (fuel+1)
                        (right.reannotate alphabet)).accepting).image
                  (fun entry =>
                    (entry.1, TypeAutomatonState.survivor 1 entry.2))) =
            insert (PactType.skip alphabet, TypeAutomatonState.final)
              ((Finset.product (buildRelationSetCoreFuel fuel left)
                  (buildRelationSetCoreFuel fuel right)).image
                (fun entry =>
                  (PactType.par alphabet entry.1.1 entry.2.1 interface,
                    TypeAutomatonState.pair entry.1.2 entry.2.2)) ∪
                ((buildRelationSetCoreFuel fuel
                      (left.reannotate alphabet)).filter
                    fun entry => entry.2 ∉
                      (compileTypeFuel fuel
                        (left.reannotate alphabet)).accepting).image
                  (fun entry =>
                    (entry.1, TypeAutomatonState.survivor 0 entry.2)) ∪
                ((buildRelationSetCoreFuel fuel
                      (right.reannotate alphabet)).filter
                    fun entry => entry.2 ∉
                      (compileTypeFuel fuel
                        (right.reannotate alphabet)).accepting).image
                  (fun entry =>
                    (entry.1, TypeAutomatonState.survivor 1 entry.2)))
          -- The product clause no longer mentions the child future menus.
          try simp only [compiledChildFutureFuel,
            Nat.min_eq_right hLeft, Nat.min_eq_right (Nat.le.step hLeft),
            Nat.min_eq_right hRight, Nat.min_eq_right (Nat.le.step hRight),
            Nat.min_eq_right hLeftR, Nat.min_eq_right (Nat.le.step hLeftR),
            Nat.min_eq_right hRightR, Nat.min_eq_right (Nat.le.step hRightR)]
          rw [ih left hLeft, ih right hRight,
            ih (left.reannotate alphabet) hLeftR,
            ih (right.reannotate alphabet) hRightR]
          -- Only the survivor filters still read a compiled child.
          try rw [hCompileLeft]
          try rw [hCompileRight]
          try rw [hCompileLeftR]
          try rw [hCompileRightR]
      | recur alphabet name body =>
          have hBody : typeCompilationFuel body ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          conv_lhs => rw [buildRelationSetCoreFuel.eq_def]
          conv_rhs => rw [buildRelationSetCoreFuel.eq_def]
          change insert (PactType.recur alphabet name body,
              TypeAutomatonState.root)
              ((buildRelationSetCoreFuel (fuel+1) body).image
                (fun entry =>
                  (entry.1.replaceVar name (.recur alphabet name body),
                    TypeAutomatonState.child 0 entry.2))) =
            insert (PactType.recur alphabet name body,
              TypeAutomatonState.root)
              ((buildRelationSetCoreFuel fuel body).image
                (fun entry =>
                  (entry.1.replaceVar name (.recur alphabet name body),
                    TypeAutomatonState.child 0 entry.2)))
          rw [ih body hBody]
      | xoffer alphabet elseType branches =>
          have hElse : typeCompilationFuel elseType ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hBranchesFuel : typeBranchCompilationFuel branches ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hItemFuel : ∀ item ∈ branches.zipIdx, typeCompilationFuel item.1.2 ≤ fuel := by
            intro item hItem
            have hFields := List.mem_zipIdx hItem
            simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hFields
            obtain ⟨hBound, hValue⟩ := hFields
            have hMember : item.1 ∈ branches := by
              have := List.getElem_mem hBound
              simpa [hValue] using this
            exact le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches item.1 hMember)
              hBranchesFuel
          apply Finset.ext
          intro entry
          simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
            mem_foldl_union_iff, Finset.notMem_empty, false_or, Finset.mem_image]
          constructor
          · rintro (h | ⟨a, ha, h⟩ | ⟨item, hItem, a, ha, hEq⟩)
            · exact Or.inl h
            · have ha' : a ∈ buildRelationSetCoreFuel fuel elseType :=
                ih elseType hElse ▸ ha
              exact Or.inr (Or.inl ⟨a, ha', h⟩)
            · have ha' : a ∈ buildRelationSetCoreFuel fuel item.1.2 :=
                ih item.1.2 (hItemFuel item hItem) ▸ ha
              exact Or.inr (Or.inr ⟨item, hItem, a, ha', hEq⟩)
          · rintro (h | ⟨a, ha, h⟩ | ⟨item, hItem, a, ha, hEq⟩)
            · exact Or.inl h
            · have ha' : a ∈ buildRelationSetCoreFuel (fuel + 1) elseType :=
                (ih elseType hElse).symm ▸ ha
              exact Or.inr (Or.inl ⟨a, ha', h⟩)
            · have ha' : a ∈ buildRelationSetCoreFuel (fuel + 1) item.1.2 :=
                (ih item.1.2 (hItemFuel item hItem)).symm ▸ ha
              exact Or.inr (Or.inr ⟨item, hItem, a, ha', hEq⟩)
      | offer alphabet elseType branches =>
          have hElse : typeCompilationFuel elseType ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hBranchesFuel : ∀ item : BareMessage × PactType,
              typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet item branches) ≤ fuel := by
            intro item
            rw [typeCompilationFuel_parallelTypeBranchesSelecting]
            simp [typeCompilationFuel] at hFuel; omega
          apply Finset.ext
          intro entry
          simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
            mem_foldl_union_iff, Finset.notMem_empty, false_or, Finset.mem_image]
          constructor
          · rintro (h | ⟨a, ha, h⟩ | ⟨item, hItem, a, ha, hEq⟩)
            · exact Or.inl h
            · have ha' : a ∈ buildRelationSetCoreFuel fuel elseType :=
                ih elseType hElse ▸ ha
              exact Or.inr (Or.inl ⟨a, ha', h⟩)
            · have ha' : a ∈ buildRelationSetCoreFuel
                  fuel
                  (parallelTypeBranchesSelecting alphabet item.1 branches) :=
                ih _ (hBranchesFuel item.1) ▸ ha
              exact Or.inr (Or.inr ⟨item, hItem, a, ha', hEq⟩)
          · rintro (h | ⟨a, ha, h⟩ | ⟨item, hItem, a, ha, hEq⟩)
            · exact Or.inl h
            · have ha' : a ∈ buildRelationSetCoreFuel (fuel + 1) elseType :=
                (ih elseType hElse).symm ▸ ha
              exact Or.inr (Or.inl ⟨a, ha', h⟩)
            · have ha' : a ∈ buildRelationSetCoreFuel
                  (fuel + 1)
                  (parallelTypeBranchesSelecting alphabet item.1 branches) :=
                (ih _ (hBranchesFuel item.1)).symm ▸ ha
              exact Or.inr (Or.inr ⟨item, hItem, a, ha', hEq⟩)

/-- Any two sufficient budgets produce the same relation set. -/
private theorem buildRelationSetCoreFuel_add_stable
     (processType : PactType)
    (fuel extra : Nat) (hFuel : typeCompilationFuel processType ≤ fuel) :
    buildRelationSetCoreFuel (fuel + extra) processType =
      buildRelationSetCoreFuel fuel processType := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ,
        buildRelationSetCoreFuel_succ_stable (fuel + extra) processType
          (by omega),
        ih]

/-- Reconciles any two sufficient fuel values against the same `processType`. -/
theorem buildRelationSetCoreFuel_eq_of_sufficient
     (processType : PactType)
    {leftFuel rightFuel : Nat}
    (hLeft : TypeCompilationFuelSufficient processType leftFuel)
    (hRight : TypeCompilationFuelSufficient processType rightFuel) :
    buildRelationSetCoreFuel leftFuel processType =
      buildRelationSetCoreFuel rightFuel processType := by
  by_cases hOrder : leftFuel ≤ rightFuel
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hOrder
    exact (buildRelationSetCoreFuel_add_stable processType leftFuel extra
      hLeft).symm
  · have hReverse : rightFuel ≤ leftFuel := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hReverse
    exact buildRelationSetCoreFuel_add_stable processType rightFuel extra hRight

/-- Defines relation membership as occurrence of the residual/state pair in the relation set. -/
def relationMembership
    (relation_set : Finset (PactType × TypeAutomatonState))
    (processType : PactType) (state : TypeAutomatonState) : Prop :=
  (processType, state) ∈ relation_set

/-- The generated correspondence relation for `ty`, against the
`auto` was compiled from. -/
def buildRelationSet (ty : PactType) (auto : TypeAutomaton) :
    Finset (PactType × TypeAutomatonState) :=
  buildRelationSetCore ty

/-- The guard a compiled symbol carries into a constructor case: its
environment and its offers are drawn from the type's own alphabet.  The paper's
`Corr` quantifies over every environment and every label public in the context,
with no condition on the label itself, and a child's label set is not contained
in its parent's — the interfaces of a sibling enlarge the parent's
observations — so the label component of `transitionAlphabet` membership is not
available to a child and is not asked for. -/
def SymbolGuard (processType : PactType) (env : TypeEnvironment)
    (offers : TypeOfferSummary) : Prop :=
  env ∈ processType.alphabet.localEnvironments ∧
    offers ∈ processType.alphabet.localOfferSummaries

/-- The fixed-target obligation used internally by constructor proofs. -/
def StepIffStatement
     (processType : PactType) : Prop :=
  ∀ {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    relationMembership
      (buildRelationSet processType (compileType processType))
      residual state →
    SymbolGuard processType env offers →
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType processType).HasEdge state env label offers
          state' ∧
        relationMembership
          (buildRelationSet processType (compileType processType))
          residual' state')

/-- The two simulations in the statement of Lemma 4.5. Targets are
existentially quantified in both directions. -/
def TypeAutomatonStepCorrespondence (processType : PactType) : Prop :=
  (∀ {residual residual' : PactType} {state : TypeAutomatonState}
      {env : TypeEnvironment} {label : TypeLabel}
      {offers : TypeOfferSummary},
      relationMembership
        (buildRelationSet processType (compileType processType))
        residual state →
      DecoratedTypeTransition env residual label offers residual' →
      ∃ state',
        (compileType processType).HasEdge state env label offers state' ∧
        relationMembership
          (buildRelationSet processType (compileType processType))
          residual' state') ∧
  (∀ {residual : PactType} {state state' : TypeAutomatonState}
      {env : TypeEnvironment} {label : TypeLabel}
      {offers : TypeOfferSummary},
      relationMembership
        (buildRelationSet processType (compileType processType))
        residual state →
      (compileType processType).HasEdge state env label offers state' →
      ∃ residual',
        DecoratedTypeTransition env residual label offers residual' ∧
        relationMembership
          (buildRelationSet processType (compileType processType))
          residual' state')

/-- The generated relation contains its initial residual/state seed pair. -/
theorem buildRelationSet_initial (ty : PactType) (auto : TypeAutomaton)
    (hAuto : auto = compileType ty := by rfl) :
    relationMembership (buildRelationSet ty auto) ty auto.initial := by
  unfold relationMembership buildRelationSet
  rw [hAuto]
  exact buildRelationSetCore_initial_mem ty

end
