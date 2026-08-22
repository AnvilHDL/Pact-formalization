import Anvilpp.PactTypes.Automata.CompileType
import Mathlib.Data.Finset.Prod

namespace Pact

open Classical

noncomputable section

/-! ### Provenance-directed relation (Task 4)

Replaces the old `Classical.choose`-over-decoration relation (unsound — see
`AGENT.md`, Task 4) with a structural one, matching `pact.pdf`'s own H12:
built by compilation rule, threading each child's own relation membership
through directly. Fuel-indexed like `compileTypeFuel`, for the same reason
(`.offer`'s generated commit type isn't `sizeOf`-smaller than `.offer`
itself). -/
def buildRelationSetCoreFuel (signature : TypeAlphabet) :
    Nat → PactType → Finset (PactType × TypeAutomatonState)
  | 0, ty => {(ty, .root)}
  | fuel + 1, ty =>
      match ty with
      | .skip => {(.skip, .root)}
      | .message msg dir => {(.message msg dir, .root), (.skip, .final)}
      | .tock => {(.tock, .root), (.skip, .final)}
      | .progress pid => {(.progress pid, .root), (.skip, .final)}
      | .var name => {(.var name, .root)}
      | .choice left right =>
          insert (ty, TypeAutomatonState.root)
            ((buildRelationSetCoreFuel signature fuel left).image
                (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
              (buildRelationSetCoreFuel signature fuel right).image
                (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2)))
      | .fairChoice _ left right =>
          insert (ty, TypeAutomatonState.root)
            ((buildRelationSetCoreFuel signature fuel left).image
                (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
              (buildRelationSetCoreFuel signature fuel right).image
                (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2)))
      | .seq left right =>
          (buildRelationSetCoreFuel signature fuel left).image
              (fun entry => (.seq entry.1 right, TypeAutomatonState.child 0 entry.2)) ∪
            (buildRelationSetCoreFuel signature fuel right).image
              (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2))
      | .par left right interface =>
          insert (PactType.skip, TypeAutomatonState.final)
            ((Finset.product (buildRelationSetCoreFuel signature fuel left)
                (buildRelationSetCoreFuel signature fuel right)).image
              (fun entry =>
                (.par entry.1.1 entry.2.1 interface,
                  TypeAutomatonState.pair entry.1.2 entry.2.2)))
      | .recur name body =>
          insert (ty, TypeAutomatonState.root)
            ((buildRelationSetCoreFuel signature fuel body).image
              (fun entry =>
                (entry.1.replaceVar name (.recur name body),
                  TypeAutomatonState.child 0 entry.2)))
      | .xoffer elseType branches =>
          insert (ty, TypeAutomatonState.root)
            ((buildRelationSetCoreFuel signature fuel elseType).image
                (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
              branches.zipIdx.foldl (fun acc indexed =>
                acc ∪ (buildRelationSetCoreFuel signature fuel indexed.1.2).image
                  (fun entry => (entry.1, TypeAutomatonState.child (indexed.2 + 1) entry.2)))
                ∅)
      | .offer elseType branches =>
          insert (ty, TypeAutomatonState.root)
            ((buildRelationSetCoreFuel signature fuel elseType).image
                (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
              branches.zipIdx.foldl (fun acc indexed =>
                acc ∪ (buildRelationSetCoreFuel signature fuel
                    (parallelTypeBranchesSelecting indexed.1 branches)).image
                  (fun entry => (entry.1, TypeAutomatonState.child (indexed.2 + 1) entry.2)))
                ∅)

/-- Public, provenance-directed relation: `buildRelationSetCoreFuel` at
`typeCompilationFuel`'s own budget. -/
def buildRelationSetCore (signature : TypeAlphabet) (ty : PactType) :
    Finset (PactType × TypeAutomatonState) :=
  buildRelationSetCoreFuel signature (typeCompilationFuel ty) ty

/-- The seed pair is always in the fuel-indexed relation, for sufficient fuel. -/
theorem buildRelationSetCoreFuel_initial_mem (signature : TypeAlphabet) :
    ∀ fuel processType, TypeCompilationFuelSufficient processType fuel →
      (processType, (compileTypeFuel signature fuel processType).initial) ∈
        buildRelationSetCoreFuel signature fuel processType := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message msg dir =>
          simp [compileTypeFuel, finishAutomatonFragment,
            buildRelationSetCoreFuel]
      | progress pid =>
          simp [compileTypeFuel, finishAutomatonFragment,
            buildRelationSetCoreFuel]
      | tock =>
          simp [compileTypeFuel, finishAutomatonFragment,
            buildRelationSetCoreFuel]
      | skip =>
          simp [compileTypeFuel, finishAutomatonFragment,
            buildRelationSetCoreFuel]
      | var name =>
          simp [compileTypeFuel, finishAutomatonFragment,
            buildRelationSetCoreFuel]
      | choice left right =>
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, buildRelationSetCoreFuel,
            Finset.mem_insert]
          exact Or.inl trivial
      | fairChoice bid left right =>
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, buildRelationSetCoreFuel,
            Finset.mem_insert]
          exact Or.inl trivial
      | recur name body =>
          simp only [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, buildRelationSetCoreFuel,
            Finset.mem_insert]
          exact Or.inl trivial
      | xoffer elseType branches =>
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, buildRelationSetCoreFuel,
            Finset.mem_insert]
          exact Or.inl trivial
      | offer elseType branches =>
          simp only [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, buildRelationSetCoreFuel,
            Finset.mem_insert]
          exact Or.inl trivial
      | seq left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hLeftMem := ih left hLeft
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childState, buildRelationSetCoreFuel,
            Finset.mem_union]
          exact Or.inl (Finset.mem_image.mpr ⟨_, hLeftMem, rfl⟩)
      | par left right interface =>
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
          refine Finset.mem_image.mpr ⟨
            ((left, (compileTypeFuel signature fuel left).initial),
              (right, (compileTypeFuel signature fuel right).initial)),
            Finset.mem_product.mpr ⟨hLeftMem, hRightMem⟩, rfl⟩

/-- The seed pair for the public compiler's own fuel choice. -/
theorem buildRelationSetCore_initial_mem
    (signature : TypeAlphabet) (processType : PactType) :
    (processType, (compileType signature processType).initial) ∈
      buildRelationSetCore signature processType := by
  simp only [compileType, buildRelationSetCore]
  exact buildRelationSetCoreFuel_initial_mem signature
    (typeCompilationFuel processType) processType
    (typeCompilationFuel_sufficient processType)

/-- Every compiled state relates to at most one residual, unconditionally. -/
theorem buildRelationSetCoreFuel_functional (signature : TypeAlphabet) :
    ∀ fuel (ty : PactType) {residual residual' : PactType}
      {state : TypeAutomatonState},
      (residual, state) ∈ buildRelationSetCoreFuel signature fuel ty →
      (residual', state) ∈ buildRelationSetCoreFuel signature fuel ty →
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
      | skip =>
          simp only [buildRelationSetCoreFuel, Finset.mem_singleton,
            Prod.mk.injEq] at h h'
          rw [h.1, h'.1]
      | message msg dir =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_singleton, Prod.mk.injEq] at h h'
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            rcases h' with ⟨rfl, hEq⟩ | ⟨rfl, hEq⟩ <;>
            first | rfl | exact absurd hEq (by decide)
      | tock =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_singleton, Prod.mk.injEq] at h h'
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            rcases h' with ⟨rfl, hEq⟩ | ⟨rfl, hEq⟩ <;>
            first | rfl | exact absurd hEq (by decide)
      | progress pid =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_singleton, Prod.mk.injEq] at h h'
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            rcases h' with ⟨rfl, hEq⟩ | ⟨rfl, hEq⟩ <;>
            first | rfl | exact absurd hEq (by decide)
      | var name =>
          simp only [buildRelationSetCoreFuel, Finset.mem_singleton,
            Prod.mk.injEq] at h h'
          rw [h.1, h'.1]
      | choice left right =>
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
      | fairChoice bid left right =>
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
      | seq left right =>
          simp only [buildRelationSetCoreFuel, Finset.mem_union,
            Finset.mem_image, Prod.mk.injEq] at h h'
          rcases h with ⟨a, ha, rfl, ha2⟩ | ⟨a, ha, rfl, ha2⟩ <;>
            rcases h' with ⟨a', ha', rfl, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩
          · have hStateEq : a.2 = a'.2 := by injection ha2.trans ha2'.symm
            have ha'' : (a'.1, a.2) ∈ buildRelationSetCoreFuel signature fuel left :=
              hStateEq ▸ ha'
            rw [ih left ha ha'']
          · exact nomatch (ha2.trans ha2'.symm)
          · exact nomatch (ha2.trans ha2'.symm)
          · have hStateEq : a.2 = a'.2 := by injection ha2.trans ha2'.symm
            have ha'' : (a'.1, a.2) ∈ buildRelationSetCoreFuel signature fuel right :=
              hStateEq ▸ ha'
            exact ih right ha ha''
      | par left right interface =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_image, Prod.mk.injEq] at h h'
          rcases h with ⟨rfl, rfl⟩ | ⟨a, haMem, ha1, ha2⟩
          · rcases h' with ⟨rfl, -⟩ | ⟨a', ha'Mem, ha1', ha2'⟩
            · rfl
            · exact nomatch ha2'
          · rcases h' with ⟨-, ha2'⟩ | ⟨a', ha'Mem, ha1', ha2'⟩
            · exact nomatch (ha2.trans ha2')
            · have hEq := ha2.trans ha2'.symm
              have hEqLeft : a.1.2 = a'.1.2 := by injection hEq
              have hEqRight : a.2.2 = a'.2.2 := by injection hEq
              obtain ⟨haMemLeft, haMemRight⟩ := Finset.mem_product.mp haMem
              obtain ⟨ha'MemLeft, ha'MemRight⟩ := Finset.mem_product.mp ha'Mem
              have hLeftMem : (a'.1.1, a.1.2) ∈
                  buildRelationSetCoreFuel signature fuel left :=
                hEqLeft ▸ ha'MemLeft
              have hRightMem : (a'.2.1, a.2.2) ∈
                  buildRelationSetCoreFuel signature fuel right :=
                hEqRight ▸ ha'MemRight
              rw [← ha1, ← ha1', ih left haMemLeft hLeftMem, ih right haMemRight hRightMem]
      | recur name body =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_image, Prod.mk.injEq] at h h'
          rcases h with ⟨rfl, rfl⟩ | ⟨a, ha, rfl, ha2⟩
          · rcases h' with ⟨rfl, -⟩ | ⟨a', ha', rfl, ha2'⟩
            · rfl
            · exact nomatch ha2'
          · rcases h' with ⟨-, ha2'⟩ | ⟨a', ha', rfl, ha2'⟩
            · exact nomatch (ha2.trans ha2')
            · have hStateEq : a.2 = a'.2 := by injection ha2.trans ha2'.symm
              have ha'' : (a'.1, a.2) ∈ buildRelationSetCoreFuel signature fuel body :=
                hStateEq ▸ ha'
              rw [ih body ha ha'']
      | xoffer elseType branches =>
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
                  buildRelationSetCoreFuel signature fuel elseType :=
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
                  buildRelationSetCoreFuel signature fuel item.1.2 :=
                hItemEq ▸ hStateEq ▸ ha'
              rw [ih item.1.2 ha ha'']
      | offer elseType branches =>
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
                  buildRelationSetCoreFuel signature fuel elseType :=
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
                  buildRelationSetCoreFuel signature fuel
                    (parallelTypeBranchesSelecting item.1 branches) :=
                hItemEq ▸ hStateEq ▸ ha'
              rw [ih (parallelTypeBranchesSelecting item.1 branches) ha ha'']

/-- The public-fuel relation is functional: each compiled state relates to at
most one residual. Unconditional — no fuel-sufficiency side condition needed,
unlike `buildRelationSetCoreFuel_initial_mem`, since `buildRelationSetCoreFuel_functional`
holds for *every* fuel value, not just sufficient ones. -/
theorem buildRelationSetCore_functional
    (signature : TypeAlphabet) (processType : PactType)
    {residual residual' : PactType} {state : TypeAutomatonState}
    (hRelated : (residual, state) ∈ buildRelationSetCore signature processType)
    (hRelated' : (residual', state) ∈ buildRelationSetCore signature processType) :
    residual = residual' :=
  buildRelationSetCoreFuel_functional signature (typeCompilationFuel processType)
    processType hRelated hRelated'

/-! ### Fuel-sufficiency stability (needed to reconcile a shared parent fuel,
e.g. `max (typeCompilationFuel left) (typeCompilationFuel right)`, with each
child's own minimal fuel `typeCompilationFuel left`/`right` — the same
reconciliation `compileTypeFuel_eq_of_sufficient` provides for `compileType`,
needed here for the same reason: `buildRelationSetCoreFuel` mirrors
`compileTypeFuel`'s exact fuel-passing convention.) -/

private theorem buildRelationSetCoreFuel_succ_stable (signature : TypeAlphabet) :
    ∀ fuel processType, typeCompilationFuel processType ≤ fuel →
      buildRelationSetCoreFuel signature (fuel + 1) processType =
        buildRelationSetCoreFuel signature fuel processType := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      have hPositive := typeCompilationFuel_positive processType
      omega
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message msg dir => rfl
      | progress pid => rfl
      | tock => rfl
      | skip => rfl
      | var name => rfl
      | choice left right =>
          have hLeft : typeCompilationFuel left ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel right ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          change insert (PactType.choice left right, TypeAutomatonState.root)
              ((buildRelationSetCoreFuel signature (fuel+1) left).image
                  (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
                (buildRelationSetCoreFuel signature (fuel+1) right).image
                  (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2))) =
            insert (PactType.choice left right, TypeAutomatonState.root)
              ((buildRelationSetCoreFuel signature fuel left).image
                  (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
                (buildRelationSetCoreFuel signature fuel right).image
                  (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2)))
          rw [ih left hLeft, ih right hRight]
      | fairChoice bid left right =>
          have hLeft : typeCompilationFuel left ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel right ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          change insert (PactType.fairChoice bid left right, TypeAutomatonState.root)
              ((buildRelationSetCoreFuel signature (fuel+1) left).image
                  (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
                (buildRelationSetCoreFuel signature (fuel+1) right).image
                  (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2))) =
            insert (PactType.fairChoice bid left right, TypeAutomatonState.root)
              ((buildRelationSetCoreFuel signature fuel left).image
                  (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
                (buildRelationSetCoreFuel signature fuel right).image
                  (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2)))
          rw [ih left hLeft, ih right hRight]
      | seq left right =>
          have hLeft : typeCompilationFuel left ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel right ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          change
              (buildRelationSetCoreFuel signature (fuel+1) left).image
                  (fun entry => (PactType.seq entry.1 right, TypeAutomatonState.child 0 entry.2)) ∪
                (buildRelationSetCoreFuel signature (fuel+1) right).image
                  (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2)) =
              (buildRelationSetCoreFuel signature fuel left).image
                  (fun entry => (PactType.seq entry.1 right, TypeAutomatonState.child 0 entry.2)) ∪
                (buildRelationSetCoreFuel signature fuel right).image
                  (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2))
          rw [ih left hLeft, ih right hRight]
      | par left right interface =>
          have hLeft : typeCompilationFuel left ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel right ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          change insert (PactType.skip, TypeAutomatonState.final)
              ((Finset.product (buildRelationSetCoreFuel signature (fuel+1) left)
                  (buildRelationSetCoreFuel signature (fuel+1) right)).image
                (fun entry =>
                  (PactType.par entry.1.1 entry.2.1 interface,
                    TypeAutomatonState.pair entry.1.2 entry.2.2))) =
            insert (PactType.skip, TypeAutomatonState.final)
              ((Finset.product (buildRelationSetCoreFuel signature fuel left)
                  (buildRelationSetCoreFuel signature fuel right)).image
                (fun entry =>
                  (PactType.par entry.1.1 entry.2.1 interface,
                    TypeAutomatonState.pair entry.1.2 entry.2.2)))
          rw [ih left hLeft, ih right hRight]
      | recur name body =>
          have hBody : typeCompilationFuel body ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          change insert (PactType.recur name body, TypeAutomatonState.root)
              ((buildRelationSetCoreFuel signature (fuel+1) body).image
                (fun entry =>
                  (entry.1.replaceVar name (.recur name body),
                    TypeAutomatonState.child 0 entry.2))) =
            insert (PactType.recur name body, TypeAutomatonState.root)
              ((buildRelationSetCoreFuel signature fuel body).image
                (fun entry =>
                  (entry.1.replaceVar name (.recur name body),
                    TypeAutomatonState.child 0 entry.2)))
          rw [ih body hBody]
      | xoffer elseType branches =>
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
            · have ha' : a ∈ buildRelationSetCoreFuel signature fuel elseType :=
                ih elseType hElse ▸ ha
              exact Or.inr (Or.inl ⟨a, ha', h⟩)
            · have ha' : a ∈ buildRelationSetCoreFuel signature fuel item.1.2 :=
                ih item.1.2 (hItemFuel item hItem) ▸ ha
              exact Or.inr (Or.inr ⟨item, hItem, a, ha', hEq⟩)
          · rintro (h | ⟨a, ha, h⟩ | ⟨item, hItem, a, ha, hEq⟩)
            · exact Or.inl h
            · have ha' : a ∈ buildRelationSetCoreFuel signature (fuel + 1) elseType :=
                (ih elseType hElse).symm ▸ ha
              exact Or.inr (Or.inl ⟨a, ha', h⟩)
            · have ha' : a ∈ buildRelationSetCoreFuel signature (fuel + 1) item.1.2 :=
                (ih item.1.2 (hItemFuel item hItem)).symm ▸ ha
              exact Or.inr (Or.inr ⟨item, hItem, a, ha', hEq⟩)
      | offer elseType branches =>
          have hElse : typeCompilationFuel elseType ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hBranchesFuel : ∀ item : BareMessage × PactType,
              typeCompilationFuel (parallelTypeBranchesSelecting item branches) ≤ fuel := by
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
            · have ha' : a ∈ buildRelationSetCoreFuel signature fuel elseType :=
                ih elseType hElse ▸ ha
              exact Or.inr (Or.inl ⟨a, ha', h⟩)
            · have ha' : a ∈ buildRelationSetCoreFuel signature fuel
                  (parallelTypeBranchesSelecting item.1 branches) :=
                ih _ (hBranchesFuel item.1) ▸ ha
              exact Or.inr (Or.inr ⟨item, hItem, a, ha', hEq⟩)
          · rintro (h | ⟨a, ha, h⟩ | ⟨item, hItem, a, ha, hEq⟩)
            · exact Or.inl h
            · have ha' : a ∈ buildRelationSetCoreFuel signature (fuel + 1) elseType :=
                (ih elseType hElse).symm ▸ ha
              exact Or.inr (Or.inl ⟨a, ha', h⟩)
            · have ha' : a ∈ buildRelationSetCoreFuel signature (fuel + 1)
                  (parallelTypeBranchesSelecting item.1 branches) :=
                (ih _ (hBranchesFuel item.1)).symm ▸ ha
              exact Or.inr (Or.inr ⟨item, hItem, a, ha', hEq⟩)

/-- Any two sufficient budgets produce the same relation set. -/
private theorem buildRelationSetCoreFuel_add_stable
    (signature : TypeAlphabet) (processType : PactType)
    (fuel extra : Nat) (hFuel : typeCompilationFuel processType ≤ fuel) :
    buildRelationSetCoreFuel signature (fuel + extra) processType =
      buildRelationSetCoreFuel signature fuel processType := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ,
        buildRelationSetCoreFuel_succ_stable signature (fuel + extra) processType
          (by omega),
        ih]

/-- Reconciles any two sufficient fuel values against the same `processType`. -/
theorem buildRelationSetCoreFuel_eq_of_sufficient
    (signature : TypeAlphabet) (processType : PactType)
    {leftFuel rightFuel : Nat}
    (hLeft : TypeCompilationFuelSufficient processType leftFuel)
    (hRight : TypeCompilationFuelSufficient processType rightFuel) :
    buildRelationSetCoreFuel signature leftFuel processType =
      buildRelationSetCoreFuel signature rightFuel processType := by
  by_cases hOrder : leftFuel ≤ rightFuel
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hOrder
    exact (buildRelationSetCoreFuel_add_stable signature processType leftFuel extra
      hLeft).symm
  · have hReverse : rightFuel ≤ leftFuel := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hReverse
    exact buildRelationSetCoreFuel_add_stable signature processType rightFuel extra hRight

/-- Defines relation membership as occurrence of the residual/state pair in the relation set. -/
def relationMembership
    (relation_set : Finset (PactType × TypeAutomatonState))
    (processType : PactType) (state : TypeAutomatonState) : Prop :=
  (processType, state) ∈ relation_set

/-- The generated correspondence relation for `ty`, against the signature
`auto` was compiled from. -/
def buildRelationSet (ty : PactType) (auto : TypeAutomaton) :
    Finset (PactType × TypeAutomatonState) :=
  buildRelationSetCore auto.signature ty

/-- The generated relation contains its initial residual/state seed pair. -/
theorem buildRelationSet_initial (ty : PactType) (auto : TypeAutomaton)
    (hAuto : auto = compileType auto.signature ty := by rfl) :
    relationMembership (buildRelationSet ty auto) ty auto.initial := by
  unfold relationMembership buildRelationSet
  rw [hAuto]
  exact buildRelationSetCore_initial_mem auto.signature ty

end

end Pact
