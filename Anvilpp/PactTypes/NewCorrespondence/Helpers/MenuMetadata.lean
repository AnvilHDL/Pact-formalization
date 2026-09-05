import Anvilpp.PactTypes.NewCorrespondence.Helpers.CompiledShape

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-- Menu metadata, like the execution fragment and canonical relation,
stabilizes once the constructor budget is sufficient. -/
theorem compileTypeMenuLinksFuel_succ_stable :
    ∀ fuel ty, typeCompilationFuel ty ≤ fuel →
      compileTypeMenuLinksFuel (fuel + 1) ty = compileTypeMenuLinksFuel fuel ty := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty hFuel
      have := typeCompilationFuel_positive ty
      omega
  | succ fuel ih =>
      intro ty hFuel
      cases ty with
      | message a m d | progress a p | skip a | tock a | var a x =>
          simp only [compileTypeMenuLinksFuel]
      | choice a left right | fairChoice a bid left right =>
          have hLeft : typeCompilationFuel left ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel right ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          simpa only [compileTypeMenuLinksFuel] using
            congrArg₂ (fun l r =>
              l.image (fun q : TypeAutomatonState × TypeAutomatonState =>
                (TypeAutomatonState.child 0 q.1, TypeAutomatonState.child 0 q.2)) ∪
              r.image (fun q : TypeAutomatonState × TypeAutomatonState =>
                (TypeAutomatonState.child 1 q.1, TypeAutomatonState.child 1 q.2)))
              (ih left hLeft) (ih right hRight)
      | seq a left right =>
          have hLeft : typeCompilationFuel left ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel right ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          conv_lhs => rw [compileTypeMenuLinksFuel]
          conv_rhs => rw [compileTypeMenuLinksFuel]
          simp only [ih left hLeft, ih right hRight,
            compileTypeFuel_eq_of_sufficient left (Nat.le.step hLeft) hLeft,
            compileTypeFuel_eq_of_sufficient right (Nat.le.step hRight) hRight,
            buildRelationSetCoreFuel_eq_of_sufficient left (Nat.le.step hLeft) hLeft]
      | recur a name body =>
          have hBody : typeCompilationFuel body ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          conv_lhs => rw [compileTypeMenuLinksFuel]
          conv_rhs => rw [compileTypeMenuLinksFuel]
          simp only [ih body hBody]
      | par a left right interface =>
          have hLeft : typeCompilationFuel (left.reannotate a) ≤ fuel := by
            rw [typeCompilationFuel_reannotate]
            simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel (right.reannotate a) ≤ fuel := by
            rw [typeCompilationFuel_reannotate]
            simp [typeCompilationFuel] at hFuel; omega
          conv_lhs => rw [compileTypeMenuLinksFuel]
          conv_rhs => rw [compileTypeMenuLinksFuel]
          simp only [ih _ hLeft, ih _ hRight,
            compileTypeFuel_eq_of_sufficient _ (Nat.le.step hLeft) hLeft,
            compileTypeFuel_eq_of_sufficient _ (Nat.le.step hRight) hRight]
      | xoffer a other branches =>
          have hElse : typeCompilationFuel other ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hItems : ∀ item ∈ branches.zipIdx,
              compileTypeMenuLinksFuel (fuel + 1) item.1.2 =
                compileTypeMenuLinksFuel fuel item.1.2 := by
            intro item hItem
            apply ih
            have hMember : item.1 ∈ branches := by
              have hFields := List.mem_zipIdx hItem
              simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hFields
              obtain ⟨hBound, hValue⟩ := hFields
              simpa [hValue] using List.getElem_mem hBound
            have := typeCompilationFuel_le_typeBranchCompilationFuel branches item.1 hMember
            simp [typeCompilationFuel] at hFuel
            omega
          ext entry
          simp only [compileTypeMenuLinksFuel, mem_foldl_union_iff, ih other hElse]
          apply or_congr Iff.rfl
          apply exists_congr
          intro item
          by_cases hItem : item ∈ branches.zipIdx
          · simp only [hItem, true_and, hItems item hItem]
          · simp [hItem]
      | offer a other branches =>
          have hElse : typeCompilationFuel other ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hItems : ∀ item : BareMessage × PactType,
              compileTypeMenuLinksFuel (fuel + 1)
                  (parallelTypeBranchesSelecting a item branches) =
                compileTypeMenuLinksFuel fuel
                  (parallelTypeBranchesSelecting a item branches) := by
            intro item
            apply ih
            rw [typeCompilationFuel_parallelTypeBranchesSelecting]
            simp [typeCompilationFuel] at hFuel
            omega
          ext entry
          simp only [compileTypeMenuLinksFuel, mem_foldl_union_iff, ih other hElse, hItems]

theorem compileTypeMenuLinksFuel_eq_of_sufficient
    (ty : PactType) {first second : Nat}
    (hFirst : typeCompilationFuel ty ≤ first)
    (hSecond : typeCompilationFuel ty ≤ second) :
    compileTypeMenuLinksFuel first ty = compileTypeMenuLinksFuel second ty := by
  have hAdd : ∀ fuel extra, typeCompilationFuel ty ≤ fuel →
      compileTypeMenuLinksFuel (fuel + extra) ty = compileTypeMenuLinksFuel fuel ty := by
    intro fuel extra hFuel
    induction extra with
    | zero => simp
    | succ extra ih =>
        rw [Nat.add_succ, compileTypeMenuLinksFuel_succ_stable (fuel + extra) ty
          (by omega), ih]
  by_cases hOrder : first ≤ second
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hOrder
    exact (hAdd first extra hFirst).symm
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show second ≤ first by omega)
    exact hAdd second extra hSecond

/-- Every menu dependency points to an existing compiled state. -/
theorem compileTypeMenuLinksFuel_targets_mem :
    ∀ fuel ty, typeCompilationFuel ty ≤ fuel → ty.OfferBranchesDisjoint →
      ∀ link ∈ compileTypeMenuLinksFuel fuel ty,
        link.2 ∈ (compileTypeFuel fuel ty).states := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty _ _ link hLink
      simp [compileTypeMenuLinksFuel] at hLink
  | succ fuel ih =>
      intro ty hFuel hDisjoint link hLink
      cases ty with
      | message a m d | progress a p | skip a | tock a | var a x =>
          simp [compileTypeMenuLinksFuel] at hLink
      | choice a left right | fairChoice a bid left right =>
          have hLeft : typeCompilationFuel left ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel right ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [compileTypeMenuLinksFuel, Finset.mem_union, Finset.mem_image] at hLink
          rcases hLink with ⟨entry, hEntry, rfl⟩ | ⟨entry, hEntry, rfl⟩
          · have ht := ih left hLeft hDisjoint.1 entry hEntry
            simp only [compileTypeFuel, buildChoiceAutomaton, finishAutomatonFragment,
              Finset.mem_union, childStates, childState]
            exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨entry.2, ht, rfl⟩))
          · have ht := ih right hRight hDisjoint.2 entry hEntry
            simp only [compileTypeFuel, buildChoiceAutomaton, finishAutomatonFragment,
              Finset.mem_union, childStates, childState]
            exact Or.inr (Finset.mem_image.mpr ⟨entry.2, ht, rfl⟩)
      | seq a left right =>
          have hLeft : typeCompilationFuel left ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel right ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          have hInitial := compileTypeFuel_initial_mem fuel right hRight
          simp only [compileTypeMenuLinksFuel, Finset.mem_union, Finset.mem_image,
            Finset.mem_filter] at hLink
          rcases hLink with (⟨entry, ⟨hEntry, _⟩, rfl⟩ | ⟨entry, hEntry, rfl⟩) |
            ⟨entry, _, rfl⟩
          · simpa only [compileTypeFuel] using sequenceRedirect_mem_states
              (compileTypeFuel fuel left) (compileTypeFuel fuel right) hInitial entry.2
              (ih left hLeft hDisjoint.1 entry hEntry)
          · have ht := ih right hRight hDisjoint.2 entry hEntry
            simp only [compileTypeFuel, buildSequenceAutomaton, finishAutomatonFragment,
              Finset.mem_union, childStates, childState]
            exact Or.inr (Finset.mem_image.mpr ⟨entry.2, ht, rfl⟩)
          · simp only [compileTypeFuel, buildSequenceAutomaton, finishAutomatonFragment,
              Finset.mem_union, childStates, childState]
            exact Or.inr (Finset.mem_image.mpr ⟨_, hInitial, rfl⟩)
      | recur a name body =>
          have hBody : typeCompilationFuel body ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [compileTypeMenuLinksFuel, Finset.mem_image] at hLink
          obtain ⟨entry, hEntry, rfl⟩ := hLink
          have ht := ih body hBody hDisjoint entry hEntry
          simp only [compileTypeFuel, buildRecursionAutomaton, finishAutomatonFragment,
            Finset.mem_union, childStates, childState]
          exact Or.inr (Finset.mem_image.mpr ⟨entry.2, ht, rfl⟩)
      | par a left right interface =>
          have hLeft : typeCompilationFuel (left.reannotate a) ≤ fuel := by
            rw [typeCompilationFuel_reannotate]
            simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel (right.reannotate a) ≤ fuel := by
            rw [typeCompilationFuel_reannotate]
            simp [typeCompilationFuel] at hFuel; omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [compileTypeMenuLinksFuel, Finset.mem_union, Finset.mem_image,
            Finset.mem_filter] at hLink
          rcases hLink with ⟨entry, ⟨hEntry, _⟩, rfl⟩ | ⟨entry, ⟨hEntry, _⟩, rfl⟩
          · have ht := ih (left.reannotate a) hLeft
              (reannotate_offerBranchesDisjoint left a hDisjoint.1) entry hEntry
            rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate fuel left hDisjoint.1 a).1] at ht
            simp only [compileTypeFuel, buildParallelAutomaton, finishAutomatonFragment,
              Finset.mem_insert, Finset.mem_union]
            split
            · exact Or.inl rfl
            · exact Or.inr (Or.inl (Or.inr (Finset.mem_image.mpr ⟨entry.2, ht, rfl⟩)))
          · have ht := ih (right.reannotate a) hRight
              (reannotate_offerBranchesDisjoint right a hDisjoint.2) entry hEntry
            rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate fuel right hDisjoint.2 a).1] at ht
            simp only [compileTypeFuel, buildParallelAutomaton, finishAutomatonFragment,
              Finset.mem_insert, Finset.mem_union]
            split
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (Finset.mem_image.mpr ⟨entry.2, ht, rfl⟩))
      | xoffer a other branches =>
          have hElse : typeCompilationFuel other ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [compileTypeMenuLinksFuel, mem_foldl_union_iff, Finset.mem_image] at hLink
          rcases hLink with ⟨entry, hEntry, rfl⟩ | ⟨item, hItem, entry, hEntry, rfl⟩
          · have ht := ih other hElse hDisjoint.1 entry hEntry
            simp only [compileTypeFuel, buildExclusiveOfferAutomaton, finishAutomatonFragment,
              Finset.mem_union, childStates, childState]
            exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨entry.2, ht, rfl⟩))
          · have hMember : item.1 ∈ branches := by
              obtain ⟨hBound, hValue⟩ := List.mem_zipIdx' hItem
              simpa [hValue] using List.getElem_mem hBound
            have hItemFuel : typeCompilationFuel item.1.2 ≤ fuel := by
              have := typeCompilationFuel_le_typeBranchCompilationFuel branches item.1 hMember
              simp [typeCompilationFuel] at hFuel
              omega
            have ht := ih item.1.2 hItemFuel
              (offerBranchesDisjoint_of_mem_branch hDisjoint.2 hMember) entry hEntry
            simp only [compileTypeFuel, buildExclusiveOfferAutomaton, finishAutomatonFragment,
              Finset.mem_union]
            right
            rw [indexedFragmentStates, mem_foldl_union_iff]
            right
            refine ⟨((item.1.1, compileTypeFuel fuel item.1.2), item.2), ?_, ?_⟩
            · rw [List.zipIdx_map]
              exact List.mem_map.mpr ⟨item, hItem, rfl⟩
            · exact Finset.mem_image.mpr ⟨entry.2, ht, rfl⟩
      | offer a other branches =>
          have hElse : typeCompilationFuel other ≤ fuel := by
            simp [typeCompilationFuel] at hFuel; omega
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [compileTypeMenuLinksFuel, mem_foldl_union_iff, Finset.mem_image] at hLink
          rcases hLink with ⟨entry, hEntry, rfl⟩ | ⟨item, hItem, entry, hEntry, rfl⟩
          · have ht := ih other hElse hDisjoint.1 entry hEntry
            simp only [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
              finishAutomatonFragment, Finset.mem_union, childStates, childState]
            exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨entry.2, ht, rfl⟩))
          · have hItemFuel : typeCompilationFuel
                (parallelTypeBranchesSelecting a item.1 branches) ≤ fuel := by
              rw [typeCompilationFuel_parallelTypeBranchesSelecting]
              simp [typeCompilationFuel] at hFuel
              omega
            have ht := ih (parallelTypeBranchesSelecting a item.1 branches) hItemFuel
              (parallelTypeBranchesSelecting_offerBranchesDisjoint item.1 branches
                (fun item hItem => offerBranchesDisjoint_of_mem_branch hDisjoint.2.2 hItem))
              entry hEntry
            simp only [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
              finishAutomatonFragment, Finset.mem_union]
            right
            rw [indexedFragmentStates, mem_foldl_union_iff]
            right
            refine ⟨((item.1.1, compileTypeFuel fuel
              (parallelTypeBranchesSelecting a item.1 branches)), item.2), ?_, ?_⟩
            · rw [List.zipIdx_map]
              exact List.mem_map.mpr ⟨item, hItem, rfl⟩
            · exact Finset.mem_image.mpr ⟨entry.2, ht, rfl⟩


/-- An indexed offer branch retains precisely its own dependencies. -/
theorem menuDependencyTargets_indexed {α : Type}
    (items : List α)
    (dependencies : α → Finset (TypeAutomatonState × TypeAutomatonState))
    (seed : Finset (TypeAutomatonState × TypeAutomatonState))
    (index : Nat) (item : α) (hItem : items[index]? = some item)
    (source : TypeAutomatonState) :
    menuDependencyTargets
      (items.zipIdx.foldl (fun acc entry => acc ∪
        (dependencies entry.1).image fun link =>
          (TypeAutomatonState.child (entry.2 + 1) link.1,
            TypeAutomatonState.child (entry.2 + 1) link.2)) seed)
      (.child (index + 1) source) =
      menuDependencyTargets seed (.child (index + 1) source) ∪
        (menuDependencyTargets (dependencies item) source).image (.child (index + 1)) := by
  classical
  ext target
  constructor
  · intro hTarget
    obtain ⟨link, hLink, hTarget⟩ := Finset.mem_image.mp hTarget
    obtain ⟨hLink, hSource⟩ := Finset.mem_filter.mp hLink
    rw [mem_foldl_union_iff] at hLink
    rcases hLink with hSeed | ⟨entry, hEntry, hCopy⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨link, Finset.mem_filter.mpr ⟨hSeed, hSource⟩, hTarget⟩)
    · obtain ⟨childLink, hChildLink, rfl⟩ := Finset.mem_image.mp hCopy
      have hIndex : entry.2 = index := by
        have := (TypeAutomatonState.child.inj hSource).1
        omega
      have hChildSource := (TypeAutomatonState.child.inj hSource).2
      have hEntryGet := List.mem_zipIdx_iff_getElem?.mp hEntry
      rw [hIndex, hItem] at hEntryGet
      have hEntryValue : entry.1 = item := (Option.some.inj hEntryGet).symm
      apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨childLink.2, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨childLink,
          Finset.mem_filter.mpr ⟨hEntryValue ▸ hChildLink, hChildSource⟩, rfl⟩
      · simpa [hIndex] using hTarget
  · intro hTarget
    rcases Finset.mem_union.mp hTarget with hSeed | hChild
    · obtain ⟨link, hLink, hTarget⟩ := Finset.mem_image.mp hSeed
      obtain ⟨hSeedMem, hSource⟩ := Finset.mem_filter.mp hLink
      apply Finset.mem_image.mpr
      refine ⟨link, Finset.mem_filter.mpr ⟨?_, hSource⟩, hTarget⟩
      rw [mem_foldl_union_iff]
      exact Or.inl hSeedMem
    · obtain ⟨childTarget, hChildTarget, rfl⟩ := Finset.mem_image.mp hChild
      obtain ⟨link, hLink, rfl⟩ := Finset.mem_image.mp hChildTarget
      obtain ⟨hLinkMem, hSource⟩ := Finset.mem_filter.mp hLink
      apply Finset.mem_image.mpr
      refine ⟨(.child (index + 1) link.1, .child (index + 1) link.2),
        Finset.mem_filter.mpr ⟨?_, by simp [hSource]⟩, rfl⟩
      rw [mem_foldl_union_iff]
      exact Or.inr ⟨(item, index), List.mem_zipIdx_iff_getElem?.mpr hItem,
        Finset.mem_image.mpr ⟨link, hLinkMem, rfl⟩⟩

/-- No constructor installs a menu-only dependency at a fresh root. -/
theorem menuDependencyTargets_indexed_zero {α : Type}
    (items : List α)
    (dependencies : α → Finset (TypeAutomatonState × TypeAutomatonState))
    (seed : Finset (TypeAutomatonState × TypeAutomatonState))
    (source : TypeAutomatonState) :
    menuDependencyTargets
      (items.zipIdx.foldl (fun acc entry => acc ∪
        (dependencies entry.1).image fun link =>
          (TypeAutomatonState.child (entry.2 + 1) link.1,
            TypeAutomatonState.child (entry.2 + 1) link.2)) seed)
      (.child 0 source) = menuDependencyTargets seed (.child 0 source) := by
  classical
  ext target
  simp only [menuDependencyTargets, Finset.mem_image, Finset.mem_filter,
    mem_foldl_union_iff, Prod.exists, TypeAutomatonState.child.injEq]
  aesop

/-- No constructor installs a menu-only dependency at a fresh root. -/
@[simp] theorem compileTypeMenuLinksFuel_root (fuel : Nat) (ty : PactType) :
    menuDependencyTargets (compileTypeMenuLinksFuel fuel ty) .root = ∅ := by
  cases fuel with
  | zero => simp [compileTypeMenuLinksFuel]
  | succ fuel =>
      cases ty <;>
        simp [compileTypeMenuLinksFuel, menuDependencyTargets, Finset.mem_image,
          mem_foldl_union_iff] <;> aesop

/-- The left child retains its own menu dependencies. -/
theorem menuDependencyTargets_choice_left
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (source : TypeAutomatonState) :
    menuDependencyTargets
        (compileTypeMenuLinksFuel (typeCompilationFuel (.choice alphabet left right)) (.choice alphabet left right))
        (.child 0 source) =
      (menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel left) left)
        source).image (.child 0) := by
  have hFuel : typeCompilationFuel (.choice alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuel, compileTypeMenuLinksFuel]
  simp only [menuDependencyTargets_union, menuDependencyTargets_child,
    ↓reduceIte, Finset.union_empty]
  rw [compileTypeMenuLinksFuel_eq_of_sufficient left (le_max_left _ _) le_rfl]
  simp

/-- The right child retains its own menu dependencies. -/
theorem menuDependencyTargets_choice_right
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (source : TypeAutomatonState) :
    menuDependencyTargets
        (compileTypeMenuLinksFuel (typeCompilationFuel (.choice alphabet left right)) (.choice alphabet left right))
        (.child 1 source) =
      (menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel right) right)
        source).image (.child 1) := by
  have hFuel : typeCompilationFuel (.choice alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuel, compileTypeMenuLinksFuel]
  simp only [menuDependencyTargets_union, menuDependencyTargets_child,
    ↓reduceIte, Finset.empty_union]
  rw [compileTypeMenuLinksFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
  simp

/-- The left child retains its own menu dependencies. -/
theorem menuDependencyTargets_fairChoice_left
    (alphabet : PactTypeAlphabet) (bid : BranchId) (left right : PactType)
    (source : TypeAutomatonState) :
    menuDependencyTargets
        (compileTypeMenuLinksFuel (typeCompilationFuel (.fairChoice alphabet bid left right)) (.fairChoice alphabet bid left right))
        (.child 0 source) =
      (menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel left) left)
        source).image (.child 0) := by
  have hFuel : typeCompilationFuel (.fairChoice alphabet bid left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuel, compileTypeMenuLinksFuel]
  simp only [menuDependencyTargets_union, menuDependencyTargets_child,
    ↓reduceIte, Finset.union_empty]
  rw [compileTypeMenuLinksFuel_eq_of_sufficient left (le_max_left _ _) le_rfl]
  simp

/-- The right child retains its own menu dependencies. -/
theorem menuDependencyTargets_fairChoice_right
    (alphabet : PactTypeAlphabet) (bid : BranchId) (left right : PactType)
    (source : TypeAutomatonState) :
    menuDependencyTargets
        (compileTypeMenuLinksFuel (typeCompilationFuel (.fairChoice alphabet bid left right)) (.fairChoice alphabet bid left right))
        (.child 1 source) =
      (menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel right) right)
        source).image (.child 1) := by
  have hFuel : typeCompilationFuel (.fairChoice alphabet bid left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuel, compileTypeMenuLinksFuel]
  simp only [menuDependencyTargets_union, menuDependencyTargets_child,
    ↓reduceIte, Finset.empty_union]
  rw [compileTypeMenuLinksFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
  simp

/-- Sequence installs no additional dependency at a right-child state. -/
theorem menuDependencyTargets_seq_right
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (source : TypeAutomatonState) :
    menuDependencyTargets
        (compileTypeMenuLinksFuel (typeCompilationFuel (.seq alphabet left right))
          (.seq alphabet left right)) (.child 1 source) =
      (menuDependencyTargets (compileTypeMenuLinksFuel (typeCompilationFuel right) right)
        source).image (.child 1) := by
  have hFuel : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuel, compileTypeMenuLinksFuel]
  simp only [menuDependencyTargets_union]
  have hInherited :
      menuDependencyTargets
        (((compileTypeMenuLinksFuel
            (max (typeCompilationFuel left) (typeCompilationFuel right)) left).filter
              fun link => link.1 ∉ sequenceDeleted
                (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) left)).image
          fun link => (TypeAutomatonState.child 0 link.1,
            sequenceRedirect
              (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
              link.2)) (.child 1 source) = ∅ := by
    ext target
    simp [menuDependencyTargets]
  rw [hInherited]
  have hNew : ∀ entries : Finset (PactType × TypeAutomatonState),
      menuDependencyTargets (entries.image fun entry =>
        (TypeAutomatonState.child 0 entry.2,
          TypeAutomatonState.child 1
            (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) right).initial))
        (.child 1 source) = ∅ := by
    intro entries
    ext target
    simp [menuDependencyTargets]
  rw [hNew]
  simp only [menuDependencyTargets_child, ↓reduceIte, Finset.empty_union, Finset.union_empty]
  rw [compileTypeMenuLinksFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]

/-- The default offer child retains its menu dependencies. -/
theorem menuDependencyTargets_xoffer_else
    (alphabet : PactTypeAlphabet) (other : PactType)
    (branches : List (BareMessage × PactType))
    (source : TypeAutomatonState) :
    menuDependencyTargets
      (compileTypeMenuLinksFuel (typeCompilationFuel (.xoffer alphabet other branches))
        (.xoffer alphabet other branches)) (.child 0 source) =
      (menuDependencyTargets
        (compileTypeMenuLinksFuel (typeCompilationFuel other) other)
        source).image (.child 0) := by
  have hFuel : typeCompilationFuel (.xoffer alphabet other branches) =
      max (typeCompilationFuel other) (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuel, compileTypeMenuLinksFuel]
  rw [menuDependencyTargets_indexed_zero branches (fun entry =>
    compileTypeMenuLinksFuel (max (typeCompilationFuel other) (typeBranchCompilationFuel branches))
      entry.2), menuDependencyTargets_child]
  simp only [↓reduceIte]
  rw [compileTypeMenuLinksFuel_eq_of_sufficient other (le_max_left _ _) le_rfl]

/-- A selected offer child retains its menu dependencies. -/
theorem menuDependencyTargets_xoffer_branch
    (alphabet : PactTypeAlphabet) (other : PactType)
    (branches : List (BareMessage × PactType))
    (index : Nat) (action : BareMessage) (branchType : PactType)
    (hBranch : branches[index]? = some (action, branchType))
    (source : TypeAutomatonState) :
    menuDependencyTargets
      (compileTypeMenuLinksFuel (typeCompilationFuel (.xoffer alphabet other branches))
        (.xoffer alphabet other branches)) (.child (index + 1) source) =
      (menuDependencyTargets
        (compileTypeMenuLinksFuel (typeCompilationFuel branchType) branchType)
        source).image (.child (index + 1)) := by
  have hFuel : typeCompilationFuel (.xoffer alphabet other branches) =
      max (typeCompilationFuel other) (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuel, compileTypeMenuLinksFuel]
  rw [menuDependencyTargets_indexed branches (fun entry =>
    compileTypeMenuLinksFuel (max (typeCompilationFuel other) (typeBranchCompilationFuel branches))
      entry.2) _ index (action, branchType) hBranch]
  simp only [menuDependencyTargets_child, if_neg (show (0 : Nat) ≠ index + 1 by omega),
    Finset.empty_union]
  have hChildFuel : typeCompilationFuel branchType ≤
      max (typeCompilationFuel other) (typeBranchCompilationFuel branches) := by
    exact le_trans
      (typeCompilationFuel_le_typeBranchCompilationFuel branches (action, branchType)
        (List.mem_of_getElem? hBranch)) (le_max_right _ _)
  rw [compileTypeMenuLinksFuel_eq_of_sufficient branchType hChildFuel le_rfl]

/-- The default offer child retains its menu dependencies. -/
theorem menuDependencyTargets_offer_else
    (alphabet : PactTypeAlphabet) (other : PactType)
    (branches : List (BareMessage × PactType))
    (source : TypeAutomatonState) :
    menuDependencyTargets
      (compileTypeMenuLinksFuel (typeCompilationFuel (.offer alphabet other branches))
        (.offer alphabet other branches)) (.child 0 source) =
      (menuDependencyTargets
        (compileTypeMenuLinksFuel (typeCompilationFuel other) other)
        source).image (.child 0) := by
  have hFuel : typeCompilationFuel (.offer alphabet other branches) =
      max (typeCompilationFuel other) (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuel, compileTypeMenuLinksFuel]
  rw [menuDependencyTargets_indexed_zero branches (fun entry =>
    compileTypeMenuLinksFuel (max (typeCompilationFuel other) (conjunctiveCompilationFuel branches))
      (parallelTypeBranchesSelecting alphabet entry branches)), menuDependencyTargets_child]
  simp only [↓reduceIte]
  rw [compileTypeMenuLinksFuel_eq_of_sufficient other (le_max_left _ _) le_rfl]

/-- A selected offer child retains its menu dependencies. -/
theorem menuDependencyTargets_offer_branch
    (alphabet : PactTypeAlphabet) (other : PactType)
    (branches : List (BareMessage × PactType))
    (index : Nat) (action : BareMessage) (branchType : PactType)
    (hBranch : branches[index]? = some (action, branchType))
    (source : TypeAutomatonState) :
    menuDependencyTargets
      (compileTypeMenuLinksFuel (typeCompilationFuel (.offer alphabet other branches))
        (.offer alphabet other branches)) (.child (index + 1) source) =
      (menuDependencyTargets
        (compileTypeMenuLinksFuel (typeCompilationFuel (parallelTypeBranchesSelecting alphabet (action, branchType) branches)) (parallelTypeBranchesSelecting alphabet (action, branchType) branches))
        source).image (.child (index + 1)) := by
  have hFuel : typeCompilationFuel (.offer alphabet other branches) =
      max (typeCompilationFuel other) (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuel, compileTypeMenuLinksFuel]
  rw [menuDependencyTargets_indexed branches (fun entry =>
    compileTypeMenuLinksFuel (max (typeCompilationFuel other) (conjunctiveCompilationFuel branches))
      (parallelTypeBranchesSelecting alphabet entry branches)) _ index (action, branchType) hBranch]
  simp only [menuDependencyTargets_child, if_neg (show (0 : Nat) ≠ index + 1 by omega),
    Finset.empty_union]
  have hChildFuel : typeCompilationFuel (parallelTypeBranchesSelecting alphabet (action, branchType) branches) ≤
      max (typeCompilationFuel other) (conjunctiveCompilationFuel branches) := by
    rw [typeCompilationFuel_parallelTypeBranchesSelecting]
    exact le_max_right _ _
  rw [compileTypeMenuLinksFuel_eq_of_sufficient (parallelTypeBranchesSelecting alphabet (action, branchType) branches) hChildFuel le_rfl]

@[simp] theorem compileTypeMenuLinksFuel_final (fuel : Nat) (ty : PactType) :
    menuDependencyTargets (compileTypeMenuLinksFuel fuel ty) .final = ∅ := by
  cases fuel with
  | zero => simp [compileTypeMenuLinksFuel]
  | succ fuel =>
      cases ty <;>
        simp [compileTypeMenuLinksFuel, menuDependencyTargets, Finset.mem_image,
          mem_foldl_union_iff] <;> aesop

/-- Optimistic links are installed at sequence states, never at product pairs. -/
@[simp] theorem compileTypeMenuLinksFuel_pair (fuel : Nat) (ty : PactType)
    (left right : TypeAutomatonState) :
    menuDependencyTargets (compileTypeMenuLinksFuel fuel ty) (.pair left right) = ∅ := by
  cases fuel with
  | zero => simp [compileTypeMenuLinksFuel]
  | succ fuel =>
      cases ty <;>
        simp [compileTypeMenuLinksFuel, menuDependencyTargets, Finset.mem_image,
          mem_foldl_union_iff] <;> aesop

/-- Survivor dependencies use the same target redirection as the component copy. -/
theorem menuDependencyTargets_par_survivorLeft
    (fuel : Nat) (alphabet : PactTypeAlphabet) (left right : PactType)
    (interface : Interface) (source : TypeAutomatonState)
    (hSource : source ∉ (compileTypeFuel fuel (left.reannotate alphabet)).accepting) :
    menuDependencyTargets
        (compileTypeMenuLinksFuel (fuel + 1) (.par alphabet left right interface))
        (.survivor 0 source) =
      (menuDependencyTargets
        (compileTypeMenuLinksFuel fuel (left.reannotate alphabet)) source).image
        (fun target => if target ∈ (compileTypeFuel fuel (left.reannotate alphabet)).accepting
          then TypeAutomatonState.final else .survivor 0 target) := by
  classical
  ext target
  simp only [compileTypeMenuLinksFuel, menuDependencyTargets, Finset.mem_image,
    Finset.mem_filter, Finset.mem_union, Prod.exists, Prod.mk.injEq,
    TypeAutomatonState.survivor.injEq]
  aesop

/-- Survivor dependencies use the same target redirection as the component copy. -/
theorem menuDependencyTargets_par_survivorRight
    (fuel : Nat) (alphabet : PactTypeAlphabet) (left right : PactType)
    (interface : Interface) (source : TypeAutomatonState)
    (hSource : source ∉ (compileTypeFuel fuel (right.reannotate alphabet)).accepting) :
    menuDependencyTargets
        (compileTypeMenuLinksFuel (fuel + 1) (.par alphabet left right interface))
        (.survivor 1 source) =
      (menuDependencyTargets
        (compileTypeMenuLinksFuel fuel (right.reannotate alphabet)) source).image
        (fun target => if target ∈ (compileTypeFuel fuel (right.reannotate alphabet)).accepting
          then TypeAutomatonState.final else .survivor 1 target) := by
  classical
  ext target
  simp only [compileTypeMenuLinksFuel, menuDependencyTargets, Finset.mem_image,
    Finset.mem_filter, Finset.mem_union, Prod.exists, Prod.mk.injEq,
    TypeAutomatonState.survivor.injEq]
  aesop

/-- A retained sequence-left state reads its redirected dependencies and,
when its canonical residual may complete, the right entry. -/
theorem menuDependencyTargets_seq_left
    (fuel : Nat) (alphabet : PactTypeAlphabet) (left right : PactType)
    (source : TypeAutomatonState)
    (hRetained : source ∉ sequenceDeleted (compileTypeFuel fuel left)) :
    menuDependencyTargets
        (compileTypeMenuLinksFuel (fuel + 1) (.seq alphabet left right)) (.child 0 source) =
      (menuDependencyTargets (compileTypeMenuLinksFuel fuel left) source).image
        (sequenceRedirect (compileTypeFuel fuel left) (compileTypeFuel fuel right)) ∪
      if ∃ residual, (residual, source) ∈ buildRelationSetCoreFuel fuel left ∧
          typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true then
        {TypeAutomatonState.child 1 (compileTypeFuel fuel right).initial}
      else ∅ := by
  classical
  rw [compileTypeMenuLinksFuel]
  simp only [menuDependencyTargets_union, menuDependencyTargets_child,
    show (1 : Nat) ≠ 0 by omega, ↓reduceIte, Finset.union_empty]
  ext target
  simp only [menuDependencyTargets, Finset.mem_image, Finset.mem_filter,
    Finset.mem_union, Prod.exists, Prod.mk.injEq]
  split_ifs with hComplete
  · obtain ⟨residual, hRelated, hComplete⟩ := hComplete
    simp only [Finset.mem_singleton]
    aesop
  · simp only [Finset.notMem_empty, or_false]
    aesop

/-- Accepting states acquire no optimistic dependencies. -/
theorem compileTypeMenuLinksFuel_accepting :
    ∀ fuel ty source, source ∈ (compileTypeFuel fuel ty).accepting →
      menuDependencyTargets (compileTypeMenuLinksFuel fuel ty) source = ∅ := by
  intro fuel
  induction fuel with
  | zero => intro ty source _; simp [compileTypeMenuLinksFuel]
  | succ fuel ih =>
      intro ty source hAccepting
      cases ty with
      | message | progress | tock | skip | var =>
          simp [compileTypeMenuLinksFuel]
      | choice alphabet left right =>
          simp only [compileTypeFuel, buildChoiceAutomaton, finishAutomatonFragment,
            Finset.mem_union] at hAccepting
          rw [compileTypeMenuLinksFuel, menuDependencyTargets_union]
          rcases hAccepting with hLeft | hRight
          · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hLeft
            simp only [childState, menuDependencyTargets_child]
            rw [ih left q hq]
            simp
          · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hRight
            simp only [childState, menuDependencyTargets_child]
            rw [ih right q hq]
            simp
      | fairChoice alphabet bid left right =>
          simp only [compileTypeFuel, buildChoiceAutomaton, finishAutomatonFragment,
            Finset.mem_union] at hAccepting
          rw [compileTypeMenuLinksFuel, menuDependencyTargets_union]
          rcases hAccepting with hLeft | hRight
          · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hLeft
            simp only [childState, menuDependencyTargets_child]
            rw [ih left q hq]
            simp
          · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hRight
            simp only [childState, menuDependencyTargets_child]
            rw [ih right q hq]
            simp
      | recur alphabet name body =>
          simp only [compileTypeFuel, buildRecursionAutomaton, finishAutomatonFragment]
            at hAccepting
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hAccepting
          simp only [compileTypeMenuLinksFuel, childState, menuDependencyTargets_child]
          simp only [↓reduceIte]
          rw [ih body q hq]
          simp
      | seq alphabet left right =>
          simp only [compileTypeFuel, buildSequenceAutomaton, finishAutomatonFragment]
            at hAccepting
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hAccepting
          have hRight := ih right q hq
          simp only [compileTypeMenuLinksFuel, menuDependencyTargets_union, childState]
          have hCopied : menuDependencyTargets
              ((compileTypeMenuLinksFuel fuel right).image fun link =>
                (TypeAutomatonState.child 1 link.1, TypeAutomatonState.child 1 link.2))
              (.child 1 q) = ∅ := by
            rw [menuDependencyTargets_child]
            simp [hRight]
          rw [hCopied]
          simp [menuDependencyTargets, childState]
          aesop
      | par alphabet left right interface =>
          simp only [compileTypeFuel, buildParallelAutomaton, finishAutomatonFragment,
            Finset.mem_singleton] at hAccepting
          subst source
          exact compileTypeMenuLinksFuel_final _ _
      | xoffer alphabet other branches =>
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hAccepting
          rw [compileTypeMenuLinksFuel]
          rcases hAccepting with hElse | hBranch
          · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hElse
            simp only [childState]
            rw [menuDependencyTargets_indexed_zero branches
              (fun item => compileTypeMenuLinksFuel fuel item.2), menuDependencyTargets_child]
            simp only [↓reduceIte, childState]
            rw [ih other q hq]
            simp
          · rw [indexedFragmentAccepting, mem_foldl_union_iff] at hBranch
            rcases hBranch with hEmpty | ⟨entry, hEntry, hq⟩
            · simp at hEmpty
            · rw [List.zipIdx_map] at hEntry
              obtain ⟨item, hItem, rfl⟩ := List.mem_map.mp hEntry
              obtain ⟨q, hqAccept, rfl⟩ := Finset.mem_image.mp hq
              have hGet := List.mem_zipIdx_iff_getElem?.mp hItem
              simp only [childState, Prod.map, id] at hqAccept ⊢
              rw [menuDependencyTargets_indexed branches
                (fun item => compileTypeMenuLinksFuel fuel item.2)
                _ item.2 item.1 hGet q, menuDependencyTargets_child]
              rw [if_neg (show (0 : Nat) ≠ item.2 + 1 by omega),
                ih _ q hqAccept]
              simp
      | offer alphabet other branches =>
          simp only [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hAccepting
          rw [compileTypeMenuLinksFuel]
          rcases hAccepting with hElse | hBranch
          · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hElse
            simp only [childState]
            rw [menuDependencyTargets_indexed_zero branches
              (fun item => compileTypeMenuLinksFuel fuel
                (parallelTypeBranchesSelecting alphabet item branches)), menuDependencyTargets_child]
            simp only [↓reduceIte, childState]
            rw [ih other q hq]
            simp
          · rw [indexedFragmentAccepting, mem_foldl_union_iff] at hBranch
            rcases hBranch with hEmpty | ⟨entry, hEntry, hq⟩
            · simp at hEmpty
            · rw [List.zipIdx_map] at hEntry
              obtain ⟨item, hItem, rfl⟩ := List.mem_map.mp hEntry
              obtain ⟨q, hqAccept, rfl⟩ := Finset.mem_image.mp hq
              have hGet := List.mem_zipIdx_iff_getElem?.mp hItem
              simp only [childState, Prod.map, id] at hqAccept ⊢
              rw [menuDependencyTargets_indexed branches
                (fun item => compileTypeMenuLinksFuel fuel (parallelTypeBranchesSelecting alphabet item branches))
                _ item.2 item.1 hGet q, menuDependencyTargets_child]
              rw [if_neg (show (0 : Nat) ≠ item.2 + 1 by omega),
                ih _ q hqAccept]
              simp

end

end Pact
