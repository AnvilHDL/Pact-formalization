import Anvilpp.PactTypes.Spec.Automata.MenuDependencies

namespace Pact

noncomputable section

@[simp] theorem menuDependencyTargets_union
    (first second : Finset (TypeAutomatonState × TypeAutomatonState))
    (source : TypeAutomatonState) :
    menuDependencyTargets (first ∪ second) source =
      menuDependencyTargets first source ∪ menuDependencyTargets second source := by
  classical
  ext target
  simp only [menuDependencyTargets, Finset.mem_image, Finset.mem_filter, Finset.mem_union]
  aesop

@[simp] theorem menuDependencyTargets_empty (source : TypeAutomatonState) :
    menuDependencyTargets ∅ source = ∅ := by
  simp [menuDependencyTargets]

@[simp] theorem menuDependencyTargets_singleton
    (origin target source : TypeAutomatonState) :
    menuDependencyTargets {(origin, target)} source =
      if origin = source then {target} else ∅ := by
  classical
  by_cases h : origin = source <;> ext state <;> simp [menuDependencyTargets, h, eq_comm]

theorem menuDependencyTargets_child
    (dependencies : Finset (TypeAutomatonState × TypeAutomatonState))
    (index tag : Nat) (source : TypeAutomatonState) :
    menuDependencyTargets (dependencies.image fun link =>
        (TypeAutomatonState.child index link.1, TypeAutomatonState.child index link.2))
        (.child tag source) =
      if index = tag then (menuDependencyTargets dependencies source).image (.child index)
      else ∅ := by
  classical
  by_cases hIndex : index = tag
  · subst tag
    simp only [↓reduceIte]
    ext target
    simp only [menuDependencyTargets, Finset.mem_image, Finset.mem_filter,
      Prod.exists, Prod.mk.injEq, TypeAutomatonState.child.injEq]
    aesop
  · ext target
    simp only [if_neg hIndex, menuDependencyTargets, Finset.mem_image,
      Finset.mem_filter, Prod.exists, Prod.mk.injEq, TypeAutomatonState.child.injEq,
      Finset.notMem_empty, iff_false]
    aesop

@[simp] theorem menuDependencyTargets_child_root
    (dependencies : Finset (TypeAutomatonState × TypeAutomatonState)) (index : Nat) :
    menuDependencyTargets (dependencies.image fun link =>
      (TypeAutomatonState.child index link.1, TypeAutomatonState.child index link.2)) .root = ∅ := by
  classical
  ext target
  simp [menuDependencyTargets]


namespace PendingAutomaton

theorem referencedStates_withMenuDependencies (automaton : PendingAutomaton)
    (dependencies : Finset (TypeAutomatonState × TypeAutomatonState))
    (source : TypeAutomatonState) :
    (automaton.withMenuDependencies dependencies).referencedStates source =
      automaton.menuStep source ∪
        (dependencies.filter fun link => link.1 = source).image Prod.snd := rfl

/-- With no dependencies, saturation follows only non-clock execution edges. -/
@[simp] theorem withMenuDependencies_empty (automaton : PendingAutomaton)
    (source : TypeAutomatonState) :
    (automaton.withMenuDependencies ∅).futureReachable source =
      automaton.futureReachable source := by
  classical
  have hGraph : automaton.withMenuDependencies ∅ =
      { states := automaton.states, referencedStates := automaton.menuStep } := by
    simp [withMenuDependencies]
  rw [hGraph]
  have hAux : ∀ fuel reached,
      (⟨automaton.states, automaton.menuStep⟩ : FiniteMenuGraph).futureReachableAux fuel reached =
        automaton.futureReachableAux fuel reached := by
    intro fuel
    induction fuel with
    | zero => intro reached; rfl
    | succ fuel ih =>
        intro reached
        simp only [FiniteMenuGraph.futureReachableAux, futureReachableAux,
          FiniteMenuGraph.futureStep, futureStep]
        exact ih _
  exact hAux _ _

theorem referencesClosed_withMenuDependencies (automaton : PendingAutomaton)
    (dependencies : Finset (TypeAutomatonState × TypeAutomatonState))
    (hClosed : automaton.MenuClosed)
    (hTargets : ∀ dependency ∈ dependencies, dependency.2 ∈ automaton.states) :
    (automaton.withMenuDependencies dependencies).ReferencesClosed := by
  classical
  intro source hSource target hTarget
  rw [referencedStates_withMenuDependencies] at hTarget
  rcases Finset.mem_union.mp hTarget with hOld | hNew
  · exact hClosed source hSource hOld
  · obtain ⟨dependency, hDependency, rfl⟩ := Finset.mem_image.mp hNew
    exact hTargets dependency (Finset.mem_filter.mp hDependency).1

/-- Adding menu dependencies retains every non-clock execution path. -/
theorem futureReachable_subset_withMenuDependencies (automaton : PendingAutomaton)
    (dependencies : Finset (TypeAutomatonState × TypeAutomatonState))
    (hClosed : (automaton.withMenuDependencies dependencies).ReferencesClosed)
    (source : TypeAutomatonState) (hSource : source ∈ automaton.states) :
    automaton.futureReachable source ⊆
      (automaton.withMenuDependencies dependencies).futureReachable source := by
  let graph := automaton.withMenuDependencies dependencies
  have hCarrier := graph.futureReachable_subset_of_reference_closed source
    graph.states hSource hClosed
  apply automaton.futureReachable_subset_of_menu_closed
  · exact graph.mem_futureReachable_self source
  · intro q hq r hr
    exact graph.futureReachable_subset_of_mem hClosed hSource hq
      (graph.referencedStates_subset_futureReachable q hClosed (hCarrier hq)
        (Finset.mem_union_left _ hr))


end PendingAutomaton

end

end Pact
