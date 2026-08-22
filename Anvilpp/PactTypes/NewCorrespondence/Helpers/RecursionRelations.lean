import Anvilpp.PactTypes.NewCorrespondence.Helpers.Parallel

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

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
  have hFuelEq : typeCompilationFuel (.recur name body) = typeCompilationFuel body + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.recur name body))
        (.recur name body) =
        buildRecursionAutomaton signature name
          (compileTypeFuel signature (typeCompilationFuel body) body) := by
    rw [hFuelEq]
    show buildRecursionAutomaton signature name
        (compileTypeFuel signature (typeCompilationFuel body) body) =
      buildRecursionAutomaton signature name
        (compileTypeFuel signature (typeCompilationFuel body) body)
    rfl
  have hInit : (compileType signature (.recur name body)).initial =
      TypeAutomatonState.root := by
    show (compileTypeFuel signature (typeCompilationFuel (.recur name body))
      (.recur name body)).initial = TypeAutomatonState.root
    rw [hWhole]
    simp [buildRecursionAutomaton, finishAutomatonFragment]
  refine buildRelationSet_preserves (.recur name body)
    (compileType signature (.recur name body))
    (recurRelationShape signature name body)
    (by
      show recurRelationShape signature name body
        (.recur name body, (compileType signature (.recur name body)).initial)
      rw [hInit]; exact Or.inl rfl)
    (by
      intro entry hEntry successor hSuccessor
      rcases relationSuccessors_mem_cases (compileType signature (.recur name body))
        entry successor hSuccessor with ⟨edge, hEdgeMem, hSource, hTarget, hStep⟩
      have hSymbolMem := compileType_hasEdge_symbol_mem signature (.recur name body)
        (show (compileType signature (.recur name body)).HasEdge edge.source
          edge.symbol.environment edge.symbol.label edge.symbol.offers edge.target
          from hEdgeMem)
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.recur name body) edge.source edge.target edge.symbol.environment
        edge.symbol.label edge.symbol.offers hSymbolMem).mp hEdgeMem
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      rcases hEntry with hRoot | ⟨q, bodyResidual, hEntryEq, hMem⟩
      · -- root case: entry represents `μX.body` itself
        have hRootSource : pendingEdge.source = TypeAutomatonState.root := by
          rw [hPSource, hSource, hRoot]
        simp only [buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
          Finset.mem_image] at hPendingMem
        rcases hPendingMem with ⟨environment, _, hEq⟩ | ⟨bodyEdge, _, hEq⟩
        · subst hEq
          simp only [childState] at hPTarget
          have hEntry1 : entry.1 = .recur name body := by rw [hRoot]
          rw [hEntry1] at hStep
          obtain ⟨hTrans, -⟩ := hStep
          generalize hTargetEq : successor.1 = actualTarget at hTrans
          generalize hLabelEq2 : edge.symbol.label = actualLabel at hTrans
          cases hTrans
          have hTargetEq2 : successor.2 = .child 0
              (compileTypeFuel signature (typeCompilationFuel body) body).initial := by
            rw [hTarget, ← hPTarget]
          refine Or.inr ⟨(compileTypeFuel signature (typeCompilationFuel body)
            body).initial, body, ?_,
            buildRelationSet_initial body (compileType signature body)⟩
          rw [← hTargetEq, ← hTargetEq2]
        · exfalso
          rw [← hEq] at hRootSource
          split at hRootSource <;> simp [childState] at hRootSource
      · -- child case: entry is already related to `q` inside `body`'s own relation
        have hEntry2 : entry.2 = .child 0 q := by rw [hEntryEq]
        have hChildSource : pendingEdge.source = .child 0 q := by
          rw [hPSource, hSource, hEntry2]
        simp only [buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
          Finset.mem_image] at hPendingMem
        rcases hPendingMem with ⟨environment, _, hEq⟩ | ⟨bodyEdge, hBodyEdgeMem, hEq⟩
        · exfalso
          rw [← hEq] at hChildSource
          simp at hChildSource
        · have hEntry1 : entry.1 = bodyResidual.replaceVar name (.recur name body) := by
            rw [hEntryEq]
          by_cases hMarker : bodyEdge.label = .variable name
          · -- marker edge: reduces to the same unfolding step as the root
            simp only [hMarker, if_true] at hEq
            subst hEq
            simp only [childState] at hPSource hPTarget
            have hSourceEq : bodyEdge.source = q := by
              simpa [childState] using hChildSource
            have hResidualEq : bodyResidual = .var name :=
              compileTypeFuel_marker_represents_var signature name body hMem
                hBodyEdgeMem hSourceEq hMarker
            rw [hEntry1, hResidualEq] at hStep
            simp only [PactType.replaceVar] at hStep
            obtain ⟨hTrans, -⟩ := hStep
            generalize hTargetEq : successor.1 = actualTarget at hTrans
            generalize hLabelEq2 : edge.symbol.label = actualLabel at hTrans
            cases hTrans
            have hTargetEq2 : successor.2 = .child 0
                (compileTypeFuel signature (typeCompilationFuel body) body).initial := by
              rw [hTarget, ← hPTarget]
            refine Or.inr ⟨(compileTypeFuel signature (typeCompilationFuel body)
              body).initial, body, ?_,
              buildRelationSet_initial body (compileType signature body)⟩
            rw [← hTargetEq, ← hTargetEq2]
          · -- copied non-marker edge: bridges to body's own relation
            simp only [hMarker, if_false] at hEq
            subst hEq
            simp only [childState] at hPSource hPTarget
            have hSourceEq : bodyEdge.source = q := by
              simpa [childState] using hChildSource
            have hInnerEdgeMem : (compileType signature body).HasEdge q
                edge.symbol.environment edge.symbol.label edge.symbol.offers
                bodyEdge.target := by
              rw [compileType_hasEdge_iff_hasResolvedEdge signature body q
                bodyEdge.target edge.symbol.environment edge.symbol.label
                edge.symbol.offers hSymbolMem]
              refine ⟨bodyEdge, hBodyEdgeMem, hSourceEq, ?_, ?_, ?_, ?_, rfl⟩
              · rw [← hPEnv]
              · rw [← hPLabel]
              · rw [← hPCurrent]
              · rw [← hPFuture]
                cases hSpec : bodyEdge.future with
                | explicit offers => simp [childFutureSpec, hSpec]
                | «at» t r =>
                    have hStateMem := compileTypeFuel_futureTargetsInStates signature
                      (typeCompilationFuel body) body le_rfl bodyEdge hBodyEdgeMem t r
                      hSpec
                    simp only [childFutureSpec, hSpec, childState]
                    rw [computeFutureOf_recursion_child signature name body
                      (.recur name body) hWhole (by omega) t hStateMem]
            rw [hEntry1] at hStep
            obtain ⟨bodyResidual', hSuccessorEq, hStep'⟩ :=
              (decoratedTypeTransition_replaceVar_iff name body bodyResidual).mp hStep
            have hTargetEq : successor.2 = .child 0 bodyEdge.target := by
              rw [hTarget, ← hPTarget]
            have hInnerMem :=
              relationMembership_of_step_edge_unique body (compileType signature body)
                hMem hInnerEdgeMem hStep'
                (fun target hTargetStep =>
                  decoratedTypeTransition_target_unique hTargetStep hStep')
            exact Or.inr ⟨bodyEdge.target, bodyResidual', by
              rw [← hSuccessorEq, ← hTargetEq], hInnerMem⟩)
    (residual, state) hRelated


end

end Pact
