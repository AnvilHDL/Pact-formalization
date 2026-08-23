import Anvilpp.PactTypes.NewCorrespondence.TypeAutoRelCore

namespace Pact

open Classical

namespace NewCorrespondence

noncomputable section

/-- Proves that any exported edge of `compileType` uses a symbol from the signature alphabet. -/
lemma compileType_hasEdge_symbol_mem
    (signature : TypeAlphabet) (processType : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileType signature processType).HasEdge source env label offers
      target) :
    TypeAutomatonSymbol.mk env label offers ∈ signature.transitionAlphabet := by
  classical
  simp [TypeAutomaton.HasEdge, compileType] at hEdge
  rcases hEdge with ⟨edge, _hEdge, hMem⟩
  cases hLabel : edge.label with
  | visible actual =>
      by_cases hSymbol :
          TypeAutomatonSymbol.mk edge.environment actual
            (TypeOfferSummary.mk edge.current edge.future) ∈
              signature.transitionAlphabet
      · simp [hLabel, hSymbol] at hMem
        rcases hMem with ⟨rfl, ⟨rfl, rfl, rfl⟩, rfl⟩
        exact hSymbol
      · simp [hLabel, hSymbol] at hMem
  | «variable» _ =>
      simp [hLabel] at hMem

/-- Proves that a transition-alphabet symbol has an environment allowed by the signature. -/
lemma transitionAlphabet_environment_mem
    (signature : TypeAlphabet)
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    env ∈ signature.environments := by
  classical
  unfold TypeAlphabet.transitionAlphabet at hSymbol
  rw [Finset.mem_biUnion] at hSymbol
  rcases hSymbol with ⟨env0, hEnv0, hRest⟩
  rw [Finset.mem_biUnion] at hRest
  rcases hRest with ⟨_label0, _hLabel0, hImage⟩
  rw [Finset.mem_image] at hImage
  rcases hImage with ⟨_offers0, _hOffers0, hEq⟩
  injection hEq with hEnvEq _ _
  simpa [hEnvEq] using hEnv0

/-- Proves that compiled `skip` has the non-clock silent self-loop edge. -/
lemma compileType_skip_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hLocal : env ∈ signature.localEnvironments)
    (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .skip).HasEdge .root env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) .root := by
  classical
  rw [compileType_hasEdge_iff_hasResolvedEdge signature .skip
    .root .root env TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) hSymbol]
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := .explicit ∅
      target := .root }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    hLocal, hClock]

/-- Proves that every compiled `skip` edge is the non-clock silent root self-loop. -/
lemma compileType_skip_edge_cases
    (signature : TypeAlphabet)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType signature .skip).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    source = .root ∧ target = .root ∧ label = TypeLabel.silent ∧
      current = ∅ ∧ future = ∅ ∧ env.clock = false := by
  classical
  have hSymbol := compileType_hasEdge_symbol_mem signature .skip hEdge
  have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
    .skip source target env label (TypeOfferSummary.mk current future)
    hSymbol).mp hEdge
  rcases hResolved with ⟨edge, hPending, hSource, hEnv, hLabel,
    hCurrent, hFuture, hTarget⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_image, Finset.mem_filter] at hPending
  rcases hPending with ⟨edgeEnv, ⟨_hLocal, hClock⟩, hEdgeEq⟩
  rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
  simp only at hSource hEnv hLabel hCurrent hFuture hTarget
  subst source
  subst env
  injection hLabel with hLabelVisible
  subst label
  subst current
  subst future
  subst target
  exact ⟨rfl, rfl, rfl, rfl, rfl, hClock⟩

/-- Proves that compiled message has the firing edge when the action is needed now. -/
lemma compileType_message_action_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hLocal : env ∈ signature.localEnvironments)
    (hNeed : env.hasNeed (msg, dir))
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.message msg dir)
      (TypeOfferSummary.mk {(msg, dir)} ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.message msg dir)).HasEdge .root env
      (TypeLabel.message msg dir) (TypeOfferSummary.mk {(msg, dir)} ∅)
      .final := by

  sorry -- Fixed the construct need to fix the below proof
  -- classical
  -- rw [compileType_hasEdge_iff_hasResolvedEdge signature (.message msg dir)
  --   .root .final env (TypeLabel.message msg dir)
  --   (TypeOfferSummary.mk {(msg, dir)} ∅) hSymbol]
  -- refine ⟨
  --   { source := .root
  --     environment := env
  --     label := .visible (TypeLabel.message msg dir)
  --     current := {(msg, dir)}
  --     future := .explicit ∅
  --     target := .final }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
  -- simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
  --   hLocal, hNeed]

/-- Proves that compiled message has the waiting edge in a non-clock no-need environment. -/
lemma compileType_message_wait_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hLocal : env ∈ signature.localEnvironments)
    (hNoNeed : ¬ env.hasNeed (msg, dir))
    (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk {(msg, dir)} ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.message msg dir)).HasEdge .root env
      TypeLabel.silent (TypeOfferSummary.mk {(msg, dir)} ∅) .root := by
  sorry -- Fixed the construct need to fix the below proof
  -- classical
  -- rw [compileType_hasEdge_iff_hasResolvedEdge signature (.message msg dir)
  --   .root .root env TypeLabel.silent
  --   (TypeOfferSummary.mk {(msg, dir)} ∅) hSymbol]
  -- refine ⟨
  --   { source := .root
  --     environment := env
  --     label := .visible TypeLabel.silent
  --     current := {(msg, dir)}
  --     future := .explicit ∅
  --     target := .root }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
  -- simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
  --   hLocal, hClock, hNoNeed]

/-- Proves that compiled message has the final-state non-clock idle edge. -/
lemma compileType_message_final_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hLocal : env ∈ signature.localEnvironments)
    (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.message msg dir)).HasEdge .final env
      TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) .final := by
  classical
  rw [compileType_hasEdge_iff_hasResolvedEdge signature (.message msg dir)
    .final .final env TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) hSymbol]
  refine ⟨
    { source := .final
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := .explicit ∅
      target := .final }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    hLocal, hClock]

/-- Proves that every compiled message edge is fire, wait, or final idle. -/
lemma compileType_message_edge_cases
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType signature (.message msg dir)).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧
        label = TypeLabel.message msg dir ∧ current = {(msg, dir)} ∧
        future = ∅ ∧ env.hasNeed (msg, dir)) ∨
      (source = .root ∧ target = .root ∧ label = TypeLabel.silent ∧
        current = {(msg, dir)} ∧ future = ∅ ∧ env.clock = false ∧
        ¬ env.hasNeed (msg, dir)) ∨
      (source = .final ∧ target = .final ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false) := by

  sorry -- Fixed the automaton construction now need to fix the below proof
  -- classical
  -- have hSymbol := compileType_hasEdge_symbol_mem signature (.message msg dir)
  --   hEdge
  -- have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
  --   (.message msg dir) source target env label
  --   (TypeOfferSummary.mk current future) hSymbol).mp hEdge
  -- rcases hResolved with ⟨edge, hPending, hSource, hEnv, hLabel,
  --   hCurrent, hFuture, hTarget⟩
  -- simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
  --   Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hPending
  -- rcases hPending with (hFiring | hWaiting) | hFinal
  -- · rcases hFiring with ⟨edgeEnv, ⟨_hLocal, hNeed⟩, hEdgeEq⟩
  --   rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
  --   simp only at hSource hEnv hLabel hCurrent hFuture hTarget
  --   subst source; subst env
  --   injection hLabel with hLabelVisible
  --   subst label; subst current; subst future; subst target
  --   exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl, hNeed⟩
  -- · rcases hWaiting with ⟨edgeEnv, ⟨_hLocal, hClock, hNoNeed⟩, hEdgeEq⟩
  --   rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
  --   simp only at hSource hEnv hLabel hCurrent hFuture hTarget
  --   subst source; subst env
  --   injection hLabel with hLabelVisible
  --   subst label; subst current; subst future; subst target
  --   exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, hClock, hNoNeed⟩)
  -- · rcases hFinal with ⟨edgeEnv, ⟨_hLocal, hClock⟩, hEdgeEq⟩
  --   rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
  --   simp only at hSource hEnv hLabel hCurrent hFuture hTarget
  --   subst source; subst env
  --   injection hLabel with hLabelVisible
  --   subst label; subst current; subst future; subst target
  --   exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, hClock⟩)

/-- Proves that compiled `#` has the clock edge in a clock environment. -/
lemma compileType_tock_action_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hLocal : env ∈ signature.localEnvironments)
    (hClock : env.clock = true)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.tock
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .tock).HasEdge .root env TypeLabel.tock
      (TypeOfferSummary.mk ∅ ∅) .final := by
  classical
  rw [compileType_hasEdge_iff_hasResolvedEdge signature .tock
    .root .final env TypeLabel.tock (TypeOfferSummary.mk ∅ ∅) hSymbol]
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.tock
      current := ∅
      future := .explicit ∅
      target := .final }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image]
  left
  exact ⟨env, hLocal, by simp [hClock]⟩

/-- Proves that compiled `#` has the non-clock waiting edge. -/
lemma compileType_tock_wait_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hLocal : env ∈ signature.localEnvironments)
    (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .tock).HasEdge .root env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) .root := by
  classical
  rw [compileType_hasEdge_iff_hasResolvedEdge signature .tock
    .root .root env TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) hSymbol]
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := .explicit ∅
      target := .root }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image]
  left
  exact ⟨env, hLocal, by simp [hClock]⟩

/-- Proves that compiled `#` has the final-state non-clock idle edge. -/
lemma compileType_tock_final_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hLocal : env ∈ signature.localEnvironments)
    (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .tock).HasEdge .final env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) .final := by
  classical
  rw [compileType_hasEdge_iff_hasResolvedEdge signature .tock
    .final .final env TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) hSymbol]
  refine ⟨
    { source := .final
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := .explicit ∅
      target := .final }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    hLocal, hClock]

/-- Proves that every compiled `#` edge is clock fire, non-clock wait, or final idle. -/
lemma compileType_tock_edge_cases
    (signature : TypeAlphabet)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType signature .tock).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧ label = TypeLabel.tock ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = true) ∨
      (source = .root ∧ target = .root ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false) ∨
      (source = .final ∧ target = .final ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false) := by
  classical
  have hSymbol := compileType_hasEdge_symbol_mem signature .tock hEdge
  have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
    .tock source target env label (TypeOfferSummary.mk current future)
    hSymbol).mp hEdge
  rcases hResolved with ⟨edge, hPending, hSource, hEnv, hLabel,
    hCurrent, hFuture, hTarget⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hPending
  rcases hPending with hAction | hFinal
  · rcases hAction with ⟨edgeEnv, _hLocal, hEdgeEq⟩
    by_cases hClock : edgeEnv.clock = true
    · rw [if_pos hClock] at hEdgeEq
      rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
      simp only at hSource hEnv hLabel hCurrent hFuture hTarget
      subst source; subst env
      injection hLabel with hLabelVisible
      subst label; subst current; subst future; subst target
      exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl, hClock⟩
    · rw [if_neg hClock] at hEdgeEq
      rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
      simp only at hSource hEnv hLabel hCurrent hFuture hTarget
      subst source; subst env
      injection hLabel with hLabelVisible
      subst label; subst current; subst future; subst target
      exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl,
        by simpa using hClock⟩)
  · rcases hFinal with ⟨edgeEnv, ⟨_hLocal, hClock⟩, hEdgeEq⟩
    rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
    simp only at hSource hEnv hLabel hCurrent hFuture hTarget
    subst source; subst env
    injection hLabel with hLabelVisible
    subst label; subst current; subst future; subst target
    exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, hClock⟩)

/-- Proves that compiled progress has the root-to-final progress edge. -/
lemma compileType_progress_action_edge
    (signature : TypeAlphabet) (pid : ProcId) {env : TypeEnvironment}
    (hLocal : env ∈ signature.localEnvironments)
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.progress pid)
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.progress pid)).HasEdge .root env
      (TypeLabel.progress pid) (TypeOfferSummary.mk ∅ ∅) .final := by
  classical
  sorry -- Fixed the construct need to fix the below proof
  -- rw [compileType_hasEdge_iff_hasResolvedEdge signature (.progress pid)
  --   .root .final env (TypeLabel.progress pid) (TypeOfferSummary.mk ∅ ∅)
  --   hSymbol]
  -- refine ⟨
  --   { source := .root
  --     environment := env
  --     label := .visible (TypeLabel.progress pid)
  --     current := ∅
  --     future := .explicit ∅
  --     target := .final }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
  -- simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
  --   hLocal]

/-- Proves that compiled progress has the final-state non-clock idle edge. -/
lemma compileType_progress_final_edge
    (signature : TypeAlphabet) (pid : ProcId) {env : TypeEnvironment}
    (hLocal : env ∈ signature.localEnvironments)
    (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.progress pid)).HasEdge .final env
      TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) .final := by
  sorry -- Fixed the construct need to fix the below proof
  -- classical
  -- rw [compileType_hasEdge_iff_hasResolvedEdge signature (.progress pid)
  --   .final .final env TypeLabel.silent (TypeOfferSummary.mk ∅ ∅)
  --   hSymbol]
  -- refine ⟨
  --   { source := .final
  --     environment := env
  --     label := .visible TypeLabel.silent
  --     current := ∅
  --     future := .explicit ∅
  --     target := .final }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
  -- simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
  --   hLocal, hClock]

/-- Proves that every compiled progress edge is progress fire or final idle. -/
lemma compileType_progress_edge_cases
    (signature : TypeAlphabet) (pid : ProcId)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType signature (.progress pid)).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧ label = TypeLabel.progress pid ∧
        current = ∅ ∧ future = ∅) ∨
      (source = .final ∧ target = .final ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false) := by
  sorry -- Fixed the construct need to fix the below proof
  -- classical
  -- have hSymbol := compileType_hasEdge_symbol_mem signature (.progress pid)
  --   hEdge
  -- have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
  --   (.progress pid) source target env label
  --   (TypeOfferSummary.mk current future) hSymbol).mp hEdge
  -- rcases hResolved with ⟨edge, hPending, hSource, hEnv, hLabel,
  --   hCurrent, hFuture, hTarget⟩
  -- simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
  --   Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hPending
  -- rcases hPending with hAction | hFinal
  -- · rcases hAction with ⟨edgeEnv, _hLocal, hEdgeEq⟩
  --   rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
  --   simp only at hSource hEnv hLabel hCurrent hFuture hTarget
  --   subst source; subst env
  --   injection hLabel with hLabelVisible
  --   subst label; subst current; subst future; subst target
  --   exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩
  -- · rcases hFinal with ⟨edgeEnv, ⟨_hLocal, hClock⟩, hEdgeEq⟩
  --   rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
  --   simp only at hSource hEnv hLabel hCurrent hFuture hTarget
  --   subst source; subst env
  --   injection hLabel with hLabelVisible
  --   subst label; subst current; subst future; subst target
  --   exact Or.inr ⟨rfl, rfl, rfl, rfl, rfl, hClock⟩

/-- Proves that any decorated message fire step from `a` targets `skip`. -/
lemma decorated_message_action_target
    {env : TypeEnvironment} {msg : MessageId} {dir : MessageDir}
    {offers : TypeOfferSummary} {target : PactType}
    (hStep : DecoratedTypeTransition env (.message msg dir)
      (TypeLabel.message msg dir) offers target) :
    target = .skip := by
  generalize hLabelEq : TypeLabel.message msg dir = actualLabel at hStep
  cases hStep.1 <;> simp [TypeLabel.message, TypeLabel.silent] at hLabelEq ⊢

/-- Proves that any decorated message wait step from `a` stays at `a`. -/
lemma decorated_message_wait_target
    {env : TypeEnvironment} {msg : MessageId} {dir : MessageDir}
    {offers : TypeOfferSummary} {target : PactType}
    (hStep : DecoratedTypeTransition env (.message msg dir)
      TypeLabel.silent offers target) :
    target = .message msg dir := by
  generalize hLabelEq : TypeLabel.silent = actualLabel at hStep
  cases hStep.1 <;> simp [TypeLabel.message, TypeLabel.silent] at hLabelEq ⊢

/-- Proves that any decorated step from `skip` targets `skip`. -/
lemma decorated_skip_target
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    {target : PactType}
    (hStep : DecoratedTypeTransition env .skip label offers target) :
    target = .skip := by
  generalize hLabelEq : label = actualLabel at hStep
  cases hStep.1
  simp_all

/-- Proves that any decorated clock step from `#` targets `skip`. -/
lemma decorated_tock_action_target
    {env : TypeEnvironment} {offers : TypeOfferSummary} {target : PactType}
    (hStep : DecoratedTypeTransition env .tock TypeLabel.tock offers target) :
    target = .skip := by
  generalize hLabelEq : TypeLabel.tock = actualLabel at hStep
  cases hStep.1 <;> simp [TypeLabel.silent] at hLabelEq ⊢

/-- Proves that any decorated non-clock wait step from `#` stays at `#`. -/
lemma decorated_tock_wait_target
    {env : TypeEnvironment} {offers : TypeOfferSummary} {target : PactType}
    (hStep : DecoratedTypeTransition env .tock TypeLabel.silent offers target) :
    target = .tock := by
  generalize hLabelEq : TypeLabel.silent = actualLabel at hStep
  cases hStep.1 <;> simp [TypeLabel.silent] at hLabelEq ⊢

/-- Proves that any decorated progress step from `$t` targets `skip`. -/
lemma decorated_progress_target
    {env : TypeEnvironment} {pid : ProcId} {offers : TypeOfferSummary}
    {target : PactType}
    (hStep : DecoratedTypeTransition env (.progress pid)
      (TypeLabel.progress pid) offers target) :
    target = .skip := by
  generalize hLabelEq : TypeLabel.progress pid = actualLabel at hStep
  cases hStep.1
  all_goals simp [TypeLabel.progress] at hLabelEq ⊢

/-- Defines the `skip` relation shape as exactly `(skip, root)`. -/
def skipRelationShape (entry : PactType × TypeAutomatonState) :
    Prop :=
  entry.1 = .skip ∧ entry.2 = .root

/-- Proves that any generated `skip` relation member has the `skip` relation
shape. Provenance-directed relation (Task 4): `buildRelationSetCoreFuel`'s
`.skip` case is the literal singleton `{(.skip, .root)}`, so this is now a
direct `Finset` unfold, no worklist-closure induction needed. -/
lemma relationMembership_skip_cases
    (signature : TypeAlphabet)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet .skip (compileType signature .skip))
        residual state) :
    residual = .skip ∧ state = .root := by
  unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
  simp only [typeCompilationFuel, buildRelationSetCoreFuel, Finset.mem_singleton,
    Prod.mk.injEq] at hRelated
  exact hRelated

/-- Defines the message relation shape as `(a, root)` or `(skip, final)`. -/
def messageRelationShape
    (msg : MessageId) (dir : MessageDir)
    (entry : PactType × TypeAutomatonState) : Prop :=
  (entry.1 = .message msg dir ∧ entry.2 = .root) ∨
    (entry.1 = .skip ∧ entry.2 = .final)

/-- Proves that any generated message relation member is one of the two PDF
pairs. See `relationMembership_skip_cases`'s doc comment for the
Task-4-enabled proof shape. -/
lemma relationMembership_message_cases
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.message msg dir)
          (compileType signature (.message msg dir)))
        residual state) :
    (residual = .message msg dir ∧ state = .root) ∨
      (residual = .skip ∧ state = .final) := by
  unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
  simp only [typeCompilationFuel, buildRelationSetCoreFuel, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq] at hRelated
  exact hRelated

/-- Defines the `#` relation shape as `(#, root)` or `(skip, final)`. -/
def tockRelationShape
    (entry : PactType × TypeAutomatonState) : Prop :=
  (entry.1 = .tock ∧ entry.2 = .root) ∨
    (entry.1 = .skip ∧ entry.2 = .final)

/-- Proves that any generated `#` relation member is one of the two PDF
pairs. See `relationMembership_skip_cases`'s doc comment for the
Task-4-enabled proof shape. -/
lemma relationMembership_tock_cases
    (signature : TypeAlphabet)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet .tock (compileType signature .tock))
        residual state) :
    (residual = .tock ∧ state = .root) ∨
      (residual = .skip ∧ state = .final) := by
  unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
  simp only [typeCompilationFuel, buildRelationSetCoreFuel, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq] at hRelated
  exact hRelated

/-- Defines the progress relation shape as `($t, root)` or `(skip, final)`. -/
def progressRelationShape
    (pid : ProcId) (entry : PactType × TypeAutomatonState) : Prop :=
  (entry.1 = .progress pid ∧ entry.2 = .root) ∨
    (entry.1 = .skip ∧ entry.2 = .final)

/-- Proves that any generated progress relation member is one of the two PDF
pairs. See `relationMembership_skip_cases`'s doc comment for the
Task-4-enabled proof shape. -/
lemma relationMembership_progress_cases
    (signature : TypeAlphabet) (pid : ProcId)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.progress pid)
          (compileType signature (.progress pid)))
        residual state) :
    (residual = .progress pid ∧ state = .root) ∨
      (residual = .skip ∧ state = .final) := by
  unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
  simp only [typeCompilationFuel, buildRelationSetCoreFuel, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq] at hRelated
  exact hRelated

end
end NewCorrespondence
end Pact
