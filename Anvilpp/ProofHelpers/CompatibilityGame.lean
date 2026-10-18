import Anvilpp.ProofHelpers.TypeSemantics

namespace Pact

noncomputable section

open Classical

/-! Honesty-aware compatibility games and their Rabin acceptance monitors. -/

/-- A clock reset or the boundary actions still allowed in the current cycle. -/
inductive HonestyMemory : Type where
  | star : HonestyMemory
  | future : Finset BareMessage → HonestyMemory
  deriving DecidableEq

/-- The environment introduces no action outside the remembered availability. -/
def HonestyMemory.Admissible : HonestyMemory → TypeEnvironment → Prop
  | .star, _ => True
  | .future allowed, env => typeAvailable env ⊆ allowed

/-- Clock resets the memory; other steps retain promises and unconsumed immediate offers. -/
def honestyNext (env : TypeEnvironment) (label : TypeLabel) : HonestyMemory :=
  match label with
  | .tock => .star
  | .actions _ => .future (env.honestyRemainder label)

/-- A resolved product edge under a fixed compiled automaton: `q →^α_e q'`. -/
def compiledTypeEdge (automaton : TypeAutomaton) (state : TypeAutomatonState)
    (env : TypeEnvironment) (label : TypeLabel) (state' : TypeAutomatonState) :
    Prop :=
  ∃ offers, automaton.HasEdge state env label offers state'

/-- Environment-choice vertices, transition-resolution vertices, and an absorbing failure sink. -/
inductive CompatibilityVertex : Type where
  | choice (state : TypeAutomatonState) (memory : HonestyMemory) :
      CompatibilityVertex
  | resolve (state : TypeAutomatonState) (memory : HonestyMemory)
      (env : TypeEnvironment) : CompatibilityVertex
  | fail : CompatibilityVertex
  deriving DecidableEq

def CompatibilityVertex.isPlayerZero : CompatibilityVertex → Prop
  | .choice _ _ => True
  | .resolve _ _ _ => False
  | .fail => False

/-- `E_choice ∪ E_resolve ∪ E_fail`. -/
def compatibilityEdge (automaton : TypeAutomaton)
    (alphabet : PactTypeAlphabet) :
    CompatibilityVertex → CompatibilityVertex → Prop
  | .choice state memory, .resolve state' memory' env =>
      state' = state ∧ memory' = memory ∧ env.WellFormed alphabet
  | .resolve state memory env, .choice state' memory' =>
      memory.Admissible env ∧
      ∃ label, compiledTypeEdge automaton state env label state' ∧
        memory' = honestyNext env label
  | .resolve state memory env, .fail =>
      ¬ memory.Admissible env ∨
        ¬ ∃ label state', compiledTypeEdge automaton state env label state'
  | .fail, .fail => True
  | _, _ => False

/-- Resolving and failure edges emit log entries; environment-choice edges emit none. -/
def compatibilityStepEntry (automaton : TypeAutomaton) :
    CompatibilityVertex → CompatibilityVertex →
      Option (TypeEnvironment × TypeLabel) → Prop
  | .choice _ _, _, entry => entry = none
  | .resolve state _ env, .choice state' memory', entry =>
      ∃ label, compiledTypeEdge automaton state env label state' ∧
        memory' = honestyNext env label ∧ entry = some (env, label)
  | .resolve _ _ env, .fail, entry => entry = some (env, TypeLabel.silent)
  | .resolve _ _ _, .resolve _ _ _, entry => entry = none
  | .fail, _, entry => entry = some (TypeEnvironment.empty, TypeLabel.silent)

/-- A two-player game with finitely many Rabin pairs; the vertex type is unrestricted. -/
structure RabinGame : Type 1 where
  Vertex : Type
  initial : Vertex
  isPlayerZero : Vertex → Prop
  edge : Vertex → Vertex → Prop
  rabinPairs : List (Set Vertex × Set Vertex)

/-- Some Rabin pair has infinitely many good visits and finitely many bad visits. -/
def RabinGame.Accepts (game : RabinGame) (play : ℕ → game.Vertex) : Prop :=
  ∃ pair ∈ game.rabinPairs,
    Set.Infinite {n | play n ∈ pair.1} ∧ ¬ Set.Infinite {n | play n ∈ pair.2}

/-- A Player-0 strategy reads the play so far, given as the non-empty list of
vertices visited, and names a successor of its last vertex. -/
abbrev RabinGame.Strategy (game : RabinGame) : Type := List game.Vertex → game.Vertex

/-- A strategy is legal when it names a successor at every Player-0 vertex. -/
def RabinGame.Legal (game : RabinGame) (strategy : game.Strategy) : Prop :=
  ∀ (history : List game.Vertex) (current : game.Vertex),
    history.getLast? = some current → game.isPlayerZero current →
    game.edge current (strategy history)

/-- The play visits edges, and at every Player-0 vertex takes the move the
strategy names for the play so far. -/
def RabinGame.Consistent (game : RabinGame) (strategy : game.Strategy)
    (play : ℕ → game.Vertex) : Prop :=
  ∀ n, game.edge (play n) (play (n + 1)) ∧
    (game.isPlayerZero (play n) →
      play (n + 1) = strategy ((List.range (n + 1)).map play))

/-- `v ∈ WinRegion` when some legal Player-0 strategy wins every play from `v`
consistent with it. -/
def RabinGame.WinRegion (game : RabinGame) : Set game.Vertex :=
  {v | ∃ strategy : game.Strategy, game.Legal strategy ∧
    ∀ play : ℕ → game.Vertex, play 0 = v →
      game.Consistent strategy play → game.Accepts play}

/-- An acceptance-monitor mark: a semantic observation or the clock. -/
inductive TypeMark : Type where
  | clock : TypeMark
  | observation : TypeObservation → TypeMark
  deriving DecidableEq

/-- The marks a label emits. -/
def typeLabelMarks : TypeLabel → Finset TypeMark
  | .tock => {TypeMark.clock}
  | .actions observations => observations.image TypeMark.observation

/-- `D_T = {live} ∪ (cal(Eta)(Θ_0) × {true,false})`. -/
inductive ObjectiveDisjunct (initial : PactType) : Type where
  | live : ObjectiveDisjunct initial
  | fair (bid : BranchId) (outcome : Bool) (mem : bid ∈ typeFairIds initial) :
      ObjectiveDisjunct initial

/-- `D_T` as a finite list. -/
def objectiveDisjuncts (initial : PactType) : List (ObjectiveDisjunct initial) :=
  ObjectiveDisjunct.live ::
    (typeFairIds initial).attach.toList.flatMap fun bid =>
      [ObjectiveDisjunct.fair bid.1 true bid.2,
        ObjectiveDisjunct.fair bid.1 false bid.2]

/-- `Req(d)`: `Req(live) = {#} ∪ {$_t | t ∈ T}` and `Req(η,b) = {#, η_b}`. -/
def ObjectiveDisjunct.req {initial : PactType} (progress : Finset ProcId) :
    ObjectiveDisjunct initial → Finset TypeMark
  | .live =>
      insert TypeMark.clock
        (progress.image fun pid => TypeMark.observation (.progress pid))
  | .fair bid outcome _ =>
      {TypeMark.clock, TypeMark.observation (.fair bid outcome)}

/-- `Forbid(d)`: empty for `live`, the opposite outcome for `(η,b)`. -/
def ObjectiveDisjunct.forbid {initial : PactType} :
    ObjectiveDisjunct initial → Finset TypeMark
  | .live => ∅
  | .fair bid outcome _ => {TypeMark.observation (.fair bid (!outcome))}

/-- Remove observed requests; when none remain, raise the completion flag and reset. -/
def monitorAdvance (req pending marks : Finset TypeMark) :
    Finset TypeMark × Bool :=
  let remaining := pending \ marks
  if remaining = ∅ then (req, true) else (remaining, false)

/-- An arena vertex with each monitor's pending requests, completion flag, and incoming log entry. -/
structure MonitoredVertex (initial : PactType) (progress : Finset ProcId) :
    Type where
  base : CompatibilityVertex
  pending : ObjectiveDisjunct initial → Finset TypeMark
  flag : ObjectiveDisjunct initial → Bool
  entry : Option (TypeEnvironment × TypeLabel)

/-- The marks observed on arrival at a vertex. -/
def MonitoredVertex.marks {initial : PactType} {progress : Finset ProcId}
    (vertex : MonitoredVertex initial progress) : Finset TypeMark :=
  match vertex.entry with
  | some entry => typeLabelMarks entry.2
  | none => ∅

/-- `s_0 = (q_0^(P,star),(c_d^0)_(d ∈ D_T))`. -/
def monitoredInitial (initial : PactType) (progress : Finset ProcId) :
    MonitoredVertex initial progress where
  base := .choice (compileType initial).initial .star
  pending := fun disjunct => ObjectiveDisjunct.req progress disjunct
  flag := fun _ => false
  entry := none

/-- The product updates every monitor on a resolving or failure log entry; the
environment-choice bookkeeping half-edge leaves the counters unchanged. -/
def monitoredEdge (initial : PactType) (progress : Finset ProcId)
    (source target : MonitoredVertex initial progress) : Prop :=
  compatibilityEdge (compileType initial) initial.alphabet source.base
      target.base ∧
    compatibilityStepEntry (compileType initial) source.base target.base
      target.entry ∧
    match target.entry with
    | some entry =>
        ∀ disjunct,
          (target.pending disjunct, target.flag disjunct) =
            monitorAdvance (ObjectiveDisjunct.req progress disjunct)
              (source.pending disjunct) (typeLabelMarks entry.2)
    | none =>
        target.pending = source.pending ∧ target.flag = fun _ => false

/-- Completion and forbidden-observation sets for each Rabin pair; failure raises no completion flag. -/
def objectiveRabinPairs (initial : PactType) (progress : Finset ProcId) :
    List (Set (MonitoredVertex initial progress) ×
      Set (MonitoredVertex initial progress)) :=
  (objectiveDisjuncts initial).map fun disjunct =>
    ({vertex | vertex.flag disjunct = true},
      {vertex | (vertex.marks ∩ ObjectiveDisjunct.forbid disjunct).Nonempty})

/-- The honesty-aware compatibility game `hat(G)_{I,T}` for a fixed compiled
automaton, monitored by `∏_(d ∈ D_T) M_d`. -/
def compatibilityGame (initial : PactType)
    (progress : Finset ProcId) : RabinGame where
  Vertex := MonitoredVertex initial progress
  initial := monitoredInitial initial progress
  isPlayerZero := fun vertex => vertex.base.isPlayerZero
  edge := monitoredEdge initial progress
  rabinPairs := objectiveRabinPairs initial progress

/-- The initial monitored position is winning for the given composition and progress set. -/
def TypeCompatible  (initial : PactType)
    (progress : Finset ProcId) : Prop :=
  let game := compatibilityGame initial progress
  game.initial ∈ game.WinRegion

end

end Pact
