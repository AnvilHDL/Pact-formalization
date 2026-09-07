import Anvilpp.ProofHelpers.TypeSemantics

namespace Pact

noncomputable section

open Classical

/-! ## The honesty-aware compatibility game

A concrete rendering of the arena: the honesty memory `H_I`, the two-player
vertex sets `V_0`/`V_1` with an absorbing failure sink, and the
environment-choice/resolve/fail edges.  The Rabin winning condition is stated
directly against the infinite play's label/environment sequence. -/

/-- `H_I = {star} ∪ {E_F | (E_C,E_F) ∈ cal(Env)_I}`. -/
inductive HonestyMemory : Type where
  | star : HonestyMemory
  | future : Finset BareMessage → HonestyMemory
  deriving DecidableEq

/-- `Adm(F,e)`. -/
def HonestyMemory.Admissible : HonestyMemory → TypeEnvironment → Prop
  | .star, _ => True
  | .future allowed, env => typeAvailable env ⊆ allowed

/-- `Next(e,α)`. -/
def honestyNext (env : TypeEnvironment) (label : TypeLabel) : HonestyMemory :=
  match label with
  | .tock => .star
  | .actions _ => .future env.future

/-- A resolved product edge under a fixed compiled automaton: `q →^α_e q'`. -/
def compiledTypeEdge (automaton : TypeAutomaton) (state : TypeAutomatonState)
    (env : TypeEnvironment) (label : TypeLabel) (state' : TypeAutomatonState) :
    Prop :=
  ∃ offers, automaton.HasEdge state env label offers state'

/-- Vertices of the honesty-aware arena, `V_0 ∪ V_1 ∪ {⊥}`: a Player-0
"about to choose an environment" position, a Player-1 "about to resolve"
position carrying the chosen environment, or the absorbing failure sink. -/
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

/-- The log entry fired by a step of the arena.  A bookkeeping `θ_e`
half-edge fires nothing; a resolving edge fires its own label `⟨e,α⟩`, the same
`α` that drives the memory update; the failure edges fire `⟨e,ε⟩` and
`⟨(∅,∅),ε⟩`. -/
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

/-- A finite Rabin game: the accepting condition is stated abstractly as
`List (Set Vertex × Set Vertex)` rather than requiring a `Fintype` instance
for `Vertex`, since establishing finiteness of the compiled arena is exactly
the content of Theorem 4.4 and is not needed to *state* the game. -/
structure RabinGame : Type 1 where
  Vertex : Type
  initial : Vertex
  isPlayerZero : Vertex → Prop
  edge : Vertex → Vertex → Prop
  rabinPairs : List (Set Vertex × Set Vertex)

/-- `(G,B)` accepts `π` iff `Inf(π) ∩ G ≠ ∅` and `Inf(π) ∩ B = ∅`; a Rabin
condition accepts when *some* pair does, matching `R_T = {(F_d,B_d) | d ∈ D_T}`
over the disjuncts `D_T`.  Recurrence of the visited-vertex sequence agrees
with the set-intersection reading on a finite graph. -/
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

/-- An observation of a completed round, or the clock.  `Req(d)` mentions `#`,
which is a label rather than a `TypeObservation`, so the monitor alphabet
adjoins it. -/
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

/-- One step of the round-robin monitor `M_d`: strike the marks just observed
off the outstanding requirements; when none remain the round is complete, so
the monitor raises its completion flag and starts the next round. -/
def monitorAdvance (req pending marks : Finset TypeMark) :
    Finset TypeMark × Bool :=
  let remaining := pending \ marks
  if remaining = ∅ then (req, true) else (remaining, false)

/-- A vertex of `hat(G)_(I,T) = G^H_I × ∏_(d ∈ D_T) M_d`: an arena vertex, the
outstanding requirements and completion flag of every monitor, and the log
entry fired by the edge that produced it.  Recording the entry is what makes a
vertex sequence a path: the log of a play reads the labels its edges fired. -/
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

/-- `R_T = {(F_d,B_d) | d ∈ D_T}`, with `F_d` the completion flag of monitor
`d` and `B_d` the marks in `Forbid(d)`.  The failure sink raises no flag, so it
belongs to no `F_d`. -/
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

/-- The compatibility query for a fixed
composition `initial` (itself an already-`||_I`-composed `PactType`) and
progress set. -/
def TypeCompatible  (initial : PactType)
    (progress : Finset ProcId) : Prop :=
  let game := compatibilityGame initial progress
  game.initial ∈ game.WinRegion

end

end Pact
