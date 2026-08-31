import Anvilpp.ProofHelpers.TypeSemantics

namespace Pact

noncomputable section

open Classical

/-! ## The honesty-aware compatibility game (`pactcompat.typ`)

This is a genuinely concrete rendering of `pactcompat.typ`'s arena: the
honesty memory `H_I`, the two-player vertex sets `V_0`/`V_1` (plus the
absorbing failure sink), and the environment-choice/resolve/fail edges. What
is *not* rendered concretely is the finite round-robin monitor product used
to turn the Rabin objective into a finite-state acceptance condition
(`pactformalappendix.typ`, "Common monitor product"): that is bookkeeping
needed only for the effective decision procedure (Theorem 4.4), so the Rabin
winning condition below is stated directly against the infinite play's
label/environment sequence instead. -/

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

/-- The label taken by a `resolve → choice` step, for reading off the log of
a play (`E_choice`/bookkeeping half-edges contribute no log entry). -/
def compatibilityStepLabel (automaton : TypeAutomaton)
    (source target : CompatibilityVertex) : Option (TypeEnvironment × TypeLabel) :=
  match source, target with
  | .resolve state _ env, .choice state' _ =>
      if h : ∃ label, compiledTypeEdge automaton state env label state' then
        some (env, h.choose)
      else none
  | .resolve state memory env, .fail =>
      if ¬ memory.Admissible env ∨
          ¬ ∃ label state', compiledTypeEdge automaton state env label state' then
        some (env, TypeLabel.silent)
      else none
  | _, _ => none

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

/-- `(G,B)` accepts `π` iff `Inf(π) ∩ G ≠ ∅` and `Inf(π) ∩ B = ∅`; rendered
via recurrence of the visited-vertex sequence, which agrees with the
set-intersection reading on a finite graph. -/
def RabinGame.Accepts (game : RabinGame) (play : ℕ → game.Vertex) : Prop :=
  ∀ pair ∈ game.rabinPairs,
    Set.Infinite {n | play n ∈ pair.1} ∧ ¬ Set.Infinite {n | play n ∈ pair.2}

/-- The (positional-strategy) semantic winning region: `v` is winning for
Player 0 when some choice function, followed at every Player-0 vertex, wins
against every Player-1 response. General Rabin objectives can require finite
memory beyond a positional strategy; this scaffold definition is deliberately
the simplest faithful semantic notion; sharpening it (or proving it agrees
with a memory-based one) is part of Theorem 4.2/4.4's remaining content. -/
def RabinGame.WinRegion (game : RabinGame) : Set game.Vertex :=
  {v | ∃ strategy : game.Vertex → game.Vertex,
    (∀ u, game.isPlayerZero u → game.edge u (strategy u)) ∧
    ∀ play : ℕ → game.Vertex, play 0 = v →
      (∀ n, (if game.isPlayerZero (play n) then play (n + 1) = strategy (play n)
        else game.edge (play n) (play (n + 1)))) →
      game.Accepts play}

/-- `D_T = {live} ∪ (cal(Eta)(Θ_0) × {true,false})`. -/
inductive ObjectiveDisjunct (initial : PactType) : Type where
  | live : ObjectiveDisjunct initial
  | fair (bid : BranchId) (outcome : Bool) (mem : bid ∈ typeFairIds initial) :
      ObjectiveDisjunct initial

/-- `Req(d)`, as the set of observations whose recurrence the disjunct
demands. -/
def ObjectiveDisjunct.req {initial : PactType} (progress : Finset ProcId) :
    ObjectiveDisjunct initial → Finset TypeObservation
  | .live => progress.image .progress
  | .fair bid outcome _ => {.fair bid outcome}

/-- `Forbid(d)`. -/
def ObjectiveDisjunct.forbid {initial : PactType} :
    ObjectiveDisjunct initial → Finset TypeObservation
  | .live => ∅
  | .fair bid outcome _ => {.fair bid (!outcome)}

/-- The full list of Rabin pairs `R_T`, over the honesty-aware arena for a
fixed compiled automaton, one pair per disjunct in `D_T`. Left as `sorry`
pending the play/log correspondence needed to state each `(F_d,B_d)`
concretely against `CompatibilityVertex` plays. -/
def objectiveRabinPairs (automaton : TypeAutomaton) (initial : PactType)
    (progress : Finset ProcId) :
    List (Set (ℕ → CompatibilityVertex) × Set (ℕ → CompatibilityVertex)) := by
  sorry

/-- The honesty-aware compatibility game `hat(G)_{I,T}` for a fixed compiled
automaton. -/
def compatibilityGame (signature : TypeAlphabet) (initial : PactType)
    (progress : Finset ProcId) : RabinGame where
  Vertex := CompatibilityVertex
  initial := .choice (compileType signature initial).initial .star
  isPlayerZero := CompatibilityVertex.isPlayerZero
  edge := compatibilityEdge (compileType signature initial) initial.alphabet
  rabinPairs := by
    sorry -- TODO(redevelopment): needs the play/log correspondence from
    -- `objectiveRabinPairs`.

/-- Definition 4.5/`pactcompat.typ`: the compatibility query for a fixed
composition `initial` (itself an already-`||_I`-composed `PactType`) and
progress set. -/
def TypeCompatible (signature : TypeAlphabet) (initial : PactType)
    (progress : Finset ProcId) : Prop :=
  let game := compatibilityGame signature initial progress
  game.initial ∈ game.WinRegion

end

end Pact
