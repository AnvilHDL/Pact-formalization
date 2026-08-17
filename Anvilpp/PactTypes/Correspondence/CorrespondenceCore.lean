import Anvilpp.PactTypes.Automata.CompileType

/-!
# Core and atomic type-automaton correspondence
-/

namespace Pact

noncomputable section

open Classical

/-!
### The static "entry" classifier

`TypeEntry processType state` holds exactly when `state` is
`processType`'s own compiled fragment's `initial` field, characterized
structurally (mirroring each `build*Automaton`'s own `initial :=` choice)
rather than through `TypeCompilationRelation`'s residual. This is needed
because `TypeCompilationRelation processType state processType` (residual
equals the whole, unstepped type) is not on its own enough to pin down
`state = initial`: a degenerate self-referential recursion such as
`.recur "x" (.var "x")` also relates its *body*'s entry state,
`.child 0 .root`, to the same residual `.recur "x" (.var "x")` (since
substituting `.var "x"` back in reproduces the original term exactly), and
`.child 0 .root ≠ .root = (.recur "x" (.var "x")).initial`. That collision is
harmless for `TypeAccepting`-based reasoning alone (the colliding state
there is never itself accepting), but `sequence_left_entry` below needs
"is the state actually kept regardless of accepting-ness" to mean "is the
literal initial tag", not merely "represents the unstepped type" — so it
pins that down with this separate, purely structural characterization.
`TypeEntry_relation`/`TypeEntry_unique` establish it matches
`(compileTypeFuel _ _ processType).initial` and is the unique state with
that property.
-/
inductive TypeEntry : PactType → TypeAutomatonState → Prop where
  | skip : TypeEntry .skip .root
  | message (msg : MessageId) (dir : MessageDir) :
      TypeEntry (.message msg dir) .root
  | cycle : TypeEntry .tock .root
  | progress (pid : ProcId) : TypeEntry (.progress pid) .root
  | var (name : String) : TypeEntry (.var name) .root
  | recur (name : String) (body : PactType) : TypeEntry (.recur name body) .root
  | choice (left right : PactType) : TypeEntry (.choice left right) .root
  | fair (bid : BranchId) (left right : PactType) :
      TypeEntry (.fairChoice bid left right) .root
  | seq (left right : PactType) (state : TypeAutomatonState) :
      TypeEntry left state →
      TypeEntry (.seq left right) (.child 0 state)
  | par (left right : PactType) (interface : Interface)
      (leftState rightState : TypeAutomatonState) :
      TypeEntry left leftState →
      TypeEntry right rightState →
      TypeEntry (.par left right interface) (.pair leftState rightState)
  | xoffer (elseType : PactType) (branches : List (BareMessage × PactType)) :
      TypeEntry (.xoffer elseType branches) .root
  | offer (elseType : PactType) (branches : List (BareMessage × PactType)) :
      TypeEntry (.offer elseType branches) .root

/-!
### The static "accepting" classifier

`TypeAccepting processType state` holds exactly when `state` lands in the
`accepting` field of `processType`'s own compiled fragment, characterized
structurally (mirroring each `build*Automaton`'s own `accepting :=` formula)
rather than through `TypeCompilationRelation`'s residual. The two questions
are genuinely different: `TypeCompilationRelation.parallel` (below) is
deliberately unconditional, so a `.par`-shaped state's *residual* is never
literally `.skip` (it stays `.par leftResidual rightResidual interface`)
even when the state is accepting. `buildSequenceAutomaton`'s redirect,
though, deletes states by the *concrete* `accepting` field, so
`TypeCompilationRelation.sequence_left_progressed`'s "survives the redirect"
exclusion has to key off this predicate, not off `residual ≠ .skip`.
`TypeAccepting_iff_mem_accepting` proves the two coincide with the real
compiled field; `par`'s own semantic one-hop collapse to `.skip` still goes
through `TypeTransition.par_fuse` directly on whatever residual `.parallel`
actually hands back (`.par .skip .skip interface`, not requiring
`TypeCompilationRelation` to call it `.skip`).
-/
inductive TypeAccepting : PactType → TypeAutomatonState → Prop where
  | skip : TypeAccepting .skip .root
  | message_final (msg : MessageId) (dir : MessageDir) :
      TypeAccepting (.message msg dir) .final
  | cycle_final : TypeAccepting .tock .final
  | progress_final (pid : ProcId) : TypeAccepting (.progress pid) .final
  | recur_body (name : String) (body : PactType) (state : TypeAutomatonState) :
      TypeAccepting body state →
      TypeAccepting (.recur name body) (.child 0 state)
  | choice_left (left right : PactType) (state : TypeAutomatonState) :
      TypeAccepting left state →
      TypeAccepting (.choice left right) (.child 0 state)
  | choice_right (left right : PactType) (state : TypeAutomatonState) :
      TypeAccepting right state →
      TypeAccepting (.choice left right) (.child 1 state)
  | fair_left (bid : BranchId) (left right : PactType)
      (state : TypeAutomatonState) :
      TypeAccepting left state →
      TypeAccepting (.fairChoice bid left right) (.child 0 state)
  | fair_right (bid : BranchId) (left right : PactType)
      (state : TypeAutomatonState) :
      TypeAccepting right state →
      TypeAccepting (.fairChoice bid left right) (.child 1 state)
  | sequence_right (left right : PactType) (state : TypeAutomatonState) :
      -- No `sequence_left` case: `F_tau = F_2` only, by `buildSequenceAutomaton`.
      TypeAccepting right state →
      TypeAccepting (.seq left right) (.child 1 state)
  | parallel (left right : PactType) (interface : Interface)
      (leftState rightState : TypeAutomatonState) :
      TypeAccepting left leftState →
      TypeAccepting right rightState →
      TypeAccepting (.par left right interface) (.pair leftState rightState)
  | xoffer_else (elseType : PactType)
      (branches : List (BareMessage × PactType)) (state : TypeAutomatonState) :
      TypeAccepting elseType state →
      TypeAccepting (.xoffer elseType branches) (.child 0 state)
  | xoffer_branch (elseType branchType : PactType)
      (branches : List (BareMessage × PactType)) (action : BareMessage)
      (index : Nat) (state : TypeAutomatonState) :
      branches[index]? = some (action, branchType) →
      TypeAccepting branchType state →
      TypeAccepting (.xoffer elseType branches) (.child (index + 1) state)
  | offer_else (elseType : PactType)
      (branches : List (BareMessage × PactType)) (state : TypeAutomatonState) :
      TypeAccepting elseType state →
      TypeAccepting (.offer elseType branches) (.child 0 state)
  | offer_branches (elseType : PactType)
      (branches : List (BareMessage × PactType))
      (selected : BareMessage × PactType) (index : Nat)
      (state : TypeAutomatonState) :
      branches[index]? = some selected →
      TypeAccepting (parallelTypeBranchesSelecting selected branches) state →
      TypeAccepting (.offer elseType branches) (.child (index + 1) state)

/-!
### Semantic residuals represented by constructor states

This relation is the invariant used by the correspondence proof.  The first
type is the fragment originally compiled; the final type is the operational
residual represented by the tagged state in the middle.
-/

inductive TypeCompilationRelation :
    PactType → TypeAutomatonState → PactType → Prop where
  | skip : TypeCompilationRelation .skip .root .skip
  | message_source (msg : MessageId) (dir : MessageDir) :
      TypeCompilationRelation (.message msg dir) .root (.message msg dir)
  | message_final (msg : MessageId) (dir : MessageDir) :
      TypeCompilationRelation (.message msg dir) .final .skip
  | cycle_source : TypeCompilationRelation .tock .root .tock
  | cycle_final : TypeCompilationRelation .tock .final .skip
  | progress_source (pid : ProcId) :
      TypeCompilationRelation (.progress pid) .root (.progress pid)
  | progress_final (pid : ProcId) :
      TypeCompilationRelation (.progress pid) .final .skip
  | variable (name : String) :
      TypeCompilationRelation (.var name) .root (.var name)
  | recur_source (name : String) (body : PactType) :
      TypeCompilationRelation (.recur name body) .root (.recur name body)
  | recur_body (name : String) (body residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation body state residual →
      TypeCompilationRelation (.recur name body) (.child 0 state)
        (residual.replaceVar name (.recur name body))
  | choice_source (left right : PactType) :
      TypeCompilationRelation (.choice left right) .root (.choice left right)
  | choice_left (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation left state residual →
      TypeCompilationRelation (.choice left right) (.child 0 state) residual
  | choice_right (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation right state residual →
      TypeCompilationRelation (.choice left right) (.child 1 state) residual
  | fair_source (bid : BranchId) (left right : PactType) :
      TypeCompilationRelation (.fairChoice bid left right) .root
        (.fairChoice bid left right)
  | fair_left (bid : BranchId) (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation left state residual →
      TypeCompilationRelation (.fairChoice bid left right) (.child 0 state) residual
  | fair_right (bid : BranchId) (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation right state residual →
      TypeCompilationRelation (.fairChoice bid left right) (.child 1 state) residual
  | sequence_left_entry (left right residual : PactType)
      (state : TypeAutomatonState) :
      -- `state` is left's own designated initial/entry position, kept by
      -- `buildSequenceAutomaton` regardless of whether it happens to be
      -- accepting (e.g. `left = .skip`). `residual` is deliberately *not*
      -- pinned to `left` itself: for a `CollapsesToSkip`-shaped `left`
      -- (nested `.par` built from `.skip`), the entry position already
      -- represents literal `.skip`, not `left` as written — same
      -- degenerate case `compileTypeFuel_initial_relation` has to account
      -- for. `TypeEntry` (not just "some residual") is required so this
      -- stays the literal `.initial` tag even for degenerate,
      -- self-referential recursions — see `TypeEntry`'s doc comment.
      TypeEntry left state →
      TypeCompilationRelation left state residual →
      TypeCompilationRelation (.seq left right) (.child 0 state)
        (.seq residual right)
  | sequence_left_progressed (left right residual : PactType)
      (state : TypeAutomatonState) :
      -- Every non-accepting left state survives the redirect unconditionally.
      -- The exclusion is `¬ TypeAccepting`, not `residual ≠ .skip`: those
      -- diverge exactly at `.par`, whose residual is never literally `.skip`
      -- even when the state is accepting (see `TypeAccepting`, below).
      TypeCompilationRelation left state residual →
      ¬ TypeAccepting left state →
      TypeCompilationRelation (.seq left right) (.child 0 state)
        (.seq residual right)
  | sequence_right (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation right state residual →
      TypeCompilationRelation (.seq left right) (.child 1 state) residual
  | parallel (left right leftResidual rightResidual : PactType)
      (interface : Interface) (leftState rightState : TypeAutomatonState) :
      -- Mirrors `TypeTransition.par`/`par_fuse`'s split: without this
      -- exclusion, a pair state whose both components are accepting would
      -- need to relate to *both* `.par .skip .skip interface` (via this
      -- clause) and `.skip` (via `parallel_fuse`), breaking
      -- `residual_unique`. Needed for `stepIff`/`CompilationStepCorrect` to
      -- hold at `.par` itself: after a real synchronized step lands both
      -- sides on `.skip`, the only available continuation is `par_fuse`,
      -- targeting literal `.skip` — so the automaton state it lands on must
      -- be *able* to represent literal `.skip`, not just the compound form.
      TypeCompilationRelation left leftState leftResidual →
      TypeCompilationRelation right rightState rightResidual →
      ¬ (leftResidual = .skip ∧ rightResidual = .skip) →
      TypeCompilationRelation (.par left right interface)
        (.pair leftState rightState)
        (.par leftResidual rightResidual interface)
  | parallel_fuse (left right : PactType)
      (interface : Interface) (leftState rightState : TypeAutomatonState) :
      TypeCompilationRelation left leftState .skip →
      TypeCompilationRelation right rightState .skip →
      TypeCompilationRelation (.par left right interface)
        (.pair leftState rightState) .skip
  | xoffer_source (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      TypeCompilationRelation (.xoffer elseType branches) .root
        (.xoffer elseType branches)
  | xoffer_else (elseType residual : PactType)
      (branches : List (BareMessage × PactType))
      (state : TypeAutomatonState) :
      TypeCompilationRelation elseType state residual →
      TypeCompilationRelation (.xoffer elseType branches) (.child 0 state) residual
  | xoffer_branch (elseType branchType residual : PactType)
      (branches : List (BareMessage × PactType)) (action : BareMessage)
      (index : Nat) (state : TypeAutomatonState) :
      branches[index]? = some (action, branchType) →
      TypeCompilationRelation branchType state residual →
      TypeCompilationRelation (.xoffer elseType branches)
        (.child (index + 1) state) residual
  | offer_source (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      TypeCompilationRelation (.offer elseType branches) .root
        (.offer elseType branches)
  | offer_branches (elseType residual : PactType)
      (branches : List (BareMessage × PactType))
      (selected : BareMessage × PactType) (index : Nat)
      (state : TypeAutomatonState) :
      branches[index]? = some selected →
      TypeCompilationRelation
          (parallelTypeBranchesSelecting selected branches) state residual →
      TypeCompilationRelation (.offer elseType branches)
        (.child (index + 1) state) residual
  | offer_else (elseType residual : PactType)
      (branches : List (BareMessage × PactType))
      (state : TypeAutomatonState) :
      TypeCompilationRelation elseType state residual →
      TypeCompilationRelation (.offer elseType branches) (.child 0 state) residual

/-- A constructor state represents at most one semantic residual. -/
theorem TypeCompilationRelation.residual_unique
    {original left right : PactType} {state : TypeAutomatonState}
    (hLeft : TypeCompilationRelation original state left)
    (hRight : TypeCompilationRelation original state right) : left = right := by
  induction hLeft generalizing right <;> cases hRight <;>
    try simp_all
  all_goals
    first
    | solve_by_elim
    | (congr 1; solve_by_elim)
    | (constructor <;> solve_by_elim)
    | (exfalso
       apply_assumption
       all_goals (symm; solve_by_elim))

/-- A type has at most one entry state. -/
theorem TypeEntry.unique
    {processType : PactType} {left right : TypeAutomatonState}
    (hLeft : TypeEntry processType left)
    (hRight : TypeEntry processType right) : left = right := by
  induction hLeft generalizing right <;> cases hRight <;>
    try simp_all
  all_goals
    first
    | solve_by_elim
    | (congr 1; solve_by_elim)
    | (constructor <;> solve_by_elim)

/-- The compiled fragment's `initial` field always satisfies `TypeEntry`. -/
theorem compileTypeFuel_initial_entry (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      TypeEntry processType (compileTypeFuel signature fuel processType).initial := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message msg dir => exact TypeEntry.message msg dir
      | progress pid => exact TypeEntry.progress pid
      | tock => exact TypeEntry.cycle
      | skip => exact TypeEntry.skip
      | var name => exact TypeEntry.var name
      | recur name body => exact TypeEntry.recur name body
      | choice left right => exact TypeEntry.choice left right
      | fairChoice bid left right => exact TypeEntry.fair bid left right
      | seq left right =>
          apply TypeEntry.seq
          apply ih left
          simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
          omega
      | par left right interface =>
          apply TypeEntry.par
          · apply ih left
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          · apply ih right
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
      | xoffer elseType branches => exact TypeEntry.xoffer elseType branches
      | offer elseType branches => exact TypeEntry.offer elseType branches

/-- What a type's own automaton-*entry* state represents, structurally.
Most constructors install a fresh `.root`/entry position (per `TypeEntry`)
that never depends on any child's own entry, so their entry represents the
type itself, unchanged. Two constructors are different, both because
`buildSequenceAutomaton`/`buildParallelAutomaton` route the entry *through*
a child's own entry rather than installing a fresh one: `.seq left right`'s
entry is `buildSequenceAutomaton`'s unconditionally-kept
`.child 0 left.initial` (never redirected/deleted, regardless of
accepting-ness — see `sequence_left_entry`), so it recursively represents
whatever `left`'s own entry represents, embedded under the same `.seq`.
`.par left right interface`'s entry is the pair of both sides' own entries,
which collapses to literal `.skip` exactly when *both* sides' entries
already do (the same collision that makes `stepIff` need `parallel_fuse`
after a real step, here for a type that is *already* at that collapsed
shape from the start — see the `parallel`/`parallel_fuse` split above). -/
def PactType.canonicalEntryResidual : PactType → PactType
  | .seq left right => .seq left.canonicalEntryResidual right
  | .par left right interface =>
      let leftResidual := left.canonicalEntryResidual
      let rightResidual := right.canonicalEntryResidual
      if leftResidual = .skip ∧ rightResidual = .skip then .skip
      else .par leftResidual rightResidual interface
  | processType => processType

/- No `.par` anywhere in the syntax tree is degenerate — that is, no product
has both sides' entries already collapsing to `.skip`.

`canonicalEntryResidual` alone is too shallow to express this: it only
descends through `.seq`'s left child and `.par`'s two children, so
`(.xoffer elseType branches).canonicalEntryResidual` is the type itself no
matter how degenerate `elseType` or a branch continuation is.  Correspondence
statements that hand a *sub*-term to a recursive call therefore need this
hereditary form, not `canonicalEntryResidual _ = _`.

The excluded shape is a product that can never step (e.g.
`.par .skip .skip ∅`): its compiled entry state can only ever represent
literal `.skip`, so pinning the represented residual to the type as written
is false for it.  Every such type is semantically `.skip`; the restriction
costs no expressiveness. -/
mutual
  def PactType.EntryCanonical : PactType → Prop
    | .message _ _ | .progress _ | .tock | .skip | .var _ => True
    | .recur _ body => body.EntryCanonical
    | .choice left right | .fairChoice _ left right | .seq left right =>
        left.EntryCanonical ∧ right.EntryCanonical
    | .par left right _ =>
        ¬ (left.canonicalEntryResidual = .skip ∧
            right.canonicalEntryResidual = .skip) ∧
          left.EntryCanonical ∧ right.EntryCanonical
    | .xoffer elseType branches | .offer elseType branches =>
        elseType.EntryCanonical ∧ PactType.EntryCanonicalBranches branches
  termination_by processType => sizeOf processType

  def PactType.EntryCanonicalBranches :
      List (BareMessage × PactType) → Prop
    | [] => True
    | (_, processType) :: rest =>
        processType.EntryCanonical ∧ PactType.EntryCanonicalBranches rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

/-- The bridge from the hereditary predicate to the shallow transform that
`compileTypeFuel_initial_relation` is stated with. -/
theorem PactType.canonicalEntryResidual_eq_self_of_entryCanonical :
    ∀ {processType : PactType}, processType.EntryCanonical →
      processType.canonicalEntryResidual = processType
  | .message _ _, _ | .progress _, _ | .tock, _ | .skip, _ | .var _, _ =>
      rfl
  | .recur _ _, _ | .choice _ _, _ | .fairChoice _ _ _, _
  | .xoffer _ _, _ | .offer _ _, _ => rfl
  | .seq left _, hCanonical => by
      simp only [canonicalEntryResidual]
      rw [canonicalEntryResidual_eq_self_of_entryCanonical
        (show left.EntryCanonical from (by
          simp only [EntryCanonical] at hCanonical
          exact hCanonical.1))]
  | .par left right _, hCanonical => by
      simp only [EntryCanonical] at hCanonical
      obtain ⟨hNotBoth, hLeft, hRight⟩ := hCanonical
      simp only [canonicalEntryResidual,
        canonicalEntryResidual_eq_self_of_entryCanonical hLeft,
        canonicalEntryResidual_eq_self_of_entryCanonical hRight]
      rw [if_neg]
      rw [canonicalEntryResidual_eq_self_of_entryCanonical hLeft,
        canonicalEntryResidual_eq_self_of_entryCanonical hRight] at hNotBoth
      exact hNotBoth

/-- Every branch entry of a hereditarily-canonical `.xoffer`/`.offer` branch
list is itself canonical.  Used to recover the per-branch hypothesis
`compilationFragmentStepCorrect_xoffer`/`_offer` and friends need to recurse
into `hBranchStep`. -/
theorem PactType.EntryCanonicalBranches.get :
    ∀ {branches : List (BareMessage × PactType)} {index : Nat}
      {action : BareMessage} {branchType : PactType},
      PactType.EntryCanonicalBranches branches →
      branches[index]? = some (action, branchType) →
      branchType.EntryCanonical
  | [], _, _, _, _, hEntry => by simp at hEntry
  | (_, _) :: _, 0, _, _, hCanonical, hEntry => by
      simp only [List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hEntry
      simp only [EntryCanonicalBranches] at hCanonical
      rw [← hEntry.2]
      exact hCanonical.1
  | (_, _) :: rest, index + 1, action, branchType, hCanonical, hEntry => by
      simp only [List.getElem?_cons_succ] at hEntry
      simp only [EntryCanonicalBranches] at hCanonical
      exact PactType.EntryCanonicalBranches.get hCanonical.2 hEntry

/-- The head branch's own continuation is canonical.  Companion to `.get`
above (which needs a `getElem?` witness); this is the direct `head :: tail`
split, useful when destructuring a concrete list literal rather than indexing
into it.  Stated with an opaque `head : BareMessage × PactType` — the match
compiles against `head.1`/`head.2` via `Prod`'s structure eta, so it applies
to non-literal pairs at the call site too. -/
theorem PactType.EntryCanonicalBranches.head :
    ∀ {head : BareMessage × PactType} {rest : List (BareMessage × PactType)},
      PactType.EntryCanonicalBranches (head :: rest) →
      head.2.EntryCanonical
  | (_, _), _, hCanonical => by
      simp only [EntryCanonicalBranches] at hCanonical
      exact hCanonical.1

/-- The tail of a hereditarily-canonical branch list is itself hereditarily
canonical. -/
theorem PactType.EntryCanonicalBranches.tail :
    ∀ {head : BareMessage × PactType} {rest : List (BareMessage × PactType)},
      PactType.EntryCanonicalBranches (head :: rest) →
      PactType.EntryCanonicalBranches rest
  | (_, _), _, hCanonical => by
      simp only [EntryCanonicalBranches] at hCanonical
      exact hCanonical.2

/-- Converse of `.head`/`.tail`: a canonical head and canonical tail rebuild a
canonical `head :: tail`. -/
theorem PactType.EntryCanonicalBranches.cons :
    ∀ {head : BareMessage × PactType} {rest : List (BareMessage × PactType)},
      head.2.EntryCanonical → PactType.EntryCanonicalBranches rest →
      PactType.EntryCanonicalBranches (head :: rest)
  | (_, _), _, hHead, hRest => by
      simp only [EntryCanonicalBranches]
      exact ⟨hHead, hRest⟩

/-- A singleton branch list is canonical exactly when its one continuation
is. -/
theorem PactType.EntryCanonicalBranches.singleton :
    ∀ {branch : BareMessage × PactType}, branch.2.EntryCanonical →
      PactType.EntryCanonicalBranches [branch]
  | (_, _), hCanonical =>
      PactType.EntryCanonicalBranches.cons hCanonical (by
        simp only [EntryCanonicalBranches])

/-- Sufficiently fuelled compilation starts in the state representing its
input's `canonicalEntryResidual` (which is the input itself, except for the
`.seq`/`.par` propagation described there). -/
theorem compileTypeFuel_initial_relation (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      TypeCompilationRelation processType
        (compileTypeFuel signature fuel processType).initial
        processType.canonicalEntryResidual := by
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
          exact TypeCompilationRelation.message_source msg dir
      | progress pid =>
          exact TypeCompilationRelation.progress_source pid
      | tock =>
          exact TypeCompilationRelation.cycle_source
      | skip =>
          exact TypeCompilationRelation.skip
      | var name =>
          exact TypeCompilationRelation.variable name
      | recur name body =>
          exact TypeCompilationRelation.recur_source name body
      | choice left right =>
          exact TypeCompilationRelation.choice_source left right
      | fairChoice bid left right =>
          exact TypeCompilationRelation.fair_source bid left right
      | seq left right =>
          apply TypeCompilationRelation.sequence_left_entry
          · apply compileTypeFuel_initial_entry
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          · apply ih left
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
      | par left right interface =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          simp only [PactType.canonicalEntryResidual]
          by_cases hCollapses :
              left.canonicalEntryResidual = .skip ∧
                right.canonicalEntryResidual = .skip
          · simp only [hCollapses, if_true]
            refine TypeCompilationRelation.parallel_fuse left right interface _ _
              ?_ ?_
            · rw [← hCollapses.1]; exact ih left hLeftFuel
            · rw [← hCollapses.2]; exact ih right hRightFuel
          · simp only [hCollapses, if_false]
            exact TypeCompilationRelation.parallel left right _ _ interface _ _
              (ih left hLeftFuel) (ih right hRightFuel) hCollapses
      | xoffer elseType branches =>
          exact TypeCompilationRelation.xoffer_source elseType branches
      | offer elseType branches =>
          exact TypeCompilationRelation.offer_source elseType branches

/-- Common-case corollary of `compileTypeFuel_initial_relation`, at a fixed
fuel rather than through the `compileType` wrapper — the shape most call
sites inside other fuel-indexed inductions need directly. -/
theorem compileTypeFuel_initial_relation_of_canonical
    (signature : TypeAlphabet) (fuel : Nat) (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel)
    (hCanonical : processType.canonicalEntryResidual = processType) :
    TypeCompilationRelation processType
      (compileTypeFuel signature fuel processType).initial processType := by
  have h := compileTypeFuel_initial_relation signature fuel processType hFuel
  rwa [hCanonical] at h

/-- The public compiler's initial state represents the original type. -/
theorem compileType_initial_relation
    (signature : TypeAlphabet) (processType : PactType) :
    TypeCompilationRelation processType
      (compileType signature processType).initial
      processType.canonicalEntryResidual := by
  apply compileTypeFuel_initial_relation signature
  exact typeCompilationFuel_sufficient processType

/-- Common-case corollary of `compileType_initial_relation`: for any type
that isn't itself already sitting at a collapsed `.par`-of-`.skip` position
(the overwhelming majority — anything not built from `.seq`/`.par` reduces
trivially, and `.seq`/`.par` reduce as long as their embedded `.par`
children aren't themselves fully collapsed), the initial state represents
the type exactly as written. -/
theorem compileType_initial_relation_of_canonical
    (signature : TypeAlphabet) (processType : PactType)
    (hCanonical : processType.canonicalEntryResidual = processType) :
    TypeCompilationRelation processType
      (compileType signature processType).initial processType := by
  have h := compileType_initial_relation signature processType
  rwa [hCanonical] at h

/-- Every sufficiently fuelled fragment contains its distinguished entry state. -/
theorem compileTypeFuel_initial_mem (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      (compileTypeFuel signature fuel processType).initial ∈
        (compileTypeFuel signature fuel processType).states := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message msg dir => simp [compileTypeFuel, finishAutomatonFragment]
      | progress pid => simp [compileTypeFuel, finishAutomatonFragment]
      | tock => simp [compileTypeFuel, finishAutomatonFragment]
      | skip => simp [compileTypeFuel, finishAutomatonFragment]
      | var name => simp [compileTypeFuel, finishAutomatonFragment]
      | recur name body =>
          simp [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment]
      | choice left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment]
      | fairChoice bid left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment]
      | seq left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hInitialOrTarget :
              (compileTypeFuel signature fuel left).initial ∈
                  (compileTypeFuel signature fuel left).states ∨
                ∃ edge ∈ (compileTypeFuel signature fuel left).edges,
                  edge.target =
                    (compileTypeFuel signature fuel left).initial :=
            Or.inl (ih left hLeft)
          simpa [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childStates, childState,
            initial_not_mem_sequenceDeleted] using hInitialOrTarget
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
            finishAutomatonFragment]
          apply Finset.mem_biUnion.mpr
          refine ⟨_, hLeftMem, ?_⟩
          exact Finset.mem_image.mpr ⟨_, hRightMem, rfl⟩
      | xoffer elseType branches =>
          simp [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
      | offer elseType branches =>
          simp [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment]

/-- Every symbolic future reference produced by sufficiently fuelled
compilation points to a state declared by the same constructor fragment. -/
theorem compileTypeFuel_futureTargetsInStates
    (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
        (compileTypeFuel signature fuel processType).FutureTargetsInStates := by
  classical
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
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          cases hEdge with
          | inl hFirst =>
            cases hFirst with
            | inl hFiring =>
              rcases hFiring with ⟨environment, _, hEq⟩
              rw [← hEq] at hFuture
              cases hFuture
            | inr hWaiting =>
              rcases hWaiting with ⟨environment, _, hEq⟩
              rw [← hEq] at hFuture
              cases hFuture
          | inr hFinal =>
            rcases hFinal with ⟨environment, _, hEq⟩
            rw [← hEq] at hFuture
            cases hFuture
      | progress pid =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with hAction | hFinal
          · rcases hAction with ⟨environment, _, hEdge⟩
            rw [← hEdge] at hFuture
            cases hFuture
          · rcases hFinal with ⟨environment, _, hEdge⟩
            rw [← hEdge] at hFuture
            cases hFuture
      | tock =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with (⟨environment, _, hEdge⟩ |
            ⟨environment, _, hEdge⟩)
          · rw [← hEdge] at hFuture
            split at hFuture <;> cases hFuture
          · rw [← hEdge] at hFuture
            cases hFuture
      | skip =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with ⟨environment, _, hEdge⟩
          rw [← hEdge] at hFuture
          cases hFuture
      | var name =>
          simp [AutomatonFragment.FutureTargetsInStates, compileTypeFuel,
            finishAutomatonFragment]
      | recur name body =>
          have hBody : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          exact buildRecursionAutomaton_futureTargetsInStates signature name
            (compileTypeFuel signature fuel body) (ih body hBody)
            (compileTypeFuel_initial_mem signature fuel body hBody)
      | choice left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          exact buildChoiceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
            TypeLabel.silent TypeLabel.silent
            (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel left hLeft)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | fairChoice bid left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          exact buildChoiceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
            (TypeLabel.fair bid true) (TypeLabel.fair bid false)
            (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel left hLeft)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | seq left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          exact buildSequenceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
            (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | par left right interface =>
          exact buildParallelAutomaton_futureTargetsInStates interface
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
      | xoffer elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hBranches : typeBranchCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          apply buildExclusiveOfferAutomaton_futureTargetsInStates signature
            branches (compileTypeFuel signature fuel elseType)
            (branches.map fun branch =>
              (branch.1, compileTypeFuel signature fuel branch.2))
          · exact ih elseType hElse
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            rcases hEntry with ⟨⟨action, branchType⟩, hBranch, rfl⟩
            apply ih branchType
            exact le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                (action, branchType) hBranch)
              hBranches
          · exact compileTypeFuel_initial_mem signature fuel elseType hElse
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            rcases hEntry with ⟨⟨action, branchType⟩, hBranch, rfl⟩
            apply compileTypeFuel_initial_mem signature fuel branchType
            exact le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                (action, branchType) hBranch)
              hBranches
      | offer elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          let selectedConjunctions := branches.map fun selected =>
            (selected.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting selected branches))
          exact buildSelectedConjunctiveOfferAutomaton_futureTargetsInStates signature
            branches (compileTypeFuel signature fuel elseType)
            selectedConjunctions (ih elseType hElse) (by
              intro entry hEntry
              simp only [selectedConjunctions, List.mem_map] at hEntry
              rcases hEntry with ⟨selected, hSelected, rfl⟩
              apply ih
              rw [TypeCompilationFuelSufficient,
                typeCompilationFuel_parallelTypeBranchesSelecting]
              simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                at hFuel
              omega)
            (compileTypeFuel_initial_mem signature fuel elseType hElse)
            (by
              intro entry hEntry
              simp only [selectedConjunctions, List.mem_map] at hEntry
              rcases hEntry with ⟨selected, hSelected, rfl⟩
              apply compileTypeFuel_initial_mem
              rw [TypeCompilationFuelSufficient,
                typeCompilationFuel_parallelTypeBranchesSelecting]
              simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                at hFuel
              omega)

/-- Sufficient compilation produces a pending graph closed under all
same-cycle symbolic references. -/
theorem compileTypeFuel_referencesClosed
    (signature : TypeAlphabet) (fuel : Nat) (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel) :
    ({ states := (compileTypeFuel signature fuel processType).states
       edges := (compileTypeFuel signature fuel processType).edges } :
      PendingAutomaton).ReferencesClosed := by
  exact PendingAutomaton.referencesClosed_of_futureTargetsInStates
    (compileTypeFuel signature fuel processType)
    (compileTypeFuel_futureTargetsInStates signature fuel processType hFuel)

/-- The initial state exposed by the public compiler belongs to its state set. -/
theorem compileType_initial_mem
    (signature : TypeAlphabet) (processType : PactType) :
    (compileType signature processType).initial ∈
      (compileType signature processType).states := by
  simp only [compileType, Finset.mem_union]
  left
  apply compileTypeFuel_initial_mem signature
  exact typeCompilationFuel_sufficient processType

/-- State-carrier side of the compiler relation.  Future embeddings need this
independently of the semantic equality: saturation stability is stated for a
declared child state. -/
theorem childState_mem_indexedFragmentAccepting_iff
    (automata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : automata[index]? = some entry)
    (state : TypeAutomatonState) :
    childState (index + 1) state ∈ indexedFragmentAccepting automata ↔
      state ∈ entry.2.accepting := by
  classical
  rw [indexedFragmentAccepting, mem_foldl_union_iff]
  constructor
  · rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
    · simp at hEmpty
    simp only [childAccepting, Finset.mem_image] at hChild
    rcases hChild with ⟨child, hChildAccepting, hState⟩
    have hIndex : indexed.2 = index := by
      injection hState with hTag _
      omega
    have hInner : child = state := by
      injection hState
    subst child
    have hIndexedFields := List.mem_zipIdx hIndexed
    simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
      at hIndexedFields
    rcases hIndexedFields with ⟨hBound, hValue⟩
    have hIndexedEntry : automata[indexed.2]? = some indexed.1 := by
      rw [List.getElem?_eq_getElem hBound, ← hValue]
    have hEntryEq : indexed.1 = entry := by
      have hOptions := congrArg (fun position => automata[position]?) hIndex
      change automata[indexed.2]? = automata[index]? at hOptions
      rw [hIndexedEntry, hEntry] at hOptions
      exact Option.some.inj hOptions
    simpa [hEntryEq] using hChildAccepting
  · intro hAccepting
    rcases List.getElem?_eq_some_iff.mp hEntry with
      ⟨hBound, hValue⟩
    have hZipBound : index < automata.zipIdx.length := by
      simpa using hBound
    have hIndexed : (entry, index) ∈ automata.zipIdx := by
      have hMember := List.getElem_mem hZipBound
      have hAt := List.getElem_zipIdx (l := automata) (i := index)
        (j := 0) hZipBound
      simp only [zero_add] at hAt
      rw [hAt, hValue] at hMember
      exact hMember
    right
    refine ⟨(entry, index), hIndexed, ?_⟩
    simp [childAccepting, childState, hAccepting]

theorem root_not_mem_indexedFragmentAccepting
    (automata : List (BareMessage × AutomatonFragment)) :
    TypeAutomatonState.root ∉ indexedFragmentAccepting automata := by
  rw [indexedFragmentAccepting, mem_foldl_union_iff]
  rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
  · simp at hEmpty
  · simp only [childAccepting, Finset.mem_image] at hChild
    rcases hChild with ⟨state, hState, hImpossible⟩
    cases hImpossible

theorem child_zero_not_mem_indexedFragmentAccepting
    (automata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) :
    childState 0 state ∉ indexedFragmentAccepting automata := by
  rw [indexedFragmentAccepting, mem_foldl_union_iff]
  rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
  · simp at hEmpty
  · simp only [childAccepting, Finset.mem_image] at hChild
    rcases hChild with ⟨other, hOther, hEquality⟩
    have hIndex : indexed.2 + 1 = 0 := by
      injection hEquality
    omega

theorem childState_mem_indexedFragmentCompleting_iff
    (automata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : automata[index]? = some entry)
    (state : TypeAutomatonState) :
    childState (index + 1) state ∈ indexedFragmentCompleting automata ↔
      state ∈ entry.2.completing := by
  classical
  rw [indexedFragmentCompleting, mem_foldl_union_iff]
  constructor
  · rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
    · simp at hEmpty
    simp only [childCompleting, Finset.mem_image] at hChild
    rcases hChild with ⟨child, hChildCompleting, hState⟩
    have hIndex : indexed.2 = index := by
      injection hState with hTag _
      omega
    have hInner : child = state := by
      injection hState
    subst child
    have hIndexedFields := List.mem_zipIdx hIndexed
    simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
      at hIndexedFields
    rcases hIndexedFields with ⟨hBound, hValue⟩
    have hIndexedEntry : automata[indexed.2]? = some indexed.1 := by
      rw [List.getElem?_eq_getElem hBound, ← hValue]
    have hEntryEq : indexed.1 = entry := by
      have hOptions := congrArg (fun position => automata[position]?) hIndex
      change automata[indexed.2]? = automata[index]? at hOptions
      rw [hIndexedEntry, hEntry] at hOptions
      exact Option.some.inj hOptions
    simpa [hEntryEq] using hChildCompleting
  · intro hCompleting
    rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
    have hZipBound : index < automata.zipIdx.length := by
      simpa using hBound
    have hIndexed : (entry, index) ∈ automata.zipIdx := by
      have hMember := List.getElem_mem hZipBound
      have hAt := List.getElem_zipIdx (l := automata) (i := index)
        (j := 0) hZipBound
      simp only [zero_add] at hAt
      rw [hAt, hValue] at hMember
      exact hMember
    right
    refine ⟨(entry, index), hIndexed, ?_⟩
    simp [childCompleting, childState, hCompleting]

theorem root_not_mem_indexedFragmentCompleting
    (automata : List (BareMessage × AutomatonFragment)) :
    TypeAutomatonState.root ∉ indexedFragmentCompleting automata := by
  rw [indexedFragmentCompleting, mem_foldl_union_iff]
  rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
  · simp at hEmpty
  · simp only [childCompleting, Finset.mem_image] at hChild
    rcases hChild with ⟨state, hState, hImpossible⟩
    cases hImpossible

theorem child_zero_not_mem_indexedFragmentCompleting
    (automata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) :
    childState 0 state ∉ indexedFragmentCompleting automata := by
  rw [indexedFragmentCompleting, mem_foldl_union_iff]
  rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
  · simp at hEmpty
  · simp only [childCompleting, Finset.mem_image] at hChild
    rcases hChild with ⟨other, hOther, hEquality⟩
    have hIndex : indexed.2 + 1 = 0 := by
      injection hEquality
    omega

/-- At every state represented by a sufficiently fuelled constructor
fragment, the compiler's `accepting` marker is exact: it holds precisely
when the state is structurally `TypeAccepting`. -/
theorem compileTypeFuel_accepting_iff
    (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      ∀ state residual,
        TypeCompilationRelation processType state residual →
        (state ∈ (compileTypeFuel signature fuel processType).accepting ↔
          TypeAccepting processType state) := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel state residual hRelated
      cases hRelated with
      | skip =>
          constructor
          · intro _; exact TypeAccepting.skip
          · intro _; simp [compileTypeFuel, finishAutomatonFragment]
      | message_source msg dir =>
          constructor
          · intro hMem; simp [compileTypeFuel, finishAutomatonFragment] at hMem
          · intro hAcc; cases hAcc
      | message_final msg dir =>
          constructor
          · intro _; exact TypeAccepting.message_final msg dir
          · intro _; simp [compileTypeFuel, finishAutomatonFragment]
      | cycle_source =>
          constructor
          · intro hMem; simp [compileTypeFuel, finishAutomatonFragment] at hMem
          · intro hAcc; cases hAcc
      | cycle_final =>
          constructor
          · intro _; exact TypeAccepting.cycle_final
          · intro _; simp [compileTypeFuel, finishAutomatonFragment]
      | progress_source pid =>
          constructor
          · intro hMem; simp [compileTypeFuel, finishAutomatonFragment] at hMem
          · intro hAcc; cases hAcc
      | progress_final pid =>
          constructor
          · intro _; exact TypeAccepting.progress_final pid
          · intro _; simp [compileTypeFuel, finishAutomatonFragment]
      | «variable» name =>
          constructor
          · intro hMem; simp [compileTypeFuel, finishAutomatonFragment] at hMem
          · intro hAcc; cases hAcc
      | recur_source name body =>
          constructor
          · intro hMem
            simp [compileTypeFuel, buildRecursionAutomaton,
              finishAutomatonFragment, childAccepting, childState] at hMem
          · intro hAcc; cases hAcc
      | recur_body name body childResidual childQ hChildRelated =>
          have hBodyFuel : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih body hBodyFuel childQ childResidual
            hChildRelated
          constructor
          · intro hMem
            have hMem' : childQ ∈ (compileTypeFuel signature fuel body).accepting := by
              simpa [compileTypeFuel, buildRecursionAutomaton,
                finishAutomatonFragment, childAccepting, childState] using hMem
            exact TypeAccepting.recur_body name body childQ (hChild.mp hMem')
          · intro hAcc
            cases hAcc with
            | recur_body _ _ _ hInner =>
                simpa [compileTypeFuel, buildRecursionAutomaton,
                  finishAutomatonFragment, childAccepting, childState]
                  using hChild.mpr hInner
      | choice_source left right =>
          constructor
          · intro hMem
            simp [compileTypeFuel, buildChoiceAutomaton,
              finishAutomatonFragment, childAccepting, childState] at hMem
          · intro hAcc; cases hAcc
      | choice_left left right _ childQ hChildRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel childQ residual
            hChildRelated
          constructor
          · intro hMem
            have hMem' : childQ ∈ (compileTypeFuel signature fuel left).accepting := by
              simpa [compileTypeFuel, buildChoiceAutomaton,
                finishAutomatonFragment, childAccepting, childState] using hMem
            exact TypeAccepting.choice_left left right childQ (hChild.mp hMem')
          · intro hAcc
            cases hAcc with
            | choice_left _ _ _ hInner =>
                simpa [compileTypeFuel, buildChoiceAutomaton,
                  finishAutomatonFragment, childAccepting, childState]
                  using hChild.mpr hInner
      | choice_right left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          constructor
          · intro hMem
            have hMem' : childQ ∈ (compileTypeFuel signature fuel right).accepting := by
              simpa [compileTypeFuel, buildChoiceAutomaton,
                finishAutomatonFragment, childAccepting, childState] using hMem
            exact TypeAccepting.choice_right left right childQ (hChild.mp hMem')
          · intro hAcc
            cases hAcc with
            | choice_right _ _ _ hInner =>
                simpa [compileTypeFuel, buildChoiceAutomaton,
                  finishAutomatonFragment, childAccepting, childState]
                  using hChild.mpr hInner
      | fair_source bid left right =>
          constructor
          · intro hMem
            simp [compileTypeFuel, buildChoiceAutomaton,
              finishAutomatonFragment, childAccepting, childState] at hMem
          · intro hAcc; cases hAcc
      | fair_left bid left right _ childQ hChildRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel childQ residual
            hChildRelated
          constructor
          · intro hMem
            have hMem' : childQ ∈ (compileTypeFuel signature fuel left).accepting := by
              simpa [compileTypeFuel, buildChoiceAutomaton,
                finishAutomatonFragment, childAccepting, childState] using hMem
            exact TypeAccepting.fair_left bid left right childQ (hChild.mp hMem')
          · intro hAcc
            cases hAcc with
            | fair_left _ _ _ _ hInner =>
                simpa [compileTypeFuel, buildChoiceAutomaton,
                  finishAutomatonFragment, childAccepting, childState]
                  using hChild.mpr hInner
      | fair_right bid left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          constructor
          · intro hMem
            have hMem' : childQ ∈ (compileTypeFuel signature fuel right).accepting := by
              simpa [compileTypeFuel, buildChoiceAutomaton,
                finishAutomatonFragment, childAccepting, childState] using hMem
            exact TypeAccepting.fair_right bid left right childQ (hChild.mp hMem')
          · intro hAcc
            cases hAcc with
            | fair_right _ _ _ _ hInner =>
                simpa [compileTypeFuel, buildChoiceAutomaton,
                  finishAutomatonFragment, childAccepting, childState]
                  using hChild.mpr hInner
      | sequence_left_entry left right _ stateL hEntry hSelfRelated =>
          -- No `sequence_left`/`.child 0` case in `TypeAccepting` at all
          -- (`F_tau = F_2` only), so this direction never holds regardless
          -- of whether `left` itself happens to be accepting.
          constructor
          · intro hMem
            simp [compileTypeFuel, buildSequenceAutomaton,
              finishAutomatonFragment, childAccepting, childState] at hMem
          · intro hAcc; cases hAcc
      | sequence_left_progressed left right childResidual childQ hChildRelated
          hNotAccepting =>
          constructor
          · intro hMem
            simp [compileTypeFuel, buildSequenceAutomaton,
              finishAutomatonFragment, childAccepting, childState] at hMem
          · intro hAcc; cases hAcc
      | sequence_right left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          constructor
          · intro hMem
            have hMem' : childQ ∈ (compileTypeFuel signature fuel right).accepting := by
              simpa [compileTypeFuel, buildSequenceAutomaton,
                finishAutomatonFragment, childAccepting, childState] using hMem
            exact TypeAccepting.sequence_right left right childQ (hChild.mp hMem')
          · intro hAcc
            cases hAcc with
            | sequence_right _ _ _ hInner =>
                simpa [compileTypeFuel, buildSequenceAutomaton,
                  finishAutomatonFragment, childAccepting, childState]
                  using hChild.mpr hInner
      | parallel left right leftResidual rightResidual interface leftState
          rightState hLeftRelated hRightRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hLeftChild := ih left hLeftFuel leftState leftResidual hLeftRelated
          have hRightChild := ih right hRightFuel rightState rightResidual hRightRelated
          constructor
          · intro hMem
            simp only [compileTypeFuel, buildParallelAutomaton,
              finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_image] at hMem
            obtain ⟨ls, hls, rs, hrs, hEq⟩ := hMem
            injection hEq with hEqL hEqR
            subst hEqL; subst hEqR
            exact TypeAccepting.parallel left right interface ls rs
              (hLeftChild.mp hls) (hRightChild.mp hrs)
          · intro hAcc
            cases hAcc with
            | parallel _ _ _ _ _ hInnerL hInnerR =>
                simp only [compileTypeFuel, buildParallelAutomaton,
                  finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_image]
                exact ⟨_, hLeftChild.mpr hInnerL, _, hRightChild.mpr hInnerR, rfl⟩
      | parallel_fuse left right interface leftState rightState hLeftRelated
          hRightRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hLeftChild := ih left hLeftFuel leftState .skip hLeftRelated
          have hRightChild := ih right hRightFuel rightState .skip hRightRelated
          constructor
          · intro hMem
            simp only [compileTypeFuel, buildParallelAutomaton,
              finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_image] at hMem
            obtain ⟨ls, hls, rs, hrs, hEq⟩ := hMem
            injection hEq with hEqL hEqR
            subst hEqL; subst hEqR
            exact TypeAccepting.parallel left right interface ls rs
              (hLeftChild.mp hls) (hRightChild.mp hrs)
          · intro hAcc
            cases hAcc with
            | parallel _ _ _ _ _ hInnerL hInnerR =>
                simp only [compileTypeFuel, buildParallelAutomaton,
                  finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_image]
                exact ⟨_, hLeftChild.mpr hInnerL, _, hRightChild.mpr hInnerR, rfl⟩
      | xoffer_source elseType branches =>
          constructor
          · intro hMem
            simp [compileTypeFuel, buildExclusiveOfferAutomaton,
              finishAutomatonFragment, childAccepting, childState,
              root_not_mem_indexedFragmentAccepting] at hMem
          · intro hAcc; cases hAcc
      | xoffer_else elseType _ branches childQ hChildRelated =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih elseType hElseFuel childQ residual
            hChildRelated
          rw [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
          simp only [Finset.mem_union]
          have hElseTag : childState 0 childQ ∈
                childAccepting 0 (compileTypeFuel signature fuel elseType) ↔
              childQ ∈
                (compileTypeFuel signature fuel elseType).accepting := by
            simp [childAccepting, childState]
          have hNotIndexed : childState 0 childQ ∉
              indexedFragmentAccepting
                (branches.map fun branch =>
                  (branch.1, compileTypeFuel signature fuel branch.2)) :=
            child_zero_not_mem_indexedFragmentAccepting _ childQ
          constructor
          · rintro (hElse | hIndexed)
            · exact TypeAccepting.xoffer_else elseType branches childQ
                (hChild.mp (hElseTag.mp hElse))
            · exact (hNotIndexed hIndexed).elim
          · intro hAcc
            cases hAcc with
            | xoffer_else _ _ _ hInner =>
                left
                exact hElseTag.mpr (hChild.mpr hInner)
      | xoffer_branch elseType branchType _ branches action index
          childQ hEntry hChildRelated =>
          have hBranchesFuel : typeBranchCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hBranchFuel : TypeCompilationFuelSufficient branchType fuel := by
            rcases List.getElem?_eq_some_iff.mp hEntry with
              ⟨hIndexBound, hIndexValue⟩
            have hBranchMem : (action, branchType) ∈ branches := by
              have hMember := List.getElem_mem hIndexBound
              simpa [hIndexValue] using hMember
            exact le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                (action, branchType) hBranchMem)
              hBranchesFuel
          have hChild := ih branchType hBranchFuel childQ residual
            hChildRelated
          let branchAutomata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          have hAutomatonEntry : branchAutomata[index]? =
              some (action, compileTypeFuel signature fuel branchType) := by
            simp [branchAutomata, hEntry]
          have hIndexed := childState_mem_indexedFragmentAccepting_iff
            branchAutomata index
              (action, compileTypeFuel signature fuel branchType)
              hAutomatonEntry childQ
          rw [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
          simp only [Finset.mem_union]
          have hNotElse : childState (index + 1) childQ ∉
              childAccepting 0 (compileTypeFuel signature fuel elseType) := by
            simp [childAccepting, childState]
          constructor
          · rintro (hElse | hBranch)
            · exact (hNotElse hElse).elim
            · exact TypeAccepting.xoffer_branch elseType branchType branches
                action index childQ hEntry (hChild.mp (hIndexed.mp hBranch))
          · intro hAcc
            cases hAcc with
            | xoffer_branch _ branchType' _ action' _ _ hEntry' hInner =>
                have hSame : (action, branchType) = (action', branchType') := by
                  rw [hEntry] at hEntry'
                  exact Option.some.inj hEntry'
                have hBranchTypeEq : branchType' = branchType :=
                  (congrArg Prod.snd hSame).symm
                subst hBranchTypeEq
                right
                exact hIndexed.mpr (hChild.mpr hInner)
      | offer_source elseType branches =>
          constructor
          · intro hMem
            simp [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
              finishAutomatonFragment, childAccepting, childState,
              root_not_mem_indexedFragmentAccepting] at hMem
          · intro hAcc; cases hAcc
      | offer_branches elseType _ branches selected index childQ hEntry
          hChildRelated =>
          have hConjunctionFuel : TypeCompilationFuelSufficient
              (parallelTypeBranchesSelecting selected branches) fuel := by
            rw [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting]
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hChild := ih
            (parallelTypeBranchesSelecting selected branches) hConjunctionFuel
              childQ residual hChildRelated
          let selectedConjunctions := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting branch branches))
          have hAutomatonEntry : selectedConjunctions[index]? = some
              (selected.1, compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting selected branches)) := by
            simp [selectedConjunctions, hEntry]
          have hIndexed := childState_mem_indexedFragmentAccepting_iff
            selectedConjunctions index
              (selected.1, compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting selected branches))
              hAutomatonEntry childQ
          rw [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment]
          simp only [Finset.mem_union]
          have hNotElse : childState (index + 1) childQ ∉
              childAccepting 0 (compileTypeFuel signature fuel elseType) := by
            simp [childAccepting, childState]
          constructor
          · rintro (hElse | hBranch)
            · exact (hNotElse hElse).elim
            · exact TypeAccepting.offer_branches elseType branches selected
                index childQ hEntry (hChild.mp (hIndexed.mp hBranch))
          · intro hAcc
            cases hAcc with
            | offer_branches _ _ selected' _ _ hEntry' hInner =>
                have hSame : selected = selected' := by
                  rw [hEntry] at hEntry'
                  exact Option.some.inj hEntry'
                subst hSame
                right
                exact hIndexed.mpr (hChild.mpr hInner)
      | offer_else elseType _ branches childQ hChildRelated =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih elseType hElseFuel childQ residual
            hChildRelated
          rw [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment]
          simp only [Finset.mem_union]
          have hNotIndexed : childState 0 childQ ∉
              indexedFragmentAccepting
                (branches.map fun selected =>
                  (selected.1, compileTypeFuel signature fuel
                    (parallelTypeBranchesSelecting selected branches))) := by
            rw [indexedFragmentAccepting, mem_foldl_union_iff]
            rintro (hEmpty | ⟨indexed, _, hMember⟩)
            · simp at hEmpty
            · simp [childAccepting, childState] at hMember
          constructor
          · rintro (hElse | hIndexed)
            · exact TypeAccepting.offer_else elseType branches childQ
                (hChild.mp (by simpa [childAccepting, childState] using hElse))
            · exact (hNotIndexed hIndexed).elim
          · intro hAcc
            cases hAcc with
            | offer_else _ _ _ hInner =>
                left
                simpa [childAccepting, childState] using hChild.mpr hInner

/-- The compiler's `accepting`-state marker agrees with `TypeAccepting` at
every state represented by the compilation relation. -/
def CompilationAcceptingCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  ∀ state residual,
    TypeCompilationRelation processType state residual →
      (state ∈ (compileTypeFuel signature
          (typeCompilationFuel processType) processType).accepting ↔
        TypeAccepting processType state)

theorem compilationAcceptingCorrect_of_compilation
    (signature : TypeAlphabet) (processType : PactType) :
    CompilationAcceptingCorrect signature processType := by
  exact compileTypeFuel_accepting_iff signature
    (typeCompilationFuel processType) processType
    (typeCompilationFuel_sufficient processType)

/-- Replacing a variable by its recursion binder yields literal `skip` exactly
when the original residual was already literal `skip`. -/
theorem PactType.replaceVar_recur_eq_skip_iff
    (processType : PactType) (name : String) (body : PactType) :
    (processType.replaceVar name (.recur name body) = .skip) ↔
      processType = .skip := by
  cases processType <;> simp only [PactType.replaceVar] <;>
    try simp
  all_goals split <;> simp_all

/-- A represented residual is literally `skip` exactly when the structural
`TypeAccepting` predicate holds at its state. Needed by `buildSequenceAutomaton`'s
redirect, which deletes/reroutes states by the *concrete* `accepting` field
(via `TypeAccepting`, see `CompilationAcceptingCorrect`) but whose callers
reason about the *residual* directly (e.g. matching on `TypeTransition.
skip_seq`/`seq_fuse`, which pattern-match a literal `.skip` child). Proved by
induction on the relation derivation; the only non-immediate case is `.par`,
where `parallel`'s exclusion hypothesis rules out its own residual being
`.skip` whenever both children are already (recursively) accepting, forcing
`parallel_fuse` to be the only derivation reaching an accepting pair state. -/
theorem TypeCompilationRelation.residual_eq_skip_iff_typeAccepting :
    ∀ {processType : PactType} {state : TypeAutomatonState} {residual : PactType},
      TypeCompilationRelation processType state residual →
      (residual = .skip ↔ TypeAccepting processType state) := by
  intro processType state residual hRelated
  induction hRelated with
  | skip => exact ⟨fun _ => TypeAccepting.skip, fun _ => rfl⟩
  | message_source msg dir =>
      exact ⟨fun h => absurd h (by simp), fun h => by cases h⟩
  | message_final msg dir =>
      exact ⟨fun _ => TypeAccepting.message_final msg dir, fun _ => rfl⟩
  | cycle_source =>
      exact ⟨fun h => absurd h (by simp), fun h => by cases h⟩
  | cycle_final =>
      exact ⟨fun _ => TypeAccepting.cycle_final, fun _ => rfl⟩
  | progress_source pid =>
      exact ⟨fun h => absurd h (by simp), fun h => by cases h⟩
  | progress_final pid =>
      exact ⟨fun _ => TypeAccepting.progress_final pid, fun _ => rfl⟩
  | «variable» name =>
      exact ⟨fun h => absurd h (by simp), fun h => by cases h⟩
  | recur_source name body =>
      exact ⟨fun h => absurd h (by simp), fun h => by cases h⟩
  | recur_body name body residual state hBody ih =>
      rw [PactType.replaceVar_recur_eq_skip_iff]
      constructor
      · intro h
        exact TypeAccepting.recur_body name body state (ih.mp h)
      · intro h
        cases h with
        | recur_body _ _ _ hInner => exact ih.mpr hInner
  | choice_source left right =>
      exact ⟨fun h => absurd h (by simp), fun h => by cases h⟩
  | choice_left left right residual state hChild ih =>
      constructor
      · intro h
        exact TypeAccepting.choice_left left right state (ih.mp h)
      · intro h
        cases h with
        | choice_left _ _ _ hInner => exact ih.mpr hInner
  | choice_right left right residual state hChild ih =>
      constructor
      · intro h
        exact TypeAccepting.choice_right left right state (ih.mp h)
      · intro h
        cases h with
        | choice_right _ _ _ hInner => exact ih.mpr hInner
  | fair_source bid left right =>
      exact ⟨fun h => absurd h (by simp), fun h => by cases h⟩
  | fair_left bid left right residual state hChild ih =>
      constructor
      · intro h
        exact TypeAccepting.fair_left bid left right state (ih.mp h)
      · intro h
        cases h with
        | fair_left _ _ _ _ hInner => exact ih.mpr hInner
  | fair_right bid left right residual state hChild ih =>
      constructor
      · intro h
        exact TypeAccepting.fair_right bid left right state (ih.mp h)
      · intro h
        cases h with
        | fair_right _ _ _ _ hInner => exact ih.mpr hInner
  | sequence_left_entry left right residual state hEntry hSelf ih =>
      exact ⟨fun h => absurd h (by simp), fun h => by cases h⟩
  | sequence_left_progressed left right residual state hChild hNotAcc ih =>
      exact ⟨fun h => absurd h (by simp), fun h => by cases h⟩
  | sequence_right left right residual state hChild ih =>
      constructor
      · intro h
        exact TypeAccepting.sequence_right left right state (ih.mp h)
      · intro h
        cases h with
        | sequence_right _ _ _ hInner => exact ih.mpr hInner
  | parallel left right leftResidual rightResidual interface leftState
      rightState hL hR hExcl ihL ihR =>
      constructor
      · intro h; exact absurd h (by simp)
      · intro h
        cases h with
        | parallel _ _ _ _ _ hAcceptL hAcceptR =>
            exact absurd ⟨ihL.mpr hAcceptL, ihR.mpr hAcceptR⟩ hExcl
  | parallel_fuse left right interface leftState rightState hL hR ihL ihR =>
      exact ⟨fun _ => TypeAccepting.parallel left right interface leftState
        rightState (ihL.mp rfl) (ihR.mp rfl), fun _ => rfl⟩
  | xoffer_source elseType branches =>
      exact ⟨fun h => absurd h (by simp), fun h => by cases h⟩
  | xoffer_else elseType residual branches state hChild ih =>
      constructor
      · intro h
        exact TypeAccepting.xoffer_else elseType branches state (ih.mp h)
      · intro h
        cases h with
        | xoffer_else _ _ _ hInner => exact ih.mpr hInner
  | xoffer_branch elseType branchType residual branches action index state
      hEntry hChild ih =>
      constructor
      · intro h
        exact TypeAccepting.xoffer_branch elseType branchType branches action
          index state hEntry (ih.mp h)
      · intro h
        cases h with
        | xoffer_branch _ branchType' _ action' _ _ hEntry' hInner =>
            have hSame : (action, branchType) = (action', branchType') := by
              rw [hEntry] at hEntry'
              exact Option.some.inj hEntry'
            have hBranchTypeEq : branchType' = branchType :=
              (congrArg Prod.snd hSame).symm
            subst hBranchTypeEq
            exact ih.mpr hInner
  | offer_source elseType branches =>
      exact ⟨fun h => absurd h (by simp), fun h => by cases h⟩
  | offer_branches elseType residual branches selected index state hEntry
      hChild ih =>
      constructor
      · intro h
        exact TypeAccepting.offer_branches elseType branches selected index
          state hEntry (ih.mp h)
      · intro h
        cases h with
        | offer_branches _ _ selected' _ _ hEntry' hInner =>
            have hSame : selected = selected' := by
              rw [hEntry] at hEntry'
              exact Option.some.inj hEntry'
            subst hSame
            exact ih.mpr hInner
  | offer_else elseType residual branches state hChild ih =>
      constructor
      · intro h
        exact TypeAccepting.offer_else elseType branches state (ih.mp h)
      · intro h
        cases h with
        | offer_else _ _ _ hInner => exact ih.mpr hInner

def CompilationStateCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  ∀ state residual,
    TypeCompilationRelation processType state residual →
      state ∈ (compileTypeFuel signature
        (typeCompilationFuel processType) processType).states

private theorem childState_mem_indexedFragmentStates
    (automata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : automata[index]? = some entry)
    (state : TypeAutomatonState) (hState : state ∈ entry.2.states) :
    childState (index + 1) state ∈ indexedFragmentStates automata := by
  classical
  rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
  have hZipBound : index < automata.zipIdx.length := by
    simpa using hBound
  have hIndexed : (entry, index) ∈ automata.zipIdx := by
    have hMember := List.getElem_mem hZipBound
    have hAt := List.getElem_zipIdx (l := automata) (i := index)
      (j := 0) hZipBound
    simp only [zero_add] at hAt
    rw [hAt, hValue] at hMember
    exact hMember
  rw [indexedFragmentStates, mem_foldl_union_iff]
  right
  refine ⟨(entry, index), hIndexed, ?_⟩
  simp [childStates, childState, hState]

/-- Every state named by `TypeCompilationRelation` belongs to the matching
sufficiently fuelled compiler fragment.  This carrier invariant is independent
of future semantics and is shared by every constructor embedding. -/
private theorem compileTypeFuel_relation_state_mem
    (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      ∀ state residual,
        TypeCompilationRelation processType state residual →
          state ∈ (compileTypeFuel signature fuel processType).states := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel state residual hRelated
      cases hRelated with
      | skip =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | message_source msg dir =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | message_final msg dir =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | cycle_source =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | cycle_final =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | progress_source pid =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | progress_final pid =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | «variable» name =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | recur_source name body =>
          simp [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment]
      | recur_body name body childResidual childQ hChildRelated =>
          have hBodyFuel : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih body hBodyFuel childQ childResidual
            hChildRelated
          simpa [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | choice_source left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment]
      | choice_left left right _ childQ hChildRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | choice_right left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | fair_source bid left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment]
      | fair_left bid left right _ childQ hChildRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | fair_right bid left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | sequence_left_entry left right residual stateL hEntry hSelfRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel stateL residual hSelfRelated
          have hStateEq : stateL =
              (compileTypeFuel signature fuel left).initial :=
            TypeEntry.unique hEntry
              (compileTypeFuel_initial_entry signature fuel left hLeftFuel)
          subst hStateEq
          rw [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment]
          simp only [Finset.mem_union, Finset.mem_image, Finset.mem_sdiff]
          exact Or.inl (Or.inl ⟨_, ⟨hChild, by simp⟩, rfl⟩)
      | sequence_left_progressed left right childResidual childQ
          hChildRelated hNotAccepting =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel childQ childResidual
            hChildRelated
          have hNotAcceptingConcrete : childQ ∉
              (compileTypeFuel signature fuel left).accepting := by
            rw [compileTypeFuel_accepting_iff signature fuel left hLeftFuel
              childQ childResidual hChildRelated]
            exact hNotAccepting
          rw [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment]
          simp only [Finset.mem_union, Finset.mem_image, Finset.mem_sdiff]
          exact Or.inl (Or.inl ⟨childQ, ⟨hChild,
            not_mem_sequenceDeleted_of_not_accepting hNotAcceptingConcrete⟩,
            rfl⟩)
      | sequence_right left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | parallel left right leftResidual rightResidual interface leftState
          rightState hLeftRelated hRightRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hLeft := ih left hLeftFuel leftState leftResidual hLeftRelated
          have hRight := ih right hRightFuel rightState rightResidual
            hRightRelated
          simp [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, hLeft, hRight]
      | parallel_fuse left right interface leftState rightState hLeftRelated
          hRightRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hLeft := ih left hLeftFuel leftState .skip hLeftRelated
          have hRight := ih right hRightFuel rightState .skip hRightRelated
          simp [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, hLeft, hRight]
      | xoffer_source elseType branches =>
          simp [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
      | xoffer_else elseType _ branches childQ hChildRelated =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih elseType hElseFuel childQ residual
            hChildRelated
          have hTagged : childState 0 childQ ∈
              childStates 0 (compileTypeFuel signature fuel elseType) := by
            exact Finset.mem_image.mpr ⟨childQ, hChild, rfl⟩
          rw [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
          change childState 0 childQ ∈
            ({TypeAutomatonState.root} ∪
              childStates 0 (compileTypeFuel signature fuel elseType)) ∪
                indexedFragmentStates
                  (branches.map fun branch =>
                    (branch.1, compileTypeFuel signature fuel branch.2))
          simp only [Finset.mem_union]
          exact Or.inl (Or.inr hTagged)
      | xoffer_branch elseType branchType _ branches action index
          childQ hEntry hChildRelated =>
          have hBranchesFuel : typeBranchCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hBranchMem : (action, branchType) ∈ branches := by
            rcases List.getElem?_eq_some_iff.mp hEntry with
              ⟨hBound, hValue⟩
            have hMember := List.getElem_mem hBound
            simpa [hValue] using hMember
          have hBranchFuel : TypeCompilationFuelSufficient branchType fuel :=
            le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                (action, branchType) hBranchMem)
              hBranchesFuel
          have hChild := ih branchType hBranchFuel childQ residual
            hChildRelated
          let branchAutomata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          have hAutomatonEntry : branchAutomata[index]? =
              some (action, compileTypeFuel signature fuel branchType) := by
            simp [branchAutomata, hEntry]
          have hIndexed := childState_mem_indexedFragmentStates branchAutomata
            index (action, compileTypeFuel signature fuel branchType)
            hAutomatonEntry childQ hChild
          rw [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
          change childState (index + 1) childQ ∈
            ({TypeAutomatonState.root} ∪
              childStates 0 (compileTypeFuel signature fuel elseType)) ∪
                indexedFragmentStates branchAutomata
          simp only [Finset.mem_union]
          exact Or.inr hIndexed
      | offer_source elseType branches =>
          simp [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment]
      | offer_branches elseType _ branches selected index childQ hEntry
          hChildRelated =>
          have hConjunctionFuel : TypeCompilationFuelSufficient
              (parallelTypeBranchesSelecting selected branches) fuel := by
            rw [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting]
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hChild := ih
            (parallelTypeBranchesSelecting selected branches) hConjunctionFuel
              childQ residual hChildRelated
          let selectedConjunctions := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting branch branches))
          have hAutomatonEntry : selectedConjunctions[index]? = some
              (selected.1, compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting selected branches)) := by
            simp [selectedConjunctions, hEntry]
          have hIndexed := childState_mem_indexedFragmentStates
            selectedConjunctions index
              (selected.1, compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting selected branches))
              hAutomatonEntry childQ hChild
          rw [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment]
          change childState (index + 1) childQ ∈
            ({TypeAutomatonState.root} ∪
              childStates 0 (compileTypeFuel signature fuel elseType)) ∪
                indexedFragmentStates selectedConjunctions
          simp only [Finset.mem_union]
          exact Or.inr hIndexed
      | offer_else elseType _ branches childQ hChildRelated =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih elseType hElseFuel childQ residual
            hChildRelated
          rw [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment]
          simp only [Finset.mem_union]
          exact Or.inl (by
            simp [childStates, childState, hChild])

theorem compilationStateCorrect_of_compilation
    (signature : TypeAlphabet) (processType : PactType) :
    CompilationStateCorrect signature processType := by
  exact compileTypeFuel_relation_state_mem signature
    (typeCompilationFuel processType) processType
    (typeCompilationFuel_sufficient processType)

/-- Graph future resolution agrees with syntactic same-cycle future offers at
every state/residual represented by the final pending compilation fragment. -/
def CompilationFutureCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  processType.EntryCanonical →
  ∀ state residual,
    TypeCompilationRelation processType state residual →
      computeFuture pending state = typeFutureOffers residual

/-- Every visible resolved edge leaving a represented constructor state reaches
another state represented by the same compiled syntax.  Temporary variable
markers and construction-only future observations are excluded by
`HasResolvedEdge`, whose label is necessarily visible. -/
def CompilationResolvedEdgeTargetsRelated
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ {source : TypeAutomatonState} {residual : PactType}
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary} {target : TypeAutomatonState},
    TypeCompilationRelation processType source residual →
    fragment.HasResolvedEdge signature processType source environment label offers
      target →
    ∃ targetResidual,
      TypeCompilationRelation processType target targetResidual

/-- Every semantic pending compiler edge has consumed its temporary recursion
marker.  Construction-only `.future` observations are intentionally exempt;
they are used by optimistic future computation and never become type steps. -/
def CompilationPendingEdgesVisible
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ edge ∈ fragment.edges, edge.label ≠ .future →
    ∃ label, edge.label = .visible label

/-- The reusable `stepIff` property for the concrete compiler relation. -/
def CompilationStepCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  ∀ {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    TypeCompilationRelation processType state residual →
    TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature processType).alphabet →
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType signature processType).HasEdge state env label offers
          state' ∧
        TypeCompilationRelation processType state' residual')

/-- The constructor metadata used only for optimistic future propagation is
exactly the syntax predicate saying that the represented residual may finish
before the next clock. -/
def CompilationCompletingCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  ∀ state residual,
    TypeCompilationRelation processType state residual →
      (state ∈ (compileTypeFuel signature
          (typeCompilationFuel processType) processType).completing ↔
        residual.CanCompleteBeforeTock = true)

theorem compilationCompletingCorrect_skip (signature : TypeAlphabet) :
    CompilationCompletingCorrect signature .skip := by
  intro state residual hRelated
  cases hRelated
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    PactType.CanCompleteBeforeTock]

theorem compilationCompletingCorrect_message
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CompilationCompletingCorrect signature (.message msg dir) := by
  intro state residual hRelated
  cases hRelated <;>
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      PactType.CanCompleteBeforeTock]

theorem compilationCompletingCorrect_tock (signature : TypeAlphabet) :
    CompilationCompletingCorrect signature .tock := by
  intro state residual hRelated
  cases hRelated <;>
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      PactType.CanCompleteBeforeTock]

theorem compilationCompletingCorrect_progress
    (signature : TypeAlphabet) (pid : ProcId) :
    CompilationCompletingCorrect signature (.progress pid) := by
  intro state residual hRelated
  cases hRelated <;>
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      PactType.CanCompleteBeforeTock]

theorem compilationCompletingCorrect_var
    (signature : TypeAlphabet) (name : String) :
    CompilationCompletingCorrect signature (.var name) := by
  intro state residual hRelated
  cases hRelated
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    PactType.CanCompleteBeforeTock]

/-- The raw constructor-fragment form of step correspondence.  It is the
compositional interface used before the public alphabet filter is applied. -/
def CompilationFragmentStepCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  processType.EntryCanonical →
  ∀ {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    TypeCompilationRelation processType state residual →
    env ∈ signature.localEnvironments →
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        fragment.HasResolvedEdge signature processType state env label offers
          state' ∧
        TypeCompilationRelation processType state' residual')

private theorem computeFuture_eq_empty_of_edges_empty
    (automaton : PendingAutomaton)
    (hEmpty : ∀ edge ∈ automaton.edges,
      edge.current = ∅ ∧ edge.future = .explicit ∅)
    (state : TypeAutomatonState) :
    computeFuture automaton state = ∅ := by
  have hExplicit : ∀ edge ∈ automaton.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    exact ⟨∅, (hEmpty edge hEdge).2⟩
  rw [computeFuture_eq_offersAt_of_all_explicit automaton hExplicit]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro action hAction
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter] at hAction
  rcases hAction with ⟨edge, ⟨hEdge, _⟩, hOffer⟩
  obtain ⟨hCurrent, hFuture⟩ := hEmpty edge hEdge
  simp [hCurrent, hFuture] at hOffer

/-- Future correctness for `skip`. -/
theorem compilationFutureCorrect_skip (signature : TypeAlphabet) :
    CompilationFutureCorrect signature .skip := by
  intro _ state residual hRelated
  cases hRelated
  let fragment := compileTypeFuel signature (typeCompilationFuel .skip) .skip
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  change computeFuture pending .root = typeFutureOffers .skip
  rw [computeFuture_eq_offersAt_of_all_explicit pending]
  · ext action
    simp [pending, fragment, PendingAutomaton.offersAt,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      typeFutureOffers, typeFutureOffersFuel]
  · intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with ⟨_, _, rfl⟩
    exact ⟨∅, rfl⟩

/-- Future correctness for an atomic progress marker. -/
theorem compilationFutureCorrect_progress
    (signature : TypeAlphabet) (pid : ProcId) :
    CompilationFutureCorrect signature (.progress pid) := by
  intro _
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.progress pid)) (.progress pid)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hEmpty : ∀ state, computeFuture pending state = ∅ := by
    intro state
    apply computeFuture_eq_empty_of_edges_empty pending
    intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with hAction | hFinal
    · rcases hAction with ⟨_, _, rfl⟩
      exact ⟨rfl, rfl⟩
    · rcases hFinal with ⟨_, _, rfl⟩
      exact ⟨rfl, rfl⟩
  intro state residual hRelated
  change computeFuture pending state = typeFutureOffers residual
  cases hRelated <;>
    simpa [typeFutureOffers, typeFutureOffersFuel] using hEmpty _

/-- Future correctness for the clock constructor. -/
theorem compilationFutureCorrect_tock (signature : TypeAlphabet) :
    CompilationFutureCorrect signature .tock := by
  intro _
  let fragment := compileTypeFuel signature
    (typeCompilationFuel .tock) .tock
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hEmpty : ∀ state, computeFuture pending state = ∅ := by
    intro state
    apply computeFuture_eq_empty_of_edges_empty pending
    intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with hAction | hFinal
    · rcases hAction with ⟨environment, _, rfl⟩
      by_cases hClock : environment.clock = true <;>
        simp [hClock]
    · rcases hFinal with ⟨_, _, rfl⟩
      exact ⟨rfl, rfl⟩
  intro state residual hRelated
  change computeFuture pending state = typeFutureOffers residual
  cases hRelated <;>
    simpa [typeFutureOffers, typeFutureOffersFuel] using hEmpty _

/-- Future correctness for an atomic message. -/
theorem compilationFutureCorrect_message
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CompilationFutureCorrect signature (.message msg dir) := by
  intro _
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.message msg dir)) (.message msg dir)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hExplicit : ∀ edge ∈ pending.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with hFiring | hWaiting | hFinal
    · rcases hFiring with ⟨_, _, rfl⟩
      exact ⟨∅, rfl⟩
    · rcases hWaiting with ⟨_, _, rfl⟩
      exact ⟨∅, rfl⟩
    · rcases hFinal with ⟨_, _, rfl⟩
      exact ⟨∅, rfl⟩
  intro state residual hRelated
  change computeFuture pending state = typeFutureOffers residual
  rw [computeFuture_eq_offersAt_of_all_explicit pending hExplicit]
  cases hRelated with
  | message_source =>
      ext action
      constructor
      · intro hAction
        simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
          Finset.mem_filter] at hAction
        rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
        simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment] at hEdge
        rcases hEdge with hFiring | hWaiting | hFinal
        · rcases hFiring with ⟨_, _, rfl⟩
          simpa using hOffer
        · rcases hWaiting with ⟨_, _, rfl⟩
          simpa using hOffer
        · rcases hFinal with ⟨_, _, rfl⟩
          simp at hSource
      · intro hAction
        simp only [typeFutureOffers, typeFutureOffersFuel,
          Finset.mem_singleton] at hAction
        subst action
        simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
          Finset.mem_filter]
        let emptyEdge : PendingAutomatonEdge :=
          { source := .root
            environment := TypeEnvironment.empty
            label := .visible TypeLabel.silent
            current := {(msg, dir)}
            future := .explicit ∅
            target := .root }
        refine ⟨emptyEdge, ?_, ?_⟩
        · constructor
          · simp [pending, fragment, emptyEdge, typeCompilationFuel,
              compileTypeFuel, finishAutomatonFragment,
              TypeAlphabet.localEnvironments,
              TypeAlphabet.localEnvironmentActions,
              TypeEnvironment.empty, TypeEnvironment.hasNeed]
          · rfl
        · simp [emptyEdge, AutomatonConstructionLabel.semantic,
            TypeLabel.silent]
  | message_final =>
      change pending.offersAt .final = ∅
      rw [Finset.eq_empty_iff_forall_notMem]
      intro action hAction
      simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
        Finset.mem_filter] at hAction
      rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
      simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment] at hEdge
      rcases hEdge with hFiring | hWaiting | hFinal
      · rcases hFiring with ⟨_, _, rfl⟩
        simp at hSource
      · rcases hWaiting with ⟨_, _, rfl⟩
        simp at hSource
      · rcases hFinal with ⟨_, _, rfl⟩
        simp at hOffer

/-- Future correctness for a free-variable marker fragment. -/
theorem compilationFutureCorrect_var
    (signature : TypeAlphabet) (name : String) :
    CompilationFutureCorrect signature (.var name) := by
  intro _ state residual hRelated
  cases hRelated
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.var name)) (.var name)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  change computeFuture pending .root = typeFutureOffers (.var name)
  rw [computeFuture_eq_offersAt_of_all_explicit pending]
  · ext action
    simp [pending, fragment, PendingAutomaton.offersAt,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      typeFutureOffers, typeFutureOffersFuel]
  · intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with ⟨_, _, rfl⟩
    exact ⟨∅, rfl⟩

/-! ### Parallel environment reconstruction -/

namespace TypeEnvironment

/-- An environment does not mention messages hidden by a parallel interface. -/
def AvoidsInterface (environment : TypeEnvironment)
    (interface : Interface) : Prop :=
  (∀ action ∈ environment.immediate, action.1 ∉ interface) ∧
    ∀ action ∈ environment.future, action.1 ∉ interface

theorem AvoidsInterface.mono
    {environment : TypeEnvironment} {larger smaller : Interface}
    (hAvoids : environment.AvoidsInterface larger)
    (hSubset : smaller ⊆ larger) :
    environment.AvoidsInterface smaller := by
  exact ⟨fun action hAction hSmaller =>
      hAvoids.1 action hAction (hSubset hSmaller),
    fun action hAction hSmaller =>
      hAvoids.2 action hAction (hSubset hSmaller)⟩

theorem tock_avoidsInterface (interface : Interface) :
    TypeEnvironment.tock.AvoidsInterface interface := by
  simp [AvoidsInterface, TypeEnvironment.tock]

end TypeEnvironment

/-- Passing through a sibling-local environment may add only actions from the
parent interface, so avoidance of a disjoint descendant interface is
preserved. -/
theorem LocalTypeEnvironment.avoidsInterface_of_disjoint
    {outer siblingEnvironment localEnvironment : TypeEnvironment}
    {parentInterface childInterface : Interface}
    {sibling : PactType} {label : TypeLabel}
    (hLocal : LocalTypeEnvironment outer parentInterface siblingEnvironment
      sibling label localEnvironment)
    (hOuterAvoids : outer.AvoidsInterface childInterface)
    (hDisjoint : Disjoint parentInterface childInterface) :
    localEnvironment.AvoidsInterface childInterface := by
  cases hLocal with
  | clock outer parentInterface sibling label hClock =>
      exact TypeEnvironment.tock_avoidsInterface childInterface
  | ordinary outer siblingEnvironment localEnvironment parentInterface sibling
      siblingTarget label current future hOuterClock hSiblingClock hOffers
      hLocalClock hImmediate hFuture =>
      constructor
      · intro action hAction hChild
        rw [hImmediate] at hAction
        rcases Finset.mem_union.mp hAction with hOuter | hParent
        · exact hOuterAvoids.1 action hOuter hChild
        · exact Finset.disjoint_left.mp hDisjoint
            (Finset.mem_filter.mp hParent).2 hChild
      · intro action hAction hChild
        rw [hFuture] at hAction
        rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hAction).1 with
          hOuter | hParent
        · exact hOuterAvoids.2 action hOuter hChild
        · exact Finset.disjoint_left.mp hDisjoint
            (Finset.mem_filter.mp hParent).2 hChild

theorem TypeEnvironment.avoidsInterface_of_ordinary_fields
    {outer localEnvironment : TypeEnvironment}
    {parentInterface childInterface : Interface}
    {current future : Finset BareMessage}
    (hOuterAvoids : outer.AvoidsInterface childInterface)
    (hDisjoint : Disjoint parentInterface childInterface)
    (hImmediate : localEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers parentInterface current)
    (hFuture : localEnvironment.future =
      (outer.future ∪ restrictTypeOffers parentInterface future) \
        localEnvironment.immediate) :
    localEnvironment.AvoidsInterface childInterface := by
  constructor
  · intro action hAction hChild
    rw [hImmediate] at hAction
    rcases Finset.mem_union.mp hAction with hOuter | hParent
    · exact hOuterAvoids.1 action hOuter hChild
    · exact Finset.disjoint_left.mp hDisjoint
        (Finset.mem_filter.mp hParent).2 hChild
  · intro action hAction hChild
    rw [hFuture] at hAction
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hAction).1 with
      hOuter | hParent
    · exact hOuterAvoids.2 action hOuter hChild
    · exact Finset.disjoint_left.mp hDisjoint
        (Finset.mem_filter.mp hParent).2 hChild

/-- Induction-facing raw correspondence.  Enclosing synchronized products may
supply local environments, provided those environments avoid every parallel
interface nested below the syntax node. -/
def CompilationScopedFragmentStepCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  processType.EntryCanonical →
  ∀ {residual residual' : PactType} {state : TypeAutomatonState}
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary},
    TypeCompilationRelation processType state residual →
    environment ∈ signature.localEnvironments →
    environment.AvoidsInterface processType.ParallelInterfaces →
    (DecoratedTypeTransition environment residual label offers residual' ↔
      ∃ target,
        fragment.HasResolvedEdge signature processType state environment label
          offers target ∧
        TypeCompilationRelation processType target residual')

/-- A free-variable marker has neither a semantic transition nor a resolved
edge: `TypeTransition` has no `.var` case, and every compiled `.var` edge is
labelled `.variable name`, never `.visible _`. -/
theorem compilationScopedFragmentStepCorrect_var
    (signature : TypeAlphabet) (name : String) :
    CompilationScopedFragmentStepCorrect signature (.var name) := by
  intro _ residual residual' state environment label offers hRelated hLocal
    hAvoids
  cases hRelated
  constructor
  · intro hStep
    cases hStep.1
  · rintro ⟨target, hEdge, _⟩
    exfalso
    simp only [AutomatonFragment.HasResolvedEdge, typeCompilationFuel,
      compileTypeFuel, finishAutomatonFragment, Finset.mem_image] at hEdge
    obtain ⟨edge, ⟨environment', _, rfl⟩, _, _, hLabel, _⟩ := hEdge
    simp at hLabel

/-- A synchronization witness selected independently of the product's actual
child target is represented by a semantic offer derivation at the same related
source. -/
def CompilationScopedResolvedOfferWitnessCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ {residual : PactType} {state : TypeAutomatonState}
    {environment : TypeEnvironment} {label : TypeLabel}
    {actualOffers : TypeOfferSummary} {actualTarget : TypeAutomatonState},
    TypeCompilationRelation processType state residual →
    environment ∈ signature.localEnvironments →
    environment.AvoidsInterface processType.ParallelInterfaces →
    fragment.HasResolvedEdge signature processType state environment label
      actualOffers
      actualTarget →
    ∀ witness ∈ resolvedAutomatonEdges fragment,
      witness.label ≠ .future →
      witness.source = state →
      witness.environment = environment →
      witness.label.semantic = label →
      ∃ target,
        TypeOffers environment residual label target witness.current
          witness.future

namespace TypeAlphabet

/-- Construction-local environments satisfy the same clock/disjointness
invariant as exported environments. -/
theorem localEnvironment_wellFormed {alphabet : TypeAlphabet}
    {environment : TypeEnvironment}
    (hEnvironment : environment ∈ alphabet.localEnvironments) :
    environment.WellFormed := by
  simp only [localEnvironments, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
    at hEnvironment
  rcases hEnvironment with rfl | ⟨immediate, _, future, hFuture, rfl⟩
  · simp [TypeEnvironment.WellFormed, TypeEnvironment.tock]
  · constructor
    · simp
    · intro _
      change immediate ∩ future = ∅
      rw [← Finset.disjoint_iff_inter_eq_empty]
      apply Finset.disjoint_left.mpr
      intro action hImmediate hFutureMember
      exact (Finset.mem_sdiff.mp (hFuture hFutureMember)).2 hImmediate

/-- A construction-local clock environment is exactly the distinguished
clock environment. -/
theorem localEnvironment_eq_tock_of_clock
    {alphabet : TypeAlphabet} {environment : TypeEnvironment}
    (hEnvironment : environment ∈ alphabet.localEnvironments)
    (hClock : environment.clock = true) :
    environment = TypeEnvironment.tock := by
  have hWellFormed := localEnvironment_wellFormed hEnvironment
  rcases hWellFormed.1 hClock with ⟨hImmediate, hFuture⟩
  cases environment
  simp_all [TypeEnvironment.tock]

/-- The future half of an exported environment cannot mention an internal
message identifier. -/
theorem environment_future_avoids_interface
    {alphabet : TypeAlphabet} {environment : TypeEnvironment}
    (hAlphabet : alphabet.WellFormed)
    (hEnvironment : environment ∈ alphabet.environments) :
    ∀ action ∈ environment.future,
      action.1 ∉ alphabet.interface := by
  simp only [environments, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
    at hEnvironment
  rcases hEnvironment with rfl | ⟨immediate, _, future, hFuture, rfl⟩
  · simp [TypeEnvironment.tock]
  · intro action hAction hInterface
    have hEnvironmentAction := (Finset.mem_sdiff.mp (hFuture hAction)).1
    simp only [environmentActions, Finset.mem_image] at hEnvironmentAction
    rcases hEnvironmentAction with ⟨boundaryAction, hBoundary, hNeed⟩
    apply hAlphabet boundaryAction hBoundary
    have hMessage := congrArg Prod.fst hNeed
    simp only [typeNeed] at hMessage
    rw [hMessage]
    exact hInterface

/-- Every exported environment avoids a declared sub-interface. -/
theorem environment_avoids_subinterface
    {alphabet : TypeAlphabet} {environment : TypeEnvironment}
    {interface : Interface}
    (hAlphabet : alphabet.WellFormed)
    (hEnvironment : environment ∈ alphabet.environments)
    (hInterface : interface ⊆ alphabet.interface) :
    environment.AvoidsInterface interface := by
  constructor
  · intro action hAction hInternal
    exact environment_immediate_avoids_interface hAlphabet hEnvironment
      action hAction (hInterface hInternal)
  · intro action hAction hInternal
    exact environment_future_avoids_interface hAlphabet hEnvironment
      action hAction (hInterface hInternal)

end TypeAlphabet

private theorem hideOffers_partition (interface : Interface)
    (offers : Finset BareMessage) :
    hideOffers interface offers ∪ interfaceOffers interface offers = offers := by
  ext action
  simp [hideOffers, interfaceOffers]
  tauto

private theorem hideOffers_disjoint_interfaceOffers (interface : Interface)
    (offers : Finset BareMessage) :
    Disjoint (hideOffers interface offers) (interfaceOffers interface offers) := by
  rw [Finset.disjoint_left]
  intro action hHidden hInterface
  exact (Finset.mem_filter.mp hHidden).2
    (Finset.mem_filter.mp hInterface).2

private theorem finset_eq_of_hideOffers_eq_of_interfaceOffers_eq
    (interface : Interface) {left right : Finset BareMessage}
    (hHidden : hideOffers interface left = hideOffers interface right)
    (hInterface : interfaceOffers interface left =
      interfaceOffers interface right) :
    left = right := by
  rw [← hideOffers_partition interface left,
    ← hideOffers_partition interface right, hHidden, hInterface]

private theorem hideOffers_union (interface : Interface)
    (left right : Finset BareMessage) :
    hideOffers interface (left ∪ right) =
      hideOffers interface left ∪ hideOffers interface right := by
  ext action
  simp [hideOffers]
  tauto

private theorem interfaceOffers_union (interface : Interface)
    (left right : Finset BareMessage) :
    interfaceOffers interface (left ∪ right) =
      interfaceOffers interface left ∪ interfaceOffers interface right := by
  ext action
  simp [interfaceOffers]
  tauto

private theorem hideOffers_restrictTypeOffers (interface : Interface)
    (offers : Finset BareMessage) :
    hideOffers interface (restrictTypeOffers interface offers) = ∅ := by
  ext action
  simp [hideOffers, restrictTypeOffers]

private theorem interfaceOffers_restrictTypeOffers (interface : Interface)
    (offers : Finset BareMessage) :
    interfaceOffers interface (restrictTypeOffers interface offers) =
      restrictTypeOffers interface offers := by
  ext action
  simp [interfaceOffers, restrictTypeOffers]

private theorem hideOffers_sdiff (interface : Interface)
    (left right : Finset BareMessage) :
    hideOffers interface (left \ right) =
      hideOffers interface left \ hideOffers interface right := by
  ext action
  simp [hideOffers]
  tauto

private theorem interfaceOffers_sdiff (interface : Interface)
    (left right : Finset BareMessage) :
    interfaceOffers interface (left \ right) =
      interfaceOffers interface left \ interfaceOffers interface right := by
  ext action
  simp [interfaceOffers]
  tauto

private theorem finset_sdiff_eq_self_of_disjoint {left right : Finset BareMessage}
    (hDisjoint : Disjoint left right) : left \ right = left := by
  ext action
  simp only [Finset.mem_sdiff]
  constructor
  · exact fun h => h.1
  · intro hLeft
    exact ⟨hLeft, fun hRight => Finset.disjoint_left.mp hDisjoint hLeft hRight⟩

private theorem hideOffers_eq_self_of_avoids
    (interface : Interface) (offers : Finset BareMessage)
    (hAvoids : ∀ action ∈ offers, action.1 ∉ interface) :
    hideOffers interface offers = offers := by
  ext action
  constructor
  · exact fun h => (Finset.mem_filter.mp h).1
  · intro hAction
    exact Finset.mem_filter.mpr ⟨hAction, hAvoids action hAction⟩

private theorem interfaceOffers_eq_empty_of_avoids
    (interface : Interface) (offers : Finset BareMessage)
    (hAvoids : ∀ action ∈ offers, action.1 ∉ interface) :
    interfaceOffers interface offers = ∅ := by
  ext action
  simp only [interfaceOffers, Finset.mem_filter]
  constructor
  · rintro ⟨hOffers, hInterface⟩
    exact (hAvoids action hOffers hInterface).elim
  · intro hEmpty
    simpa using hEmpty

/- The exact ordinary local-environment equations reconstruct the original
outer environment after hiding the interface.  No offer-summary disjointness
is needed: the semantic future subtraction is retained verbatim. -/
/-- The product environment reconstruction uses only well-formedness and
avoidance of the current interface; exportedness is one sufficient way to
obtain those facts, but nested products use this more general form. -/
private theorem combineAutomatonEnvironment_eq_of_ordinaryLocalFields_of_avoids
    (interface : Interface)
    {outer leftEnvironment rightEnvironment : TypeEnvironment}
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    (hOuterWellFormed : outer.WellFormed)
    (hOuterAvoids : outer.AvoidsInterface interface)
    (hOuterClock : outer.clock = false)
    (hLeftClock : leftEnvironment.clock = false)
    (hRightClock : rightEnvironment.clock = false)
    (hLeftImmediate : leftEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface rightCurrent)
    (hLeftFuture : leftEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface rightFuture) \
        leftEnvironment.immediate)
    (hRightImmediate : rightEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface leftCurrent)
    (hRightFuture : rightEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface leftFuture) \
        rightEnvironment.immediate) :
    combineAutomatonEnvironment interface leftEnvironment rightEnvironment =
      outer := by
  have hOuterDisjoint : Disjoint outer.future outer.immediate := by
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm]
    exact hOuterWellFormed.2 hOuterClock
  have hHideOuterImmediate :=
    hideOffers_eq_self_of_avoids interface outer.immediate hOuterAvoids.1
  have hHideOuterFuture :=
    hideOffers_eq_self_of_avoids interface outer.future hOuterAvoids.2
  have hHideLeftImmediate :
      hideOffers interface leftEnvironment.immediate = outer.immediate := by
    rw [hLeftImmediate, hideOffers_union, hHideOuterImmediate,
      hideOffers_restrictTypeOffers, Finset.union_empty]
  have hHideRightImmediate :
      hideOffers interface rightEnvironment.immediate = outer.immediate := by
    rw [hRightImmediate, hideOffers_union, hHideOuterImmediate,
      hideOffers_restrictTypeOffers, Finset.union_empty]
  have hHideLeftFuture :
      hideOffers interface leftEnvironment.future = outer.future := by
    rw [hLeftFuture, hideOffers_sdiff, hideOffers_union, hHideOuterFuture,
      hideOffers_restrictTypeOffers, Finset.union_empty, hHideLeftImmediate]
    exact finset_sdiff_eq_self_of_disjoint hOuterDisjoint
  have hHideRightFuture :
      hideOffers interface rightEnvironment.future = outer.future := by
    rw [hRightFuture, hideOffers_sdiff, hideOffers_union, hHideOuterFuture,
      hideOffers_restrictTypeOffers, Finset.union_empty, hHideRightImmediate]
    exact finset_sdiff_eq_self_of_disjoint hOuterDisjoint
  have hCombinedImmediate :
        hideOffers interface
            (leftEnvironment.immediate ∪ rightEnvironment.immediate) =
          outer.immediate := by
    rw [hideOffers_union, hHideLeftImmediate, hHideRightImmediate,
      Finset.union_self]
  have hCombinedFuture :
        hideOffers interface
            (leftEnvironment.future ∪ rightEnvironment.future) =
          outer.future := by
    rw [hideOffers_union, hHideLeftFuture, hHideRightFuture,
      Finset.union_self]
  cases outer with
  | mk immediate future clock =>
      cases clock
      · simp [combineAutomatonEnvironment, hLeftClock, hRightClock,
          hCombinedImmediate, hCombinedFuture]
      · simp at hOuterClock

/-- The exact ordinary local-environment equations reconstruct the original
outer environment after hiding the interface.  No offer-summary disjointness
is needed: the semantic future subtraction is retained verbatim. -/

private theorem combineAutomatonEnvironment_eq_of_ordinaryLocalFields
    (signature : TypeAlphabet) (interface : Interface)
    {outer leftEnvironment rightEnvironment : TypeEnvironment}
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    (hAlphabet : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hOuterEnvironment : outer ∈ signature.environments)
    (hOuterClock : outer.clock = false)
    (hLeftClock : leftEnvironment.clock = false)
    (hRightClock : rightEnvironment.clock = false)
    (hLeftImmediate : leftEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface rightCurrent)
    (hLeftFuture : leftEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface rightFuture) \
        leftEnvironment.immediate)
    (hRightImmediate : rightEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface leftCurrent)
    (hRightFuture : rightEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface leftFuture) \
        rightEnvironment.immediate) :
    combineAutomatonEnvironment interface leftEnvironment rightEnvironment =
      outer := by
  have hOuterWellFormed :=
    TypeAlphabet.environment_wellFormed hOuterEnvironment
  have hOuterDisjoint : Disjoint outer.future outer.immediate := by
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm]
    exact hOuterWellFormed.2 hOuterClock
  have hImmediateAvoids :
      ∀ action ∈ outer.immediate, action.1 ∉ interface := by
    intro action hAction hInternal
    exact TypeAlphabet.environment_immediate_avoids_interface
      hAlphabet hOuterEnvironment action hAction (hInterface hInternal)
  have hFutureAvoids :
      ∀ action ∈ outer.future, action.1 ∉ interface := by
    intro action hAction hInternal
    exact TypeAlphabet.environment_future_avoids_interface
      hAlphabet hOuterEnvironment action hAction (hInterface hInternal)
  have hHideOuterImmediate :=
    hideOffers_eq_self_of_avoids interface outer.immediate hImmediateAvoids
  have hInterfaceOuterImmediate :=
    interfaceOffers_eq_empty_of_avoids interface outer.immediate hImmediateAvoids
  have hHideOuterFuture :=
    hideOffers_eq_self_of_avoids interface outer.future hFutureAvoids
  have hHideLeftImmediate :
      hideOffers interface leftEnvironment.immediate = outer.immediate := by
    rw [hLeftImmediate, hideOffers_union, hHideOuterImmediate,
      hideOffers_restrictTypeOffers, Finset.union_empty]
  have hHideRightImmediate :
      hideOffers interface rightEnvironment.immediate = outer.immediate := by
    rw [hRightImmediate, hideOffers_union, hHideOuterImmediate,
      hideOffers_restrictTypeOffers, Finset.union_empty]
  have hHideLeftFuture :
      hideOffers interface leftEnvironment.future = outer.future := by
    rw [hLeftFuture, hideOffers_sdiff, hideOffers_union, hHideOuterFuture,
      hideOffers_restrictTypeOffers, Finset.union_empty, hHideLeftImmediate]
    exact finset_sdiff_eq_self_of_disjoint hOuterDisjoint
  have hHideRightFuture :
      hideOffers interface rightEnvironment.future = outer.future := by
    rw [hRightFuture, hideOffers_sdiff, hideOffers_union, hHideOuterFuture,
      hideOffers_restrictTypeOffers, Finset.union_empty, hHideRightImmediate]
    exact finset_sdiff_eq_self_of_disjoint hOuterDisjoint
  have hCombinedImmediate :
        hideOffers interface
            (leftEnvironment.immediate ∪ rightEnvironment.immediate) =
          outer.immediate := by
    rw [hideOffers_union, hHideLeftImmediate, hHideRightImmediate,
      Finset.union_self]
  have hCombinedFuture :
        hideOffers interface
            (leftEnvironment.future ∪ rightEnvironment.future) =
          outer.future := by
    rw [hideOffers_union, hHideLeftFuture, hHideRightFuture,
      Finset.union_self]
  cases outer with
  | mk immediate future clock =>
      cases clock
      · simp [combineAutomatonEnvironment, hLeftClock, hRightClock,
          hCombinedImmediate, hCombinedFuture]
      · simp at hOuterClock

/-- Elimination form of `LocalTypeEnvironment` exposing the exact ordinary
environment equations without losing the clock alternative. -/
private theorem LocalTypeEnvironment.clock_or_ordinary
    {outer siblingEnvironment localEnvironment : TypeEnvironment}
    {interface : Interface} {sibling : PactType} {label : TypeLabel}
    (hLocal : LocalTypeEnvironment outer interface siblingEnvironment sibling
      label localEnvironment) :
    (outer.clock = true ∧
        siblingEnvironment = TypeEnvironment.tock ∧
        localEnvironment = TypeEnvironment.tock) ∨
      ∃ siblingTarget current future,
        outer.clock = false ∧
        siblingEnvironment.clock = false ∧
        TypeOffers siblingEnvironment sibling label siblingTarget
          current future ∧
        localEnvironment.clock = false ∧
        localEnvironment.immediate =
          outer.immediate ∪ restrictTypeOffers interface current ∧
        localEnvironment.future =
          (outer.future ∪ restrictTypeOffers interface future) \
            localEnvironment.immediate := by
  cases hLocal with
  | clock outer interface sibling label hClock =>
      exact Or.inl ⟨hClock, rfl, rfl⟩
  | ordinary outer siblingEnvironment localEnvironment interface sibling
      siblingTarget label current future hOuterClock hSiblingClock hOffers
      hLocalClock hImmediate hFuture =>
      exact Or.inr ⟨siblingTarget, current, future, hOuterClock,
        hSiblingClock, hOffers, hLocalClock, hImmediate, hFuture⟩

/-- Regression: the current syntactic linearity check does not yet imply
disjoint current/future decorations.  An `offer` may expose a branch head as
current while its else continuation immediately re-offers the same message. -/
theorem sameCycleMessageLinear_offer_else_current_future_overlap :
    let action : BareMessage := ("same", .send)
    let elseType : PactType := .message action.1 action.2
    let processType : PactType := .offer elseType [(action, .skip)]
    processType.SameCycleMessageLinear ∧
      TypeOffers TypeEnvironment.empty processType TypeLabel.silent elseType
        {action} {action} ∧
      ¬ Disjoint ({action} : Finset BareMessage) {action} := by
  dsimp
  constructor
  · simp [PactType.SameCycleMessageLinear,
      PactType.SameCycleMessageLinearBranches, PactType.PrefixMessageIds]
  · constructor
    · have hOffers := TypeOffers.offer_else TypeEnvironment.empty
          (.message "same" .send) [(("same", .send), .skip)] (by
            simp [TypeEnvironment.empty, TypeEnvironment.WellFormed,
              TypeNoImmediateBranch, TypeResolved, typeBranchNeeds, typeNeed])
      simpa [typeBranchActions, typeFutureOffers, typeFutureOffersFuel] using
        hOffers
    · intro hDisjoint
      have hMember : (("same", .send) : BareMessage) ∈
          ({("same", .send)} : Finset BareMessage) := by simp
      exact Finset.disjoint_left.mp hDisjoint hMember hMember

/-- Every operational offer decoration is an exact decomposition of the
syntax-derived future menu of its target, modulo offers already current on the
edge.  This theorem is intentionally syntax-side: constructor automata use it
only to justify following an execution target when placed under sequencing. -/
theorem TypeOffers.current_union_future_eq_targetFuture :
    ∀ source environment target label current future,
      TypeOffers environment source label target current future →
        current ∪ future = current ∪ typeFutureOffers target := by
  intro source
  induction hSize : sizeOf source using Nat.strong_induction_on
      generalizing source with
  | h n ih =>
      intro environment target label current future hOffers
      cases source with
      | par left right interface =>
          cases hOffers with
          | par outer leftEnvironment rightEnvironment interface left
              leftTarget right rightTarget leftLabel rightLabel leftCurrent
              leftFuture rightCurrent rightFuture hLeftOffers hRightOffers
              _ _ _ =>
              have hLeft := ih (sizeOf left) (by
                rw [← hSize]
                simp_wf
                omega) left rfl _ _ _ _ _ hLeftOffers
              have hRight := ih (sizeOf right) (by
                rw [← hSize]
                simp_wf
                omega) right rfl _ _ _ _ _ hRightOffers
              rw [typeFutureOffers_parallel]
              ext action
              simp only [hideTypeOffers, Finset.mem_filter,
                Finset.mem_union]
              constructor
              · rintro (⟨hCurrent, hOutside⟩ | ⟨hFuture, hOutside⟩)
                · exact Or.inl ⟨hCurrent, hOutside⟩
                · rcases hFuture with hLeftFuture | hRightFuture
                  · have hMember : action ∈ leftCurrent ∪
                        typeFutureOffers leftTarget := by
                      rw [← hLeft]
                      exact Finset.mem_union_right _ hLeftFuture
                    rcases Finset.mem_union.mp hMember with hCurrent | hTarget
                    · exact Or.inl ⟨Or.inl hCurrent, hOutside⟩
                    · exact Or.inr ⟨Or.inl hTarget, hOutside⟩
                  · have hMember : action ∈ rightCurrent ∪
                        typeFutureOffers rightTarget := by
                      rw [← hRight]
                      exact Finset.mem_union_right _ hRightFuture
                    rcases Finset.mem_union.mp hMember with hCurrent | hTarget
                    · exact Or.inl ⟨Or.inr hCurrent, hOutside⟩
                    · exact Or.inr ⟨Or.inr hTarget, hOutside⟩
              · rintro (⟨hCurrent, hOutside⟩ | ⟨hTarget, hOutside⟩)
                · exact Or.inl ⟨hCurrent, hOutside⟩
                · rcases hTarget with hLeftTarget | hRightTarget
                  · have hMember : action ∈ leftCurrent ∪ leftFuture := by
                      rw [hLeft]
                      exact Finset.mem_union_right _ hLeftTarget
                    rcases Finset.mem_union.mp hMember with hCurrent | hFuture
                    · exact Or.inl ⟨Or.inl hCurrent, hOutside⟩
                    · exact Or.inr ⟨Or.inl hFuture, hOutside⟩
                  · have hMember : action ∈ rightCurrent ∪ rightFuture := by
                      rw [hRight]
                      exact Finset.mem_union_right _ hRightTarget
                    rcases Finset.mem_union.mp hMember with hCurrent | hFuture
                    · exact Or.inl ⟨Or.inr hCurrent, hOutside⟩
                    · exact Or.inr ⟨Or.inr hFuture, hOutside⟩
          | par_fuse outer leftEnvironment rightEnvironment interface left
              right leftLabel rightLabel leftCurrent leftFuture rightCurrent
              rightFuture hLeftOffers hRightOffers _ =>
              have hLeft := ih (sizeOf left) (by
                rw [← hSize]
                simp_wf
                omega) left rfl _ _ _ _ _ hLeftOffers
              have hRight := ih (sizeOf right) (by
                rw [← hSize]
                simp_wf
                omega) right rfl _ _ _ _ _ hRightOffers
              simp only [typeFutureOffers, typeFutureOffersFuel,
                Finset.union_empty] at hLeft hRight ⊢
              have hLeftSub : leftFuture ⊆ leftCurrent := by
                intro a ha
                rw [← hLeft]
                exact Finset.mem_union_right _ ha
              have hRightSub : rightFuture ⊆ rightCurrent := by
                intro a ha
                rw [← hRight]
                exact Finset.mem_union_right _ ha
              have hSub : hideTypeOffers interface (leftFuture ∪ rightFuture) ⊆
                  hideTypeOffers interface (leftCurrent ∪ rightCurrent) := by
                apply Finset.filter_subset_filter
                exact Finset.union_subset_union hLeftSub hRightSub
              exact Finset.union_eq_left.mpr hSub
      | message msg dir =>
          cases hOffers <;> simp [typeFutureOffers, typeFutureOffersFuel]
      | progress pid =>
          cases hOffers <;> simp [typeFutureOffers, typeFutureOffersFuel]
      | tock =>
          cases hOffers <;> simp [typeFutureOffers, typeFutureOffersFuel]
      | skip =>
          cases hOffers <;> simp [typeFutureOffers, typeFutureOffersFuel]
      | var name => cases hOffers
      | recur name body => cases hOffers <;> simp
      | choice left right => cases hOffers <;> simp
      | fairChoice bid left right => cases hOffers <;> simp
      | seq left right =>
          cases hOffers <;> simp [typeFutureOffers_sequence]
      | xoffer elseType branches =>
          cases hOffers <;> simp [typeFutureOffers, typeFutureOffersFuel]
      | offer elseType branches =>
          cases hOffers <;> simp [typeFutureOffers, typeFutureOffersFuel]

/-- Package explicitly chosen witness edges into the existential product test. -/
private theorem syncAutomatonEdges_of_witnesses
    (interface : Interface) {leftEdges rightEdges : Finset AutomatonFragmentEdge}
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    (hLeftWitness : leftWitness ∈ leftEdges)
    (hRightWitness : rightWitness ∈ rightEdges)
    (hSync : syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness) :
    syncAutomatonEdges interface leftEdges rightEdges left right := by
  exact ⟨leftWitness, hLeftWitness, rightWitness, hRightWitness, hSync⟩

/-- The ordinary local-environment fields, using independent witness offer
summaries, are exactly the strict witness synchronization predicate. -/
private theorem syncAutomatonEdgeWitnesses_of_ordinaryLocalFields
    (interface : Interface)
    {outer : TypeEnvironment}
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    (hOuter : combineAutomatonEnvironment interface left.environment
      right.environment = outer)
    (hLeftMatch : matchesAutomatonOfferWitness left leftWitness)
    (hRightMatch : matchesAutomatonOfferWitness right rightWitness)
    (hLeftClock : left.environment.clock = false)
    (hRightClock : right.environment.clock = false)
    (hLeftImmediate : left.environment.immediate =
      outer.immediate ∪ restrictTypeOffers interface rightWitness.current)
    (hLeftFuture : left.environment.future =
      (outer.future ∪ restrictTypeOffers interface rightWitness.future) \
        left.environment.immediate)
    (hRightImmediate : right.environment.immediate =
      outer.immediate ∪ restrictTypeOffers interface leftWitness.current)
    (hRightFuture : right.environment.future =
      (outer.future ∪ restrictTypeOffers interface leftWitness.future) \
        right.environment.immediate)
    (hLabelSync : TypeLabel.Sync interface left.label.semantic
      right.label.semantic) :
    syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness := by
  unfold syncAutomatonEdgeWitnesses
  simp only [hLeftClock, if_false]
  rw [hOuter]
  exact ⟨hLeftMatch, hRightMatch,
    ⟨True.intro, hRightClock, hLeftImmediate, hLeftFuture,
      hRightImmediate, hRightFuture⟩, hLabelSync⟩

/-- Realizing the offer summaries existentially stored in two semantic local
judgments as resolved witness edges yields the compiler's existential product
test.  Actual edges are used as witnesses in the clock case. -/
private theorem localTypeEnvironments_to_syncAutomatonEdges
    (signature : TypeAlphabet) (interface : Interface)
    {leftEdges rightEdges : Finset AutomatonFragmentEdge}
    {outer : TypeEnvironment} {leftEdge rightEdge : AutomatonFragmentEdge}
    {left right : PactType}
    (hAlphabet : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hOuterEnvironment : outer ∈ signature.environments)
    (hLeftEdge : leftEdge ∈ leftEdges)
    (hRightEdge : rightEdge ∈ rightEdges)
    (hLeftLocal : LocalTypeEnvironment outer interface
      rightEdge.environment right rightEdge.label.semantic
      leftEdge.environment)
    (hRightLocal : LocalTypeEnvironment outer interface
      leftEdge.environment left leftEdge.label.semantic
      rightEdge.environment)
    (hLeftRealizes :
      ∀ {target current future},
        TypeOffers leftEdge.environment left leftEdge.label.semantic target
          current future →
        ∃ witness ∈ leftEdges,
          matchesAutomatonOfferWitness leftEdge witness ∧
            witness.current = current ∧ witness.future = future)
    (hRightRealizes :
      ∀ {target current future},
        TypeOffers rightEdge.environment right rightEdge.label.semantic target
          current future →
        ∃ witness ∈ rightEdges,
          matchesAutomatonOfferWitness rightEdge witness ∧
            witness.current = current ∧ witness.future = future)
    (hLabelSync : TypeLabel.Sync interface leftEdge.label.semantic
      rightEdge.label.semantic) :
    syncAutomatonEdges interface leftEdges rightEdges leftEdge rightEdge ∧
      combineAutomatonEnvironment interface leftEdge.environment
        rightEdge.environment = outer := by
  have hLeftCases := LocalTypeEnvironment.clock_or_ordinary hLeftLocal
  have hRightCases := LocalTypeEnvironment.clock_or_ordinary hRightLocal
  rcases hLeftCases with hClock | hOrdinary
  · rcases hClock with ⟨hOuterClock, hRightTock, hLeftTock⟩
    have hOuterLocal : outer ∈ signature.localEnvironments :=
      signature.environments_subset_localEnvironments hOuterEnvironment
    have hOuterTock := TypeAlphabet.localEnvironment_eq_tock_of_clock
      hOuterLocal hOuterClock
    have hCombined : combineAutomatonEnvironment interface
        leftEdge.environment rightEdge.environment = outer := by
      rw [hLeftTock, hRightTock, hOuterTock]
      simp [combineAutomatonEnvironment, TypeEnvironment.tock]
    constructor
    · apply syncAutomatonEdges_of_witnesses interface hLeftEdge hRightEdge
      unfold syncAutomatonEdgeWitnesses
      simp [matchesAutomatonOfferWitness, hLeftTock, hRightTock,
        hLabelSync]
      intro hFalse
      simp [TypeEnvironment.tock] at hFalse
    · exact hCombined
  · rcases hOrdinary with
      ⟨rightTarget, rightCurrent, rightFuture, hOuterClock,
        hRightClock, hRightOffers, hLeftClock, hLeftImmediate, hLeftFuture⟩
    rcases hRightCases with hClock | hOrdinary
    · rcases hClock with ⟨_, hLeftTock, hRightTock⟩
      rw [hRightTock] at hRightClock
      simp [TypeEnvironment.tock] at hRightClock
    · rcases hOrdinary with
        ⟨leftTarget, leftCurrent, leftFuture, _, hLeftClock',
          hLeftOffers, hRightClock', hRightImmediate, hRightFuture⟩
      obtain ⟨leftWitness, hLeftWitness, hLeftMatch,
          hLeftCurrent, hLeftFutureSummary⟩ := hLeftRealizes hLeftOffers
      obtain ⟨rightWitness, hRightWitness, hRightMatch,
          hRightCurrent, hRightFutureSummary⟩ := hRightRealizes hRightOffers
      rw [← hLeftCurrent] at hRightImmediate
      rw [← hLeftFutureSummary] at hRightFuture
      rw [← hRightCurrent] at hLeftImmediate
      rw [← hRightFutureSummary] at hLeftFuture
      have hCombined :=
        combineAutomatonEnvironment_eq_of_ordinaryLocalFields
          signature interface hAlphabet hInterface hOuterEnvironment
          hOuterClock hLeftClock hRightClock hLeftImmediate hLeftFuture
          hRightImmediate hRightFuture
      constructor
      · apply syncAutomatonEdges_of_witnesses interface
          hLeftWitness hRightWitness
        exact syncAutomatonEdgeWitnesses_of_ordinaryLocalFields interface
          hCombined hLeftMatch hRightMatch hLeftClock hRightClock
          hLeftImmediate hLeftFuture hRightImmediate hRightFuture hLabelSync
      · exact hCombined

/-- Local-domain form of sibling-environment reconstruction.  Avoidance of
the current interface replaces exportedness/signature well-formedness. -/
theorem localTypeEnvironments_to_syncAutomatonEdges_local
    (signature : TypeAlphabet) (interface : Interface)
    {leftEdges rightEdges : Finset AutomatonFragmentEdge}
    {outer : TypeEnvironment} {leftEdge rightEdge : AutomatonFragmentEdge}
    {left right : PactType}
    (hInterface : interface ⊆ signature.interface)
    (hOuterEnvironment : outer ∈ signature.localEnvironments)
    (hOuterAvoids : outer.AvoidsInterface interface)
    (hLeftEdge : leftEdge ∈ leftEdges)
    (hRightEdge : rightEdge ∈ rightEdges)
    (hLeftLocal : LocalTypeEnvironment outer interface
      rightEdge.environment right rightEdge.label.semantic
      leftEdge.environment)
    (hRightLocal : LocalTypeEnvironment outer interface
      leftEdge.environment left leftEdge.label.semantic
      rightEdge.environment)
    (hLeftRealizes :
      ∀ {target current future},
        TypeOffers leftEdge.environment left leftEdge.label.semantic target
          current future →
        ∃ witness ∈ leftEdges,
          matchesAutomatonOfferWitness leftEdge witness ∧
            witness.current = current ∧ witness.future = future)
    (hRightRealizes :
      ∀ {target current future},
        TypeOffers rightEdge.environment right rightEdge.label.semantic target
          current future →
        ∃ witness ∈ rightEdges,
          matchesAutomatonOfferWitness rightEdge witness ∧
            witness.current = current ∧ witness.future = future)
    (hLabelSync : TypeLabel.Sync interface leftEdge.label.semantic
      rightEdge.label.semantic) :
    syncAutomatonEdges interface leftEdges rightEdges leftEdge rightEdge ∧
      combineAutomatonEnvironment interface leftEdge.environment
        rightEdge.environment = outer := by
  have hLeftCases := LocalTypeEnvironment.clock_or_ordinary hLeftLocal
  have hRightCases := LocalTypeEnvironment.clock_or_ordinary hRightLocal
  rcases hLeftCases with hClock | hOrdinary
  · rcases hClock with ⟨hOuterClock, hRightTock, hLeftTock⟩
    have hOuterTock := TypeAlphabet.localEnvironment_eq_tock_of_clock
      hOuterEnvironment hOuterClock
    have hCombined : combineAutomatonEnvironment interface
        leftEdge.environment rightEdge.environment = outer := by
      rw [hLeftTock, hRightTock, hOuterTock]
      simp [combineAutomatonEnvironment, TypeEnvironment.tock]
    constructor
    · apply syncAutomatonEdges_of_witnesses interface hLeftEdge hRightEdge
      unfold syncAutomatonEdgeWitnesses
      simp [matchesAutomatonOfferWitness, hLeftTock, hRightTock,
        hLabelSync]
      intro hFalse
      simp [TypeEnvironment.tock] at hFalse
    · exact hCombined
  · rcases hOrdinary with
      ⟨rightTarget, rightCurrent, rightFuture, hOuterClock,
        hRightClock, hRightOffers, hLeftClock, hLeftImmediate, hLeftFuture⟩
    rcases hRightCases with hClock | hOrdinary
    · rcases hClock with ⟨_, hLeftTock, hRightTock⟩
      rw [hRightTock] at hRightClock
      simp [TypeEnvironment.tock] at hRightClock
    · rcases hOrdinary with
        ⟨leftTarget, leftCurrent, leftFuture, _, hLeftClock',
          hLeftOffers, hRightClock', hRightImmediate, hRightFuture⟩
      obtain ⟨leftWitness, hLeftWitness, hLeftMatch,
          hLeftCurrent, hLeftFutureSummary⟩ := hLeftRealizes hLeftOffers
      obtain ⟨rightWitness, hRightWitness, hRightMatch,
          hRightCurrent, hRightFutureSummary⟩ := hRightRealizes hRightOffers
      rw [← hLeftCurrent] at hRightImmediate
      rw [← hLeftFutureSummary] at hRightFuture
      rw [← hRightCurrent] at hLeftImmediate
      rw [← hRightFutureSummary] at hLeftFuture
      have hCombined :=
        combineAutomatonEnvironment_eq_of_ordinaryLocalFields_of_avoids
          interface
          (TypeAlphabet.localEnvironment_wellFormed hOuterEnvironment)
          hOuterAvoids hOuterClock hLeftClock hRightClock hLeftImmediate
          hLeftFuture hRightImmediate hRightFuture
      constructor
      · apply syncAutomatonEdges_of_witnesses interface
          hLeftWitness hRightWitness
        exact syncAutomatonEdgeWitnesses_of_ordinaryLocalFields interface
          hCombined hLeftMatch hRightMatch hLeftClock hRightClock
          hLeftImmediate hLeftFuture hRightImmediate hRightFuture hLabelSync
      · exact hCombined

/-- Strict witness synchronization reconstructs the two semantic
sibling-local environments using the witness summaries, while the actual
edges retain the product target and exposed offer summary. -/
theorem syncAutomatonEdgeWitnesses_to_localTypeEnvironments
    (interface : Interface)
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    {leftType leftTarget rightType rightTarget : PactType}
    (hLeftOffers : TypeOffers leftWitness.environment leftType
      leftWitness.label.semantic leftTarget leftWitness.current
      leftWitness.future)
    (hRightOffers : TypeOffers rightWitness.environment rightType
      rightWitness.label.semantic rightTarget rightWitness.current
      rightWitness.future)
    (hSync : syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness) :
    let outer := combineAutomatonEnvironment interface
      left.environment right.environment
    LocalTypeEnvironment outer interface right.environment rightType
        right.label.semantic left.environment ∧
      LocalTypeEnvironment outer interface left.environment leftType
        left.label.semantic right.environment := by
  unfold syncAutomatonEdgeWitnesses at hSync
  rcases hSync with ⟨hLeftMatch, hRightMatch, hFields, hLabelSync⟩
  rcases hLeftMatch with ⟨hLeftSource, hLeftEnvironment, hLeftLabel⟩
  rcases hRightMatch with ⟨hRightSource, hRightEnvironment, hRightLabel⟩
  rw [hLeftEnvironment, hLeftLabel] at hLeftOffers
  rw [hRightEnvironment, hRightLabel] at hRightOffers
  cases hLeftClock : left.environment.clock with
  | true =>
      simp only [hLeftClock, if_true] at hFields
      rcases hFields with ⟨hLeftTock, hRightTock⟩
      rw [hLeftTock, hRightTock]
      simp only [combineAutomatonEnvironment, TypeEnvironment.tock]
      exact ⟨LocalTypeEnvironment.clock TypeEnvironment.tock interface
          rightType right.label.semantic rfl,
        LocalTypeEnvironment.clock TypeEnvironment.tock interface
          leftType left.label.semantic rfl⟩
  | false =>
      simp only [hLeftClock, if_false] at hFields
      rcases hFields with ⟨hLeftClock', hRightClock, hLeftImmediate,
        hLeftFuture, hRightImmediate, hRightFuture⟩
      let outer := combineAutomatonEnvironment interface
        left.environment right.environment
      have hOuterClock : outer.clock = false := by
        simp [outer, combineAutomatonEnvironment, hLeftClock, hRightClock]
      change LocalTypeEnvironment outer interface right.environment rightType
          right.label.semantic left.environment ∧
        LocalTypeEnvironment outer interface left.environment leftType
          left.label.semantic right.environment
      exact ⟨
        LocalTypeEnvironment.ordinary outer right.environment left.environment
          interface rightType rightTarget right.label.semantic
          rightWitness.current rightWitness.future hOuterClock hRightClock
          hRightOffers hLeftClock hLeftImmediate hLeftFuture,
        LocalTypeEnvironment.ordinary outer left.environment right.environment
          interface leftType leftTarget left.label.semantic
          leftWitness.current leftWitness.future hOuterClock hLeftClock
          hLeftOffers hRightClock hRightImmediate hRightFuture⟩

/-- The step-for-step relation of Lemma 4.5. -/
structure TypeAutomatonCorrespondence
    (processType : PactType) (automaton : TypeAutomaton) : Type where
  relation : PactType → TypeAutomatonState → Prop
  initial : relation processType automaton.initial
  initial_mem : automaton.initial ∈ automaton.states
  stepIff :
    ∀ {residual residual' : PactType} {state : TypeAutomatonState}
      {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
      relation residual state →
      ({ environment := env, label := label, offers := offers } :
          TypeAutomatonSymbol) ∈ automaton.alphabet →
      (DecoratedTypeTransition env residual label offers residual' ↔
        ∃ state',
          automaton.HasEdge state env label offers state' ∧
          relation residual' state')

/-- The atomic `skip` constructor already satisfies the full step correspondence. -/
theorem compileType_skip_correspondence (signature : TypeAlphabet) :
    Nonempty (TypeAutomatonCorrespondence .skip (compileType signature .skip)) :=
  sorry
theorem compileType_message_action_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hNeed : env.hasNeed (msg, dir))
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.message msg dir)
      (TypeOfferSummary.mk {(msg, dir)} ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.message msg dir)).HasEdge .root env
      (TypeLabel.message msg dir) (TypeOfferSummary.mk {(msg, dir)} ∅)
      .final :=
  sorry
theorem compileType_message_wait_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hNoNeed : ¬ env.hasNeed (msg, dir)) (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk {(msg, dir)} ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.message msg dir)).HasEdge .root env
      TypeLabel.silent (TypeOfferSummary.mk {(msg, dir)} ∅) .root :=
  sorry
theorem compileType_message_final_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.message msg dir)).HasEdge .final env
      TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) .final :=
  sorry
private theorem TypeOffers.message_action_fields
    {env : TypeEnvironment} {msg : MessageId} {dir : MessageDir}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.message msg dir) (TypeLabel.message msg dir)
      .skip current future) :
    current = {(msg, dir)} ∧ future = ∅ :=
  sorry
private theorem TypeOffers.message_wait_fields
    {env : TypeEnvironment} {msg : MessageId} {dir : MessageDir}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.message msg dir) TypeLabel.silent
      (.message msg dir) current future) :
    current = {(msg, dir)} ∧ future = ∅ :=
  sorry
private theorem TypeOffers.skip_fields
    {env : TypeEnvironment} {current future : Finset BareMessage}
    (hOffers : TypeOffers env .skip TypeLabel.silent .skip current future) :
    current = ∅ ∧ future = ∅ :=
  sorry
theorem compileType_message_step_to_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation (.message msg dir) state residual)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature (.message msg dir)).alphabet)
    (hStep : DecoratedTypeTransition env residual label offers residual') :
    ∃ state',
      (compileType signature (.message msg dir)).HasEdge state env label offers
          state' ∧
        TypeCompilationRelation (.message msg dir) state' residual' :=
  sorry
private theorem compileType_message_edge_cases
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
        current = ∅ ∧ future = ∅ ∧ env.clock = false) :=
  sorry
theorem compileType_message_edge_to_step
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {residual residual' : PactType} {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hEnvironment : env ∈ signature.environments)
    (hRelated : TypeCompilationRelation (.message msg dir) state residual)
    (hEdge : (compileType signature (.message msg dir)).HasEdge state env label
      offers state')
    (hTarget : TypeCompilationRelation (.message msg dir) state' residual') :
    DecoratedTypeTransition env residual label offers residual' :=
  sorry
theorem compileType_message_correspondence
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    Nonempty (TypeAutomatonCorrespondence (.message msg dir)
      (compileType signature (.message msg dir))) :=
  sorry
theorem compileType_tock_action_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = true)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.tock
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .tock).HasEdge .root env TypeLabel.tock
      (TypeOfferSummary.mk ∅ ∅) .final :=
  sorry
theorem compileType_tock_wait_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .tock).HasEdge .root env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) .root :=
  sorry
theorem compileType_tock_final_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .tock).HasEdge .final env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) .final :=
  sorry
private theorem TypeOffers.tock_action_fields
    {env : TypeEnvironment} {current future : Finset BareMessage}
    (hOffers : TypeOffers env .tock TypeLabel.tock .skip current future) :
    current = ∅ ∧ future = ∅ :=
  sorry
private theorem TypeOffers.tock_wait_fields
    {env : TypeEnvironment} {current future : Finset BareMessage}
    (hOffers : TypeOffers env .tock TypeLabel.silent .tock current future) :
    current = ∅ ∧ future = ∅ :=
  sorry
theorem compileType_tock_step_to_edge
    (signature : TypeAlphabet)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation .tock state residual)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature .tock).alphabet)
    (hStep : DecoratedTypeTransition env residual label offers residual') :
    ∃ state',
      (compileType signature .tock).HasEdge state env label offers state' ∧
        TypeCompilationRelation .tock state' residual' :=
  sorry
private theorem compileType_tock_edge_cases
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
        current = ∅ ∧ future = ∅ ∧ env.clock = false) :=
  sorry
theorem compileType_tock_edge_to_step
    (signature : TypeAlphabet)
    {residual residual' : PactType} {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hEnvironment : env ∈ signature.environments)
    (hRelated : TypeCompilationRelation .tock state residual)
    (hEdge : (compileType signature .tock).HasEdge state env label offers state')
    (hTarget : TypeCompilationRelation .tock state' residual') :
    DecoratedTypeTransition env residual label offers residual' :=
  sorry
theorem compileType_tock_correspondence (signature : TypeAlphabet) :
    Nonempty (TypeAutomatonCorrespondence .tock
      (compileType signature .tock)) :=
  sorry
theorem compileType_progress_action_edge
    (signature : TypeAlphabet) (pid : ProcId) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.progress pid)
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.progress pid)).HasEdge .root env
      (TypeLabel.progress pid) (TypeOfferSummary.mk ∅ ∅) .final :=
  sorry
theorem compileType_progress_final_edge
    (signature : TypeAlphabet) (pid : ProcId) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.progress pid)).HasEdge .final env
      TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) .final :=
  sorry
private theorem TypeOffers.progress_fields
    {env : TypeEnvironment} {pid : ProcId}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.progress pid) (TypeLabel.progress pid)
      .skip current future) :
    current = ∅ ∧ future = ∅ :=
  sorry
theorem compileType_progress_step_to_edge
    (signature : TypeAlphabet) (pid : ProcId)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation (.progress pid) state residual)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature (.progress pid)).alphabet)
    (hStep : DecoratedTypeTransition env residual label offers residual') :
    ∃ state',
      (compileType signature (.progress pid)).HasEdge state env label offers
          state' ∧
        TypeCompilationRelation (.progress pid) state' residual' :=
  sorry
private theorem compileType_progress_edge_cases
    (signature : TypeAlphabet) (pid : ProcId)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType signature (.progress pid)).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧
        label = TypeLabel.progress pid ∧ current = ∅ ∧ future = ∅) ∨
      (source = .final ∧ target = .final ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false) :=
  sorry
theorem compileType_progress_edge_to_step
    (signature : TypeAlphabet) (pid : ProcId)
    {residual residual' : PactType} {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hEnvironment : env ∈ signature.environments)
    (hRelated : TypeCompilationRelation (.progress pid) state residual)
    (hEdge : (compileType signature (.progress pid)).HasEdge state env label
      offers state')
    (hTarget : TypeCompilationRelation (.progress pid) state' residual') :
    DecoratedTypeTransition env residual label offers residual' :=
  sorry
theorem compileType_progress_correspondence
    (signature : TypeAlphabet) (pid : ProcId) :
    Nonempty (TypeAutomatonCorrespondence (.progress pid)
      (compileType signature (.progress pid))) :=
  sorry/-! ### Visible-edge target relatedness for atomic fragments -/

theorem compilationResolvedEdgeTargetsRelated_skip
    (signature : TypeAlphabet) :
    CompilationResolvedEdgeTargetsRelated signature .skip := by
  intro source residual environment label offers target hRelated hEdge
  cases hRelated
  rcases hEdge with ⟨edge, hPending, hSource, _, _, _, _, hTarget⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_image, Finset.mem_filter] at hPending
  rcases hPending with ⟨edgeEnvironment, _, rfl⟩
  simp only at hSource hTarget
  subst target
  exact ⟨.skip, TypeCompilationRelation.skip⟩

theorem compilationResolvedEdgeTargetsRelated_message
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CompilationResolvedEdgeTargetsRelated signature (.message msg dir) := by
  intro source residual environment label offers target hRelated hEdge
  rcases hEdge with ⟨edge, hPending, hSource, _, _, _, _, hTarget⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hPending
  rcases hPending with (hFiring | hWaiting) | hFinal
  · rcases hFiring with ⟨edgeEnvironment, _, rfl⟩
    simp only at hSource hTarget
    cases hRelated with
    | message_source =>
        subst target
        exact ⟨.skip, TypeCompilationRelation.message_final msg dir⟩
    | message_final => simp at hSource
  · rcases hWaiting with ⟨edgeEnvironment, _, rfl⟩
    simp only at hSource hTarget
    cases hRelated with
    | message_source =>
        subst target
        exact ⟨.message msg dir,
          TypeCompilationRelation.message_source msg dir⟩
    | message_final => simp at hSource
  · rcases hFinal with ⟨edgeEnvironment, _, rfl⟩
    simp only at hSource hTarget
    cases hRelated with
    | message_source => simp at hSource
    | message_final =>
        subst target
        exact ⟨.skip, TypeCompilationRelation.message_final msg dir⟩

theorem compilationResolvedEdgeTargetsRelated_tock
    (signature : TypeAlphabet) :
    CompilationResolvedEdgeTargetsRelated signature .tock := by
  intro source residual environment label offers target hRelated hEdge
  rcases hEdge with ⟨edge, hPending, hSource, _, _, _, _, hTarget⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hPending
  rcases hPending with hAction | hFinal
  · rcases hAction with ⟨edgeEnvironment, _, rfl⟩
    by_cases hClock : edgeEnvironment.clock
    · simp only [hClock, if_true] at hSource hTarget
      cases hRelated with
      | cycle_source =>
          subst target
          exact ⟨.skip, TypeCompilationRelation.cycle_final⟩
      | cycle_final => simp at hSource
    · simp only [hClock, if_false] at hSource hTarget
      cases hRelated with
      | cycle_source =>
          subst target
          exact ⟨.tock, TypeCompilationRelation.cycle_source⟩
      | cycle_final => simp at hSource
  · rcases hFinal with ⟨edgeEnvironment, _, rfl⟩
    simp only at hSource hTarget
    cases hRelated with
    | cycle_source => simp at hSource
    | cycle_final =>
        subst target
        exact ⟨.skip, TypeCompilationRelation.cycle_final⟩

theorem compilationResolvedEdgeTargetsRelated_progress
    (signature : TypeAlphabet) (pid : ProcId) :
    CompilationResolvedEdgeTargetsRelated signature (.progress pid) := by
  intro source residual environment label offers target hRelated hEdge
  rcases hEdge with ⟨edge, hPending, hSource, _, _, _, _, hTarget⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hPending
  rcases hPending with hAction | hFinal
  · rcases hAction with ⟨edgeEnvironment, _, rfl⟩
    simp only at hSource hTarget
    cases hRelated with
    | progress_source =>
        subst target
        exact ⟨.skip, TypeCompilationRelation.progress_final pid⟩
    | progress_final => simp at hSource
  · rcases hFinal with ⟨edgeEnvironment, _, rfl⟩
    simp only at hSource hTarget
    cases hRelated with
    | progress_source => simp at hSource
    | progress_final =>
        subst target
        exact ⟨.skip, TypeCompilationRelation.progress_final pid⟩

theorem compilationResolvedEdgeTargetsRelated_var
    (signature : TypeAlphabet) (name : String) :
    CompilationResolvedEdgeTargetsRelated signature (.var name) := by
  intro source residual environment label offers target hRelated hEdge
  cases hRelated
  rcases hEdge with ⟨edge, hPending, _, _, hLabel, _, _, _⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_image] at hPending
  rcases hPending with ⟨edgeEnvironment, _, rfl⟩
  simp at hLabel


end

end Pact
