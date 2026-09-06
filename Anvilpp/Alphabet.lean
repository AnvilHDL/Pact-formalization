import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Anvilpp.Base

/-!
# Written alphabets

The alphabet carried by every signed process and signed type.  Processes and
types share one alphabet notion, so `Ω(abs(P)) = Ω(P)` holds definitionally.
-/

namespace Pact

/-- The polarity of a message action. -/
inductive MessageDir : Type where
  | send : MessageDir
  | recv : MessageDir
  deriving DecidableEq

namespace MessageDir
  /-- Flip direction between send and recv. -/
  def invert (dir : MessageDir) : MessageDir :=
    match dir with
    | send => recv
    | recv => send

  @[simp] theorem invert_invert (dir : MessageDir) : dir.invert.invert = dir := by
    cases dir <;> rfl
end MessageDir

/-- A finite synchronization interface, as in `P ||_I P`. -/
abbrev Interface := Finset MessageId

/-- A message identifier paired with its polarity: the paper's `m!`/`m?`. -/
abbrev BareMessage := MessageId × MessageDir

/-- `Need` on a polarized action: flip its polarity. -/
def bareNeed (action : BareMessage) : BareMessage := (action.1, action.2.invert)

@[simp] theorem bareNeed_bareNeed (action : BareMessage) :
    bareNeed (bareNeed action) = action := by
  cases action with
  | mk msg dir => simp [bareNeed]

/-- The fixed alphabet attached to one signed node.

`actions` stores the polarized message actions owned by this node.  The
unpolarized message names are derived from `actions`.
-/
structure PactTypeAlphabet : Type where
  actions : Finset BareMessage
  deriving DecidableEq

instance : SizeOf PactTypeAlphabet := ⟨fun _ => 0⟩

namespace PactTypeAlphabet

  /-- `MsgWF(Ω)`: no message is owned in both polarities. -/
  def OnePolarity (alphabet : PactTypeAlphabet) : Prop :=
    ∀ msg, ¬ ((msg, MessageDir.send) ∈ alphabet.actions ∧
      (msg, MessageDir.recv) ∈ alphabet.actions)

  def WellFormed (alphabet : PactTypeAlphabet) : Prop :=
    alphabet.OnePolarity

  def empty : PactTypeAlphabet :=
    { actions := ∅ }

  def ofAction (action : BareMessage) : PactTypeAlphabet :=
    { actions := {action} }

  def union (left right : PactTypeAlphabet) : PactTypeAlphabet :=
    { actions := left.actions ∪ right.actions }

  /-- `A \ I`: drop both polarities of every interface message. -/
  def hideInterface (alphabet : PactTypeAlphabet)
      (interface : Interface) : PactTypeAlphabet :=
    { actions := alphabet.actions.filter fun action => action.1 ∉ interface }

  /-- `A |_I`: keep the actions whose message lies in `I`. -/
  def restrictInterface (alphabet : PactTypeAlphabet)
      (interface : Interface) : PactTypeAlphabet :=
    { actions := alphabet.actions.filter fun action => action.1 ∈ interface }

  /-- `overline(Ω)`: flip every polarity. -/
  def flip (alphabet : PactTypeAlphabet) : PactTypeAlphabet := by
    classical
    exact { actions := alphabet.actions.image bareNeed }

  def mergeHidden (left right : PactTypeAlphabet)
      (interface : Interface) : PactTypeAlphabet :=
    { actions :=
        (left.actions ∪ right.actions).filter fun action =>
          action.1 ∉ interface }

  /-- `Π_I(Ω,Ω_c)`: a child keeps its interface actions and receives the whole
  incoming alphabet. -/
  def projectParallel (parent child : PactTypeAlphabet)
      (interface : Interface) : PactTypeAlphabet :=
    { actions :=
        (child.actions.filter fun action => action.1 ∈ interface) ∪
          parent.actions }

  def ComplementaryOn
      (left right : PactTypeAlphabet) (interface : Interface) : Prop :=
    ∀ msg ∈ interface,
      (((msg, MessageDir.send) ∈ left.actions ∧
          (msg, MessageDir.recv) ∈ right.actions) ∨
        ((msg, MessageDir.recv) ∈ left.actions ∧
          (msg, MessageDir.send) ∈ right.actions))

  /-- `ParCompat_I(Ω,Ω₁,Ω₂)`.

  The parent declares no interface action.  Each interface message occurs in
  both child alphabets with opposite polarities.  Away from the interface both
  child alphabets equal the parent. -/
  structure ParallelCompatible
      (parent left right : PactTypeAlphabet) (interface : Interface) : Prop where
    parent_hides_interface : ∀ action ∈ parent.actions, action.1 ∉ interface
    complementary : ComplementaryOn left right interface
    parent_eq_left : hideInterface left interface = parent
    parent_eq_right : hideInterface right interface = parent

end PactTypeAlphabet

end Pact
