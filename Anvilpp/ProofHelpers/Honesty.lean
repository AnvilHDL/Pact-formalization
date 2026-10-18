import Anvilpp.PactTypes.Spec.Syntax.TypeErasure

namespace Pact

noncomputable section

open Classical

/-- Complementary boundary actions consumed by the message observations in a label. -/
def TypeLabel.usedEnvironmentActions : TypeLabel → Finset BareMessage
  | .tock => ∅
  | .actions observations => observations.biUnion fun observation =>
      match observation with
      | .message msg dir => {(msg, dir.invert)}
      | _ => ∅

/-- Future promises and immediate offers not consumed by the current step. -/
def TypeEnvironment.honestyRemainder (env : TypeEnvironment) (label : TypeLabel) :
    Finset BareMessage :=
  env.future ∪ (env.immediate \ label.usedEnvironmentActions)

/-- Process honesty retains the same bare actions as its erased environment and label. -/
def Environment.honestyRemainder (env : Environment) (label : Label) : Finset BareMessage :=
  (eraseEnvironment env).honestyRemainder (eraseLabel label)

theorem TypeEnvironment.honestyRemainder_subset (env : TypeEnvironment) (label : TypeLabel) :
    env.honestyRemainder label ⊆ env.immediate ∪ env.future := by
  intro action h
  rcases Finset.mem_union.mp h with hFuture | hImmediate
  · exact Finset.mem_union_right _ hFuture
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hImmediate).1

@[simp] theorem TypeLabel.usedEnvironmentActions_silent :
    TypeLabel.silent.usedEnvironmentActions = ∅ := by
  simp [TypeLabel.silent, TypeLabel.usedEnvironmentActions]

@[simp] theorem TypeLabel.usedEnvironmentActions_message (msg : MessageId) (dir : MessageDir) :
    (TypeLabel.message msg dir).usedEnvironmentActions = {(msg, dir.invert)} := by
  simp [TypeLabel.message, TypeLabel.usedEnvironmentActions]

@[simp] theorem TypeEnvironment.honestyRemainder_silent (env : TypeEnvironment) :
    env.honestyRemainder TypeLabel.silent = env.future ∪ env.immediate := by
  simp [TypeEnvironment.honestyRemainder]

/-- A boundary action advertised now survives exactly when it is not consumed. -/
theorem TypeEnvironment.mem_honestyRemainder_of_immediate
    {env : TypeEnvironment} {alphabet : PactTypeAlphabet} {label : TypeLabel}
    {action : BareMessage} (hWF : env.WellFormed alphabet)
    (hImmediate : action ∈ env.immediate) :
    action ∈ env.honestyRemainder label ↔ action ∉ label.usedEnvironmentActions := by
  have hNonclock : env.clock = false := by
    cases hClock : env.clock with
    | false => rfl
    | true => simp [(hWF.1 hClock).1] at hImmediate
  have hNotFuture : action ∉ env.future := by
    intro hFuture
    have hBoth := Finset.mem_inter.mpr ⟨hImmediate, hFuture⟩
    simp [hWF.2.1 hNonclock] at hBoth
  simp [TypeEnvironment.honestyRemainder, hImmediate, hNotFuture]

end

end Pact
