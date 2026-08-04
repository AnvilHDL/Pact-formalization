import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.List.Zip
import Mathlib.Data.List.Forall2
import Anvilpp.Base
import Anvilpp.Proc
import Anvilpp.Types
import Anvilpp.Typing
import Anvilpp.Automata
import Anvilpp.Helpers
import Anvilpp.Subtyping
import Anvilpp.Trans

private lemma insertIdx_eq_take_drop {T : Type} : ∀ (l : List T) (i : Nat) (a : T),
    i ≤ l.length → l.insertIdx i a = l.take i ++ a :: l.drop i := by
  intro l
  induction l with
  | nil =>
    intro i a h; cases i with
    | zero => rfl
    | succ n => grind
  | cons x xs ih =>
    intro i a h; cases i with
    | zero => simp [List.insertIdx]
    | succ n =>
      simp only [List.insertIdx, List.modifyTailIdx_succ_cons, List.take_succ_cons,
                 List.drop_succ_cons, List.cons_append]
      exact congrArg (x :: ·) (ih n a (by simp at h; omega))

private lemma list_append_cons_insertIdx_eq {T : Type} : ∀ (l₁ : List T) (e : T) (l₂ : List T),
    l₁ ++ e :: l₂ = (l₁ ++ l₂).insertIdx l₁.length e := by
  intro l₁; induction l₁ with
  | nil => intros; rfl
  | cons x xs ih =>
    intro e l₂
    show x :: (xs ++ e :: l₂) = x :: (xs ++ l₂).insertIdx xs.length e
    exact congrArg (x :: ·) (ih e l₂)

private lemma zip_append_of_length {T U : Type} : ∀ (l₁ l₂ : List T) (m₁ m₂ : List U),
    l₁.length = m₁.length → (l₁ ++ l₂).zip (m₁ ++ m₂) = l₁.zip m₁ ++ l₂.zip m₂ := by
  intro l₁; induction l₁ with
  | nil => intro l₂ m₁ m₂ H; cases m₁ with | nil => rfl | cons h t => simp at H
  | cons x xs ih =>
    intro l₂ m₁ m₂ H; cases m₁ with
    | nil => simp at H
    | cons y ys =>
      simp only [List.cons_append, List.zip_cons_cons]
      exact congrArg _ (ih l₂ ys m₂ (by simp at H; exact H))

private lemma branch_to_xoffer_ty_guarded (me : MessageExch) (ty : ProcTy)
    (H_guarded : ProcTyGuardedClosed ty) : ProcTyGuardedClosed (branch_to_xoffer_ty (me, ty)) := by
  simp only [branch_to_xoffer_ty]
  apply ProcTyGuarded.xoffer <;> [exact ProcTyGuarded.skip _ _ _; skip]
  intro m τ H_mem; simp only [List.mem_singleton] at H_mem; obtain ⟨-, rfl⟩ := H_mem; exact H_guarded

private lemma foldl_par_guarded' : ∀ (τs : List ProcTy), (∀ τ ∈ τs, ProcTyGuardedClosed τ) →
    ∀ τ₀, ProcTyGuardedClosed τ₀ →
    ProcTyGuardedClosed (List.foldl (fun acc τ => ProcTy.par acc τ) τ₀ τs) := by
  intro τs; induction τs with
  | nil => exact fun _ _ h => h
  | cons τ₁ rest ih =>
    intro H_all τ₀ H₀; simp only [List.foldl_cons]
    apply ih (fun τ hm => H_all τ (List.mem_cons_of_mem _ hm))
    apply ProcTyGuarded.par
    . exact H₀
    . apply H_all
      grind

private lemma mem_zip_of_map'
    {α β γ δ : Type} (f : α → γ) (g : β → δ)
    {l₁ : List α} {l₂ : List β} {a' : γ} {b' : δ}
    (h : (a', b') ∈ (l₁.map f).zip (l₂.map g)) :
    ∃ a b, (a, b) ∈ l₁.zip l₂ ∧ f a = a' ∧ g b = b' := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons a₀ as ih =>
    cases l₂ with
    | nil => simp at h
    | cons b₀ bs =>
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨a₀, b₀, List.mem_cons.mpr (Or.inl rfl), rfl, rfl⟩
      · obtain ⟨a, b, hmem, hfa, hgb⟩ := ih h
        exact ⟨a, b, List.mem_cons.mpr (Or.inr hmem), hfa, hgb⟩

private lemma mem_zip_erase_lift
    {α β : Type} :
    ∀ (l₁ : List α) (l₂ : List β) (idx : ℕ) (x : α) {a : α} {b : β},
      idx < l₁.length + 1 →
      (l₁.insertIdx idx x).length = l₂.length →
      (a, b) ∈ l₁.zip (l₂.eraseIdx idx) →
      (a, b) ∈ (l₁.insertIdx idx x).zip l₂ := by
  intro l₁; induction l₁ with
  | nil =>
    intro l₂ idx x a b hidx hlen hmem
    simp at hmem
  | cons h t ih =>
    intro l₂ idx x a b hidx hlen hmem
    cases idx with
    | zero =>
      cases l₂ with
      | nil => simp at hlen
      | cons y ys =>
        simp at hlen
        have : (a, b) ∈ (h :: t).zip ys := hmem
        simpa [List.insertIdx, List.zip_cons_cons, List.mem_cons] using Or.inr this
    | succ idx' =>
      cases l₂ with
      | nil => simp at hlen
      | cons y ys =>
        simp at hlen
        have hsplit : (a = h ∧ b = y) ∨ (a, b) ∈ t.zip (ys.eraseIdx idx') := by
          simpa [List.eraseIdx, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] using hmem
        rcases hsplit with hhead | htail
        · simpa [List.insertIdx, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] using Or.inl hhead
        · have htail' : (a, b) ∈ (List.insertIdx t idx' x).zip ys :=
            ih ys idx' x (by simpa using hidx) (by simpa using hlen) htail
          simpa [List.insertIdx, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] using Or.inr htail'

private lemma ex_cond_of_branches
    {branches : List ChoiceBranch} {branch_tys : List (MessageExch × ProcTy)}
    {ex_msg : Finset (MessageId × MessageDir)}
    (H_send_ty : ∀ m e p br_ty, (ChoiceBranch.send m e p, br_ty) ∈ branches.zip branch_tys → br_ty.1 = MessageExch.send m)
    (H_recv_ty : ∀ m x p br_ty, (ChoiceBranch.recv m x p, br_ty) ∈ branches.zip branch_tys → br_ty.1 = MessageExch.recv m)
    (H_len : branches.length = branch_tys.length)
    (H_ex_cond : ∀ mx ∈ branches.map ChoiceBranch.getMessage, (mx.1, mx.2.invert) ∈ ex_msg) :
    ∀ m ty, (m, ty) ∈ branch_tys → (m.messageId, m.direction.invert) ∈ ex_msg := by
  intro m ty H_mem
  obtain ⟨br, H_zip'⟩ := Trivia.zip_list_exists branch_tys branches (m, ty) H_len.symm.le H_mem
  have H_zip : (br, (m, ty)) ∈ branches.zip branch_tys := Trivia.zip_flip _ _ _ _ H_zip'
  have H_br_mem : br ∈ branches := (List.of_mem_zip H_zip).1
  cases br with
  | send msg' e' p' =>
    have H_m : m = MessageExch.send msg' := by have := H_send_ty msg' e' p' (m, ty) H_zip; simp at this; exact this
    subst H_m
    have := @H_ex_cond (msg', MessageDir.send) (by simp only [List.mem_map]; exact ⟨_, H_br_mem, rfl⟩)
    simpa [MessageExch.messageId, MessageExch.direction, MessageDir.invert] using this
  | recv msg' var' p' =>
    have H_m : m = MessageExch.recv msg' := by have := H_recv_ty msg' var' p' (m, ty) H_zip; simp at this; exact this
    subst H_m
    have := @H_ex_cond (msg', MessageDir.recv) (by simp only [List.mem_map]; exact ⟨_, H_br_mem, rfl⟩)
    simpa [MessageExch.messageId, MessageExch.direction, MessageDir.invert] using this

set_option maxHeartbeats 2000000
