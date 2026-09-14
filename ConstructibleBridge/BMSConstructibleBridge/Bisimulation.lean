import BMSConstructibleBridge.TreeTransfer
import Mathlib.Data.Nat.Pairing

/-!
# 不同自然数码图之间的最大双模拟

将树码换码引理中原先作为参数的等价关系实际构造出来。见证 `H` 是自然数对的
集合；其局部条件只含数量词，故不是对三阶关系族作选择。最大关系以存在量化
单个见证定义，并由原双模拟的反向、复合及扩张直接证明全部规格。

这仍不是 KL 的全部树解释：树域、集合论公理验证及原标签映射另有义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.Bisimulation

set_option autoImplicit false

variable (R S : Nat → Nat → Prop)

/-- 一张见证图的双向子节点匹配条件。 -/
def witness_l (H : Nat → Nat → Prop) : Prop :=
  ∀ ⦃a b⦄, H a b →
    (∀ ⦃c⦄, R c a → ∃ d, S d b ∧ H c d) ∧
    (∀ ⦃d⦄, S d b → ∃ c, R c a ∧ H c d)

/-- 由实际双模拟见证定义的换码关系。 -/
def eq_l (a b : Nat) : Prop := ∃ H, witness_l R S H ∧ H a b

theorem refl_l (a : Nat) : eq_l R R a a := by
  refine ⟨Eq, ?_, rfl⟩
  rintro b c rfl
  exact ⟨fun _ h => ⟨_, h, rfl⟩, fun _ h => ⟨_, h, rfl⟩⟩

theorem symm_l {a b : Nat} (h : eq_l R S a b) : eq_l S R b a := by
  obtain ⟨H, hH, h⟩ := h
  refine ⟨fun c d => H d c, ?_, h⟩
  intro c d h
  exact ⟨fun _ h₀ => (hH h).2 h₀, fun _ h₀ => (hH h).1 h₀⟩

theorem trans_l (T : Nat → Nat → Prop) {a b c : Nat}
    (h₀ : eq_l R S a b) (h₁ : eq_l S T b c) : eq_l R T a c := by
  obtain ⟨H, hH, h₀⟩ := h₀
  obtain ⟨K, hK, h₁⟩ := h₁
  refine ⟨fun d e => ∃ f, H d f ∧ K f e, ?_, b, h₀, h₁⟩
  rintro d e ⟨f, h₂, h₃⟩
  constructor
  · intro g h₄
    obtain ⟨i, h₅, h₆⟩ := (hH h₂).1 h₄
    obtain ⟨j, h₇, h₈⟩ := (hK h₃).1 h₅
    exact ⟨j, h₇, i, h₆, h₈⟩
  · intro g h₄
    obtain ⟨i, h₅, h₆⟩ := (hK h₃).2 h₄
    obtain ⟨j, h₇, h₈⟩ := (hH h₂).2 h₅
    exact ⟨j, h₇, i, h₈, h₆⟩

/-- 最大关系本身保持双向子节点匹配。 -/
theorem witness_eq_l : witness_l R S (eq_l R S) := by
  rintro a b ⟨H, hH, h⟩
  constructor
  · intro c h₀
    obtain ⟨d, h₁, h₂⟩ := (hH h).1 h₀
    exact ⟨d, h₁, H, hH, h₂⟩
  · intro d h₀
    obtain ⟨c, h₁, h₂⟩ := (hH h).2 h₀
    exact ⟨c, h₁, H, hH, h₂⟩

/-- 不仅有正向匹配：最大双模拟满足完整的双向递归方程。 -/
theorem unfold_l (a b : Nat) : eq_l R S a b ↔
    (∀ c, R c a → ∃ d, S d b ∧ eq_l R S c d) ∧
    (∀ d, S d b → ∃ c, R c a ∧ eq_l R S c d) := by
  constructor
  · intro h
    exact ⟨fun _ h₀ => (witness_eq_l R S h).1 h₀, fun _ h₀ => (witness_eq_l R S h).2 h₀⟩
  · intro h
    refine ⟨fun c d => eq_l R S c d ∨ (c = a ∧ d = b), ?_, Or.inr ⟨rfl, rfl⟩⟩
    intro c d h₀
    rcases h₀ with h₀ | ⟨rfl, rfl⟩
    · constructor
      · intro e h₁
        obtain ⟨f, h₂, h₃⟩ := (witness_eq_l R S h₀).1 h₁
        exact ⟨f, h₂, Or.inl h₃⟩
      · intro e h₁
        obtain ⟨f, h₂, h₃⟩ := (witness_eq_l R S h₀).2 h₁
        exact ⟨f, h₂, Or.inl h₃⟩
    · constructor
      · intro e h₁
        obtain ⟨f, h₂, h₃⟩ := h.1 e h₁
        exact ⟨f, h₂, Or.inl h₃⟩
      · intro e h₁
        obtain ⟨f, h₂, h₃⟩ := h.2 e h₁
        exact ⟨f, h₂, Or.inl h₃⟩

/-- 完整的换码证书由双模拟定义产生，而非作为额外背景假设输入。 -/
theorem congruence_l : TreeTransfer.congruence_l R (eq_l R R) := {
  refl := refl_l R
  symm := symm_l R R
  trans := trans_l R R R
  forth := fun h h₀ => (witness_eq_l R R h).1 h₀ }

/-- 换码后的成员关系确实继承指定根的外部良基性。 -/
theorem acc_l {a : Nat} (h : Acc R a) : Acc (TreeTransfer.mem_l R (eq_l R R)) a :=
  TreeTransfer.acc_l (congruence_l R) h

private def code (H : Nat → Nat → Prop) : Set Nat := {n | H n.unpair.1 n.unpair.2}

/-- 每张双模拟见证只需一个实数码，不要求集合族的选择函数。 -/
theorem coded_l (a b : Nat) : eq_l R S a b ↔
    ∃ X : Set Nat, witness_l R S (fun c d => Nat.pair c d ∈ X) ∧ Nat.pair a b ∈ X := by
  constructor
  · rintro ⟨H, hH, h⟩
    refine ⟨code H, ?_, ?_⟩
    · simpa only [witness_l, code, Set.mem_ofPred_eq, Nat.unpair_pair] using hH
    · simpa only [code, Set.mem_ofPred_eq, Nat.unpair_pair] using h
  · rintro ⟨X, hX, h⟩
    exact ⟨fun c d => Nat.pair c d ∈ X, hX, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.Bisimulation
