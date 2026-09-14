import BMSConstructibleBridge.Bisimulation
import Mathlib.Data.Nat.Find

/-!
# 换码下降链到实际子节点链的逐步构造

使用自然数最小见证逐步生成一条链，不调用对实数族的可数选择，也不把模型
内部的基础公理当成环境良基性。每一步只需原成员见证与已证的双模拟匹配。
这使树码传输可以直接消费外部“无路径”命题，而非先假定宿主 `Acc` 证书。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.TreeChain

set_option autoImplicit false

open Bisimulation

variable {R : Nat → Nat → Prop}

/-- 任意换码成员下降链可以从指定等价节点开始，逐步提升为实际子节点链。 -/
theorem lift_l (f : Nat → Nat)
    (h : ∀ n, TreeTransfer.mem_l R (eq_l R R) (f (n + 1)) (f n))
    {a : Nat} (h₀ : eq_l R R (f 0) a) :
    ∃ g : Nat → Nat, g 0 = a ∧ (∀ n, eq_l R R (f n) (g n)) ∧
      ∀ n, R (g (n + 1)) (g n) := by
  classical
  have h₁ : ∀ n b, eq_l R R (f n) b → ∃ c, R c b ∧ eq_l R R (f (n + 1)) c := by
    intro n b h₁
    exact (TreeTransfer.mem_congr_l (congruence_l R) (refl_l R _) h₁).mp (h n)
  let g : ∀ n, {b // eq_l R R (f n) b} :=
    Nat.rec ⟨a, h₀⟩ fun n b =>
      ⟨Nat.find (h₁ n b.1 b.2), (Nat.find_spec (h₁ n b.1 b.2)).2⟩
  refine ⟨fun n => (g n).1, rfl, fun n => (g n).2, ?_⟩
  intro n
  exact (Nat.find_spec (h₁ n (g n).1 (g n).2)).1

/-- 指定根中的成员下降链会给出以该根起始的实际子节点下降链。 -/
theorem root_l (f : Nat → Nat) {a : Nat}
    (h₀ : TreeTransfer.mem_l R (eq_l R R) (f 0) a)
    (h : ∀ n, TreeTransfer.mem_l R (eq_l R R) (f (n + 1)) (f n)) :
    ∃ g : Nat → Nat, g 0 = a ∧ ∀ n, R (g (n + 1)) (g n) := by
  obtain ⟨b, h₀, h₁⟩ := h₀
  obtain ⟨g, hg, _, h₂⟩ := lift_l f h h₁
  let t : Nat → Nat | 0 => a | n + 1 => g n
  refine ⟨t, rfl, ?_⟩
  intro n
  cases n with
  | zero => simpa only [t, hg] using h₀
  | succ n => exact h₂ n

/-- 外部无路径对真实成员下降成立；不要求其他代码树良基。 -/
theorem no_chain_l {a : Nat}
    (h₀ : ¬∃ g : Nat → Nat, g 0 = a ∧ ∀ n, R (g (n + 1)) (g n)) :
    ¬∃ f : Nat → Nat, TreeTransfer.mem_l R (eq_l R R) (f 0) a ∧
      ∀ n, TreeTransfer.mem_l R (eq_l R R) (f (n + 1)) (f n) := by
  rintro ⟨f, h₁, h₂⟩
  exact h₀ (root_l f h₁ h₂)

end YesMetaZFC.BMS.ConstructibleBridge.TreeChain
