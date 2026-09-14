import Mathlib.Logic.Godel.GodelBetaFunction

/-!
# 原始递归的纯算术有限历史

先核验实际有限计算历史的算术关系，再供公式编译使用。β 读取关系只用加乘、
等式和数量词，不量化函数、有限列表或实数；存在历史由 Gödel β 引理保证。
这里的正确性仍是宿主定理，不能当作对象 PA 中的总性推导证书。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PrimitiveHistory

set_option autoImplicit false

/-- 以商和差值见证定义 β 读取；矩阵完全使用加乘和等式。 -/
def beta_l (b c i v : Nat) : Prop :=
  ∃ q d, b = q * ((i + 1) * c + 1) + v ∧ v + (d + 1) = (i + 1) * c + 1

/-- 纯算术读取关系恰好是库中 β 函数的图。 -/
theorem beta_iff_l (b c i v : Nat) : beta_l b c i v ↔
    Nat.beta (Nat.pair b c) i = v := by
  simp only [Nat.beta, Nat.unpair_pair]
  let m := (i + 1) * c + 1
  have hm : 0 < m := Nat.succ_pos _
  change beta_l b c i v ↔ b % m = v
  constructor
  · rintro ⟨q, d, h, h₀⟩
    have h₁ : v < m := by change v + (d + 1) = m at h₀; omega
    change b = q * m + v at h
    rw [h]
    simp [Nat.add_mod, Nat.mod_eq_of_lt h₁]
  · intro h
    have h₀ : v < m := h ▸ Nat.mod_lt b hm
    refine ⟨b / m, m - v - 1, ?_, ?_⟩
    · change b = b / m * m + v
      have h₁ := Nat.mod_add_div b m
      rw [h] at h₁
      simpa only [Nat.mul_comm, Nat.add_comm] using h₁.symm
    · change v + (m - v - 1 + 1) = m
      omega

/-- 与 `Nat.Primrec.prec` 完全相同的数值递归，不重新规定计算算法。 -/
def run_l (f g : Nat → Nat) (x : Nat) : Nat → Nat :=
  Nat.rec (f x) (fun i y => g (Nat.pair x (Nat.pair i y)))

/-- 有限历史规格；每一步只查询三个局部算术图。 -/
def history_l (f g : Nat → Nat) (x n y : Nat) : Prop :=
  ∃ b c, beta_l b c 0 (f x) ∧ beta_l b c n y ∧
    ∀ i < n, ∃ u v, beta_l b c i u ∧ beta_l b c (i + 1) v ∧
      g (Nat.pair x (Nat.pair i u)) = v

/-- 任意有限计算具有 β 历史，且所有满足局部规则的历史给出唯一正确输出。 -/
theorem history_iff_l (f g : Nat → Nat) (x n y : Nat) :
    history_l f g x n y ↔ run_l f g x n = y := by
  constructor
  · rintro ⟨b, c, h₀, h₁, h₂⟩
    have h₃ : ∀ i ≤ n, Nat.beta (Nat.pair b c) i = run_l f g x i := by
      intro i hi
      induction i with
      | zero => exact (beta_iff_l _ _ _ _).mp h₀
      | succ i hᵢ =>
          obtain ⟨u, v, h₄, h₅, h₆⟩ := h₂ i (by omega)
          have h₇ : u = run_l f g x i :=
            ((beta_iff_l _ _ _ _).mp h₄).symm.trans (hᵢ (by omega))
          rw [h₇] at h₆
          exact ((beta_iff_l _ _ _ _).mp h₅).trans h₆.symm
    exact (h₃ n le_rfl).symm.trans ((beta_iff_l _ _ _ _).mp h₁)
  · intro h
    let s := (List.range (n + 1)).map (run_l f g x)
    let a := Nat.unbeta s
    have h₀ : ∀ i ≤ n, beta_l a.unpair.1 a.unpair.2 i (run_l f g x i) := by
      intro i hi
      apply (beta_iff_l _ _ _ _).mpr
      rw [Nat.pair_unpair]
      have h₁ : i < s.length := by simp only [s, List.length_map, List.length_range]; omega
      have h₂ := Nat.beta_unbeta_coe s ⟨i, h₁⟩
      change Nat.beta a i = s[i] at h₂
      simpa only [s, List.getElem_map, List.getElem_range] using h₂
    refine ⟨a.unpair.1, a.unpair.2, h₀ 0 (Nat.zero_le n), ?_, ?_⟩
    · exact h ▸ h₀ n le_rfl
    · intro i hi
      exact ⟨run_l f g x i, run_l f g x (i + 1), h₀ i (by omega),
        h₀ (i + 1) (by omega), rfl⟩

end YesMetaZFC.BMS.ConstructibleBridge.PrimitiveHistory
