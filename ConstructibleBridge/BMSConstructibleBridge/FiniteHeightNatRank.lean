import BMSConstructibleBridge.FiniteHeight

/-!
# 固定正高度目标不存在自然数值下降秩

一行种子的一次展开可有任意多列；零号展开又逐次删去一列。
任何沿真实严格步下降的自然数值函数都必须至少等于当前列数，
因而同一种子的秩必须大于所有自然数，矛盾。

这里只排除宿主标准目标上的 Nat 值严格秩；不否定固定高度良基性、
带其他比较关系的自然数编码或真正序数秩，也不声称对象 Z₂ 终点已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.FiniteHeightNatRank

open FiniteHeight
open HeightDescent (height_l expand_le_l diagonal_le_l)

set_option autoImplicit false

/-- 删末列给出任意自然数严格秩的必要下界。 -/
theorem length_le_l {N : Nat} (f : carrier_l N → Nat)
    (hf : ∀ {a b}, step_l N a b → f a < f b) (a : carrier_l N) :
    a.1.1.raw.length ≤ f a := by
  generalize hn : a.1.1.raw.length = n
  induction n generalizing a with
  | zero => omega
  | succ n ih =>
      let b : carrier_l N := ⟨⟨a.1.1.expand 0, .expand a.1.2 0⟩,
        Nat.le_trans (expand_le_l a.1.1 0) a.2⟩
      have hb : b.1.1.raw.length = n := by
        change (a.1.1.expand 0).raw.length = n
        rw [ValidArray.length_expand_zero, hn]
        omega
      have h₀ : step_l N b a :=
        ValidArray.step_expand_zero_of_pos a.1.1 (by omega)
      have h₁ := ih b hb
      have h₂ := hf h₀
      omega

/-- 每个正高度上界下，真实生成数组的严格展开都不可能由通常自然数序计秩。 -/
theorem no_nat_rank_l (N : Nat) (hN : 0 < N) :
    ¬ ∃ f : carrier_l N → Nat, ∀ {a b}, step_l N a b → f a < f b := by
  rintro ⟨f, hf⟩
  have h₁ : height_l (validSeed 1) ≤ N := by
    change 1 ≤ N
    omega
  let a : carrier_l N := ⟨⟨validSeed 1, .seed 1⟩, h₁⟩
  let k := f a + 2
  let b : carrier_l N := ⟨⟨SeedExpansion.diagonal_l 0 k, by
    rw [← SeedExpansion.expand_l]
    exact .expand (.seed 1) k⟩, Nat.le_trans (diagonal_le_l 0 k) (Nat.zero_le N)⟩
  have hb : b.1.1.raw.length = k + 1 := SeedExpansion.length_l 0 k
  have ha : a.1.1.raw.length = 2 := rfl
  have h₂ : step_l N b a := by
    refine ⟨⟨k, (SeedExpansion.expand_l 0 k).symm⟩, ?_⟩
    intro h
    have h₃ := congrArg (fun c : ValidArray => c.raw.length) h
    change b.1.1.raw.length = a.1.1.raw.length at h₃
    rw [hb, ha] at h₃
    dsimp [k] at h₃
    omega
  have h₃ := length_le_l f hf b
  have h₄ := hf h₂
  rw [hb] at h₃
  dsimp [k] at h₃
  omega

end YesMetaZFC.BMS.ConstructibleBridge.FiniteHeightNatRank
