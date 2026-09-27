import BMSConstructibleBridge.FiniteHeight
import BMSConstructibleBridge.FiniteStableBoundary

/-!
# 固定行数的直接稳定表示

在一个最小有限层边界以下，用单点反射逐次延长稳定链。
所有列对均在指定层稳定，因而覆盖任意合法数组的真实祖先边。
不使用生成历史、种子覆盖或全局 BMS 良基性。
稳定边界及公式数据仍是显式前提，尚非对象 Z₂ 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.FiniteHeightRepresentation

open StabilityFrame

set_option autoImplicit false

universe u

variable (D : ConstructibleStabilityFormulaData.{u}
  (stageStableLt : Nat → Ordinal.{u} → Ordinal.{u} → Prop))
variable {H : Nat} {σ : Ordinal.{u}} (hσ : FiniteStability.boundary_l (H + 1) σ)

include D hσ

/-- 同一固定层边界下存在任意有限长度的稳定链，各项也稳定于边界。 -/
theorem chain_l (n : Nat) :
    ∃ f : Nat → Ordinal.{u},
      (∀ i, i < n → stageStableLt H (f i) σ) ∧
      (∀ i j, i < j → j < n → stageStableLt H (f i) (f j)) := by
  induction n with
  | zero => exact ⟨fun _ => σ, by omega, by omega⟩
  | succ n h =>
    obtain ⟨f, hf, hF⟩ := h
    obtain ⟨β, hβ⟩ := hσ.1
    obtain ⟨γ, h₀, h₁, h₂, h₃⟩ := exists_reflectedSingleton_l D
      (lower := fun i : Fin n => f i)
      (cutoff := H + 1) hβ
      (fun i => (hf i i.2).2.1)
      (fun i _ h => FiniteStability.cutoff_l hσ (hf i i.2).2.1 h)
    refine ⟨fun i => if i < n then f i else γ, ?_, ?_⟩
    · intro i hi
      by_cases h : i < n
      · simpa only [if_pos h] using hf i h
      · simpa only [if_neg h] using h₃ H (Nat.lt_succ_self H)
    · intro i j hij hj
      have hi : i < n := by omega
      by_cases h : j < n
      · simpa only [if_pos hi, if_pos h] using hF i j hij h
      · simpa only [if_pos hi, if_neg h] using h₂ ⟨i, hi⟩ H (hf i hi)

/-- 所有当前高度有界的合法数组都有同一边界内的有界表示。 -/
theorem representation_l (a : ValidArray) (ha : HeightDescent.height_l a ≤ H) :
    ∃ p : StableRepresentation (boundedConstructibleStabilityFrame σ) a,
      ∃ α, p.BoundedBy α := by
  obtain ⟨f, hf, hF⟩ := chain_l D hσ (a.raw.length + 1)
  let p : StableRepresentation (boundedConstructibleStabilityFrame σ) a := {
    label := fun i => ⟨f i, (hf i (by omega)).2.1⟩
    strictlyIncreasing := fun {i j} hij => (hF i j hij (by omega)).2.1
    preservesAncestor := by
      intro k i j h
      obtain ⟨x, y, hx, _, _⟩ := ancestor_entries_lt h
      have hk := row_lt_uniformHeight_of_entry?_eq_some (HeightDescent.uniform_l a) hx
      exact stageStableLt_levelMonotone (by omega)
        (hF i j (isAncestor_lt h) (by omega)) }
  refine ⟨p, ⟨f a.raw.length, (hf _ (Nat.lt_succ_self _)).2.1⟩, ?_⟩
  intro i
  exact (hF i a.raw.length i.2 (Nat.lt_succ_self _)).2.1

/-- 固定层边界直接给出所有当前行数有界合法数组的可达性。 -/
theorem acc_l (a : ValidArray) (ha : HeightDescent.height_l a ≤ H) : Acc Step a := by
  obtain ⟨p, α, hα⟩ := representation_l D hσ a ha
  exact LocalDescent.acc_l
    (ExpansionReflectionState.expand_bounded (boundedFiniteReflection_l D σ)
      (FiniteStability.support_l hσ) (fun h₁ h₂ => h₁.trans h₂)
      boundedConstructibleStabilityFrame_stableLt_trans) p hα

/-- 固定行数目标不再需要高种子的覆盖或其良基性。 -/
theorem wf_l : WellFounded (FiniteHeight.step_l H) := by
  refine ⟨fun a => ?_⟩
  have h : Acc GeneratedStep a.1 := InvImage.accessible Subtype.val (acc_l D hσ a.1.1 a.2)
  exact InvImage.accessible Subtype.val h

end YesMetaZFC.BMS.ConstructibleBridge.FiniteHeightRepresentation
