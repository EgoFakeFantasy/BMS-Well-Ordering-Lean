import BMSConstructibleBridge.PowerlessRelabelAppend

/-!
# 三段标签图的坐标与稳定边读回

在已经实际构造的 f+h+g 中，逐项读回旧前缀、反射块和恢复的原末块。
具名稳定边与顶端迹因此保持原列身份；跨新旧块的低行稳定边由顶端迹和传递性取得。
本模块不把这些源稳定条件冒充为已经验证的 BMS 祖先性质。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelCoordinates

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ c N α β p q r s f g h u v : carrier_l ℳ}
  {Λ Θ : List (Nat × carrier_l ℳ)}
  (hS : PowerlessRelabelAppend.step_l ω e T t₁ t₂ t₃ c N α β p q r s f g h u v Λ Θ)

include hℳ hS

/-- 两次拼接后，旧前缀的同一下标仍读取原值。 -/
theorem prefix_l {A i a : carrier_l ℳ} (hf : map_l f p A) (hi : member_l ℳ i p) :
    value_l v i a ↔ value_l f i a := by
  obtain ⟨b, ⟨_, hb⟩, _⟩ := hf.2 i hi
  have hb₀ := (hS.prefix_graph_l i b).mpr (Or.inl hb)
  exact (PowerlessConcatenation.prefix_l hℳ hS.prefix_map_l hS.map_l hS.graph_l
    (PowerlessFunction.value_mem_l hℳ hS.prefix_map_l hb₀).1).trans
    (PowerlessConcatenation.prefix_l hℳ hf hS.prefix_map_l hS.prefix_graph_l hi)

/-- 中间块在 p+j 处读取同一反射图的第 j 项。 -/
theorem middle_l {i j a : carrier_l ℳ} (hj : member_l ℳ j q)
    (hi : PowerlessAddition.addition_l ω e p j i) : value_l v i a ↔ value_l h j a := by
  obtain ⟨b, ⟨_, hb⟩, _⟩ := hS.image_map_l.2 j hj
  have hb₀ := (hS.prefix_graph_l i b).mpr (Or.inr ⟨j, hi, hb⟩)
  exact (PowerlessConcatenation.prefix_l hℳ hS.prefix_map_l hS.map_l hS.graph_l
    (PowerlessFunction.value_mem_l hℳ hS.prefix_map_l hb₀).1).trans
    (PowerlessConcatenation.shift_l hℳ hS.image_map_l hS.prefix_map_l hS.prefix_graph_l hj hi)

/-- 最后恢复的块在 r+j 处读取原 g，而不是另一张新选的图。 -/
theorem last_l {B i j a : carrier_l ℳ} (hg : map_l g q B) (hj : member_l ℳ j q)
    (hi : PowerlessAddition.addition_l ω e r j i) : value_l v i a ↔ value_l g j a :=
  PowerlessConcatenation.shift_l hℳ hg hS.map_l hS.graph_l hj hi

/-- 原前缀到原块的具名稳定边，转为实际拼接图中前缀到反射块的边。 -/
theorem lower_l {A B i j x a b a₁ b₁ : carrier_l ℳ} {t : Nat × carrier_l ℳ}
    (hf : map_l f p A) (hg : map_l g q B) (ht : t ∈ Λ)
    (ha : value_l f i a) (hb : value_l g j b)
    (hαβ : PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 a b)
    (hx : PowerlessAddition.addition_l ω e p j x) (ha₁ : value_l v i a₁)
    (hb₁ : value_l v x b₁) : PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 a₁ b₁ := by
  have ha₂ := (prefix_l hℳ hS hf (PowerlessFunction.value_mem_l hℳ hf ha).1).mp ha₁
  have hb₂ := (middle_l hℳ hS (PowerlessFunction.value_mem_l hℳ hg hb).1 hx).mp hb₁
  exact PowerlessFunction.value_unique_l hℳ hf ha ha₂ ▸
    hS.image_l.lower_stable_l t ht i j a b b₁ ha hb hαβ hb₂

/-- 原块内部的具名稳定边，保留在反射块对应的两处实际全局坐标上。 -/
theorem upper_l {B i j x y a b a₁ b₁ : carrier_l ℳ} {t : Nat × carrier_l ℳ}
    (hg : map_l g q B) (ht : t ∈ Λ) (ha : value_l g i a) (hb : value_l g j b)
    (hαβ : PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 a b)
    (hx : PowerlessAddition.addition_l ω e p i x)
    (hy : PowerlessAddition.addition_l ω e p j y) (ha₁ : value_l v x a₁)
    (hb₁ : value_l v y b₁) : PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 a₁ b₁ :=
  hS.image_l.upper_stable_l t ht i j a b a₁ b₁ ha hb hαβ
    ((middle_l hℳ hS (PowerlessFunction.value_mem_l hℳ hg ha).1 hx).mp ha₁)
    ((middle_l hℳ hS (PowerlessFunction.value_mem_l hℳ hg hb).1 hy).mp hb₁)

/-- 低行顶端迹从 β 降到 α，同时保留拼接后的实际列坐标。 -/
theorem top_l {B i j a b : carrier_l ℳ} {t : Nat × carrier_l ℳ}
    (hg : map_l g q B) (ht : t ∈ Θ) (ha : value_l g j a)
    (hαβ : PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 a β)
    (hi : PowerlessAddition.addition_l ω e p j i) (hb : value_l v i b) :
    PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 b α :=
  hS.image_l.top_l t ht j a b ha hαβ
    ((middle_l hℳ hS (PowerlessFunction.value_mem_l hℳ hg ha).1 hi).mp hb)

/-- 新反射块到恢复末块的低行边：先反射到 α，再接原 α 到右标签的边或等式。 -/
theorem cross_l {B i j x y a b a₁ b₁ : carrier_l ℳ} {t : Nat × carrier_l ℳ}
    (hω : omega_l ω) (hg : map_l g q B) (ht : t ∈ Θ)
    (ha : value_l g i a) (hb : value_l g j b)
    (hαβ : PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 a β)
    (hα : b = α ∨ PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 α b)
    (hx : PowerlessAddition.addition_l ω e p i x)
    (hy : PowerlessAddition.addition_l ω e r j y) (ha₁ : value_l v x a₁)
    (hb₁ : value_l v y b₁) : PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ t.2 a₁ b₁ := by
  have h₀ := top_l hℳ hS hg ht ha hαβ hx ha₁
  have hb₂ := (last_l hℳ hS hg (PowerlessFunction.value_mem_l hℳ hg hb).1 hy).mp hb₁
  have hb₃ := PowerlessFunction.value_unique_l hℳ hg hb hb₂
  rcases hα with hα | hα
  · exact hα.symm.trans hb₃ ▸ h₀
  · exact hb₃ ▸ PowerlessStageStabilityOrder.trans_l hℳ hω h₀ hα

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelCoordinates
