import BMSConstructibleBridge.PowerlessBMSRepresentation

/-!
# 同一反射图保持完整原标签表示

反射记录中的每个具名层与表示要求的实际数码通过唯一性对齐。
全部新标签共用同一图；原数组码、实际宽度和祖先程序均不改变。
这里消费已经构造的反射图，不以“存在反射图”替代展开构造义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSRepresentationReflection

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelabelLevels (level_m levels_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

theorem image_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {T t₁ t₂ t₃ c N α β f g h : carrier_l ℳ} {H : Nat}
    {x q : PowerlessArithmetic.num_l ω} {Λ Θ : List (Nat × carrier_l ℳ)}
    (hG : PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H x q β g)
    (hh : map_l h q.val α)
    (hI : PowerlessRelabelPreservation.image_l ω e T t₁ t₂ t₃ c N α β f g h Λ Θ)
    (hΛ : Λ.map Prod.fst = levels_m (H + 1) (H + 1))
    (hΛ₀ : ∀ s ∈ Λ, PowerlessNumeral.numeral_l e s.1 s.2) :
    PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
      T t₁ t₂ t₃ c N H x q α h := by
  have hV (i a : carrier_l ℳ) (ha : value_l h i a) : ∃ b, value_l g i b := by
    obtain ⟨b, ⟨_, hb⟩, _⟩ := hG.map_l.2 i (PowerlessFunction.value_mem_l hℳ hh ha).1
    exact ⟨b, hb⟩
  refine ⟨hG.width_l, hh, hI.labels_l, ?_, ?_⟩
  · intro i j a b hij ha hb
    obtain ⟨a₀, ha₀⟩ := hV i a ha
    obtain ⟨b₀, hb₀⟩ := hV j b hb
    exact hI.order_l i j a₀ b₀ a b ha₀ hb₀ (hG.order_l i j a₀ b₀ hij ha₀ hb₀) ha hb
  · intro j hj r hr i t h₁ a b ha hb
    obtain ⟨a₀, ha₀⟩ := hV i.val a ha
    obtain ⟨b₀, hb₀⟩ := hV t.val b hb
    obtain ⟨m, hm, h₂⟩ := hG.edge_l j hj r hr i t h₁ a₀ b₀ ha₀ hb₀
    have hj₀ : level_m (H + 1) j ∈ Λ.map Prod.fst :=
      hΛ.symm ▸ PowerlessRelabelLevels.mem_m (H + 1) (Nat.lt_trans hj (Nat.lt_succ_self H))
    obtain ⟨s, hs, hs₀⟩ := List.mem_map.mp hj₀
    have hs₁ : PowerlessNumeral.numeral_l e (level_m (H + 1) j) s.2 := hs₀ ▸ hΛ₀ s hs
    have hm₀ : m = s.2 := PowerlessNumeral.unique_l hℳ hm hs₁
    refine ⟨s.2, hs₁, ?_⟩
    exact hI.upper_stable_l s hs i.val t.val a₀ b₀ a b ha₀ hb₀ (hm₀ ▸ h₂) ha hb

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSRepresentationReflection
