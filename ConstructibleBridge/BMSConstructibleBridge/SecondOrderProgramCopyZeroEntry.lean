import BMSConstructibleBridge.SecondOrderProgramCopyEntry

/-!
# 零号副本的原逐坐标回调不改变条目

不论上升测试结果和两个可选坐标是否存在，零倍增量都为零。
全部参数仍是任意内部数，不要求数组矩形或坐标外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyZeroEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 零倍复制在任意可选首末值上恰好保留原条目。 -/
theorem update_zero_l (hℳ : Theory.Models ℳ theory_m) {U : set_l ℳ}
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    (v f l y : num_l ℳ) :
    relation_l U (value_l v (value_l (zero_l ℳ) (value_l f l))) y ↔ v = y := by
  rcases predecessor_l hℳ f with rfl | ⟨a, rfl⟩
  · exact SecondOrderProgramCopyOptional.update_none_l hℳ hU v (zero_l ℳ) _ l y (Or.inl rfl)
  rcases predecessor_l hℳ l with rfl | ⟨b, rfl⟩
  · exact SecondOrderProgramCopyOptional.update_none_l hℳ hU v (zero_l ℳ) _ _ y (Or.inr rfl)
  obtain ⟨D, hDf, hD⟩ := graph_total_l hℳ SecondOrderProgramSubtraction.sub_m
  rw [SecondOrderProgramCopyOptional.update_some_l hℳ hU hD]
  simp only [SecondOrderMultiplication.zero_mul_l hℳ, add_zero_l hℳ]
  obtain ⟨d, hd, _⟩ := hDf (value_l b a)
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨d, hd, h⟩⟩

/-- 原entry回调的零号副本分支恒等，包括上升测试失败和缺行情况。 -/
theorem entry_zero_l (hℳ : Theory.Models ℳ theory_m) {R : set_l ℳ}
    (hR : graph_semantics_l (graph_m SecondOrderProgramCopyEntry.entry_m) R)
    (A f l j r v y : num_l ℳ) :
    relation_l R (value_l (value_l (value_l A (value_l (zero_l ℳ) (value_l f l))) j)
      (value_l r v)) y ↔ v = y := by
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ SecondOrderProgramAscending.ascending_m
  obtain ⟨O, hOf, hO⟩ := graph_total_l hℳ SecondOrderProgramOptionalLookup.optional_m
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ SecondOrderProgramCopyOptional.update_m
  rw [SecondOrderProgramCopyEntry.entry_rel_l hℳ hR hB hO hU]
  constructor
  · rintro (⟨_, hy⟩ | ⟨_, first, last, _, _, hy⟩)
    · exact hy
    · exact (update_zero_l hℳ hU v first last y).mp hy
  · intro hy
    by_cases hb : relation_l B (value_l A (value_l j r)) (zero_l ℳ)
    · exact Or.inl ⟨hb, hy⟩
    · obtain ⟨first, hf, _⟩ := hOf (value_l f r)
      obtain ⟨last, hl, _⟩ := hOf (value_l l r)
      exact Or.inr ⟨hb, first, last, hf, hl, (update_zero_l hℳ hU v first last y).mpr hy⟩

#print axioms update_zero_l
#print axioms entry_zero_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyZeroEntry
