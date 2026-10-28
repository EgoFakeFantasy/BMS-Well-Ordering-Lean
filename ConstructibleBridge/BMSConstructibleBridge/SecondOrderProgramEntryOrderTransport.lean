import BMSConstructibleBridge.SecondOrderProgramUniformParentComparison

/-!
# 条目图逐值搬运严格比较

两个列对的实际 `entry_m` 输出逐值一致时，其严格坐标比较一致。
这是图关系的纯逻辑搬运，不引入新的模型或选择假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramEntryOrderTransport

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramUniformParentComparison (entry_order_l)
open SecondOrderProgramEntry (entry_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 两列的可选条目图分别逐输出一致，则这对列的严格比较一致。 -/
theorem entry_order_congr_l (J : set_l ℳ)
    {x y row i j i' j' : num_l ℳ}
    (hi : ∀ q, relation_l J (value_l x (value_l i row)) q ↔
      relation_l J (value_l y (value_l i' row)) q)
    (hj : ∀ q, relation_l J (value_l x (value_l j row)) q ↔
      relation_l J (value_l y (value_l j' row)) q) :
    entry_order_l J x row i j ↔ entry_order_l J y row i' j' := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    exact ⟨a, b, (hi _).mp ha, (hj _).mp hb, hab⟩
  · rintro ⟨a, b, ha, hb, hab⟩
    exact ⟨a, b, (hi _).mpr ha, (hj _).mpr hb, hab⟩

/-- 已知两端真实 some 坐标时，条目比较正是这两个坐标的模型内部严格序。 -/
theorem entry_order_some_l (hℳ : Theory.Models ℳ theory_m) {J : set_l ℳ}
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {x row i j a b : num_l ℳ}
    (ha : relation_l J (value_l x (value_l i row)) (succ_l a))
    (hb : relation_l J (value_l x (value_l j row)) (succ_l b)) :
    entry_order_l J x row i j ↔ SecondOrderOrder.lt_l a b := by
  have hJf := function_of_semantics_l hℳ entry_m hJ
  constructor
  · rintro ⟨a', b', ha', hb', hlt⟩
    have hae : a' = a := SecondOrderModel.injective_l hℳ
      (function_value_unique_l hJf ha' ha)
    have hbe : b' = b := SecondOrderModel.injective_l hℳ
      (function_value_unique_l hJf hb' hb)
    exact hae ▸ hbe ▸ hlt
  · intro hlt
    exact ⟨a, b, ha, hb, hlt⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramEntryOrderTransport
