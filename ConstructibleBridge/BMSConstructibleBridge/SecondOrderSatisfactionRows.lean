import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionRows
import BMSConstructibleBridge.SecondOrderFunctionUpdate

/-! # 原 Z₂ 商中的指定槽完整查询读数

查询正文逐字复用原 query_m/query_l。原商映射的坐标界与定义域
唯一性将有界更新读为全部原商坐标的实际更新，不要求 Class 资格
或完整源理论。本模块不重新构造 Sat，也不改变原查询的赋值界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSatisfactionRows

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeClassSatisfactionRows (query_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem read_l {ω A S e R p c f n x : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω A S)
    (hp : ordered_l (ℳ := 𝒱) c f p) (hc : mem_l hℳ c ω)
    (hn : mem_l hℳ n ω) (hf : map_l (ℳ := 𝒱) f n A)
    (he : mem_l hℳ e n) (hx : mem_l hℳ x A) :
    query_l (ℳ₀ := 𝒱) ω A S e R p x ↔
      ∃ g : type_l hℳ, map_l (ℳ := 𝒱) g n A ∧
        PowerlessAssignmentUpdate.update_l (ℳ := 𝒱) f e x g ∧ value_l (ℳ := 𝒱) R c g := by
  constructor
  · rintro ⟨c', f', n', g, _, _, _, _, hp', hf', hg, he', hUpdate, hValue⟩
    obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hp' hp).mp rfl
    have hn' := SecondOrderFunctionUpdate.length_unique_l hℳ hf' hf
    subst n'
    exact ⟨g, hg, (PowerlessAssignmentUpdateBounded.update_iff_l hℳ hf hg he hx).mp hUpdate, hValue⟩
  · rintro ⟨g, hg, hUpdate, hValue⟩
    exact ⟨c, f, n, g, hc, (hS f).mpr ⟨n, hn, hf⟩, hn, (hS g).mpr ⟨n, hn, hg⟩,
      hp, hf, hg, he, (PowerlessAssignmentUpdateBounded.update_iff_l hℳ hf hg he hx).mpr hUpdate, hValue⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSatisfactionRows
