import BMSConstructibleBridge.SecondOrderGraphFormulaGuard
import BMSConstructibleBridge.SecondOrderSequenceCode
import BMSConstructibleBridge.PowerlessBMSQuotientCoding
import BMSConstructibleBridge.SecondOrderFunctionProperties

/-! # 原商内部有限 ω 值函数的单数编码

先把实际原商函数的求值关系转成原 Z₂ 关系实数，再使用已验证的二进制编码。
所得数精确编码全部内部坐标；不要求长度外部标准。
这是后续类内枚举的数值编码辅助接口，不宣称枚举图已经属于类。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderQuotientFiniteSequenceCode

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem relation_l (K : source_coding_l hℳ) (f : type_l hℳ) :
    ∃ H : SecondOrderModel.set_l ℳ, ∀ i j, SecondOrderPairing.relation_l H i j ↔
      SecondOrderFunctionObjects.value_l hℳ f (numberCode_l K i).val (numberCode_l K j).val := by
  let φ : Formula ℒ [] [.set, .set, .set] := SecondOrderObjectSyntax.value_m
    (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set] := (Env.empty).pushFree f
  obtain ⟨H, hH⟩ := SecondOrderGraphFormulaGuard.exists_l hℳ φ η K.less K.less
  refine ⟨H, fun i j => (hH i j).trans ?_⟩
  constructor
  · rintro ⟨hi, hj, h⟩
    exact (ThirdOrderSemantics.value_formula_l _ _ _ _).mp h
  · intro h
    exact ⟨SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec i,
      SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec j,
      (ThirdOrderSemantics.value_formula_l _ _ _ _).mpr h⟩

theorem exists_l (K : source_coding_l hℳ) {E : SecondOrderModel.set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (n : SecondOrderModel.num_l ℳ) {f : type_l hℳ}
    (hf : SecondOrderFunctionObjects.map_l hℳ f (numberCode_l K n).val K.omega) :
    ∃ c : SecondOrderModel.num_l ℳ, ∀ i j,
      SecondOrderDigit.holds_l c (SecondOrderPowers.value_l hE (SecondOrderPairing.value_l i j)) ↔
        mem_l hℳ (numberCode_l K i).val (numberCode_l K n).val ∧
          SecondOrderFunctionObjects.value_l hℳ f (numberCode_l K i).val (numberCode_l K j).val := by
  obtain ⟨H, hH⟩ := relation_l K f
  have hTotal : ∀ i, SecondOrderOrder.lt_l i n → ∃! j, SecondOrderPairing.relation_l H i j := by
    intro i hi
    obtain ⟨y, hy, _⟩ := hf.2 (numberCode_l K i).val ((numberCode_mem_iff_lt_l K i n).mpr hi)
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨y, hy.1⟩
    have hj' : (numberCode_l K j).val = y := congrArg Subtype.val hj
    refine ⟨j, (hH i j).mpr (hj'.symm ▸ hy.2), ?_⟩
    intro k hk
    apply numberCode_injective_l K
    apply Subtype.ext
    exact SecondOrderFunctionProperties.value_unique_l hℳ hf ((hH i k).mp hk) (hj'.symm ▸ hy.2)
  obtain ⟨c, hc⟩ := SecondOrderSequenceCode.exists_l hℳ hE H n hTotal
  exact ⟨c, fun i j => (hc i j).trans
    (and_congr (numberCode_mem_iff_lt_l K i n).symm (hH i j))⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderQuotientFiniteSequenceCode
