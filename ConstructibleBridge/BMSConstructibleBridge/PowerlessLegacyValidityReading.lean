import BMSConstructibleBridge.PowerlessLegacyNumericReading
import BMSConstructibleBridge.SecondOrderInternalFormulaSyntax

/-! # 原五标签有界检查器的一步读数

背景是原 num/set 语言的 Z₂ 模型及同一 quotient 数码编码 K；完整 raw
Seq(ω,ω) 参数 N 只用于读取旧平方配对。显式 hRead 在全部内部数坐标上
把任意 raw 表 f 的值一查询连接到实际内部实数 X。

逐分支读数保持旧零码和五标签规则：否定只读取子码合法性，存在分支读取
后继槽数，不改成新三角 quotation。本模块是有限证书拼接的语义辅助接口，
不构造 Class 图，也不宣称原推导核中的统一合法性或 BMS 终局已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyValidityReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)
open SecondOrderModel (num_l set_l zero_l succ_l)
open SecondOrderEvaluationRule (numeral_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

variable (K : source_coding_l hℳ) {N : type_l hℳ}
  (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
    K.omega K.omega N)

include hN

/-- 原子公式的两个内部变量编号均严格小于当前槽数。 -/
theorem atomic_l (payload l : num_l ℳ) :
    PowerlessLegacyValidityBounded.atomic_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N (code_l K payload) (code_l K l) ↔
    SecondOrderInternalFormulaSyntax.atomic_l payload l := by
  unfold PowerlessLegacyValidityBounded.atomic_holds_l SecondOrderInternalFormulaSyntax.atomic_l
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro i
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro j
  exact and_congr
    ((PowerlessBoundedNumericPairing.instance_l K hN i j (code_l K payload)).trans
      ((PowerlessLegacyNumericReading.code_eq_l K payload _).trans ⟨Eq.symm, Eq.symm⟩))
    (and_congr (numberCode_mem_iff_lt_l K i l) (numberCode_mem_iff_lt_l K j l))

variable {f : type_l hℳ} (X : set_l ℳ)
  (hRead : ∀ n l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f
    (code_l K (SecondOrderPairing.value_l n l)) (code_l K (numeral_l ℳ 1)) ↔
      SecondOrderPairing.relation_l X n l)

include hRead

/-- 值一查询只消费给定的全内部坐标读数，不要求 f 是 Class 或零一总图。 -/
theorem query_l (n l : num_l ℳ) :
    PowerlessLegacyValidityBounded.query_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N (code_l K (numeral_l ℳ 1)) f
        (code_l K n) (code_l K l) ↔ SecondOrderPairing.relation_l X n l :=
  (PowerlessLegacyNumericReading.query_l K hN f n l).trans (hRead n l)

/-- 合取严格使用原平方配对解码两个子码，并读取同一槽数的合法性。 -/
theorem binary_l (payload l : num_l ℳ) :
    PowerlessLegacyValidityBounded.binary_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N (code_l K (numeral_l ℳ 1)) f
        (code_l K payload) (code_l K l) ↔
    SecondOrderEvaluationRule.conjunction_l X payload l := by
  unfold PowerlessLegacyValidityBounded.binary_holds_l SecondOrderEvaluationRule.conjunction_l
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro i
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro j
  exact and_congr
    ((PowerlessBoundedNumericPairing.instance_l K hN i j (code_l K payload)).trans
      ((PowerlessLegacyNumericReading.code_eq_l K payload _).trans ⟨Eq.symm, Eq.symm⟩))
    (and_congr (query_l K hN X hRead i l) (query_l K hN X hRead j l))

/-- 存在分支的原集合后继精确读取内部槽数后继。 -/
theorem existential_l (payload l : num_l ℳ) :
    PowerlessLegacyValidityBounded.existential_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N (code_l K (numeral_l ℳ 1)) f
        (code_l K payload) (code_l K l) ↔
    SecondOrderPairing.relation_l X payload (succ_l l) := by
  unfold PowerlessLegacyValidityBounded.existential_holds_l
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  simp only [PowerlessNumberSuccessorReading.successor_l K,
    PowerlessLegacyNumericReading.code_eq_l K, query_l K hN X hRead]
  constructor
  · rintro ⟨m, rfl, h⟩
    exact h
  · intro h
    exact ⟨succ_l l, rfl, h⟩

/-- 五个标签逐项对应；标签二读取子码合法性，不对该值作布尔反转。 -/
theorem cases_l (tag payload l : num_l ℳ) :
    PowerlessLegacyValidityBounded.cases_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N
        (code_l K (numeral_l ℳ 1)) (code_l K (numeral_l ℳ 2))
        (code_l K (numeral_l ℳ 3)) (code_l K (numeral_l ℳ 4)) f
        (code_l K tag) (code_l K payload) (code_l K l) ↔
    SecondOrderInternalFormulaSyntax.cases_l X l tag payload := by
  unfold PowerlessLegacyValidityBounded.cases_holds_l SecondOrderInternalFormulaSyntax.cases_l
  exact or_congr
    (and_congr
      (or_congr (PowerlessLegacyNumericReading.code_eq_l K tag _)
        (PowerlessLegacyNumericReading.code_eq_l K tag _))
      (atomic_l K hN payload l))
    (or_congr
      (and_congr (PowerlessLegacyNumericReading.code_eq_l K tag _)
        (query_l K hN X hRead payload l))
      (or_congr
        (and_congr (PowerlessLegacyNumericReading.code_eq_l K tag _)
          (binary_l K hN X hRead payload l))
        (and_congr (PowerlessLegacyNumericReading.code_eq_l K tag _)
          (existential_l K hN X hRead payload l))))

omit hRead

/-- 旧零码与全部内部节点的一步规则精确读取原合法性算子。 -/
theorem rule_l (f : type_l hℳ) (X : set_l ℳ) (n l : num_l ℳ)
    (hRead : ∀ i j, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f
      (code_l K (SecondOrderPairing.value_l i j)) (code_l K (numeral_l ℳ 1)) ↔
        SecondOrderPairing.relation_l X i j) :
    PowerlessLegacyValidityBounded.rule_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N
        (code_l K (numeral_l ℳ 1)) (code_l K (numeral_l ℳ 2))
        (code_l K (numeral_l ℳ 3)) (code_l K (numeral_l ℳ 4)) f
        (code_l K n) (code_l K l) ↔ SecondOrderInternalFormulaSyntax.rule_l X n l := by
  unfold PowerlessLegacyValidityBounded.rule_holds_l SecondOrderInternalFormulaSyntax.rule_l
  refine or_congr (PowerlessLegacyNumericReading.code_eq_l K n (zero_l ℳ)) ?_
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro tag
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro payload
  exact and_congr
    ((PowerlessLegacyNumericReading.node_l K hN tag payload (code_l K n)).trans
      ((PowerlessLegacyNumericReading.code_eq_l K n _).trans ⟨Eq.symm, Eq.symm⟩))
    (cases_l K hN X hRead tag payload l)

#print axioms atomic_l
#print axioms query_l
#print axioms binary_l
#print axioms existential_l
#print axioms cases_l
#print axioms rule_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyValidityReading
