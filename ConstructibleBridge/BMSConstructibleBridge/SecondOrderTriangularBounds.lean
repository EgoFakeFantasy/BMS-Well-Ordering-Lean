import BMSConstructibleBridge.SecondOrderTriangularArithmetic

/-! # 三角数支配输入与严格后继增长

前驱分支及上一三角数的存在足够给出下界，不使用宿主归纳或数域良基性。
增长直接读取已证递推方程的正差；两个界限均有原算术闭句推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularBounds

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel SecondOrderNumbers
open SecondOrderTriangularArithmetic (relation_l relation_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem lower_l (hℳ : Theory.Models ℳ theory_m) {n t : num_l ℳ} (ht : relation_l n t) :
    n = t ∨ SecondOrderOrder.lt_l n t := by
  rcases predecessor_l hℳ n with rfl | ⟨k, rfl⟩
  · have hZero : relation_l (zero_l ℳ) (zero_l ℳ) := by
      change add_l (zero_l ℳ) (zero_l ℳ) = mul_l (zero_l ℳ) (succ_l (zero_l ℳ))
      rw [add_zero_l hℳ, SecondOrderMultiplication.zero_mul_l hℳ]
    exact Or.inl (SecondOrderTriangularArithmetic.unique_l hℳ ht hZero).symm
  · obtain ⟨q, hq⟩ := SecondOrderTriangularArithmetic.exists_l hℳ k
    have hStep := SecondOrderTriangularArithmetic.successor_l hℳ hq ht
    rcases predecessor_l hℳ q with rfl | ⟨v, rfl⟩
    · exact Or.inl (hStep.trans (zero_add_l hℳ _)).symm
    · exact Or.inr ⟨v, (add_comm_l hℳ (succ_l k) (succ_l v)).trans hStep.symm⟩

theorem growth_l (hℳ : Theory.Models ℳ theory_m) {n t v : num_l ℳ}
    (ht : relation_l n t) (hv : relation_l (succ_l n) v) : SecondOrderOrder.lt_l t v :=
  ⟨n, (SecondOrderTriangularArithmetic.successor_l hℳ ht hv).symm⟩

def sentence_m : Sentence signature_m := .forallE .num <| .forallE .num <|
  .imp (relation_m (.bvar (.there .here)) (.bvar .here)) <| .conj
    (.disj (.equal (.bvar (.there .here)) (.bvar .here))
      (PrimitiveFormulas.lt_m (.bvar (.there .here)) (.bvar .here))) <|
    .forallE .num <| .imp
      (relation_m (Term.app (σ := signature_m) .succ (.cons (.bvar (.there (.there .here))) .nil)) (.bvar .here))
      (PrimitiveFormulas.lt_m (.bvar (.there .here)) (.bvar .here))

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies,
    SecondOrderTriangularArithmetic.relation_formula_l, SecondOrderOrder.formula_l, Term.eval]
  intro n t ht
  exact ⟨lower_l hℳ ht, fun v hv => growth_l hℳ ht hv⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularBounds
