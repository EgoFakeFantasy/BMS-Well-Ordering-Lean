import BMSConstructibleBridge.PowerlessBoundedCode
import BMSConstructibleBridge.PowerlessEvaluationAgreement

/-!
# 成员有界数码在传递子域上的绝对性规则

直接比较同一码、同一赋值图在两个实际求值器中的查询。
原子与与非不需传递性；有界存在仅需子域传递性和子码上的比较。
这里没有假定全初等性，也尚未把局部规则称为完整内部分类证书。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedAgreement

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationAgreement

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T A U t₁ t₂ t₃ S R F G : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hAU : subset_l A U)
  (hS : ∀ f, ThirdOrderSemantics.member_l ℳ f S ↔ ∃ n, ThirdOrderSemantics.member_l ℳ n ω ∧ map_l f n U)
  (hR : ∀ f, ThirdOrderSemantics.member_l ℳ f R ↔ ∃ n, ThirdOrderSemantics.member_l ℳ n ω ∧ map_l f n A)
  (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F)
  (hG : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G)

include hℳ hω ht hT hAU hS hR hF hG

theorem member_l {i j c : carrier_l ℳ} (hc : PowerlessFormulaConstructor.constructor_l ω e T e i j c) :
    point_l ω A F G c := by
  intro f hf
  obtain ⟨n, hn, hf⟩ := hf
  have h := PowerlessFunction.range_l hℳ hf (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hf hy).2)
  exact ((PowerlessEvaluationEquations.member_l hℳ hω ht hT hF hc f).trans (and_iff_right ((hS f).mpr ⟨n, hn, h⟩))).trans
    (((PowerlessEvaluationEquations.member_l hℳ hω ht hT hG hc f).trans (and_iff_right ((hR f).mpr ⟨n, hn, hf⟩))).symm)

theorem equal_l {i j c : carrier_l ℳ} (hc : PowerlessFormulaConstructor.constructor_l ω e T t₁ i j c) :
    point_l ω A F G c := by
  intro f hf
  obtain ⟨n, hn, hf⟩ := hf
  have h := PowerlessFunction.range_l hℳ hf (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hf hy).2)
  exact ((PowerlessEvaluationEquations.equal_l hℳ hω ht hT hF hc f).trans (and_iff_right ((hS f).mpr ⟨n, hn, h⟩))).trans
    (((PowerlessEvaluationEquations.equal_l hℳ hω ht hT hG hc f).trans (and_iff_right ((hR f).mpr ⟨n, hn, hf⟩))).symm)

theorem nand_l {a b c : carrier_l ℳ} (hc : PowerlessFormulaConstructor.constructor_l ω e T t₂ a b c)
    (ha : point_l ω A F G a) (hb : point_l ω A F G b) : point_l ω A F G c := by
  intro f hf
  obtain ⟨n, hn, hf⟩ := hf
  have h := PowerlessFunction.range_l hℳ hf (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hf hy).2)
  exact ((PowerlessEvaluationEquations.nand_l hℳ hω ht hT hF hc f).trans (and_iff_right ((hS f).mpr ⟨n, hn, h⟩))).trans
    ((not_congr (and_congr (ha f ⟨n, hn, hf⟩) (hb f ⟨n, hn, hf⟩))).trans
      (((PowerlessEvaluationEquations.nand_l hℳ hω ht hT hG hc f).trans (and_iff_right ((hR f).mpr ⟨n, hn, hf⟩))).symm))

theorem bounded_l {i j b c : carrier_l ℳ} (hA : PowerlessNaturalOrder.transitive_l A)
    (hc : PowerlessBoundedCode.code_l ω e T t₂ t₃ i j b c) (hb : point_l ω A F G b) : point_l ω A F G c := by
  intro f hf
  obtain ⟨n, hn, hf⟩ := hf
  have h := PowerlessFunction.range_l hℳ hf (fun _ y hy => hAU y (PowerlessFunction.value_mem_l hℳ hf hy).2)
  exact (PowerlessBoundedCode.equation_l hℳ hω ht hT hF hS hc f ((hS f).mpr ⟨n, hn, h⟩)).trans
    ((PowerlessBoundedQuantifier.compare_l hℳ hAU hA ⟨n, hn, hf⟩ hb).trans
      (PowerlessBoundedCode.equation_l hℳ hω ht hT hG hR hc f ((hR f).mpr ⟨n, hn, hf⟩)).symm)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedAgreement
