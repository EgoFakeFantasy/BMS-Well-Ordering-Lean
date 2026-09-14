import BMSConstructibleBridge.SecondOrderSubsetLayer
import BMSConstructibleBridge.SecondOrderGraftSemantics

/-!
# 统一内部子集族的集合对象

先用一张关系图同时构造所有切片根，再把它们拼到新根下。输出为原图商
解释中的真正集合代码，不假定外部可数个关系实数可被收集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubsetCollection

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem selector_l (hℳ : Theory.Models ℳ theory_m) : ∃ P : set_l ℳ,
    ∀ a, mem_l a P ↔ ∃ i, SecondOrderSubsetLayer.root_l i = a := by
  let φ : Formula signature_m [] [.num] :=
    .existsE .num (PrimitiveFormulas.pair_m (numeral_m 1) (.bvar .here) (.fvar .here))
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ (pure_language_m _ rfl) Env.empty
  refine ⟨P, fun a => (hP a).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.formula_l]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ) (F : set_l ℳ) :
    ∃ G, ∃ hG : SecondOrderSubsetLayer.spec_l A.real F A.root G, ∃ H : SecondOrderGraph.code_l ℳ,
      ∀ B, SecondOrderGraph.mem_l B H ↔ ∃ i, SecondOrderGraph.eq_l B (SecondOrderSubsetLayer.code_l hℳ A F G hG i) := by
  obtain ⟨G, hG⟩ := SecondOrderSubsetLayer.exists_l hℳ A.real F A.root
  obtain ⟨P, hP⟩ := selector_l hℳ
  have hD (a : num_l ℳ) (ha : mem_l a P) : SecondOrderDomain.wf_l G a := by
    obtain ⟨i, rfl⟩ := (hP a).mp ha
    exact SecondOrderSubsetLayer.wf_l hℳ A F G hG i
  obtain ⟨H, hH⟩ := SecondOrderGraftSemantics.exists_l hℳ G P hD
  refine ⟨G, hG, H, fun B => (hH B).trans ?_⟩
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨i, rfl⟩ := (hP a).mp ha
    exact ⟨i, h⟩
  · rintro ⟨i, h⟩
    exact ⟨_, (hP _).mpr ⟨i, rfl⟩, h⟩

/-- 无隐藏外部收集假设的完整成员规格。 -/
theorem family_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ) (F : set_l ℳ) :
    ∃ H : SecondOrderGraph.code_l ℳ, ∀ B, SecondOrderGraph.mem_l B H ↔ ∃ i, ∀ C,
      SecondOrderGraph.mem_l C B ↔ ∃ a, relation_l A.real a A.root ∧ relation_l F i a ∧
        SecondOrderBisimulation.eq_l C.real A.real C.root a := by
  obtain ⟨G, hG, H, hH⟩ := exists_l hℳ A F
  refine ⟨H, fun B => (hH B).trans ?_⟩
  constructor
  · rintro ⟨i, h⟩
    exact ⟨i, fun C => (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ C) h).trans
      (SecondOrderSubsetLayer.mem_l hℳ A F G hG i C)⟩
  · rintro ⟨i, h⟩
    exact ⟨i, (SecondOrderGraph.ext_l hℳ B _).mpr
      (fun C => (h C).trans (SecondOrderSubsetLayer.mem_l hℳ A F G hG i C).symm)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubsetCollection
