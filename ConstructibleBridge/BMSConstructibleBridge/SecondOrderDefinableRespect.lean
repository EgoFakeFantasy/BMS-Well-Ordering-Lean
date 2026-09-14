import BMSConstructibleBridge.SecondOrderEvaluationRespect

/-!
# 统一子集族的代表不变性

数域上的 Q 自反且两个原子图对 Q 相容时，族中每个内部索引的切片均在域 D
内保持 Q 等价，不仅限于外部标准源公式。切片本身仍是同一模型中的内部集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableRespect

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderRelatedAssignments (respects_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem row_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (D Q R T F : set_l ℳ) (h₀ : ∀ x, relation_l Q x x) (hQ : respects_l Q Q) (hR : respects_l Q R)
    (hT : SecondOrderEvaluationEquations.spec_l E D Q R T) (hF : SecondOrderDefinableFamily.spec_l E D T F)
    (i x y : num_l ℳ) (hx : mem_l x D) (hy : mem_l y D) (hxy : relation_l Q x y) :
    relation_l F i x ↔ relation_l F i y := by
  rw [hF, hF]
  change (mem_l x D ∧ _) ↔ (mem_l y D ∧ _)
  rw [and_iff_right hx, and_iff_right hy]
  apply exists_congr
  intro p
  apply exists_congr
  intro l
  apply exists_congr
  intro c
  apply and_congr Iff.rfl
  apply and_congr_right
  intro hc
  have hcc := SecondOrderRelatedAssignments.reflexive_l E Q h₀ c l hc
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨b, hb⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE c l y hc
    have h₁ := SecondOrderRelatedAssignments.extension_l hℳ E Q l c c a b x y hcc ha hb hxy
    exact ⟨b, hb, (SecondOrderEvaluationRespect.respect_l hℳ hE D Q R T h₀ hQ hR hT p
      (succ_l l) a b ha.1 hb.1 h₁).mp h⟩
  · rintro ⟨b, hb, h⟩
    obtain ⟨a, ha⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE c l x hc
    have h₁ := SecondOrderRelatedAssignments.extension_l hℳ E Q l c c a b x y hcc ha hb hxy
    exact ⟨a, ha, (SecondOrderEvaluationRespect.respect_l hℳ hE D Q R T h₀ hQ hR hT p
      (succ_l l) a b ha.1 hb.1 h₁).mpr h⟩

theorem slice_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (D Q R T F : set_l ℳ) (h₀ : ∀ x, relation_l Q x x) (hQ : respects_l Q Q) (hR : respects_l Q R)
    (hT : SecondOrderEvaluationEquations.spec_l E D Q R T) (hF : SecondOrderDefinableFamily.spec_l E D T F)
    (i : num_l ℳ) : ∃ X : set_l ℳ,
      (∀ x, mem_l x X ↔ relation_l F i x) ∧ (∀ x, mem_l x X → mem_l x D) ∧
      ∀ x y, mem_l x D → mem_l y D → relation_l Q x y → (mem_l x X ↔ mem_l y X) := by
  obtain ⟨X, hX⟩ := SecondOrderSections.exists_l hℳ F i
  refine ⟨X, hX, fun x hx => ((hF i x).mp ((hX x).mp hx)).1, ?_⟩
  intro x y hx hy hxy
  exact (hX x).trans ((row_l hℳ hE D Q R T F h₀ hQ hR hT hF i x y hx hy hxy).trans (hX y).symm)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableRespect
