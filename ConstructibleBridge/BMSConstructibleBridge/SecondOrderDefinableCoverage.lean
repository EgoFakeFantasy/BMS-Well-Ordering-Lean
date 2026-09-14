import BMSConstructibleBridge.SecondOrderDefinableFamily

/-!
# 内部子集族覆盖全部源公式的参数定义

同一个内部族包含每个源环境和每个源公式定义的数域子集。这里只证明数域
逆像；尚未将所有内部索引的切片下降到商结构或等同于集合论 Def。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableCoverage

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderAssignmentSyntax (valid_l)
open SecondOrderSourceEnvironment (represents_l)
open SecondOrderDefinableFamily (index_l)

set_option autoImplicit false

universe u v

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} {𝒩 : FirstOrder.Structure.{0, 0, 0, v} ℒ}

theorem formula_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (D Q R T F : set_l ℳ) (hT : SecondOrderEvaluationEquations.spec_l E D Q R T)
    (hF : SecondOrderDefinableFamily.spec_l E D T F) (f : num_l ℳ → 𝒩.Carrier .set)
    (hS : ∀ y, ∃ x, mem_l x D ∧ f x = y)
    (hQ : ∀ x y, mem_l x D → mem_l y D → (relation_l Q x y ↔ f x = f y))
    (hR : ∀ x y, mem_l x D → mem_l y D → (relation_l R x y ↔ SecondOrderSourceSatisfaction.member_l 𝒩 (f x) (f y)))
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ (.set :: Γ) Δ) (η : Env 𝒩 Γ Δ)
    (l c : num_l ℳ) (hc : valid_l E c l) (hη : represents_l f η E D c) (x : num_l ℳ) :
    relation_l F (index_l (SecondOrderFormulaCompilation.formula_l ℳ φ) l c) x ↔
      mem_l x D ∧ Formula.satisfies (η.pushBound (f x)) φ := by
  refine (SecondOrderDefinableFamily.row_index_l hℳ E D T F hF _ l c x).trans ?_
  apply and_congr_right
  intro hx
  rw [and_iff_right hc]
  constructor
  · rintro ⟨d, hd, h⟩
    exact (SecondOrderSourceSatisfaction.formula_l hℳ hE D Q R T hT f hS hQ hR φ (η.pushBound (f x))
      (succ_l l) d hd.1 (SecondOrderSourceEnvironment.extend_l f η E D c l d x hη hd hx)).mp h
  · intro h
    obtain ⟨d, hd⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE c l x hc
    exact ⟨d, hd, (SecondOrderSourceSatisfaction.formula_l hℳ hE D Q R T hT f hS hQ hR φ (η.pushBound (f x))
      (succ_l l) d hd.1 (SecondOrderSourceEnvironment.extend_l f η E D c l d x hη hd hx)).mpr h⟩

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (D Q R : set_l ℳ) (f : num_l ℳ → 𝒩.Carrier .set)
    (hS : ∀ y, ∃ x, mem_l x D ∧ f x = y)
    (hQ : ∀ x y, mem_l x D → mem_l y D → (relation_l Q x y ↔ f x = f y))
    (hR : ∀ x y, mem_l x D → mem_l y D → (relation_l R x y ↔ SecondOrderSourceSatisfaction.member_l 𝒩 (f x) (f y))) :
    ∃ E T F, SecondOrderBinaryPowers.spec_l E ∧ SecondOrderEvaluationEquations.spec_l E D Q R T ∧
      SecondOrderDefinableFamily.spec_l E D T F ∧
      ∀ (Γ Δ : SortContext ℒ) (η : Env 𝒩 Γ Δ), ∃ l c, valid_l E c l ∧ represents_l f η E D c ∧
        ∀ (φ : Formula ℒ (.set :: Γ) Δ) (x : num_l ℳ),
          relation_l F (index_l (SecondOrderFormulaCompilation.formula_l ℳ φ) l c) x ↔
            mem_l x D ∧ Formula.satisfies (η.pushBound (f x)) φ := by
  obtain ⟨E, hE⟩ := SecondOrderBinaryPowers.exists_l hℳ
  obtain ⟨T, hT, _⟩ := SecondOrderEvaluationFixedPoint.exists_l hℳ E D Q R
  obtain ⟨F, hF, _⟩ := SecondOrderDefinableFamily.exists_l hℳ E D T
  refine ⟨E, T, F, hE, hT, hF, ?_⟩
  intro Γ Δ η
  obtain ⟨l, c, hc, hη⟩ := SecondOrderSourceAssignment.exists_l hℳ hE D f hS η
  exact ⟨l, c, hc, hη, fun φ x => formula_l hℳ hE D Q R T F hT hF f hS hQ hR φ η l c hc hη x⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableCoverage
