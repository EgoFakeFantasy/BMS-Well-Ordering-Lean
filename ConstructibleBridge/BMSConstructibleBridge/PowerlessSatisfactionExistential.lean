import BMSConstructibleBridge.PowerlessSatisfactionLogicalBranches
import BMSConstructibleBridge.PowerlessRelativeClassFunctionProperties

/-! # 合法性守卫求值图的指定槽存在量词分支

量词更新保持同一个内部赋值长度。原存在方程中的长度见证通过函数定义域
唯一性对齐，再把每个更新赋值上的 G 读数换成 R；不按外部长度归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionExistential

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessFormulaValidityReading (code_l)
open PowerlessSatisfactionLogicalBranches (read_class_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem transfer_l {ω A G R f i b L : type_l hℳ B}
    (hf : map_l (ℳ := structure_l hℳ B hBase) f L A)
    (hRead : ∀ g, map_l (ℳ := structure_l hℳ B hBase) g L A →
      (value_l (ℳ := structure_l hℳ B hBase) G b g ↔ value_l (ℳ := structure_l hℳ B hBase) R b g)) :
    PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := structure_l hℳ B hBase) ω A G f i b ↔
      PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := structure_l hℳ B hBase) ω A R f i b := by
  constructor
  · rintro ⟨m, hm, hfm, hi, a, ha, g, hg, hUpdate, hValue⟩
    have hLength := PowerlessRelativeClassFunctionProperties.domain_unique_l hfm hf
    subst m
    exact ⟨L, hm, hfm, hi, a, ha, g, hg, hUpdate, (hRead g hg).mp hValue⟩
  · rintro ⟨m, hm, hfm, hi, a, ha, g, hg, hUpdate, hValue⟩
    have hLength := PowerlessRelativeClassFunctionProperties.domain_unique_l hfm hf
    subst m
    exact ⟨L, hm, hfm, hi, a, ha, g, hg, hUpdate, (hRead g hg).mpr hValue⟩

theorem equation_l (K : source_coding_l hℳ) {V : SecondOrderModel.set_l ℳ}
    {ω A S F G R e T t₁ t₂ t₃ : type_l hℳ B} (hωEq : ω.val = K.omega)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val A.val S.val)
    (hF : ∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
      PowerlessRelationalCodeValidity.valid_l K V c l)
    (hR : ∀ c f, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val c f ↔
      PowerlessSatisfactionBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val A.val S.val F.val G.val c f)
    (hSystem : PowerlessRelativeClassEvaluationSystem.spec_l
      (𝒩 := structure_l hℳ B hBase) ω A e t₁ t₂ t₃ T S G)
    (he : e.val = code_l K (SecondOrderModel.zero_l ℳ))
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    {c i b L f : type_l hℳ B} {n j k l : SecondOrderModel.num_l ℳ}
    (hc : c.val = code_l K n) (hi : i.val = code_l K j) (hb : b.val = code_l K k)
    (hL : L.val = code_l K l)
    (hCode : PowerlessFormulaConstructor.constructor_l (ℳ := structure_l hℳ B hBase) ω e T t₃ i b c)
    (hj : mem_l hℳ i.val L.val) (hk : SecondOrderPairing.relation_l V k l)
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f L A) :
    value_l (ℳ := structure_l hℳ B hBase) R c f ↔
      PowerlessFiniteEvaluationRelationEquations.exists_l (𝒩 := structure_l hℳ B hBase) ω A R f i b := by
  obtain ⟨_, _, ht₃⟩ := PowerlessRelativeClassSyntaxReading.tags_l K he hSystem.1
  have hNative := PowerlessRelativeClassSyntaxReading.constructor_l K hωEq he hT hSpec ht₃ hi hb hc hCode
  have hValid := (SecondOrderTriangularFormulaBranches.existential_l hℳ hV hNative l).mpr
    ⟨PowerlessRelativeClassSyntaxReading.index_lt_l K hi hL hj, hk⟩
  have hcω : mem_l hℳ c.val ω.val := by
    rw [hc, hωEq]
    exact (numberCode_l K n).property
  have hLω : mem_l hℳ L.val ω.val := by
    rw [hL, hωEq]
    exact (numberCode_l K l).property
  have hf : mem_l hℳ f.val S.val := (hSystem.2.2.2.1 f).mpr ⟨L, hLω, hMap⟩
  have hEquation := ((hSystem.2.2.2.2.2 c hcω f i b).2.2.2 hCode).trans (and_iff_right hf)
  exact (read_class_l K hωEq hS hF hR hc hL hValid hMap).trans
    (hEquation.trans (transfer_l hMap (fun g hg => (read_class_l K hωEq hS hF hR hb hL hk hg).symm)))

#print axioms transfer_l
#print axioms equation_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionExistential
