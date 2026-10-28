import BMSConstructibleBridge.PowerlessSatisfactionSpecification
import BMSConstructibleBridge.PowerlessSatisfactionExistential

/-! # 实际类内求值图满足完整 Sat 规格

通过内部数码满射消去四分支接口中的原算术数值参数。定义域从同一张
有界图读取，零码在所有赋值上恒假；不把外部语法归纳施于模型内部 ω。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionSpecification

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessFormulaValidityReading (code_l)
open PowerlessRelativeClassSyntaxReading (number_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem validity_l (K : source_coding_l hℳ) {V : SecondOrderModel.set_l ℳ} {F : type_l hℳ B}
    (hF : ∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
      PowerlessRelationalCodeValidity.valid_l K V c l)
    {c L : type_l hℳ B} {n l : SecondOrderModel.num_l ℳ}
    (hc : c.val = code_l K n) (hL : L.val = code_l K l) :
    value_l (ℳ := structure_l hℳ B hBase) F c L ↔ SecondOrderPairing.relation_l V n l := by
  refine (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F c L).trans
    ((hF c.val L.val).trans ?_)
  constructor
  · rintro ⟨n', l', hn, hl, hValid⟩
    have hnEq : n = n' := numberCode_injective_l K (Subtype.ext (hc.symm.trans hn))
    have hlEq : l = l' := numberCode_injective_l K (Subtype.ext (hL.symm.trans hl))
    subst n'
    subst l'
    exact hValid
  · intro hValid
    exact ⟨n, l, hc, hL, hValid⟩

variable {ω A S F G R : type_l hℳ B}
  (hR : ∀ c f, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val c f ↔
    PowerlessSatisfactionBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      ω.val A.val S.val F.val G.val c f)

include hR

theorem domain_l : PowerlessSatisfactionSpecification.domain_l (𝒩 := structure_l hℳ B hBase) ω A F R := by
  intro c f hValue
  have hRaw := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R c f).mp hValue
  obtain ⟨hc, _, L, hL, hF, hMap, _⟩ := (hR c.val f.val).mp hRaw
  let L' : type_l hℳ B := ⟨L, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hL⟩
  exact ⟨hc, L', hL,
    (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F c L').mpr hF,
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f L' A).mpr hMap⟩

theorem zero_l {e : type_l hℳ B}
    (hZero : ∀ f, ¬value_l (ℳ := structure_l hℳ B hBase) G e f) :
    PowerlessSatisfactionSpecification.zero_l (𝒩 := structure_l hℳ B hBase) e R := by
  intro f hValue
  have hRaw := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R e f).mp hValue
  obtain ⟨_, _, _, _, _, _, hG⟩ := (hR e.val f.val).mp hRaw
  exact hZero f ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G e f).mpr hG)

theorem instance_l (K : source_coding_l hℳ) {V : SecondOrderModel.set_l ℳ}
    {e T t₁ t₂ t₃ : type_l hℳ B} (hωEq : ω.val = K.omega)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val A.val S.val)
    (hF : ∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
      PowerlessRelationalCodeValidity.valid_l K V c l)
    (hSystem : PowerlessRelativeClassEvaluationSystem.spec_l
      (𝒩 := structure_l hℳ B hBase) ω A e t₁ t₂ t₃ T S G)
    (he : e.val = code_l K (SecondOrderModel.zero_l ℳ))
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    (hV : SecondOrderTriangularFormulaSyntax.spec_l V) :
    PowerlessSatisfactionSpecification.spec_l (𝒩 := structure_l hℳ B hBase) ω A e t₁ t₂ t₃ T F R := by
  refine ⟨domain_l hR, zero_l hR hSystem.2.2.2.2.1, ?_⟩
  intro c L f hcω hLω hMap a b
  obtain ⟨n, hc⟩ := number_l K hωEq hcω
  obtain ⟨l, hL⟩ := number_l K hωEq hLω
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hCode hi hj
    obtain ⟨i, ha⟩ := number_l K hωEq hCode.1
    obtain ⟨j, hb⟩ := number_l K hωEq hCode.2.1
    exact PowerlessSatisfactionLogicalBranches.membership_l K hωEq hS hF hR hSystem he hT hSpec hV
      hc ha hb hL hCode hi hj hMap
  · intro hCode hi hj
    obtain ⟨i, ha⟩ := number_l K hωEq hCode.1
    obtain ⟨j, hb⟩ := number_l K hωEq hCode.2.1
    exact PowerlessSatisfactionLogicalBranches.equality_l K hωEq hS hF hR hSystem he hT hSpec hV
      hc ha hb hL hCode hi hj hMap
  · intro hCode hi hj
    obtain ⟨i, ha⟩ := number_l K hωEq hCode.1
    obtain ⟨j, hb⟩ := number_l K hωEq hCode.2.1
    exact PowerlessSatisfactionLogicalBranches.nand_l K hωEq hS hF hR hSystem he hT hSpec hV
      hc ha hb hL hCode ((validity_l K hF ha hL).mp hi) ((validity_l K hF hb hL).mp hj) hMap
  · intro hCode hi hj
    obtain ⟨i, ha⟩ := number_l K hωEq hCode.1
    obtain ⟨j, hb⟩ := number_l K hωEq hCode.2.1
    exact PowerlessSatisfactionExistential.equation_l K hωEq hS hF hR hSystem he hT hSpec hV
      hc ha hb hL hCode hi ((validity_l K hF hb hL).mp hj) hMap

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionSpecification
