import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionUnique
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlots
import BMSConstructibleBridge.PowerlessRelativeClassRowOrderCanonical

/-! # 固定编码的 Sat 唯一性传至全槽查询与规范行序

传输保留任意内部更新赋值见证；不比较宿主公式求值，也不抽取查询函数。
这里只消去同一编码包、指标集及指标序下的辅助 Sat 图差异。
编码包可先于所有层固定；尚未据此构造跨层历史。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionQueryUnique

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

theorem rows_congr_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {ω A S S' e R R' p x : carrier_l ℳ₀}
    (hS : ∀ f, member_l ℳ₀ f S ↔ member_l ℳ₀ f S')
    (hR : ∀ c f, value_l (ℳ := ℳ₀) R c f ↔ value_l (ℳ := ℳ₀) R' c f) :
    PowerlessRelativeClassSatisfactionRows.query_l (ℳ₀ := ℳ₀) ω A S e R p x ↔
      PowerlessRelativeClassSatisfactionRows.query_l (ℳ₀ := ℳ₀) ω A S' e R' p x := by
  constructor
  · rintro ⟨c, f, n, g, hc, hf, hn, hg, hp, hfMap, hgMap, he, hUpdate, hValue⟩
    exact ⟨c, f, n, g, hc, (hS f).mp hf, hn, (hS g).mp hg, hp, hfMap, hgMap, he, hUpdate,
      (hR c g).mp hValue⟩
  · rintro ⟨c, f, n, g, hc, hf, hn, hg, hp, hfMap, hgMap, he, hUpdate, hValue⟩
    exact ⟨c, f, n, g, hc, (hS f).mpr hf, hn, (hS g).mpr hg, hp, hfMap, hgMap, he, hUpdate,
      (hR c g).mpr hValue⟩

theorem slots_congr_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {ω A S S' I I' R R' t x : carrier_l ℳ₀}
    (hS : ∀ f, member_l ℳ₀ f S ↔ member_l ℳ₀ f S')
    (hI : ∀ p, member_l ℳ₀ p I ↔ member_l ℳ₀ p I')
    (hR : ∀ c f, value_l (ℳ := ℳ₀) R c f ↔ value_l (ℳ := ℳ₀) R' c f) :
    PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := ℳ₀) ω A S I R t x ↔
      PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := ℳ₀) ω A S' I' R' t x :=
  exists_congr fun _e => exists_congr fun p => and_congr Iff.rfl (and_congr (hI p)
    (and_congr Iff.rfl (rows_congr_l hS hR)))

theorem queries_congr_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {ω A S I R R' J Q Q' : carrier_l ℳ₀}
    (hR : ∀ c f, value_l (ℳ := ℳ₀) R c f ↔ value_l (ℳ := ℳ₀) R' c f)
    (hQ : ∀ t x, value_l (ℳ := ℳ₀) Q t x ↔ member_l ℳ₀ t J ∧ member_l ℳ₀ x A ∧
      PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := ℳ₀) ω A S I R t x)
    (hQ' : ∀ t x, value_l (ℳ := ℳ₀) Q' t x ↔ member_l ℳ₀ t J ∧ member_l ℳ₀ x A ∧
      PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := ℳ₀) ω A S I R' t x) :
    ∀ t x, value_l (ℳ := ℳ₀) Q t x ↔ value_l (ℳ := ℳ₀) Q' t x :=
  fun t x => (hQ t x).trans ((and_congr Iff.rfl (and_congr Iff.rfl
    (slots_congr_l (fun _ => Iff.rfl) (fun _ => Iff.rfl) hR))).trans (hQ' t x).symm)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem queries_l (K : source_coding_l hℳ) {ω A e t₁ t₂ t₃ T F R R' S I J Q Q' : type_l hℳ B}
    (hω : ω.val = K.omega) (he : e.val = code_l K (SecondOrderModel.zero_l ℳ))
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := 𝒞) e t₁ t₂ t₃)
    (hT : map_l (ℳ := 𝒱) T.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hF : ∀ c L, value_l (ℳ := 𝒱) F.val c L ↔ PowerlessRelationalCodeValidity.valid_l K V c L)
    (hR : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒞) ω A e t₁ t₂ t₃ T F R)
    (hR' : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒞) ω A e t₁ t₂ t₃ T F R')
    (hQ : ∀ t x, value_l (ℳ := 𝒱) Q.val t x ↔ mem_l hℳ t J.val ∧ mem_l hℳ x A.val ∧
      PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒱) ω.val A.val S.val I.val R.val t x)
    (hQ' : ∀ t x, value_l (ℳ := 𝒱) Q'.val t x ↔ mem_l hℳ t J.val ∧ mem_l hℳ x A.val ∧
      PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒱) ω.val A.val S.val I.val R'.val t x) :
    ∀ t x, value_l (ℳ := 𝒱) Q.val t x ↔ value_l (ℳ := 𝒱) Q'.val t x :=
  queries_congr_l (ℳ₀ := 𝒱) (ω := ω.val) (A := A.val) (S := S.val) (I := I.val) (J := J.val)
    (PowerlessRelativeClassSatisfactionUnique.values_l K hω he hTags hT hPair hV hF hR hR') hQ hQ'

/-- 精确规范图不随辅助查询图变化；不能用本结论省略精确成员前提。 -/
theorem orders_l {J U A Q Q' Y L L' : SecondOrderQuotient.type_l hℳ}
    (hQ : ∀ t x, value_l (ℳ := 𝒱) Q t x ↔ value_l (ℳ := 𝒱) Q' t x)
    (hL : PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒱) J U A Q Y L)
    (hL' : PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒱) J U A Q' Y L') : L = L' :=
  PowerlessRelativeClassRowOrderCanonical.graph_unique_l
    (PowerlessRelativeClassRowOrderCanonical.graph_congr_l (fun _ _ => Iff.rfl) hQ hL) hL'

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionQueryUnique
