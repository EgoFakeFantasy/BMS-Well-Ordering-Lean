import BMSConstructibleBridge.PowerlessFormulaValidityGraph
import BMSConstructibleBridge.PowerlessFormulaValidityTrace
import BMSConstructibleBridge.PowerlessRelationalCodeValidity

/-! # 类内合法性图与原内部合法性关系的精确对应

保留同一编码 K、三角图和标签，先构造 Seq(ω)，再对有界查询实施分离。
图规格量化全部原商坐标；合法性由实际内部自然数见证给出，不限于外部
标准数码，也不假定原二阶实数 V 本身属于相对类。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassValidity

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
  (K : source_coding_l hℳ) {ω e T t₁ t₂ t₃ : type_l hℳ B}
  (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) (hωEq : ω.val = K.omega)
  (he : e.val = code_l K (SecondOrderModel.zero_l ℳ))
  (ht : PowerlessEvaluationTags.tags_l (ℳ := structure_l hℳ B hBase) e t₁ t₂ t₃)
  (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega)
  (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
  {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)

include hω hωEq he ht hT hSpec hV

theorem query_iff_l {N : type_l hℳ B}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N.val)
    (c l : SecondOrderQuotient.type_l hℳ) :
    PowerlessFormulaValidityBounded.query_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      ω.val e.val N.val T.val t₁.val t₂.val t₃.val c l ↔
      PowerlessRelationalCodeValidity.valid_l K V c l := by
  obtain ⟨ht₁, ht₂, ht₃⟩ := PowerlessRelativeClassSyntaxReading.tags_l K he ht
  have hRead (n m : SecondOrderModel.num_l ℳ) :
      PowerlessFormulaValidityBounded.query_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val e.val N.val T.val t₁.val t₂.val t₃.val (code_l K n) (code_l K m) ↔
        SecondOrderPairing.relation_l V n m := by
    rw [hωEq, he, ht₁, ht₂, ht₃]
    exact PowerlessFormulaValidityTrace.query_iff_l K hω hωEq hN hT hSpec hV n m
  constructor
  · intro hQuery
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨c, hωEq ▸ hQuery.1⟩
    obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨l, hωEq ▸ hQuery.2.1⟩
    have hc : c = code_l K n := (congrArg Subtype.val hn).symm
    have hl : l = code_l K m := (congrArg Subtype.val hm).symm
    refine ⟨n, m, hc, hl, ?_⟩
    rw [hc, hl] at hQuery
    exact (hRead n m).mp hQuery
  · rintro ⟨n, m, rfl, rfl, hValid⟩
    exact (hRead n m).mpr hValid

theorem exists_l {N : type_l hℳ B}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N.val) :
    ∃ F : type_l hℳ B, ∀ c l : SecondOrderQuotient.type_l hℳ,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
        PowerlessRelationalCodeValidity.valid_l K V c l := by
  obtain ⟨F, hF⟩ := PowerlessFormulaValidityGraph.exists_l (hBase := hBase) ω e N T t₁ t₂ t₃
  exact ⟨F, fun c l => (hF c l).trans (query_iff_l K hω hωEq he ht hT hSpec hV hN c l)⟩

/-- 有限证书的母集实际构造，不把 Seq(ω) 的存在作为额外前提。 -/
theorem exists_for_coding_l : ∃ N F : type_l hℳ B,
    PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N.val ∧
      ∀ c l : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
          PowerlessRelationalCodeValidity.valid_l K V c l := by
  obtain ⟨N, hN, _⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l (X := ω) hω
  rw [hωEq] at hN
  obtain ⟨F, hF⟩ := exists_l K hω hωEq he ht hT hSpec hV hN
  exact ⟨N, F, hN, hF⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassValidity
