import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseValues
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseEvaluation
import BMSConstructibleBridge.PowerlessRelativeClassStaticCodingReading

/-! # 同一实际坍缩图的原静态数码读回

源配数图和合法性图的既有读数通过同一个 H 的数字坐标保持性运输。
目标完整静态包提供所有 raw 合法性坐标的真实 ω 界，因此结论覆盖
全部原商输入，而非仅数字输入。零、标签、完整数值序列和实际自映射
直接读取目标原包，不更换任何图，也不假定目标是 Class 或可构造层。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseCodingReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}


private theorem tags_l (K : source_coding_l hℳ) {e t₁ t₂ t₃ : type_l hℳ}
    (h : PowerlessEvaluationTags.tags_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) e t₁ t₂ t₃) :
    e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val ∧
      t₁ = (numberCode_l K (numeral_l ℳ 1)).val ∧
        t₂ = (numberCode_l K (numeral_l ℳ 2)).val ∧
          t₃ = (numberCode_l K (numeral_l ℳ 3)).val := by
  have he : e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
    SecondOrderQuotient.ext_l hℳ _ _ (fun x => iff_of_false
      (h.1 x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  have h₁ := h.2.1
  rw [he] at h₁
  have ht₁ : t₁ = (numberCode_l K (numeral_l ℳ 1)).val :=
    PowerlessBMSQuotientRecursion.successor_unique_l
      (a := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val) h₁
      (PowerlessBMSQuotientSuccessor.successor_l K (SecondOrderModel.zero_l ℳ))
  have h₂ := h.2.2.1
  rw [ht₁] at h₂
  have ht₂ : t₂ = (numberCode_l K (numeral_l ℳ 2)).val :=
    PowerlessBMSQuotientRecursion.successor_unique_l
      (a := (numberCode_l K (numeral_l ℳ 1)).val) h₂
      (PowerlessBMSQuotientSuccessor.successor_l K (numeral_l ℳ 1))
  have h₃ := h.2.2.2
  rw [ht₂] at h₃
  exact ⟨he, ht₁, ht₂, PowerlessBMSQuotientRecursion.successor_unique_l
    (a := (numberCode_l K (numeral_l ℳ 2)).val) h₃
    (PowerlessBMSQuotientSuccessor.successor_l K (numeral_l ℳ 2))⟩

/-- 两张实际图沿同一个 H 的读数；非法 raw 坐标由原目标包排除。 -/
theorem reading_l (K : source_coding_l hℳ) {I W T H : type_l hℳ}
    (hI : ∃ x, mem_l hℳ x I) (hT : ∃ x, mem_l hℳ x T)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) W)
    (hIW : subset_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) I W)
    (h : PowerlessRelativeFiniteHullClosure.pair_matrix_reflection_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) I W)
    (hPair : ∀ a b p, mem_l hℳ a I → mem_l hℳ b I →
      pair_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) a b p → mem_l hℳ p I)
    (hωI : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x I)
    (P₀ F₀ : PowerlessMemberStructure.type_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) I)
    (P F : PowerlessMemberStructure.type_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) T)
    (hP : PowerlessMemberCollapseTransport.relation_l H P₀ P)
    (hF : PowerlessMemberCollapseTransport.relation_l H F₀ F)
    (hP₀ : PowerlessBMSQuotientPairingBounds.spec_l K P₀.val)
    (hF₀ : ∀ V : SecondOrderModel.set_l ℳ, SecondOrderTriangularFormulaSyntax.spec_l V →
      ∀ c L, value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) F₀.val c L ↔ PowerlessRelationalCodeValidity.valid_l K V c L)
    {e t₁ t₂ t₃ N : type_l hℳ}
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := (SecondOrderQuotient.structure_l hℳ))
      K.omega e t₁ t₂ t₃ P.val N F.val) :
    e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val ∧
      t₁ = (numberCode_l K (numeral_l ℳ 1)).val ∧
        t₂ = (numberCode_l K (numeral_l ℳ 2)).val ∧
          t₃ = (numberCode_l K (numeral_l ℳ 3)).val ∧
            PowerlessFiniteSequencesSyntax.spec_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) K.omega K.omega N ∧
              map_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) P.val K.omega K.omega ∧
                PowerlessBMSQuotientPairingBounds.spec_l K P.val ∧
                  ∀ V : SecondOrderModel.set_l ℳ, SecondOrderTriangularFormulaSyntax.spec_l V →
                    ∀ c L, value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) F.val c L ↔
                      PowerlessRelationalCodeValidity.valid_l K V c L := by
  obtain ⟨he, ht₁, ht₂, ht₃⟩ := tags_l K hStatic.1
  have hPN := PowerlessRelativeMembershipCollapseValues.numeric_l K
    hI hT hH hW hIW h hPair hωI P₀ P hP
  have hFN := PowerlessRelativeMembershipCollapseValues.numeric_l K
    hI hT hH hW hIW h hPair hωI F₀ F hF
  refine ⟨he, ht₁, ht₂, ht₃, hStatic.2.2.2.1, hStatic.2.1.1,
    fun n s => (hPN n s).symm.trans (hP₀ n s), ?_⟩
  intro V hV c L
  constructor
  · intro hValue
    have hQuery := (hStatic.2.2.2.2 c L).mp hValue
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨c, hQuery.1⟩
    obtain ⟨l, hl⟩ := numberCode_surjective_l K ⟨L, hQuery.2.1⟩
    have hc : c = (numberCode_l K n).val := (congrArg Subtype.val hn).symm
    have hL : L = (numberCode_l K l).val := (congrArg Subtype.val hl).symm
    rw [hc, hL] at hValue ⊢
    exact (hF₀ V hV _ _).mp ((hFN n l).mpr hValue)
  · rintro ⟨n, l, rfl, rfl, hValid⟩
    exact (hFN n l).mp ((hF₀ V hV _ _).mpr ⟨n, l, rfl, rfl, hValid⟩)

#print axioms reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseCodingReading
