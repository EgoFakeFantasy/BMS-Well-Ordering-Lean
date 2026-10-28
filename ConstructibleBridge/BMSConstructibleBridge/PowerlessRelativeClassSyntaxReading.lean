import BMSConstructibleBridge.PowerlessBMSQuotientTriangularSyntax
import BMSConstructibleBridge.PowerlessRelativeClassConstructorTotal
import BMSConstructibleBridge.SecondOrderTriangularFormulaBranches
import BMSConstructibleBridge.SecondOrderTriangularFormulaLength

/-! # 相对类数码的原算术读数

只对实际 ω 内对象使用既有数码满射。原标签 0/1 是成员/相等；后继绝对性
把全部标签对齐到同一原编码。内部小于和非严格长度界由实际成员关系读取。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSyntaxReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem number_l (K : source_coding_l hℳ) {ω a : type_l hℳ B}
    (hω : ω.val = K.omega) (ha : mem_l hℳ a.val ω.val) :
    ∃ n, a.val = (numberCode_l K n).val := by
  obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨a.val, hω ▸ ha⟩
  exact ⟨n, (congrArg Subtype.val hn).symm⟩

theorem index_lt_l (K : source_coding_l hℳ) {a N : type_l hℳ B}
    {i l : SecondOrderModel.num_l ℳ} (ha : a.val = (numberCode_l K i).val)
    (hN : N.val = (numberCode_l K l).val) (h : mem_l hℳ a.val N.val) : SecondOrderOrder.lt_l i l := by
  rw [ha, hN] at h
  exact (numberCode_mem_iff_lt_l K i l).mp h

theorem index_le_l (K : source_coding_l hℳ) {N M : type_l hℳ B}
    {l m : SecondOrderModel.num_l ℳ} (hN : N.val = (numberCode_l K l).val)
    (hM : M.val = (numberCode_l K m).val) (h : subset_l (ℳ := structure_l hℳ B hBase) N M) :
    l = m ∨ SecondOrderOrder.lt_l l m := by
  rcases SecondOrderOrder.trichotomy_l hℳ l m with hLt | hEq | hLt
  · exact Or.inr hLt
  · exact Or.inl hEq
  · have hMN : mem_l hℳ M.val N.val := by
      rw [hM, hN]
      exact (numberCode_mem_iff_lt_l K m l).mpr hLt
    have hMM : mem_l hℳ M.val M.val := h M hMN
    exact (SecondOrderNaturalCases.asymmetry_l hℳ hMM hMM).elim

theorem tags_l (K : source_coding_l hℳ) {e t₁ t₂ t₃ : type_l hℳ B}
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (ht : PowerlessEvaluationTags.tags_l (ℳ := structure_l hℳ B hBase) e t₁ t₂ t₃) :
    t₁.val = (numberCode_l K (numeral_l ℳ 1)).val ∧
    t₂.val = (numberCode_l K (numeral_l ℳ 2)).val ∧
    t₃.val = (numberCode_l K (numeral_l ℳ 3)).val := by
  have h₁ := (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) e t₁).mp ht.2.1
  rw [he] at h₁
  have h₁Eq : t₁.val = (numberCode_l K (numeral_l ℳ 1)).val :=
    PowerlessBMSQuotientRecursion.successor_unique_l
      (a := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val) h₁
      (PowerlessBMSQuotientSuccessor.successor_l K (SecondOrderModel.zero_l ℳ))
  have h₂ := (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₁ t₂).mp ht.2.2.1
  rw [h₁Eq] at h₂
  have h₂Eq : t₂.val = (numberCode_l K (numeral_l ℳ 2)).val :=
    PowerlessBMSQuotientRecursion.successor_unique_l
      (a := (numberCode_l K (numeral_l ℳ 1)).val) h₂
      (PowerlessBMSQuotientSuccessor.successor_l K (numeral_l ℳ 1))
  have h₃ := (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₂ t₃).mp ht.2.2.2
  rw [h₂Eq] at h₃
  exact ⟨h₁Eq, h₂Eq, PowerlessBMSQuotientRecursion.successor_unique_l
    (a := (numberCode_l K (numeral_l ℳ 2)).val) h₃
    (PowerlessBMSQuotientSuccessor.successor_l K (numeral_l ℳ 2))⟩

theorem constructor_l (K : source_coding_l hℳ) {ω e T t a b c : type_l hℳ B}
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    {k i j n : SecondOrderModel.num_l ℳ}
    (ht : t.val = (numberCode_l K k).val) (ha : a.val = (numberCode_l K i).val)
    (hb : b.val = (numberCode_l K j).val) (hc : c.val = (numberCode_l K n).val)
    (hCode : PowerlessFormulaConstructor.constructor_l (ℳ := structure_l hℳ B hBase) ω e T t a b c) :
    SecondOrderTriangularConstructor.constructor_l k i j n := by
  have hRaw := PowerlessRelativeClassConstructorBounds.constructor_to_ambient_l (hω.symm ▸ K.omega_spec) hCode
  rw [hω, he, ht, ha, hb, hc] at hRaw
  exact (PowerlessBMSQuotientTriangularSyntax.constructor_l K hT hSpec k i j n).mp hRaw

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSyntaxReading
