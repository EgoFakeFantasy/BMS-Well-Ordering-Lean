import BMSConstructibleBridge.PowerlessRelativeClassSyntaxReading
import BMSConstructibleBridge.PowerlessRelationalSourceCompilation

/-! # 同一编译输出属于原内部合法性关系

有限构造证书解释到原 Z₂ 已构造的合法性关系 V；反向并不成立，也不作
反向声明。最终 valid_l 明确给出实际原自然数见证，避免条件读数空泛成立。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCodeValidity

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelationalCodeDerivation (derivation_l)
open PowerlessRelativeClassSyntaxReading (number_l index_lt_l index_le_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

def valid_l (K : source_coding_l hℳ) (V : SecondOrderModel.set_l ℳ)
    (c N : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∃ n l, c = (numberCode_l K n).val ∧ N = (numberCode_l K l).val ∧ SecondOrderPairing.relation_l V n l

variable (K : source_coding_l hℳ) {ω e T t₁ t₂ t₃ : type_l hℳ B}
  (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
  (ht : PowerlessEvaluationTags.tags_l (ℳ := structure_l hℳ B hBase) e t₁ t₂ t₃)
  (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega)
  (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
  {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)

include hω he ht hT hSpec hV

theorem reads_l {c N : type_l hℳ B}
    (h : derivation_l (𝒩 := structure_l hℳ B hBase) ω e T t₁ t₂ t₃ c N) :
    ∀ n l, c.val = (numberCode_l K n).val → N.val = (numberCode_l K l).val → SecondOrderPairing.relation_l V n l := by
  obtain ⟨ht₁, ht₂, ht₃⟩ := PowerlessRelativeClassSyntaxReading.tags_l K he ht
  refine derivation_l.rec (motive := fun (c N : type_l hℳ B) _ =>
    ∀ n l, c.val = (numberCode_l K n).val → N.val = (numberCode_l K l).val →
      SecondOrderPairing.relation_l V n l) ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro N n l hn _
    have hZero : n = SecondOrderModel.zero_l ℳ := numberCode_injective_l K (Subtype.ext (hn.symm.trans he))
    subst n
    exact SecondOrderTriangularFormulaBranches.zero_l hV l
  · intro a b c N hCode ha hb n l hn hl
    obtain ⟨i, hi⟩ := number_l K hω hCode.1
    obtain ⟨j, hj⟩ := number_l K hω hCode.2.1
    have hNative := PowerlessRelativeClassSyntaxReading.constructor_l K hω he hT hSpec he hi hj hn hCode
    exact (SecondOrderTriangularFormulaBranches.membership_l hℳ hV hNative l).mpr
      ⟨index_lt_l K hi hl ha, index_lt_l K hj hl hb⟩
  · intro a b c N hCode ha hb n l hn hl
    obtain ⟨i, hi⟩ := number_l K hω hCode.1
    obtain ⟨j, hj⟩ := number_l K hω hCode.2.1
    have hNative := PowerlessRelativeClassSyntaxReading.constructor_l K hω he hT hSpec ht₁ hi hj hn hCode
    exact (SecondOrderTriangularFormulaBranches.equality_l hℳ hV hNative l).mpr
      ⟨index_lt_l K hi hl ha, index_lt_l K hj hl hb⟩
  · intro a b c N hCode _ _ ih₁ ih₂ n l hn hl
    obtain ⟨i, hi⟩ := number_l K hω hCode.1
    obtain ⟨j, hj⟩ := number_l K hω hCode.2.1
    have hNative := PowerlessRelativeClassSyntaxReading.constructor_l K hω he hT hSpec ht₂ hi hj hn hCode
    exact (SecondOrderTriangularFormulaBranches.nand_l hℳ hV hNative l).mpr ⟨ih₁ i l hi hl, ih₂ j l hj hl⟩
  · intro i b c N hCode hi _ ih n l hn hl
    obtain ⟨i, hiEq⟩ := number_l K hω hCode.1
    obtain ⟨j, hjEq⟩ := number_l K hω hCode.2.1
    have hNative := PowerlessRelativeClassSyntaxReading.constructor_l K hω he hT hSpec ht₃ hiEq hjEq hn hCode
    exact (SecondOrderTriangularFormulaBranches.existential_l hℳ hV hNative l).mpr
      ⟨index_lt_l K hiEq hl hi, ih j l hjEq hl⟩
  · intro c N M _ hN _ hNM ih n m hn hm
    obtain ⟨l, hl⟩ := number_l K hω hN
    exact SecondOrderTriangularFormulaLength.monotone_l hℳ hV n l m
      (index_le_l K hl hm hNM) (ih n l hn hl)

theorem of_derivation_l {c N : type_l hℳ B}
    (h : derivation_l (𝒩 := structure_l hℳ B hBase) ω e T t₁ t₂ t₃ c N)
    (hc : mem_l hℳ c.val ω.val) (hN : mem_l hℳ N.val ω.val) : valid_l K V c.val N.val := by
  obtain ⟨n, hn⟩ := number_l K hω hc
  obtain ⟨l, hl⟩ := number_l K hω hN
  exact ⟨n, l, hn, hl, reads_l K hω he ht hT hSpec hV h n l hn hl⟩

theorem formula_l (hωClass : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hConstruct : PowerlessRelativeClassConstructorTotal.functional_l (𝒩 := structure_l hℳ B hBase) ω e T)
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (ξ : Env (structure_l hℳ B hBase) Γ Δ)
    {k : type_l hℳ B} (hk : mem_l hℳ k.val ω.val) (hξ : PowerlessSourceEnvironment.bounded_l ξ k) :
    ∃ c N : type_l hℳ B, mem_l hℳ c.val ω.val ∧ mem_l hℳ N.val ω.val ∧
      subset_l (ℳ := structure_l hℳ B hBase) k N ∧ valid_l K V c.val N.val ∧
      PowerlessRelationalSourceSpecification.spec_l ω e T t₁ t₂ t₃ c N ξ φ := by
  obtain ⟨c, N, hc, hN, hkN, hD, h⟩ :=
    PowerlessRelationalSourceCompilation.formula_certified_l hωClass ht hConstruct φ ξ hk hξ
  exact ⟨c, N, hc, hN, hkN, of_derivation_l K hω he ht hT hSpec hV hD hc hN, h⟩

#print axioms of_derivation_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCodeValidity
