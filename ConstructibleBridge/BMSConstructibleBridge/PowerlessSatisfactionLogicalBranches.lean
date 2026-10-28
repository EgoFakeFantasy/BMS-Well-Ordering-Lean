import BMSConstructibleBridge.PowerlessRelativeClassSatisfaction

/-! # 合法性守卫求值图的零码与命题分支

在同一个内部赋值长度上，将原商合法性图的读数搬回实际类内求值系统。
原子分支保留两个槽界，NAND 保留两个子码的合法性；全部数码属于原模型
的内部自然数，不使用外部语法归纳。此处尚未给出存在量词分支或最终目标。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionLogicalBranches

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
  (K : source_coding_l hℳ) {V : SecondOrderModel.set_l ℳ}
  {ω A S F G R : type_l hℳ B} (hωEq : ω.val = K.omega)
  (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val A.val S.val)
  (hF : ∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
    PowerlessRelationalCodeValidity.valid_l K V c l)
  (hR : ∀ c f, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val c f ↔
    PowerlessSatisfactionBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      ω.val A.val S.val F.val G.val c f)

include hωEq hS hF hR

/-- 同一内部长度与合法码上的类内读数，直接复用全原商规格。 -/
theorem read_class_l {c L f : type_l hℳ B} {n l : SecondOrderModel.num_l ℳ}
    (hc : c.val = code_l K n) (hL : L.val = code_l K l)
    (hValid : SecondOrderPairing.relation_l V n l)
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f L A) :
    value_l (ℳ := structure_l hℳ B hBase) R c f ↔
      value_l (ℳ := structure_l hℳ B hBase) G c f := by
  have hMapRaw := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f L A).mp hMap
  rw [hL] at hMapRaw
  have hRead := PowerlessRelativeClassSatisfaction.read_l K hωEq hS hF hR (f := f.val) hValid hMapRaw
  rw [← hc] at hRead
  exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R c f).trans
    (hRead.trans (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G c f).symm)

variable {e T t₁ t₂ t₃ : type_l hℳ B}
  (hSystem : PowerlessRelativeClassEvaluationSystem.spec_l
    (𝒩 := structure_l hℳ B hBase) ω A e t₁ t₂ t₃ T S G)

include hSystem

theorem zero_l (he : e.val = code_l K (SecondOrderModel.zero_l ℳ))
    (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    {L f : type_l hℳ B} {l : SecondOrderModel.num_l ℳ}
    (hL : L.val = code_l K l) (hMap : map_l (ℳ := structure_l hℳ B hBase) f L A) :
    ¬value_l (ℳ := structure_l hℳ B hBase) R e f := by
  intro h
  exact hSystem.2.2.2.2.1 f ((read_class_l K hωEq hS hF hR he hL
    (SecondOrderTriangularFormulaBranches.zero_l hV l) hMap).mp h)

variable (he : e.val = code_l K (SecondOrderModel.zero_l ℳ))
  (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega)
  (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
  (hV : SecondOrderTriangularFormulaSyntax.spec_l V)

include he hT hSpec hV

theorem membership_l {c a b L f : type_l hℳ B} {n i j l : SecondOrderModel.num_l ℳ}
    (hc : c.val = code_l K n) (ha : a.val = code_l K i) (hb : b.val = code_l K j)
    (hL : L.val = code_l K l)
    (hCode : PowerlessFormulaConstructor.constructor_l (ℳ := structure_l hℳ B hBase) ω e T e a b c)
    (hi : mem_l hℳ a.val L.val) (hj : mem_l hℳ b.val L.val)
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f L A) :
    value_l (ℳ := structure_l hℳ B hBase) R c f ↔
      PowerlessEvaluationClause.member_l (ℳ := structure_l hℳ B hBase) f a b := by
  have hNative := PowerlessRelativeClassSyntaxReading.constructor_l K hωEq he hT hSpec he ha hb hc hCode
  have hValid := (SecondOrderTriangularFormulaBranches.membership_l hℳ hV hNative l).mpr
    ⟨PowerlessRelativeClassSyntaxReading.index_lt_l K ha hL hi,
      PowerlessRelativeClassSyntaxReading.index_lt_l K hb hL hj⟩
  have hcω : mem_l hℳ c.val ω.val := by
    rw [hc, hωEq]
    exact (numberCode_l K n).property
  have hLω : mem_l hℳ L.val ω.val := by
    rw [hL, hωEq]
    exact (numberCode_l K l).property
  have hf : mem_l hℳ f.val S.val := (hSystem.2.2.2.1 f).mpr ⟨L, hLω, hMap⟩
  exact (read_class_l K hωEq hS hF hR hc hL hValid hMap).trans
    (((hSystem.2.2.2.2.2 c hcω f a b).1 hCode).trans (and_iff_right hf))

theorem equality_l {c a b L f : type_l hℳ B} {n i j l : SecondOrderModel.num_l ℳ}
    (hc : c.val = code_l K n) (ha : a.val = code_l K i) (hb : b.val = code_l K j)
    (hL : L.val = code_l K l)
    (hCode : PowerlessFormulaConstructor.constructor_l (ℳ := structure_l hℳ B hBase) ω e T t₁ a b c)
    (hi : mem_l hℳ a.val L.val) (hj : mem_l hℳ b.val L.val)
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f L A) :
    value_l (ℳ := structure_l hℳ B hBase) R c f ↔
      PowerlessEvaluationClause.equal_l (ℳ := structure_l hℳ B hBase) f a b := by
  obtain ⟨ht₁, _, _⟩ := PowerlessRelativeClassSyntaxReading.tags_l K he hSystem.1
  have hNative := PowerlessRelativeClassSyntaxReading.constructor_l K hωEq he hT hSpec ht₁ ha hb hc hCode
  have hValid := (SecondOrderTriangularFormulaBranches.equality_l hℳ hV hNative l).mpr
    ⟨PowerlessRelativeClassSyntaxReading.index_lt_l K ha hL hi,
      PowerlessRelativeClassSyntaxReading.index_lt_l K hb hL hj⟩
  have hcω : mem_l hℳ c.val ω.val := by
    rw [hc, hωEq]
    exact (numberCode_l K n).property
  have hLω : mem_l hℳ L.val ω.val := by
    rw [hL, hωEq]
    exact (numberCode_l K l).property
  have hf : mem_l hℳ f.val S.val := (hSystem.2.2.2.1 f).mpr ⟨L, hLω, hMap⟩
  exact (read_class_l K hωEq hS hF hR hc hL hValid hMap).trans
    (((hSystem.2.2.2.2.2 c hcω f a b).2.1 hCode).trans (and_iff_right hf))

theorem nand_l {c a b L f : type_l hℳ B} {n i j l : SecondOrderModel.num_l ℳ}
    (hc : c.val = code_l K n) (ha : a.val = code_l K i) (hb : b.val = code_l K j)
    (hL : L.val = code_l K l)
    (hCode : PowerlessFormulaConstructor.constructor_l (ℳ := structure_l hℳ B hBase) ω e T t₂ a b c)
    (hi : SecondOrderPairing.relation_l V i l) (hj : SecondOrderPairing.relation_l V j l)
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f L A) :
    value_l (ℳ := structure_l hℳ B hBase) R c f ↔
      ¬(value_l (ℳ := structure_l hℳ B hBase) R a f ∧
        value_l (ℳ := structure_l hℳ B hBase) R b f) := by
  obtain ⟨_, ht₂, _⟩ := PowerlessRelativeClassSyntaxReading.tags_l K he hSystem.1
  have hNative := PowerlessRelativeClassSyntaxReading.constructor_l K hωEq he hT hSpec ht₂ ha hb hc hCode
  have hValid := (SecondOrderTriangularFormulaBranches.nand_l hℳ hV hNative l).mpr ⟨hi, hj⟩
  have hcω : mem_l hℳ c.val ω.val := by
    rw [hc, hωEq]
    exact (numberCode_l K n).property
  have hLω : mem_l hℳ L.val ω.val := by
    rw [hL, hωEq]
    exact (numberCode_l K l).property
  have hf : mem_l hℳ f.val S.val := (hSystem.2.2.2.1 f).mpr ⟨L, hLω, hMap⟩
  have hEquation := ((hSystem.2.2.2.2.2 c hcω f a b).2.2.1 hCode).trans (and_iff_right hf)
  have hReadA := read_class_l K hωEq hS hF hR ha hL hi hMap
  have hReadB := read_class_l K hωEq hS hF hR hb hL hj hMap
  exact (read_class_l K hωEq hS hF hR hc hL hValid hMap).trans
    (hEquation.trans (not_congr (and_congr hReadA.symm hReadB.symm)))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionLogicalBranches
