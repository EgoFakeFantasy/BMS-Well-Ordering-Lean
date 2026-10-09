import BMSConstructibleBridge.PowerlessLegacyEvaluationRawInduction
import BMSConstructibleBridge.PowerlessLegacyEvaluationRawBranches
import BMSConstructibleBridge.PowerlessLegacyEvaluationRawExistential
import BMSConstructibleBridge.SecondOrderEvaluationLogic

/-! # 全内部原码、全原商赋值的 Sat 求值保持

实际纯公式归纳行覆盖所有内部码及任意原商有限图，不含 Class 守卫。
存在分支由原 Z₂ 的关系像构造更新图；其余分支消费同一完整 raw Sat。
不预供完整源理论，不假定内部自然数外部标准。本模块完成原求值
保持这一中间环节；原 Def 的精确认同与最终无条件 Derives 仍须接续。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationRawPreservation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)
open SecondOrderLegacyFormulaTranslation (query_l)
open SecondOrderLegacyFormulaTranslationLength (bound_l)
open SecondOrderModel
open SecondOrderAlgebra

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem preservation_l (K : source_coding_l hℳ) {ω A e t₁ t₂ t₃ P F S : type_l hℳ}
    {W E D Q R T C : SecondOrderModel.set_l ℳ}
    (hω : ω = K.omega)
    (he : e = (numberCode_l K (zero_l ℳ)).val)
    (hP : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) P K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K P)
    (hF : ∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F c l ↔
      PowerlessRelationalCodeValidity.valid_l K W c l)
    (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      ω A e t₁ t₂ t₃ P F S)
    (ht₁ : t₁ = (numberCode_l K (SecondOrderEvaluationRule.numeral_l ℳ 1)).val)
    (ht₂ : t₂ = (numberCode_l K (SecondOrderEvaluationRule.numeral_l ℳ 2)).val)
    (ht₃ : t₃ = (numberCode_l K (SecondOrderEvaluationRule.numeral_l ℳ 3)).val)
    (hW : SecondOrderTriangularFormulaSyntax.spec_l W)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C)
    (hE : SecondOrderBinaryPowers.spec_l E) (hD : ∀ v, mem_l v D)
    (hT : SecondOrderEvaluationEquations.spec_l E D Q R T)
    {U : SecondOrderQuotient.type_l hℳ}
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A)
    (hOnto : ∀ y, member_l (SecondOrderQuotient.structure_l hℳ) y A →
      ∃ v, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K v).val y)
    (hQ : ∀ a b x y,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K a).val x →
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K b).val y →
      (SecondOrderPairing.relation_l Q a b ↔ x = y))
    (hR : ∀ a b x y,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K a).val x →
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K b).val y →
      (SecondOrderPairing.relation_l R a b ↔ member_l (SecondOrderQuotient.structure_l hℳ) x y)) :
    ∀ n, PowerlessLegacyEvaluationRawRow.row_l K A U S E C T n := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  apply PowerlessLegacyEvaluationRawInduction.induct_l K A U S E C T
  intro n ih l c q L z f hGuard hfRaw hLink
  obtain ⟨hc, hQuery, hBound⟩ := hGuard
  have hBoundLe : l + n ≤ L := hBound
  have hPrefixLe : l ≤ L := (le_add_of_nonneg_right (zero_le_l hℳ n)).trans hBoundLe
  have hPrefix : l = L ∨ SecondOrderOrder.lt_l l L := hPrefixLe
  have hChildBound {k : num_l ℳ} (hk : SecondOrderOrder.lt_l k n) : bound_l l k L := by
    change l + k ≤ L
    exact (add_le_add le_rfl (le_of_lt hk)).trans hBoundLe
  have hChildValue {k a : num_l ℳ} (hk : SecondOrderOrder.lt_l k n) (ha : query_l C k l a) :
      SecondOrderPairing.relation_l T k (SecondOrderPairing.value_l l c) ↔
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) S (numberCode_l K a).val f :=
    ih k hk l c a L z f ⟨hc, ha, hChildBound hk⟩ hfRaw hLink
  have hChildValid {k a : num_l ℳ} (hk : SecondOrderOrder.lt_l k n) (ha : query_l C k l a) :
      SecondOrderPairing.relation_l W a L :=
    SecondOrderLegacyFormulaTranslationLength.length_l hℳ hC hW k l a L ha (hChildBound hk)
  rcases (SecondOrderLegacyFormulaTranslation.equation_l hℳ hC n l q).mp hQuery with
    ⟨rfl, rfl⟩ | ⟨t, p, hNode, hCases⟩
  · exact ⟨fun h => (SecondOrderEvaluationLogic.falsum_l hℳ E D Q R T hT _ h).elim,
      fun h => (PowerlessLegacyEvaluationRawTarget.zero_l K he hSat f h).elim⟩
  · have hpLt := (SecondOrderFormulaCode.bounds_l hℳ t p).2
    rw [hNode] at hpLt
    rcases hCases with hAtom | ⟨hTag, hNeg⟩ | ⟨hTag, hConj⟩ | ⟨hTag, hExists⟩
    · obtain ⟨i, j, r, s, hPairCode, hr, hs, hTags⟩ := hAtom
      rcases hTags with ⟨hTag, hCode⟩ | ⟨hTag, hCode⟩
      · rw [← hNode, ← hPairCode, hTag]
        exact PowerlessLegacyEvaluationRawBranches.equality_l
          K hω he hP hPair hSat hT ht₁ hc hPrefix hr hs hLink hU hQ hCode hfRaw
      · rw [← hNode, ← hPairCode, hTag]
        exact PowerlessLegacyEvaluationRawBranches.membership_l
          K hω he hP hPair hSat hT hc hPrefix hr hs hLink hU hR hCode hfRaw
    · obtain ⟨a, ha, hCode⟩ := hNeg
      have hValue := hChildValue hpLt ha
      have hValid := hChildValid hpLt ha
      rw [← hNode, hTag]
      exact PowerlessLegacyEvaluationRawBranches.negation_l
        K hω he hP hPair hSat hT hF ht₂ hc hCode hValid hfRaw hValue
    · obtain ⟨i, j, a, b, d, hPairCode, ha, hb, hd, hCode⟩ := hConj
      have hChildren := SecondOrderFormulaCode.children_l hℳ t i j
      rw [hPairCode, hNode] at hChildren
      have hValueA := hChildValue hChildren.1 ha
      have hValueB := hChildValue hChildren.2 hb
      have hValidA := hChildValid hChildren.1 ha
      have hValidB := hChildValid hChildren.2 hb
      rw [← hNode, ← hPairCode, hTag]
      exact PowerlessLegacyEvaluationRawBranches.conjunction_l
        K hω he hP hPair hSat hT hF ht₂ hW hc hd hCode hValidA hValidB hfRaw hValueA hValueB
    · obtain ⟨a, ha, hCode⟩ := hExists
      have hSuccP : succ_l p ≤ n := by
        rw [succ_eq_l hℳ]
        exact (lt_iff_add_one_le_l hℳ p n).mp hpLt
      have hNextBound : bound_l (succ_l l) p L := by
        change add_l (succ_l l) p ≤ L
        calc
          add_l (succ_l l) p = add_l l (succ_l p) := by
            rw [SecondOrderNumbers.succ_add_l hℳ, SecondOrderModel.add_succ_l hℳ]
          _ ≤ add_l l n := add_le_add le_rfl hSuccP
          _ ≤ L := hBoundLe
      have hPositive : SecondOrderOrder.lt_l (zero_l ℳ) n := by
        rw [← hNode]
        exact SecondOrderOrder.zero_succ_l hℳ _
      have hSlot : SecondOrderOrder.lt_l l L :=
        lt_of_lt_of_le (lt_add_of_pos_right l hPositive) hBoundLe
      have hValid := SecondOrderLegacyFormulaTranslationLength.length_l hℳ hC hW
        p (succ_l l) a L ha hNextBound
      have hNext (d : num_l ℳ) (g : type_l hℳ)
          (hd : SecondOrderAssignmentSyntax.valid_l E d (succ_l l))
          (hg : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) g (numberCode_l K L).val A)
          (hNewLink : PowerlessLegacyAssignmentSyntax.link_l K E d (succ_l l) L z U g) :
          SecondOrderPairing.relation_l T p (SecondOrderPairing.value_l (succ_l l) d) ↔
            value_l (ℳ := SecondOrderQuotient.structure_l hℳ) S (numberCode_l K a).val g :=
        ih p hpLt (succ_l l) d a L z g ⟨hd, ha, hNextBound⟩ hg hNewLink
      rw [← hNode, hTag]
      exact PowerlessLegacyEvaluationRawExistential.equation_l K hω he hP hPair
        hF hSat ht₃ hE hD hT hc hSlot hLink hU hOnto hCode hValid hfRaw hNext

#print axioms preservation_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationRawPreservation
