import BMSConstructibleBridge.PowerlessLegacyEvaluationInduction
import BMSConstructibleBridge.PowerlessLegacyEvaluationBranches
import BMSConstructibleBridge.PowerlessLegacyEvaluationExistential
import BMSConstructibleBridge.SecondOrderEvaluationLogic

/-! # 全内部原公式码的实际 Sat 求值保持

归纳性质是已经读取的环境商纯公式，所有数码、长度和赋值均属于
原模型内部域。各构造子消费实际求值图及合法性图的证书，量词覆盖
任意正确前插表示。本文件只完成求值保持这一语义中间环节；原 Def
的类成员、良序限制及最终对象 Derives 仍须接续。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationPreservation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessLegacyEvaluationTarget (number_l)
open SecondOrderLegacyFormulaTranslation (query_l)
open SecondOrderLegacyFormulaTranslationLength (bound_l)
open SecondOrderModel
open SecondOrderAlgebra

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

theorem preservation_l (K : source_coding_l hℳ) {ω A e t₁ t₂ t₃ P F S : type_l hℳ B}
    {W E D Q R T C : SecondOrderModel.set_l ℳ}
    (hΩ : omega_l (ℳ := structure_l hℳ B hBase) ω) (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (zero_l ℳ)).val)
    (hP : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) P.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K P.val)
    (hF : ∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
      PowerlessRelationalCodeValidity.valid_l K W c l)
    (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := structure_l hℳ B hBase)
      ω A e t₁ t₂ t₃ P F S)
    (ht₁ : t₁.val = (numberCode_l K (SecondOrderEvaluationRule.numeral_l ℳ 1)).val)
    (ht₂ : t₂.val = (numberCode_l K (SecondOrderEvaluationRule.numeral_l ℳ 2)).val)
    (ht₃ : t₃.val = (numberCode_l K (SecondOrderEvaluationRule.numeral_l ℳ 3)).val)
    (hW : SecondOrderTriangularFormulaSyntax.spec_l W)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C)
    (hE : SecondOrderBinaryPowers.spec_l E) (hD : ∀ v, mem_l v D)
    (hT : SecondOrderEvaluationEquations.spec_l E D Q R T)
    {U : SecondOrderQuotient.type_l hℳ}
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A.val)
    (hOnto : ∀ y, member_l (SecondOrderQuotient.structure_l hℳ) y A.val →
      ∃ v, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K v).val y)
    (hQ : ∀ a b x y,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K a).val x →
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K b).val y →
      (SecondOrderPairing.relation_l Q a b ↔ x = y))
    (hR : ∀ a b x y,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K a).val x →
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K b).val y →
      (SecondOrderPairing.relation_l R a b ↔ member_l (SecondOrderQuotient.structure_l hℳ) x y)) :
    ∀ n, PowerlessLegacyEvaluationRow.row_l K B A.val U S.val E C T n := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  apply PowerlessLegacyEvaluationInduction.induct_l K B A.val U S.val E C T
  intro n ih l c q L z f hGuard hfClass hfRaw hLink
  obtain ⟨hc, hQuery, hBound⟩ := hGuard
  let f' : type_l hℳ B := ⟨f, hfClass⟩
  have hf : map_l (ℳ := structure_l hℳ B hBase) f' (number_l (hBase := hBase) K L) A :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f' _ A).mpr hfRaw
  have hBoundLe : l + n ≤ L := hBound
  have hPrefixLe : l ≤ L := (le_add_of_nonneg_right (zero_le_l hℳ n)).trans hBoundLe
  have hPrefix : l = L ∨ SecondOrderOrder.lt_l l L := hPrefixLe
  have hChildBound {k : num_l ℳ} (hk : SecondOrderOrder.lt_l k n) : bound_l l k L := by
    change l + k ≤ L
    exact (add_le_add le_rfl (le_of_lt hk)).trans hBoundLe
  have hChildValue {k a : num_l ℳ} (hk : SecondOrderOrder.lt_l k n) (ha : query_l C k l a) :
      SecondOrderPairing.relation_l T k (SecondOrderPairing.value_l l c) ↔
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) S.val (numberCode_l K a).val f :=
    ih k hk l c a L z f ⟨hc, ha, hChildBound hk⟩ hfClass hfRaw hLink
  have hChildValid {k a : num_l ℳ} (hk : SecondOrderOrder.lt_l k n) (ha : query_l C k l a) :
      SecondOrderPairing.relation_l W a L :=
    SecondOrderLegacyFormulaTranslationLength.length_l hℳ hC hW k l a L ha (hChildBound hk)
  rcases (SecondOrderLegacyFormulaTranslation.equation_l hℳ hC n l q).mp hQuery with
    ⟨rfl, rfl⟩ | ⟨t, p, hNode, hCases⟩
  · exact ⟨fun h => (SecondOrderEvaluationLogic.falsum_l hℳ E D Q R T hT _ h).elim,
      fun h => (PowerlessLegacyEvaluationTarget.zero_l (hBase := hBase) K he hSat f' h).elim⟩
  · have hpLt := (SecondOrderFormulaCode.bounds_l hℳ t p).2
    rw [hNode] at hpLt
    rcases hCases with hAtom | ⟨hTag, hNeg⟩ | ⟨hTag, hConj⟩ | ⟨hTag, hExists⟩
    · obtain ⟨i, j, r, s, hPairCode, hr, hs, hTags⟩ := hAtom
      rcases hTags with ⟨hTag, hCode⟩ | ⟨hTag, hCode⟩
      · rw [← hNode, ← hPairCode, hTag]
        exact PowerlessLegacyEvaluationBranches.equality_l (hBase := hBase)
          K hω he hP hPair hSat hT ht₁ hc hPrefix hr hs hLink hU hQ hCode hf
      · rw [← hNode, ← hPairCode, hTag]
        exact PowerlessLegacyEvaluationBranches.membership_l (hBase := hBase)
          K hω he hP hPair hSat hT hc hPrefix hr hs hLink hU hR hCode hf
    · obtain ⟨a, ha, hCode⟩ := hNeg
      have hValue := hChildValue hpLt ha
      have hValid := hChildValid hpLt ha
      rw [← hNode, hTag]
      exact PowerlessLegacyEvaluationBranches.negation_l (hBase := hBase)
        K hω he hP hPair hSat hT hF ht₂ hc hCode hValid hf hValue
    · obtain ⟨i, j, a, b, d, hPairCode, ha, hb, hd, hCode⟩ := hConj
      have hChildren := SecondOrderFormulaCode.children_l hℳ t i j
      rw [hPairCode, hNode] at hChildren
      have hValueA := hChildValue hChildren.1 ha
      have hValueB := hChildValue hChildren.2 hb
      have hValidA := hChildValid hChildren.1 ha
      have hValidB := hChildValid hChildren.2 hb
      rw [← hNode, ← hPairCode, hTag]
      exact PowerlessLegacyEvaluationBranches.conjunction_l (hBase := hBase)
        K hω he hP hPair hSat hT hF ht₂ hW hc hd hCode hValidA hValidB hf hValueA hValueB
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
      have hNext (d : num_l ℳ) (g : type_l hℳ B)
          (hd : SecondOrderAssignmentSyntax.valid_l E d (succ_l l))
          (hg : map_l (ℳ := structure_l hℳ B hBase) g (number_l (hBase := hBase) K L) A)
          (hNewLink : PowerlessLegacyAssignmentSyntax.link_l K E d (succ_l l) L z U g.val) :
          SecondOrderPairing.relation_l T p (SecondOrderPairing.value_l (succ_l l) d) ↔
            value_l (ℳ := SecondOrderQuotient.structure_l hℳ) S.val (numberCode_l K a).val g.val :=
        ih p hpLt (succ_l l) d a L z g.val ⟨hd, ha, hNextBound⟩ g.property
          ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) g _ A).mp hg) hNewLink
      rw [← hNode, hTag]
      exact PowerlessLegacyEvaluationExistential.equation_l (hBase := hBase) K hΩ hω he hP hPair
        hF hSat ht₃ hE hD hT hc hSlot hLink hU hOnto hCode hValid hf hNext

#print axioms preservation_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationPreservation
