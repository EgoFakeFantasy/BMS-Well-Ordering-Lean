import BMSConstructibleBridge.PowerlessLegacyAssignmentReading
import BMSConstructibleBridge.PowerlessLegacyEvaluationTarget

/-! # 原五标签翻译的原子、否定及合取求值保持

原子分支拼接原求值方程、反转填充槽读数及实际 Sat。否定用重复
NAND，合取用两层 NAND；子码的求值保持和合法性仍明确传入，
以便由覆盖全部内部码的强归纳给出，而不是由宿主语法归纳给出。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationBranches

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessLegacyAssignmentSyntax (link_l)
open SecondOrderLegacyAssignmentReversal (index_l)
open SecondOrderEvaluationEquations (node_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

variable (K : source_coding_l hℳ) {ω A e t₁ t₂ t₃ P F S : type_l hℳ B}
  {W E D Q R T : SecondOrderModel.set_l ℳ}
  (hω : ω.val = K.omega)
  (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
  (hP : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) P.val K.omega K.omega)
  (hPair : PowerlessBMSQuotientPairingBounds.spec_l K P.val)
  (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := structure_l hℳ B hBase)
    ω A e t₁ t₂ t₃ P F S)
  (hT : SecondOrderEvaluationEquations.spec_l E D Q R T)

include hω he hP hPair hSat hT

theorem equality_l (ht₁ : t₁.val = (numberCode_l K (numeral_l ℳ 1)).val)
    {l c L z i j r s q : SecondOrderModel.num_l ℳ} {U : SecondOrderQuotient.type_l hℳ}
    {f : type_l hℳ B} (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (hLength : l = L ∨ SecondOrderOrder.lt_l l L) (hi : index_l l i r) (hj : index_l l j s)
    (hLink : link_l K E c l L z U f.val)
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A.val)
    (hQ : ∀ a b x y,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K a).val x →
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K b).val y →
      (SecondOrderPairing.relation_l Q a b ↔ x = y))
    (hCode : SecondOrderTriangularConstructor.constructor_l (numeral_l ℳ 1) r s q)
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f
      (PowerlessLegacyEvaluationTarget.number_l (hBase := hBase) K L) A) :
    SecondOrderPairing.relation_l T (node_l 0 (SecondOrderPairing.value_l i j))
      (SecondOrderPairing.value_l l c) ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) S.val (numberCode_l K q).val f.val := by
  have hr := (SecondOrderLegacyAssignmentReversal.bounds_l hℳ hi).2
  have hs := (SecondOrderLegacyAssignmentReversal.bounds_l hℳ hj).2
  have hrL := hLength.elim (fun h => h ▸ hr) (fun h => SecondOrderOrder.trans_l hℳ hr h)
  have hsL := hLength.elim (fun h => h ▸ hs) (fun h => SecondOrderOrder.trans_l hℳ hs h)
  exact (SecondOrderEvaluationEquations.equality_l hℳ E D Q R T hT l c i j hc).trans
    ((PowerlessLegacyAssignmentReading.equality_l K hLength hi hj hLink hU hQ).trans
      (PowerlessLegacyEvaluationTarget.equality_l (hBase := hBase) K hω he hP hPair hSat ht₁
        hCode hrL hsL hMap).symm)

theorem membership_l
    {l c L z i j r s q : SecondOrderModel.num_l ℳ} {U : SecondOrderQuotient.type_l hℳ}
    {f : type_l hℳ B} (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (hLength : l = L ∨ SecondOrderOrder.lt_l l L) (hi : index_l l i r) (hj : index_l l j s)
    (hLink : link_l K E c l L z U f.val)
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A.val)
    (hR : ∀ a b x y,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K a).val x →
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K b).val y →
      (SecondOrderPairing.relation_l R a b ↔ member_l (SecondOrderQuotient.structure_l hℳ) x y))
    (hCode : SecondOrderTriangularConstructor.constructor_l (numeral_l ℳ 0) r s q)
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f
      (PowerlessLegacyEvaluationTarget.number_l (hBase := hBase) K L) A) :
    SecondOrderPairing.relation_l T (node_l 1 (SecondOrderPairing.value_l i j))
      (SecondOrderPairing.value_l l c) ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) S.val (numberCode_l K q).val f.val := by
  have hr := (SecondOrderLegacyAssignmentReversal.bounds_l hℳ hi).2
  have hs := (SecondOrderLegacyAssignmentReversal.bounds_l hℳ hj).2
  have hrL := hLength.elim (fun h => h ▸ hr) (fun h => SecondOrderOrder.trans_l hℳ hr h)
  have hsL := hLength.elim (fun h => h ▸ hs) (fun h => SecondOrderOrder.trans_l hℳ hs h)
  exact (SecondOrderEvaluationEquations.membership_l hℳ E D Q R T hT l c i j hc).trans
    ((PowerlessLegacyAssignmentReading.membership_l K hLength hi hj hLink hU hR).trans
      (PowerlessLegacyEvaluationTarget.membership_l (hBase := hBase) K hω he hP hPair hSat
        hCode hrL hsL hMap).symm)

variable (hF : ∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
    PowerlessRelationalCodeValidity.valid_l K W c l)
  (ht₂ : t₂.val = (numberCode_l K (numeral_l ℳ 2)).val)

include hF ht₂

theorem negation_l {l c L p a q : SecondOrderModel.num_l ℳ} {f : type_l hℳ B}
    (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (hCode : SecondOrderTriangularConstructor.constructor_l (numeral_l ℳ 2) a a q)
    (ha : SecondOrderPairing.relation_l W a L)
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f
      (PowerlessLegacyEvaluationTarget.number_l (hBase := hBase) K L) A)
    (hChild : SecondOrderPairing.relation_l T p (SecondOrderPairing.value_l l c) ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) S.val (numberCode_l K a).val f.val) :
    SecondOrderPairing.relation_l T (node_l 2 p) (SecondOrderPairing.value_l l c) ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) S.val (numberCode_l K q).val f.val := by
  have hTarget := PowerlessLegacyEvaluationTarget.nand_l (hBase := hBase) K hω he hP hPair hF hSat
    ht₂ hCode ha ha hMap
  simp only [and_self] at hTarget
  exact (SecondOrderEvaluationEquations.negation_l hℳ E D Q R T hT l c p hc).trans
    ((not_congr hChild).trans hTarget.symm)

theorem conjunction_l (hW : SecondOrderTriangularFormulaSyntax.spec_l W)
    {l c L p q a b d n : SecondOrderModel.num_l ℳ} {f : type_l hℳ B}
    (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (hd : SecondOrderTriangularConstructor.constructor_l (numeral_l ℳ 2) a b d)
    (hn : SecondOrderTriangularConstructor.constructor_l (numeral_l ℳ 2) d d n)
    (ha : SecondOrderPairing.relation_l W a L) (hb : SecondOrderPairing.relation_l W b L)
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f
      (PowerlessLegacyEvaluationTarget.number_l (hBase := hBase) K L) A)
    (hLeft : SecondOrderPairing.relation_l T p (SecondOrderPairing.value_l l c) ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) S.val (numberCode_l K a).val f.val)
    (hRight : SecondOrderPairing.relation_l T q (SecondOrderPairing.value_l l c) ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) S.val (numberCode_l K b).val f.val) :
    SecondOrderPairing.relation_l T (node_l 3 (SecondOrderPairing.value_l p q))
      (SecondOrderPairing.value_l l c) ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) S.val (numberCode_l K n).val f.val := by
  classical
  have hValidD := (SecondOrderTriangularFormulaBranches.nand_l hℳ hW hd L).mpr ⟨ha, hb⟩
  have hD := PowerlessLegacyEvaluationTarget.nand_l (hBase := hBase) K hω he hP hPair hF hSat
    ht₂ hd ha hb hMap
  have hN := PowerlessLegacyEvaluationTarget.nand_l (hBase := hBase) K hω he hP hPair hF hSat
    ht₂ hn hValidD hValidD hMap
  simp only [and_self] at hN
  have hNN := hN.trans (not_congr hD)
  simp only [not_not] at hNN
  exact (SecondOrderEvaluationEquations.conjunction_l hℳ E D Q R T hT l c p q hc).trans
    ((and_congr hLeft hRight).trans hNN.symm)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationBranches
