import BMSConstructibleBridge.SecondOrderProgramUniformParentSpecification
import BMSConstructibleBridge.SecondOrderProgramUniformParentOrder
import BMSConstructibleBridge.SecondOrderProgramAncestorPrefixCongruence

/-!
# 前缀内统一父查询对应的零行与后继行

前缀的全部实际entry一致时，第零行候选比较一致；上一行父查询在前缀内一致，
则真实祖先成员也一致，故后继行最大候选选择一致。宽度检查两侧分别核验，
不假定整个数组等宽或前缀外坐标相同。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentPrefixStep

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramAncestorMembership (member_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 零行只比较前缀内有效候选与目标的原entry，返回同一个some/none码。 -/
theorem zero_congr_l (hℳ : Theory.Models ℳ theory_m) {P L J : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x z n m b : num_l ℳ}
    (hx : relation_l L x n) (hz : relation_l L z m)
    (hbx : b = n ∨ SecondOrderOrder.lt_l b n) (hbz : b = m ∨ SecondOrderOrder.lt_l b m)
    (hentry : ∀ j, SecondOrderOrder.lt_l j b → ∀ v,
      relation_l J (value_l x (value_l j (zero_l ℳ))) v ↔
        relation_l J (value_l z (value_l j (zero_l ℳ))) v)
    {t : num_l ℳ} (ht : SecondOrderOrder.lt_l t b) (q : num_l ℳ) :
    relation_l P (value_l (value_l x (zero_l ℳ)) t) q ↔
      relation_l P (value_l (value_l z (zero_l ℳ)) t) q := by
  letI := order_l hℳ
  have htx : t < n := lt_of_lt_of_le ht hbx
  have htz : t < m := lt_of_lt_of_le ht hbz
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ SecondOrderProgramParentZero.parent_zero_m
  rw [SecondOrderProgramUniformParentLookup.parent_zero_l hℳ hP hQ hL x n t q hx htx,
    SecondOrderProgramUniformParentLookup.parent_zero_l hℳ hP hQ hL z m t q hz htz]
  have he (i : num_l ℳ) (hi : i < t) :
      SecondOrderProgramParentZero.eligible_l J x t i ↔ SecondOrderProgramParentZero.eligible_l J z t i := by
    simp only [SecondOrderProgramParentZero.eligible_l, hentry i (lt_trans hi ht), hentry t ht]
  rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
  · rw [SecondOrderProgramParentZero.parent_zero_none_l hℳ hQ hL hJ hx,
      SecondOrderProgramParentZero.parent_zero_none_l hℳ hQ hL hJ hz]
    simp only [not_le_of_gt htx, not_le_of_gt htz, false_or]
    exact forall_congr' fun i => imp_congr_right fun hi => not_congr (he i hi)
  · rw [SecondOrderProgramParentZero.parent_zero_some_l hℳ hQ hL hJ hx,
      SecondOrderProgramParentZero.parent_zero_some_l hℳ hQ hL hJ hz]
    simp only [htx, htz, true_and]
    apply and_congr_right
    intro hp
    exact and_congr (he p hp)
      (forall_congr' fun i => imp_congr_right fun _ => imp_congr_right fun hi => not_congr (he i hi))

/-- 前一内部行的界内父对应经原祖先程序传到本行候选，最大性保留同一输出。 -/
theorem succ_congr_l (hℳ : Theory.Models ℳ theory_m) {P L J : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x z n m b : num_l ℳ}
    (hx : relation_l L x n) (hz : relation_l L z m)
    (hbx : b = n ∨ SecondOrderOrder.lt_l b n) (hbz : b = m ∨ SecondOrderOrder.lt_l b m)
    (r : num_l ℳ)
    (hentry : ∀ j, SecondOrderOrder.lt_l j b → ∀ v,
      relation_l J (value_l x (value_l j (succ_l r))) v ↔
        relation_l J (value_l z (value_l j (succ_l r))) v)
    (hprev : ∀ j, SecondOrderOrder.lt_l j b → ∀ q,
      relation_l P (value_l (value_l x r) j) q ↔ relation_l P (value_l (value_l z r) j) q)
    {t : num_l ℳ} (ht : SecondOrderOrder.lt_l t b) (q : num_l ℳ) :
    relation_l P (value_l (value_l x (succ_l r)) t) q ↔
      relation_l P (value_l (value_l z (succ_l r)) t) q := by
  letI := order_l hℳ
  have htx : t < n := lt_of_lt_of_le ht hbx
  have htz : t < m := lt_of_lt_of_le ht hbz
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (member_m parent_m)
  have hm (i v : num_l ℳ) :
      relation_l M (value_l (value_l (value_l x r) t) i) v ↔
        relation_l M (value_l (value_l (value_l z r) t) i) v :=
    SecondOrderProgramAncestorPrefixCongruence.member_congr_l hℳ parent_m parent_m hP hP hM hM
      (value_l x r) (value_l z r) b
      (fun _ _ hp => SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hp) hprev ht i v
  have he (i : num_l ℳ) (hi : i < t) :
      SecondOrderProgramUniformParentSpecification.eligible_l M J x r t i ↔
        SecondOrderProgramUniformParentSpecification.eligible_l M J z r t i := by
    simp only [SecondOrderProgramUniformParentSpecification.eligible_l, hm i,
      hentry i (lt_trans hi ht), hentry t ht]
  rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
  · rw [SecondOrderProgramUniformParentSpecification.parent_succ_none_l hℳ hP hL hM hJ hx,
      SecondOrderProgramUniformParentSpecification.parent_succ_none_l hℳ hP hL hM hJ hz]
    simp only [not_le_of_gt htx, not_le_of_gt htz, false_or]
    exact forall_congr' fun i => imp_congr_right fun hi => not_congr (he i hi)
  · rw [SecondOrderProgramUniformParentSpecification.parent_succ_some_l hℳ hP hL hM hJ hx,
      SecondOrderProgramUniformParentSpecification.parent_succ_some_l hℳ hP hL hM hJ hz]
    simp only [htx, htz, true_and]
    apply and_congr_right
    intro hp
    exact and_congr (he p hp)
      (forall_congr' fun i => imp_congr_right fun _ => imp_congr_right fun hi => not_congr (he i hi))

#print axioms zero_congr_l
#print axioms succ_congr_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentPrefixStep
