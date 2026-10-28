import BMSConstructibleBridge.SecondOrderProgramUniformParentPrefix
import BMSConstructibleBridge.SecondOrderProgramParentPrefixStep

/-!
# 逐行严格比较保持统一父与祖先关系

统一父程序只读取同一行条目的有定义性及严格序，而不依赖坐标的绝对值。本模块把
前缀一致性从“条目逐值相同”弱化为“全部界内列对的严格比较模式相同”，再用原公式
归纳同时覆盖模型中的非标准行号。这个接口供各副本按同一常数平移坐标时使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentComparison

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramAncestorMembership (member_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 同一数组、同一行上两列的真实 some 坐标严格比较。 -/
def entry_order_l (J : set_l ℳ) (x r i j : num_l ℳ) : Prop :=
  ∃ a b, relation_l J (value_l x (value_l i r)) (succ_l a) ∧
    relation_l J (value_l x (value_l j r)) (succ_l b) ∧ SecondOrderOrder.lt_l a b

/-- 第零行的全部候选只由界内条目严格比较模式决定。 -/
theorem zero_congr_l (hℳ : Theory.Models ℳ theory_m) {P L J : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x z n m b : num_l ℳ}
    (hx : relation_l L x n) (hz : relation_l L z m)
    (hbx : b = n ∨ SecondOrderOrder.lt_l b n) (hbz : b = m ∨ SecondOrderOrder.lt_l b m)
    (horder : ∀ i j, SecondOrderOrder.lt_l i b → SecondOrderOrder.lt_l j b →
      (entry_order_l J x (zero_l ℳ) i j ↔ entry_order_l J z (zero_l ℳ) i j))
    {t : num_l ℳ} (ht : SecondOrderOrder.lt_l t b) (q : num_l ℳ) :
    relation_l P (value_l (value_l x (zero_l ℳ)) t) q ↔
      relation_l P (value_l (value_l z (zero_l ℳ)) t) q := by
  letI := SecondOrderAlgebra.order_l hℳ
  have htx : t < n := lt_of_lt_of_le ht hbx
  have htz : t < m := lt_of_lt_of_le ht hbz
  obtain ⟨P0, _, hP0⟩ := graph_total_l hℳ SecondOrderProgramParentZero.parent_zero_m
  rw [SecondOrderProgramUniformParentLookup.parent_zero_l hℳ hP hP0 hL x n t q hx htx,
    SecondOrderProgramUniformParentLookup.parent_zero_l hℳ hP hP0 hL z m t q hz htz]
  have he (i : num_l ℳ) (hi : i < t) :
      SecondOrderProgramParentZero.eligible_l J x t i ↔
        SecondOrderProgramParentZero.eligible_l J z t i := by
    exact horder i t (lt_trans hi ht) ht
  rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
  · rw [SecondOrderProgramParentZero.parent_zero_none_l hℳ hP0 hL hJ hx,
      SecondOrderProgramParentZero.parent_zero_none_l hℳ hP0 hL hJ hz]
    simp only [not_le_of_gt htx, not_le_of_gt htz, false_or]
    exact forall_congr' fun i => imp_congr_right fun hi => not_congr (he i hi)
  · rw [SecondOrderProgramParentZero.parent_zero_some_l hℳ hP0 hL hJ hx,
      SecondOrderProgramParentZero.parent_zero_some_l hℳ hP0 hL hJ hz]
    simp only [htx, htz, true_and]
    apply and_congr_right
    intro hp
    exact and_congr (he p hp)
      (forall_congr' fun i => imp_congr_right fun _ => imp_congr_right fun hi => not_congr (he i hi))

/-- 前一行的父查询一致且本行严格比较模式一致时，后继行父查询一致。 -/
theorem succ_congr_l (hℳ : Theory.Models ℳ theory_m) {P L J : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x z n m b r : num_l ℳ}
    (hx : relation_l L x n) (hz : relation_l L z m)
    (hbx : b = n ∨ SecondOrderOrder.lt_l b n) (hbz : b = m ∨ SecondOrderOrder.lt_l b m)
    (horder : ∀ i j, SecondOrderOrder.lt_l i b → SecondOrderOrder.lt_l j b →
      (entry_order_l J x (succ_l r) i j ↔ entry_order_l J z (succ_l r) i j))
    (hprev : ∀ j, SecondOrderOrder.lt_l j b → ∀ q,
      relation_l P (value_l (value_l x r) j) q ↔ relation_l P (value_l (value_l z r) j) q)
    {t : num_l ℳ} (ht : SecondOrderOrder.lt_l t b) (q : num_l ℳ) :
    relation_l P (value_l (value_l x (succ_l r)) t) q ↔
      relation_l P (value_l (value_l z (succ_l r)) t) q := by
  letI := SecondOrderAlgebra.order_l hℳ
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
    exact and_congr (not_congr (hm i (zero_l ℳ))) (horder i t (lt_trans hi ht) ht)
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

/-- 全部内部行上的界内严格比较模式决定全部父查询。 -/
theorem parent_congr_l (hℳ : Theory.Models ℳ theory_m) {P L J : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x z n m b : num_l ℳ}
    (hx : relation_l L x n) (hz : relation_l L z m)
    (hbx : b = n ∨ SecondOrderOrder.lt_l b n) (hbz : b = m ∨ SecondOrderOrder.lt_l b m)
    (horder : ∀ r i j, SecondOrderOrder.lt_l i b → SecondOrderOrder.lt_l j b →
      (entry_order_l J x r i j ↔ entry_order_l J z r i j))
    (r : num_l ℳ) : ∀ t, SecondOrderOrder.lt_l t b → ∀ q,
    relation_l P (value_l (value_l x r) t) q ↔
      relation_l P (value_l (value_l z r) t) q := by
  apply SecondOrderModel.induct_l hℳ SecondOrderProgramUniformParentPrefix.prefix_m
    SecondOrderProgramUniformParentPrefix.prefix_language_m
    (((((Env.empty (M := ℳ)).pushFree P).pushFree b).pushFree z).pushFree x)
    (fun r => ∀ t, SecondOrderOrder.lt_l t b → ∀ q,
      relation_l P (value_l (value_l x r) t) q ↔ relation_l P (value_l (value_l z r) t) q)
    (SecondOrderProgramUniformParentPrefix.prefix_syntax_l P x z b) ?_ ?_ r
  · intro t ht q
    exact zero_congr_l hℳ hP hL hJ hx hz hbx hbz (horder (zero_l ℳ)) ht q
  · intro s hs t ht q
    exact succ_congr_l hℳ hP hL hJ hx hz hbx hbz (horder (succ_l s)) hs ht q

/-- 全部内部行上的界内严格比较模式决定实际祖先成员关系。 -/
theorem member_congr_l (hℳ : Theory.Models ℳ theory_m) {M L J : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x z n m b : num_l ℳ}
    (hx : relation_l L x n) (hz : relation_l L z m)
    (hbx : b = n ∨ SecondOrderOrder.lt_l b n) (hbz : b = m ∨ SecondOrderOrder.lt_l b m)
    (horder : ∀ r i j, SecondOrderOrder.lt_l i b → SecondOrderOrder.lt_l j b →
      (entry_order_l J x r i j ↔ entry_order_l J z r i j))
    (r : num_l ℳ) {t : num_l ℳ} (ht : SecondOrderOrder.lt_l t b) (i q : num_l ℳ) :
    relation_l M (value_l (value_l (value_l x r) t) i) q ↔
      relation_l M (value_l (value_l (value_l z r) t) i) q := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  exact SecondOrderProgramAncestorPrefixCongruence.member_congr_l hℳ parent_m parent_m hP hP hM hM
    (value_l x r) (value_l z r) b
    (fun _ _ hp => SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hp)
    (parent_congr_l hℳ hP hL hJ hx hz hbx hbz horder r) ht i q

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentComparison
