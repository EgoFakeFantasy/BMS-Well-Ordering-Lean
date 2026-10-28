import BMSConstructibleBridge.SecondOrderProgramExpansionFallback
import BMSConstructibleBridge.SecondOrderProgramUniformParentOrder

/-!
# 最大父行实际选中的末列父节点

最大父行返回some r时，原末列在r行的父查询必有some输出，且该父列严格小于末列。
这同时排除空输入，并给出末列下标与真实宽度的关系。结论来自内部最大搜索规格，
不从标准eval推广，也不预先删除原展开程序保留的Option失败分支。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramMaximalParentSelection

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m height_m test_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramGreatest (greatest_m)
open SecondOrderProgramListCode (pred_m pred_zero_l pred_succ_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 实际最大行some输出保证该行末列父查询非零，末列由原下标图给出。 -/
theorem parent_nonzero_l (hℳ : Theory.Models ℳ theory_m) {M P J : set_l ℳ}
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hJ : graph_semantics_l (graph_m last_index_m) J) {x r j : num_l ℳ}
    (hm : relation_l M x (succ_l r)) (hj : relation_l J x j) :
    ¬relation_l P (value_l (value_l x r) j) (zero_l ℳ) := by
  obtain ⟨H, hHf, hH⟩ := graph_total_l hℳ height_m
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ (greatest_m test_m)
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ test_m
  obtain ⟨h, hh, _⟩ := hHf x
  have ht := ((SecondOrderProgramMaximalParentRow.maximal_some_l hℳ hM hG hH hT hh r).mp hm).2.1
  intro hp
  exact ht ((SecondOrderProgramMaximalParentRow.test_rel_l hℳ hT hP hJ x r _).mpr ⟨j, hj, hp⟩)

/-- 同一原下标和父查询产生实际父列；行号、末列和父列均可非标准。 -/
theorem parent_some_l (hℳ : Theory.Models ℳ theory_m) {M P J : set_l ℳ}
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hJ : graph_semantics_l (graph_m last_index_m) J) {x r : num_l ℳ}
    (hm : relation_l M x (succ_l r)) : ∃ j p,
    relation_l J x j ∧ relation_l P (value_l (value_l x r) j) (succ_l p) ∧
      SecondOrderOrder.lt_l p j := by
  obtain ⟨j, hj, _⟩ := function_of_semantics_l hℳ last_index_m hJ x
  obtain ⟨q, hq, _⟩ := function_of_semantics_l hℳ parent_m hP (value_l (value_l x r) j)
  rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
  · exact False.elim (parent_nonzero_l hℳ hM hP hJ hm hj hq)
  · exact ⟨j, p, hj, hq, SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hq⟩

/-- 最大父行存在时输入确实非空，末列是实际宽度的前驱且所选父列严格在前。 -/
theorem width_parent_l (hℳ : Theory.Models ℳ theory_m) {M P L : set_l ℳ}
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L) {x r : num_l ℳ}
    (hm : relation_l M x (succ_l r)) : ∃ n p,
    relation_l L x (succ_l n) ∧ relation_l P (value_l (value_l x r) n) (succ_l p) ∧
      SecondOrderOrder.lt_l p n := by
  letI := order_l hℳ
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ last_index_m
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ pred_m
  obtain ⟨j, p, hj, hp, hlt⟩ := parent_some_l hℳ hM hP hJ hm
  obtain ⟨n, hn, _⟩ := function_of_semantics_l hℳ length_m hL x
  have hd := (SecondOrderProgramExpansionFallback.index_rel_l hℳ hJ hL hD hn j).mp hj
  rcases predecessor_l hℳ n with rfl | ⟨n, rfl⟩
  · have he := (pred_zero_l hℳ hD j).mp hd
    have hp0 : SecondOrderOrder.lt_l p (zero_l ℳ) := by simpa only [← he] using hlt
    exact False.elim ((not_lt_of_ge (zero_le_l hℳ p)) hp0)
  · have he := (pred_succ_l hℳ hD n j).mp hd
    exact ⟨n, p, hn, he.symm ▸ hp, he.symm ▸ hlt⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramMaximalParentSelection
