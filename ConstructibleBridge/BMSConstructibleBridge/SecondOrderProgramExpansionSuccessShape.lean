import BMSConstructibleBridge.SecondOrderProgramExpansionSuccess
import BMSConstructibleBridge.SecondOrderProgramCopiesShape

/-!
# 成功展开中好块与所有副本的内部宽度

好块准确来自take父列，复制参数来自同一坏块和末列。原展开指标k给出succ k份副本，
故宽度为好块宽加坏块宽乘succ k。这里先保留真实坏块的长度证据；尚不把这个宽度
公式当作序数下降，也不擅自把最大搜索预算或坏块边界换成裁剪高度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionSuccessShape

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramExpansionSuccess
open SecondOrderProgramCopies (copies_m)
open SecondOrderProgramMaximalParentRow (last_column_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListTake (take_m take_length_min_l)
open SecondOrderProgramListAppend (append_m append_length_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 好部分的内部调用准确是原take父列，不误用最大父行作前缀长度。 -/
theorem good_rel_l (hℳ : Theory.Models ℳ theory_m) {G K : set_l ℳ}
    (hG : graph_semantics_l (graph_m good_m) G)
    (hK : graph_semantics_l (graph_m take_m) K) (x k r p y : num_l ℳ) :
    relation_l G (value_l x (value_l k (value_l r p))) y ↔ relation_l K (value_l x p) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ take_m hK
  have hp : value_spec_l parent_m _ := comp_value_l hℳ
    (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)) (right_value_l hℳ)
  have hv : value_spec_l good_m _ := comp_value_l hℳ hf (pair_value_l hℳ (left_value_l hℳ) hp)
  simp only [hv hG, hf hK, SecondOrderUnpairing.unpair_l]

/-- 复制正文使用同一实际坏块、原末列与succ k次数；保留完整内部参数顺序。 -/
theorem copied_rel_l (hℳ : Theory.Models ℳ theory_m) {C B H R : set_l ℳ}
    (hC : graph_semantics_l (graph_m copied_m) C)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hH : graph_semantics_l (graph_m last_column_m) H)
    (hR : graph_semantics_l (graph_m copies_m) R) (x k r p y : num_l ℳ) :
    relation_l C (value_l x (value_l k (value_l r p))) y ↔ ∃ b l,
      relation_l B (value_l x (value_l k (value_l r p))) b ∧ relation_l H x l ∧
        relation_l R (value_l (value_l b (value_l (value_l x (value_l r p)) l)) (succ_l k)) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ bad_m hB
  obtain ⟨g, hg, _⟩ := value_exists_l hℳ last_column_m hH
  obtain ⟨c, hc, _⟩ := value_exists_l hℳ copies_m hR
  have hr : value_spec_l row_m _ := comp_value_l hℳ
    (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ)) (right_value_l hℳ)
  have hp : value_spec_l parent_m _ := comp_value_l hℳ
    (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)) (right_value_l hℳ)
  have hk : value_spec_l index_m _ := comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ)
  have hq : value_spec_l parameter_m _ := pair_value_l hℳ hf
    (pair_value_l hℳ (pair_value_l hℳ (left_value_l hℳ) (pair_value_l hℳ hr hp))
      (comp_value_l hℳ hg (left_value_l hℳ)))
  have hv : value_spec_l copied_m _ := comp_value_l hℳ hc
    (pair_value_l hℳ hq (comp_value_l hℳ (succ_value_l hℳ) hk))
  simp only [hv hC, hf hB, hg hH, hc hR, SecondOrderUnpairing.unpair_l]
  constructor
  · intro hy
    exact ⟨_, _, rfl, rfl, hy⟩
  · rintro ⟨_, _, rfl, rfl, hy⟩
    exact hy

/-- 全部原副本的总宽度恰为同一坏块宽乘succ k，参数仍可非标准。 -/
theorem copied_width_l (hℳ : Theory.Models ℳ theory_m) {C B L : set_l ℳ}
    (hC : graph_semantics_l (graph_m copied_m) C)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L) {x k r p b w y : num_l ℳ}
    (hb : relation_l B (value_l x (value_l k (value_l r p))) b) (hw : relation_l L b w)
    (hy : relation_l C (value_l x (value_l k (value_l r p))) y) :
    relation_l L y (mul_l w (succ_l k)) := by
  obtain ⟨H, _, hH⟩ := graph_total_l hℳ last_column_m
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ copies_m
  obtain ⟨b', l, hb', _, hr⟩ := (copied_rel_l hℳ hC hB hH hR x k r p y).mp hy
  have he := function_value_unique_l (function_of_semantics_l hℳ bad_m hB) hb' hb
  subst b'
  exact SecondOrderProgramCopiesShape.copies_width_l hℳ hR hL hw hr

/-- 原成功正文的总宽度是实际好前缀宽与所有坏块副本宽之和。 -/
theorem success_width_l (hℳ : Theory.Models ℳ theory_m) {S B L : set_l ℳ}
    (hS : graph_semantics_l (graph_m success_m) S)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L) {x k r p b n w y : num_l ℳ}
    (hn : relation_l L x n)
    (hb : relation_l B (value_l x (value_l k (value_l r p))) b) (hw : relation_l L b w)
    (hy : relation_l S (value_l x (value_l k (value_l r p))) y) :
    letI := order_l hℳ
    relation_l L y (add_l (min n p) (mul_l w (succ_l k))) := by
  letI := order_l hℳ
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ good_m
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ copied_m
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ append_m
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ take_m
  obtain ⟨g, c, hg, hc, ha⟩ := (success_rel_l hℳ hS hG hC hA _ y).mp hy
  have hgl := take_length_min_l hℳ hK hL hn ((good_rel_l hℳ hG hK x k r p g).mp hg)
  have hcl := copied_width_l hℳ hC hB hL hb hw hc
  exact append_length_l hℳ hA hL hgl hcl ha

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionSuccessShape
