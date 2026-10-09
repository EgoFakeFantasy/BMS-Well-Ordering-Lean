import BMSConstructibleBridge.SecondOrderPredecessorUnion
import BMSConstructibleBridge.SecondOrderPairSet

/-! # 内部前驱并集的根域与精确成员

所有行都由同一个模型实数编码。成员规格遍历模型自身的前驱索引，不将
模型内序数变成宿主序数，也不为各行抽取 Type 层选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorUnionSemantics

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def rows_wf_l (R H : set_l ℳ) (n : num_l ℳ) : Prop :=
  ∀ i, relation_l R i n → ∀ Y, SecondOrderSections.spec_l H i Y →
    SecondOrderDomain.wf_l Y (zero_l ℳ)

theorem selected_domain_l (hℳ : Theory.Models ℳ theory_m) {R H G P W : set_l ℳ}
    {n : num_l ℳ} (h : SecondOrderPredecessorUnion.spec_l R H n G P W)
    (hRows : rows_wf_l R H n) : ∀ c, mem_l c P → SecondOrderDomain.wf_l G c := by
  intro c hc
  obtain ⟨i, a, hi, rfl, ha⟩ := (h.selection c).mp hc
  obtain ⟨Y, hY⟩ := SecondOrderSections.exists_l hℳ H i
  have hEdge : relation_l Y a (zero_l ℳ) := (hY _).mpr ha
  exact SecondOrderPredecessorTaggedGraph.wf_l hℳ h.graph hi hY
    (SecondOrderDomain.child_l hℳ Y (zero_l ℳ) a (hRows i hi Y hY) hEdge)

theorem root_l (hℳ : Theory.Models ℳ theory_m) {R H G P W : set_l ℳ} {n : num_l ℳ}
    (h : SecondOrderPredecessorUnion.spec_l R H n G P W) (hRows : rows_wf_l R H n) :
    SecondOrderDomain.wf_l W (zero_l ℳ) :=
  SecondOrderGraftDomain.root_l hℳ G P W h.graft (selected_domain_l hℳ h hRows)

def code_l (hℳ : Theory.Models ℳ theory_m) {R H G P W : set_l ℳ} {n : num_l ℳ}
    (h : SecondOrderPredecessorUnion.spec_l R H n G P W) (hRows : rows_wf_l R H n) :
    SecondOrderGraph.code_l ℳ := ⟨W, zero_l ℳ, root_l hℳ h hRows⟩

theorem mem_l (hℳ : Theory.Models ℳ theory_m) {R H G P W : set_l ℳ} {n : num_l ℳ}
    (h : SecondOrderPredecessorUnion.spec_l R H n G P W) (hRows : rows_wf_l R H n)
    (B : SecondOrderGraph.code_l ℳ) : SecondOrderGraph.mem_l B (code_l hℳ h hRows) ↔
      ∃ i, ∃ Y : SecondOrderGraph.code_l ℳ, relation_l R i n ∧
        SecondOrderSections.spec_l H i Y.real ∧ Y.root = zero_l ℳ ∧ SecondOrderGraph.mem_l B Y := by
  have hRead := SecondOrderGraftSemantics.mem_l hℳ G P W h.graft (selected_domain_l hℳ h hRows) B
  change SecondOrderGraph.mem_l B
    (SecondOrderGraftSemantics.code_l hℳ G P W h.graft (selected_domain_l hℳ h hRows)) ↔ _
  rw [hRead]
  constructor
  · rintro ⟨c, hc, hB⟩
    obtain ⟨i, a, hi, rfl, ha⟩ := (h.selection c).mp hc
    obtain ⟨Y, hY⟩ := SecondOrderSections.exists_l hℳ H i
    have hTag := SecondOrderPairSet.tag_eq_l hℳ i Y G
      (SecondOrderPredecessorTaggedGraph.fiber_l hℳ h.graph hi hY) a
    refine ⟨i, ⟨Y, zero_l ℳ, hRows i hi Y hY⟩, hi, hY, rfl, a, (hY _).mpr ha, ?_⟩
    exact SecondOrderBisimulation.trans_l hℳ B.real G Y B.root (value_l i a) a hB
      (SecondOrderBisimulation.symm_l hℳ Y G a (value_l i a) hTag)
  · rintro ⟨i, Y, hi, hY, hRoot, a, ha, hB⟩
    have hEdge : relation_l Y.real a (zero_l ℳ) := hRoot ▸ ha
    have hTag := SecondOrderPairSet.tag_eq_l hℳ i Y.real G
      (SecondOrderPredecessorTaggedGraph.fiber_l hℳ h.graph hi hY) a
    refine ⟨value_l i a, (h.selection _).mpr ⟨i, a, hi, rfl, (hY _).mp hEdge⟩, ?_⟩
    exact SecondOrderBisimulation.trans_l hℳ B.real Y.real G B.root a (value_l i a) hB hTag

#print axioms root_l
#print axioms mem_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPredecessorUnionSemantics
