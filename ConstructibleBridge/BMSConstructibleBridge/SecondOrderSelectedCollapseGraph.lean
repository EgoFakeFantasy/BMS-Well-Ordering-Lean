import BMSConstructibleBridge.SecondOrderCollapseGraph

/-! # 按实际选点集构造坍缩值域和完整图

原 Z₂ 任意模型中的辅助构造。选点集 P 包含所需的全部节点，允许孤立点；
前驱封闭保证精确值域传递。旧的关系域域构造保持不动，本模块提供泛用
选点版本。根值是原图商，所有见证由内部理解、拼接及实际混合关系像产生。
此处是接线辅助语义接口，不等于最终对象层 BMS 定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSelectedCollapseGraph

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing
open SecondOrderCollapseGraph (code_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem range_l (hℳ : Theory.Models ℳ theory_m) (S P : set_l ℳ)
    (hS : ∀ n, SecondOrderDomain.wf_l S n)
    (hClosed : ∀ a, mem_l a P → ∀ b, relation_l S b a → mem_l b P) :
    ∃ U : SecondOrderGraph.code_l ℳ,
      (∀ X, SecondOrderGraph.mem_l X U ↔ ∃ n, mem_l n P ∧ SecondOrderGraph.eq_l X (code_l S hS n)) ∧
        SecondOrderTransitiveSuperset.transitive_l U := by
  obtain ⟨U, hU⟩ := SecondOrderGraftSemantics.exists_l hℳ S P (fun n _ => hS n)
  refine ⟨U, hU, ?_⟩
  intro B C hB hC
  obtain ⟨b, hb, hEq⟩ := (hU B).mp hB
  obtain ⟨c, hc, hCB⟩ := hC
  obtain ⟨d, hd, hCD⟩ := (SecondOrderBisimulation.match_l B.real S B.root b hEq).1 c hc
  exact (hU C).mpr ⟨d, hClosed b hb d hd,
    SecondOrderBisimulation.trans_l hℳ C.real B.real S C.root c d hCB hCD⟩

theorem identity_l (hℳ : Theory.Models ℳ theory_m) (P : set_l ℳ) :
    ∃ T : set_l ℳ, ∀ a b, relation_l T a b ↔ mem_l a P ∧ a = b := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .conj (.rel .mem (.cons (.fvar .here) (.cons (.fvar (.there (.there .here))) .nil)))
      (.equal (.fvar .here) (.fvar (.there .here)))
  obtain ⟨T, hT⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    (Env.empty.pushFree P)
  exact ⟨T, hT⟩

theorem graph_l (hℳ : Theory.Models ℳ theory_m) (R S P : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b)
    (hS : ∀ n, SecondOrderDomain.wf_l S n) :
    ∃ f : SecondOrderQuotient.type_l hℳ, ∀ p, SecondOrderQuotient.mem_l hℳ p f ↔
      ∃ n, mem_l n P ∧ SecondOrderPairObjects.ordered_l hℳ
        (SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR n))
        (SecondOrderQuotient.mk_l hℳ (code_l S hS n)) p := by
  obtain ⟨T, hT⟩ := identity_l hℳ P
  obtain ⟨f, hf⟩ := SecondOrderMixedImage.exists_l hℳ R S T
    (fun a b _ => ⟨SecondOrderNaturalGraph.wf_l hℳ R hR a, hS b⟩)
  refine ⟨f, fun p => (hf p).trans ?_⟩
  constructor
  · rintro ⟨a, b, h, hp⟩
    obtain ⟨ha, rfl⟩ := (hT a b).mp h
    exact ⟨a, ha, hp⟩
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, n, (hT n n).mpr ⟨hn, rfl⟩, hp⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSelectedCollapseGraph
