import BMSConstructibleBridge.SecondOrderGraphMinimum
import BMSConstructibleBridge.SecondOrderBisimulation

/-! # 有效图根上的隶属关系保持内部良基

关系边可通过内部双模拟表达集合隶属，不要求它是原图的字面子关系。
反例链的双模拟饱和值域由实际理解构造，原图的成员极小根产生矛盾。
这一步不将内部良基性替换为外部良基，也不抽取匹配函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootRelationWellFounded

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem saturated_range_l (hℳ : Theory.Models ℳ theory_m) (A X : set_l ℳ) :
    ∃ P : set_l ℳ, ∀ a, mem_l a P ↔ ∃ i b, relation_l X i b ∧
      SecondOrderBisimulation.eq_l A A a b := by
  obtain ⟨Q, hQ⟩ := SecondOrderBisimulation.maximum_l hℳ A A
  let φ : Formula signature_m [] [.num, .set, .set] :=
    .existsE .num <| .existsE .num <| .conj
      (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar .here))
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree Q).pushFree X)
  refine ⟨P, fun a => (hP a).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
  change (∃ i b, relation_l X i b ∧ relation_l Q a b) ↔ _
  exact exists_congr (fun i => exists_congr (fun b => and_congr Iff.rfl (hQ a b)))

theorem wf_l (hℳ : Theory.Models ℳ theory_m) (A R : set_l ℳ)
    (hParents : ∀ i j, relation_l R i j → SecondOrderDomain.wf_l A j)
    (hEdges : ∀ i j, relation_l R i j → ∃ c, relation_l A c j ∧
      SecondOrderBisimulation.eq_l A A i c) : ∀ n, SecondOrderDomain.wf_l R n := by
  intro n X hX h₀
  classical
  by_contra hNoBreak
  have hChain : ∀ i b c, relation_l X i b → relation_l X (succ_l i) c → relation_l R c b := by
    intro i b c hb hc
    by_contra hEdge
    exact hNoBreak ⟨i, b, c, hb, hc, hEdge⟩
  obtain ⟨k, hk, _⟩ := hX (succ_l (zero_l ℳ))
  have hn : SecondOrderDomain.wf_l A n := hParents k n (hChain (zero_l ℳ) n k h₀ hk)
  obtain ⟨P, hP⟩ := saturated_range_l hℳ A X
  have hStart : mem_l n P := (hP n).mpr ⟨zero_l ℳ, n, h₀, SecondOrderBisimulation.refl_l hℳ A n⟩
  obtain ⟨a, ha, _, hMin⟩ := SecondOrderGraphMinimum.exists_l hℳ A P n hn hStart
  obtain ⟨i, b, hb, hEq⟩ := (hP a).mp ha
  obtain ⟨d, hd, _⟩ := hX (succ_l i)
  obtain ⟨c, hc, hDC⟩ := hEdges d b (hChain i b d hb hd)
  obtain ⟨e, he, hEC⟩ := (SecondOrderBisimulation.match_l A A a b hEq).2 c hc
  have hED := SecondOrderBisimulation.trans_l hℳ A A A e c d hEC
    (SecondOrderBisimulation.symm_l hℳ A A d c hDC)
  exact hMin e he ((hP e).mpr ⟨succ_l i, d, hd, hED⟩)

#print axioms wf_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootRelationWellFounded
