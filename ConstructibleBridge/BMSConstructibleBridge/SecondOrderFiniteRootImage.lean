import BMSConstructibleBridge.SecondOrderFiniteExtensionGraph
import BMSConstructibleBridge.SecondOrderFiniteRange

/-!
# 内部有限根序列的精确集合像

原模型中的截段函数图已有统一数值界。由理解形成根值域，再调用扩展图的
有界根闭包，得到内部有限序列的精确集合像。输入仍须为实际实数函数图，
不接受只有宿主函数或逐点存在而尚未统一编码的根代表。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteRootImage

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFiniteExtensionGraph

set_option autoImplicit false

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) {S E G : set_l ℳ}
    {hE : SecondOrderBinaryPowers.spec_l E} (hG : spec_l S E hE G)
    (hS : ∀ n, SecondOrderDomain.wf_l S n) (F : set_l ℳ) (k : num_l ℳ)
    (hF : ∀ i, SecondOrderOrder.lt_l i k → ∃! n, relation_l F i n) :
    ∃ c, ∀ B : SecondOrderGraph.code_l ℳ,
      SecondOrderGraph.mem_l B (code_l hℳ hG hS (value_l (succ_l (zero_l ℳ)) c)) ↔
        ∃ i n, SecondOrderOrder.lt_l i k ∧ relation_l F i n ∧
          SecondOrderGraph.eq_l B (code_l hℳ hG hS n) := by
  obtain ⟨b, hb⟩ := SecondOrderFiniteRange.partial_bound_l hℳ F k hF
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .existsE .num (.conj (PrimitiveFormulas.lt_m (.bvar .here) (.fvar (.there .here)))
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar .here) (.fvar .here)))
  obtain ⟨X, hX⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree F).pushFree k)
  have hx n : mem_l n X ↔ ∃ i, SecondOrderOrder.lt_l i k ∧ relation_l F i n := by
    refine (hX n).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderOrder.formula_l, SecondOrderPairing.edge_l]
    rfl
  obtain ⟨c, hc⟩ := bounded_l hℳ hG hS X b
  refine ⟨c, fun B => (hc B).trans ?_⟩
  constructor
  · rintro ⟨n, _, hn, hBn⟩
    obtain ⟨i, hi, hIn⟩ := (hx n).mp hn
    exact ⟨i, n, hi, hIn, hBn⟩
  · rintro ⟨i, n, hi, hIn, hBn⟩
    exact ⟨n, hb i hi n hIn, (hx n).mpr ⟨i, hi, hIn⟩, hBn⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteRootImage
