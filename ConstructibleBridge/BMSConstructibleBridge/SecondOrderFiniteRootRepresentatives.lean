import BMSConstructibleBridge.SecondOrderFiniteRootImage
import BMSConstructibleBridge.SecondOrderMinimum

/-!
# 根代表不唯一时的内部有限像

只要求同一索引的根代表双模拟等价，不要求数码相等。原最小数选择定理生成
实际内部选择图，再形成有限像。没有抽取宿主 Type 选择函数；调用者仍须给出
一个统一实数关系以及所需截段上的非空性和双模拟单值性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteRootRepresentatives

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFiniteExtensionGraph

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 只在所需截段要求关系非空，界外显式补零；原理解形成统一选择图。 -/
theorem select_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) (k : num_l ℳ)
    (hR : ∀ i, SecondOrderOrder.lt_l i k → ∃ n, relation_l R i n) :
    ∃ F : set_l ℳ, SecondOrderFunctions.function_l F ∧
      ∀ i, SecondOrderOrder.lt_l i k → ∀ n, relation_l F i n → relation_l R i n := by
  let φ : Formula signature_m [] [.num, .num, .num, .set] :=
    .disj (.conj (PrimitiveFormulas.lt_m (.fvar .here) (.fvar (.there (.there .here))))
      (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.fvar .here) (.fvar (.there .here))))
      (.conj (.neg (PrimitiveFormulas.lt_m (.fvar .here) (.fvar (.there (.there .here)))))
        (.equal (.fvar (.there .here)) (Term.app (σ := signature_m) .zero .nil)))
  obtain ⟨T, hT⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree R).pushFree k)
  have ht i n : relation_l T i n ↔
      (SecondOrderOrder.lt_l i k ∧ relation_l R i n) ∨
        (¬SecondOrderOrder.lt_l i k ∧ n = zero_l ℳ) := by
    refine (hT i n).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderOrder.formula_l, SecondOrderPairing.edge_l]
    rfl
  have hTotal i : ∃ n, relation_l T i n := by
    classical
    by_cases hi : SecondOrderOrder.lt_l i k
    · obtain ⟨n, hn⟩ := hR i hi
      exact ⟨n, (ht i n).mpr (Or.inl ⟨hi, hn⟩)⟩
    · exact ⟨zero_l ℳ, (ht i _).mpr (Or.inr ⟨hi, rfl⟩)⟩
  obtain ⟨F, hF, hFT⟩ := SecondOrderMinimum.choice_l hℳ T hTotal
  refine ⟨F, hF, fun i hi n hn => ?_⟩
  exact (((ht i n).mp (hFT i n hn)).resolve_right (fun h => h.1 hi)).2

theorem exists_l (hℳ : Theory.Models ℳ theory_m) {S E G : set_l ℳ}
    {hE : SecondOrderBinaryPowers.spec_l E} (hG : spec_l S E hE G)
    (hS : ∀ n, SecondOrderDomain.wf_l S n) (R : set_l ℳ) (k : num_l ℳ)
    (hR : ∀ i, SecondOrderOrder.lt_l i k → ∃ n, relation_l R i n)
    (hUnique : ∀ i, SecondOrderOrder.lt_l i k → ∀ n m, relation_l R i n → relation_l R i m →
      SecondOrderGraph.eq_l (code_l hℳ hG hS n) (code_l hℳ hG hS m)) :
    ∃ c, ∀ B : SecondOrderGraph.code_l ℳ,
      SecondOrderGraph.mem_l B (code_l hℳ hG hS (value_l (succ_l (zero_l ℳ)) c)) ↔
        ∃ i n, SecondOrderOrder.lt_l i k ∧ relation_l R i n ∧
          SecondOrderGraph.eq_l B (code_l hℳ hG hS n) := by
  obtain ⟨F, hF, hFR⟩ := select_l hℳ R k hR
  obtain ⟨c, hc⟩ := SecondOrderFiniteRootImage.exists_l hℳ hG hS F k (fun i _ => hF i)
  refine ⟨c, fun B => (hc B).trans ?_⟩
  constructor
  · rintro ⟨i, n, hi, hIn, hBn⟩
    exact ⟨i, n, hi, hFR i hi n hIn, hBn⟩
  · rintro ⟨i, n, hi, hIn, hBn⟩
    obtain ⟨m, hIm, _⟩ := hF i
    exact ⟨i, m, hi, hIm, SecondOrderGraph.trans_l hℳ hBn
      (hUnique i hi n m hIn (hFR i hi m hIm))⟩

#print axioms select_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteRootRepresentatives
