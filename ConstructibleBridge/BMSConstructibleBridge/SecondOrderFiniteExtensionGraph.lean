import BMSConstructibleBridge.SecondOrderFiniteSetGraph
import BMSConstructibleBridge.SecondOrderRankedDomain
import BMSConstructibleBridge.SecondOrderValidRootGraph
import BMSConstructibleBridge.SecondOrderPairSet

/-!
# 任意基础图上的有限集合构造节点

标签 0 保留基础图，标签 1 的码 c 以 c 的二进制位指定子根。标签互斥保证
基础纤维不受新增边干扰；新增边严格降低数值，故基础根无链时所有根无链。
这构造的是闭包载体的图，不宣称已分离出精确 FC(X)。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteExtensionGraph

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderAlgebra

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l (S E : set_l ℳ) (hE : SecondOrderBinaryPowers.spec_l E) (G : set_l ℳ) : Prop :=
  ∀ x y, relation_l G x y ↔
    (∃ a b, value_l (zero_l ℳ) a = x ∧ value_l (zero_l ℳ) b = y ∧ relation_l S a b) ∨
    (∃ c, value_l (succ_l (zero_l ℳ)) c = y ∧
      SecondOrderDigit.holds_l c (SecondOrderPowers.value_l hE x))

private def zero_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def one_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons zero_m .nil)

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (S E : set_l ℳ)
    (hE : SecondOrderBinaryPowers.spec_l E) : ∃ G, spec_l S E hE G := by
  let φ : Formula signature_m [] [.num, .num, .set, .set] := .disj
    (.existsE .num (.existsE .num (.conj
      (PrimitiveFormulas.pair_m zero_m (.bvar (.there .here)) (.fvar .here))
      (.conj (PrimitiveFormulas.pair_m zero_m (.bvar .here) (.fvar (.there .here)))
        (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))))))
    (.existsE .num (.existsE .num (.conj
      (PrimitiveFormulas.pair_m one_m (.bvar (.there .here)) (.fvar (.there .here)))
      (.conj (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.fvar .here) (.bvar .here))
        (SecondOrderDigit.formula_m (.bvar (.there .here)) (.bvar .here))))))
  obtain ⟨G, hG⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree E).pushFree S)
  refine ⟨G, fun x y => (hG x y).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.formula_l, SecondOrderPairing.edge_l,
    SecondOrderDigit.formula_l]
  change (_ ∨ ∃ c p, value_l (succ_l (zero_l ℳ)) c = y ∧ relation_l E x p ∧
    SecondOrderDigit.holds_l c p) ↔ _
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨c, p, hc, hp, hd⟩
    obtain rfl := (SecondOrderPowers.eq_l hE x p).mp hp
    exact ⟨c, hc, hd⟩
  · rintro ⟨c, hc, hd⟩
    exact ⟨c, _, hc, SecondOrderPowers.edge_l hE x, hd⟩

theorem fiber_l (hℳ : Theory.Models ℳ theory_m) {S E G : set_l ℳ}
    {hE : SecondOrderBinaryPowers.spec_l E} (hG : spec_l S E hE G) :
    SecondOrderTaggedGraph.fiber_l (zero_l ℳ) S G := by
  intro x b
  rw [hG]
  constructor
  · rintro (⟨a, d, ha, hd, h⟩ | ⟨c, hc, _⟩)
    · obtain rfl := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hd).2
      exact ⟨a, ha.symm, h⟩
    · exact False.elim (nonzero_l hℳ (zero_l ℳ)
        (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hc).1)
  · rintro ⟨a, rfl, ha⟩
    exact Or.inl ⟨a, b, rfl, rfl, ha⟩

theorem wf_l (hℳ : Theory.Models ℳ theory_m) {S E G : set_l ℳ}
    {hE : SecondOrderBinaryPowers.spec_l E} (hG : spec_l S E hE G)
    (hS : ∀ n, SecondOrderDomain.wf_l S n) : ∀ n, SecondOrderDomain.wf_l G n := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  apply SecondOrderRankedDomain.wf_l hℳ G (fun n => ∃ a, n = value_l (zero_l ℳ) a)
  · rintro n ⟨a, rfl⟩
    exact SecondOrderTaggedDomain.wf_l hℳ _ S G (fiber_l hℳ hG) a (hS a)
  · intro y hy x hxy
    rcases (hG x y).mp hxy with ⟨a, b, _, hb, _⟩ | ⟨c, hc, hd⟩
    · exact False.elim (hy ⟨b, hb.symm⟩)
    · apply Or.inr
      have hBound : SecondOrderPowers.value_l hE x ≤ c :=
        le_of_not_gt (fun h => SecondOrderDigit.below_l hℳ _ _ h hd)
      have hxc : x < c := lt_of_lt_of_le (SecondOrderBinaryPowers.growth_l hℳ hE x) hBound
      rw [← hc]
      exact lt_of_lt_of_le hxc (SecondOrderProgramListCode.coordinates_le_pair_l hℳ _ c).2

theorem constructor_l (hℳ : Theory.Models ℳ theory_m) {S E G : set_l ℳ}
    {hE : SecondOrderBinaryPowers.spec_l E} (hG : spec_l S E hE G) (x c : num_l ℳ) :
    relation_l G x (value_l (succ_l (zero_l ℳ)) c) ↔
      SecondOrderDigit.holds_l c (SecondOrderPowers.value_l hE x) := by
  rw [hG]
  constructor
  · rintro (⟨a, b, _, hb, _⟩ | ⟨d, hd, h⟩)
    · exact False.elim (nonzero_l hℳ (zero_l ℳ)
        (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hb).1.symm)
    · obtain rfl := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hd).2
      exact h
  · intro h
    exact Or.inr ⟨c, rfl, h⟩

def code_l (hℳ : Theory.Models ℳ theory_m) {S E G : set_l ℳ}
    {hE : SecondOrderBinaryPowers.spec_l E} (hG : spec_l S E hE G)
    (hS : ∀ n, SecondOrderDomain.wf_l S n) (a : num_l ℳ) : SecondOrderGraph.code_l ℳ :=
  ⟨G, a, wf_l hℳ hG hS a⟩

/-- 所有内部有界根集都有精确成员构造码，允许根来自原基础图或新增节点。 -/
theorem bounded_l (hℳ : Theory.Models ℳ theory_m) {S E G : set_l ℳ}
    {hE : SecondOrderBinaryPowers.spec_l E} (hG : spec_l S E hE G)
    (hS : ∀ n, SecondOrderDomain.wf_l S n) (X : set_l ℳ) (k : num_l ℳ) :
    ∃ c, ∀ B : SecondOrderGraph.code_l ℳ,
      SecondOrderGraph.mem_l B (code_l hℳ hG hS (value_l (succ_l (zero_l ℳ)) c)) ↔
        ∃ n, SecondOrderOrder.lt_l n k ∧ mem_l n X ∧ SecondOrderGraph.eq_l B (code_l hℳ hG hS n) := by
  obtain ⟨c, _, hc⟩ := SecondOrderFiniteCode.segment_l hℳ hE X k
  refine ⟨c, fun B => ?_⟩
  change (∃ n, relation_l G n (value_l (succ_l (zero_l ℳ)) c) ∧
    SecondOrderBisimulation.eq_l B.real G B.root n) ↔ _
  exact exists_congr (fun n =>
    (and_congr ((constructor_l hℳ hG n c).trans (hc n)) Iff.rfl).trans and_assoc)

/-- 原有效根经过限制和标签嵌入后仍代表原集合；所有存在见证留在 Prop。 -/
theorem extension_exists_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) :
    ∃ G : set_l ℳ, (∀ n, SecondOrderDomain.wf_l G n) ∧
      ∀ a, SecondOrderDomain.wf_l R a →
        SecondOrderBisimulation.eq_l R G a (value_l (zero_l ℳ) a) := by
  obtain ⟨E, hE⟩ := SecondOrderBinaryPowers.exists_l hℳ
  obtain ⟨S, hS⟩ := SecondOrderValidRootGraph.exists_l hℳ R
  obtain ⟨G, hG⟩ := exists_l hℳ S E hE
  refine ⟨G, wf_l hℳ hG (SecondOrderValidRootGraph.wf_l hS), fun a ha => ?_⟩
  exact SecondOrderBisimulation.trans_l hℳ R S G a a _
    (SecondOrderValidRootGraph.agrees_l hℳ hS a ha)
    (SecondOrderPairSet.tag_eq_l hℳ _ S G (fiber_l hℳ hG) a)

#print axioms exists_l
#print axioms wf_l
#print axioms bounded_l
#print axioms extension_exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteExtensionGraph
