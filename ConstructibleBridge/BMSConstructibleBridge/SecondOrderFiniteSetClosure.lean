import BMSConstructibleBridge.SecondOrderFiniteSetGraph

/-!
# 二进制成员图的基本集合闭包

所有内部根组成传递集合，并在根编码中含空集、无序对及并集。这里的根可以
是非标准数；不把内部有限性误认成宿主有限性，也尚不宣称已构造任意 FC(X)。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteSetClosure

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderAlgebra SecondOrderFiniteSetGraph

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
  (hE : SecondOrderBinaryPowers.spec_l E) {R : set_l ℳ} (hR : spec_l E hE R)

theorem empty_l (B : SecondOrderGraph.code_l ℳ) :
    ¬SecondOrderGraph.mem_l B (code_l hℳ hE hR (zero_l ℳ)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  rintro ⟨n, hn, _⟩
  exact (not_lt_of_ge (zero_le_l hℳ n)) (edge_lt_l hℳ hE hR hn)

theorem pair_l (a b : num_l ℳ) : ∃ c, ∀ B : SecondOrderGraph.code_l ℳ,
    SecondOrderGraph.mem_l B (code_l hℳ hE hR c) ↔
      SecondOrderGraph.eq_l B (code_l hℳ hE hR a) ∨
      SecondOrderGraph.eq_l B (code_l hℳ hE hR b) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  let k := max a b + 1
  letI := ordered_l hℳ
  have ha : a < k := lt_of_le_of_lt (le_max_left a b) (lt_add_one _)
  have hb : b < k := lt_of_le_of_lt (le_max_right a b) (lt_add_one _)
  let φ : Formula signature_m [] [.num, .num, .num] :=
    .disj (.equal (.fvar .here) (.fvar (.there .here)))
      (.equal (.fvar .here) (.fvar (.there (.there .here))))
  obtain ⟨X, hX⟩ := comprehension_l hℳ φ rfl (((Env.empty (M := ℳ)).pushFree b).pushFree a)
  have hx n : mem_l n X ↔ n = a ∨ n = b := hX n
  obtain ⟨c, hc⟩ := bounded_l hℳ hE hR X k
  refine ⟨c, fun B => (hc B).trans ?_⟩
  constructor
  · rintro ⟨n, _, hn, hBn⟩
    rcases (hx n).mp hn with rfl | rfl
    · exact Or.inl hBn
    · exact Or.inr hBn
  · rintro (h | h)
    · exact ⟨a, ha, (hx a).mpr (Or.inl rfl), h⟩
    · exact ⟨b, hb, (hx b).mpr (Or.inr rfl), h⟩

theorem union_l (a : num_l ℳ) : ∃ c, ∀ B : SecondOrderGraph.code_l ℳ,
    SecondOrderGraph.mem_l B (code_l hℳ hE hR c) ↔ ∃ D : SecondOrderGraph.code_l ℳ,
      SecondOrderGraph.mem_l B D ∧ SecondOrderGraph.mem_l D (code_l hℳ hE hR a) := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .existsE .num (.conj (GraphSyntax.edge_m (.fvar (.there (.there .here)))
      (.bvar .here) (.fvar (.there .here)))
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar .here)))
  obtain ⟨X, hX⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree R).pushFree a)
  have hx n : mem_l n X ↔ ∃ m, relation_l R m a ∧ relation_l R n m := by
    refine (hX n).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
    rfl
  obtain ⟨c, hc⟩ := bounded_l hℳ hE hR X a
  refine ⟨c, fun B => (hc B).trans ?_⟩
  constructor
  · rintro ⟨n, _, hn, hBn⟩
    obtain ⟨m, hm, hnm⟩ := (hx n).mp hn
    exact ⟨code_l hℳ hE hR m, ⟨n, hnm, hBn⟩,
      m, hm, SecondOrderGraph.refl_l hℳ (code_l hℳ hE hR m)⟩
  · rintro ⟨D, hBD, m, hm, hDm⟩
    have hBm := (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ B)
      (show SecondOrderGraph.eq_l D (code_l hℳ hE hR m) from hDm)).mp hBD
    obtain ⟨n, hn, hBn⟩ := hBm
    exact ⟨n, SecondOrderOrder.trans_l hℳ (edge_lt_l hℳ hE hR hn)
      (edge_lt_l hℳ hE hR hm), (hx n).mpr ⟨m, hm, hn⟩, hBn⟩

theorem transitive_l (H : SecondOrderGraph.code_l ℳ)
    (hH : ∀ B, SecondOrderGraph.mem_l B H ↔ ∃ n, SecondOrderGraph.eq_l B (code_l hℳ hE hR n))
    {A B : SecondOrderGraph.code_l ℳ} (hA : SecondOrderGraph.mem_l A H)
    (hBA : SecondOrderGraph.mem_l B A) : SecondOrderGraph.mem_l B H := by
  obtain ⟨n, hn⟩ := (hH A).mp hA
  obtain ⟨m, _, hm⟩ := (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ B) hn).mp hBA
  exact (hH B).mpr ⟨m, hm⟩

#print axioms pair_l
#print axioms union_l
#print axioms transitive_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteSetClosure
