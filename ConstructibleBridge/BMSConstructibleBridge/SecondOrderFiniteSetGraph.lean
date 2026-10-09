import BMSConstructibleBridge.SecondOrderFiniteCode
import BMSConstructibleBridge.SecondOrderNaturalGraph
import BMSConstructibleBridge.SecondOrderGraftSemantics

/-!
# 内部有限集合的二进制成员图

边 n → m 表示 m 的第 n 个二进制位为 1。所有边严格降低内部自然数，故所有
根满足原无内部下降链公式。任意有界内部根集都有一个恰以其为成员的根。
这里只证明根编码闭包，尚未把它等同于任意母集的完整有限子集闭包 FC。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteSetGraph

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderAlgebra

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l (E : set_l ℳ) (hE : SecondOrderBinaryPowers.spec_l E) (R : set_l ℳ) : Prop :=
  ∀ n m, relation_l R n m ↔ SecondOrderDigit.holds_l m (SecondOrderPowers.value_l hE n)

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (E : set_l ℳ)
    (hE : SecondOrderBinaryPowers.spec_l E) : ∃ R, spec_l E hE R := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .existsE .num (.conj (GraphSyntax.edge_m (.fvar (.there (.there .here)))
      (.fvar .here) (.bvar .here))
      (SecondOrderDigit.formula_m (.fvar (.there .here)) (.bvar .here)))
  obtain ⟨R, hR⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((Env.empty (M := ℳ)).pushFree E)
  refine ⟨R, fun n m => (hR n m).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderDigit.formula_l]
  change (∃ p, relation_l E n p ∧ SecondOrderDigit.holds_l m p) ↔ _
  constructor
  · rintro ⟨p, hp, h⟩
    obtain rfl := (SecondOrderPowers.eq_l hE n p).mp hp
    exact h
  · intro h
    exact ⟨_, SecondOrderPowers.edge_l hE n, h⟩

theorem edge_lt_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) {R : set_l ℳ} (hR : spec_l E hE R)
    {n m : num_l ℳ} (h : relation_l R n m) : SecondOrderOrder.lt_l n m := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have hDigit := (hR n m).mp h
  have hBound : SecondOrderPowers.value_l hE n ≤ m :=
    le_of_not_gt (fun hm => SecondOrderDigit.below_l hℳ _ _ hm hDigit)
  exact lt_of_lt_of_le (SecondOrderBinaryPowers.growth_l hℳ hE n) hBound

theorem wf_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) {R : set_l ℳ} (hR : spec_l E hE R)
    (n : num_l ℳ) : SecondOrderDomain.wf_l R n := by
  obtain ⟨S, hS⟩ := SecondOrderNaturalGraph.relation_exists_l hℳ
  exact SecondOrderDomain.mono_l S R n
    (fun _ _ h => (hS _ _).mpr (edge_lt_l hℳ hE hR h))
    (SecondOrderNaturalGraph.wf_l hℳ S hS n)

def code_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) {R : set_l ℳ} (hR : spec_l E hE R)
    (n : num_l ℳ) : SecondOrderGraph.code_l ℳ := ⟨R, n, wf_l hℳ hE hR n⟩

/-- 包括非标准界在内的每个内部有界根集，都由一个根精确表示。 -/
theorem bounded_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) {R : set_l ℳ} (hR : spec_l E hE R)
    (X : set_l ℳ) (k : num_l ℳ) : ∃ c, ∀ B : SecondOrderGraph.code_l ℳ,
      SecondOrderGraph.mem_l B (code_l hℳ hE hR c) ↔
        ∃ n, SecondOrderOrder.lt_l n k ∧ mem_l n X ∧ SecondOrderGraph.eq_l B (code_l hℳ hE hR n) := by
  obtain ⟨c, _, hc⟩ := SecondOrderFiniteCode.segment_l hℳ hE X k
  refine ⟨c, fun B => ?_⟩
  change (∃ n, relation_l R n c ∧ SecondOrderBisimulation.eq_l B.real R B.root n) ↔ _
  exact exists_congr (fun n =>
    (and_congr ((hR n c).trans (hc n)) Iff.rfl).trans and_assoc)

/-- 收集全部内部根而不遗漏无前驱的空集根。 -/
theorem range_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) {R : set_l ℳ} (hR : spec_l E hE R) :
    ∃ H : SecondOrderGraph.code_l ℳ, ∀ B,
      SecondOrderGraph.mem_l B H ↔ ∃ n, SecondOrderGraph.eq_l B (code_l hℳ hE hR n) := by
  let φ : Formula signature_m [] [.num] := .equal (.fvar .here) (.fvar .here)
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ rfl Env.empty
  have hAll n : mem_l n P := (hP n).mpr rfl
  obtain ⟨H, hH⟩ := SecondOrderGraftSemantics.exists_l hℳ R P (fun n _ => wf_l hℳ hE hR n)
  refine ⟨H, fun B => (hH B).trans ?_⟩
  exact exists_congr (fun n => and_iff_right (hAll n))

#print axioms wf_l
#print axioms bounded_l
#print axioms range_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteSetGraph
