import BMSConstructibleBridge.SecondOrderValidRootGraph
import BMSConstructibleBridge.SecondOrderPairSet
import BMSConstructibleBridge.SecondOrderDomainClosure
import BMSConstructibleBridge.SecondOrderListInduction

/-! # 在原图上添加内部 ω 长的序数尾节点

标签零保留基础图；标签一的第 n 个节点包含基础根及其成员，另含所有
较早的尾节点。只用实际公式的内部强归纳核验无下降链，不调用 Collection。
本文件构造图及根码，序数与极限性质由后续成员规格验证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalTailGraph

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def zero_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num := .app (σ := signature_m) .zero .nil
private def one_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num := .app (σ := signature_m) .succ (.cons zero_m .nil)

def spec_l (S : set_l ℳ) (r : num_l ℳ) (G : set_l ℳ) : Prop :=
  ∀ x y, relation_l G x y ↔
    (∃ a b, value_l (zero_l ℳ) a = x ∧ value_l (zero_l ℳ) b = y ∧ relation_l S a b) ∨
    (∃ n, value_l (succ_l (zero_l ℳ)) n = y ∧
      ((∃ a, value_l (zero_l ℳ) a = x ∧ (relation_l S a r ∨ a = r)) ∨
        ∃ m, value_l (succ_l (zero_l ℳ)) m = x ∧ SecondOrderOrder.lt_l m n))

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (S : set_l ℳ) (r : num_l ℳ) :
    ∃ G, spec_l S r G := by
  let φ : Formula signature_m [] [.num, .num, .set, .num] := .disj
    (.existsE .num (.existsE .num (.conj
      (PrimitiveFormulas.pair_m zero_m (.bvar (.there .here)) (.fvar .here))
      (.conj (PrimitiveFormulas.pair_m zero_m (.bvar .here) (.fvar (.there .here)))
        (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))))))
    (.existsE .num (.conj (PrimitiveFormulas.pair_m one_m (.bvar .here) (.fvar (.there .here)))
      (.disj
        (.existsE .num (.conj (PrimitiveFormulas.pair_m zero_m (.bvar .here) (.fvar .here))
          (.disj (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar .here) (.fvar (.there (.there (.there .here)))))
            (.equal (.bvar .here) (.fvar (.there (.there (.there .here))))))))
        (.existsE .num (.conj (PrimitiveFormulas.pair_m one_m (.bvar .here) (.fvar .here))
          (PrimitiveFormulas.lt_m (.bvar .here) (.bvar (.there .here))))))))
  obtain ⟨G, hG⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree r).pushFree S)
  refine ⟨G, fun x y => (hG x y).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.formula_l, SecondOrderPairing.edge_l,
    SecondOrderOrder.formula_l, zero_m, one_m, Term.eval]
  rfl

theorem fiber_l (hℳ : Theory.Models ℳ theory_m) {S G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l S r G) : SecondOrderTaggedGraph.fiber_l (zero_l ℳ) S G := by
  intro x b
  rw [hG]
  constructor
  · rintro (⟨a, d, ha, hd, h⟩ | ⟨n, hn, _⟩)
    · obtain rfl := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hd).2
      exact ⟨a, ha.symm, h⟩
    · exact (nonzero_l hℳ (zero_l ℳ)
        (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hn).1).elim
  · rintro ⟨a, rfl, ha⟩
    exact Or.inl ⟨a, b, rfl, rfl, ha⟩

theorem tail_edge_l (hℳ : Theory.Models ℳ theory_m) {S G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l S r G) (x n : num_l ℳ) :
    relation_l G x (value_l (succ_l (zero_l ℳ)) n) ↔
      (∃ a, value_l (zero_l ℳ) a = x ∧ (relation_l S a r ∨ a = r)) ∨
        ∃ m, value_l (succ_l (zero_l ℳ)) m = x ∧ SecondOrderOrder.lt_l m n := by
  rw [hG]
  constructor
  · rintro (⟨a, b, _, hb, _⟩ | ⟨m, hm, h⟩)
    · exact (nonzero_l hℳ (zero_l ℳ)
        (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hb).1.symm).elim
    · obtain rfl := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hm).2
      exact h
  · exact fun h => Or.inr ⟨n, rfl, h⟩

theorem wf_l (hℳ : Theory.Models ℳ theory_m) {S G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l S r G) (hS : ∀ a, SecondOrderDomain.wf_l S a) :
    ∀ a, SecondOrderDomain.wf_l G a := by
  classical
  have hBase (a : num_l ℳ) : SecondOrderDomain.wf_l G (value_l (zero_l ℳ) a) :=
    SecondOrderTaggedDomain.wf_l hℳ _ S G (fiber_l hℳ hG) a (hS a)
  let φ : Formula signature_m [] [.num, .set] := .existsE .num (.conj
    (PrimitiveFormulas.pair_m one_m (.fvar .here) (.bvar .here))
    (GraphTranslation.domain_m (.fvar (.there .here)) (.bvar .here)))
  have hPure : language_m φ = true := by
    change (true && _) = true
    exact GraphTranslation.domain_pure_m _ _ rfl rfl
  have hRead (n : num_l ℳ) : φ.satisfies
      (((Env.empty (M := ℳ)).pushFree G).pushFree n) ↔
        SecondOrderDomain.wf_l G (value_l (succ_l (zero_l ℳ)) n) := by
    simp only [φ, Formula.satisfies, SecondOrderPairing.formula_l,
      SecondOrderInterpretation.domain_l, one_m, zero_m, Term.eval]
    change (∃ z : num_l ℳ, value_l (succ_l (zero_l ℳ)) n = z ∧ SecondOrderDomain.wf_l G z) ↔ _
    exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩
  have hTail := SecondOrderListInduction.strong_induct_l hℳ φ hPure
    ((Env.empty (M := ℳ)).pushFree G)
    (fun n => SecondOrderDomain.wf_l G (value_l (succ_l (zero_l ℳ)) n)) hRead
    (fun n ih => SecondOrderDomainClosure.intro_l hℳ G _ (fun x hx => by
      rcases (tail_edge_l hℳ hG x n).mp hx with ⟨a, ha, _⟩ | ⟨m, hm, hmn⟩
      · exact ha ▸ hBase a
      · exact hm ▸ ih m hmn))
  intro a
  by_cases hZero : ∃ b, value_l (zero_l ℳ) b = a
  · obtain ⟨b, rfl⟩ := hZero
    exact hBase b
  by_cases hOne : ∃ n, value_l (succ_l (zero_l ℳ)) n = a
  · obtain ⟨n, rfl⟩ := hOne
    exact hTail n
  exact SecondOrderDomain.leaf_l G a (fun x hx => by
    rcases (hG x a).mp hx with ⟨_, b, _, hb, _⟩ | ⟨n, hn, _⟩
    · exact hZero ⟨b, hb⟩
    · exact hOne ⟨n, hn⟩)

noncomputable def code_l (hℳ : Theory.Models ℳ theory_m) {S G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l S r G) (hS : ∀ a, SecondOrderDomain.wf_l S a) (n : num_l ℳ) :
    SecondOrderGraph.code_l ℳ := ⟨G, value_l (succ_l (zero_l ℳ)) n, wf_l hℳ hG hS _⟩

#print axioms exists_l
#print axioms wf_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalTailGraph
