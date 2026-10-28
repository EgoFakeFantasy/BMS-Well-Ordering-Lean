import BMSConstructibleBridge.SecondOrderOrdinalTailGraph

/-! # 在基础图上添加内部字典序 ω² 尾

标签零保留基础图，标签一包裹两个内部数的配对码。无下降链证明依次对
「第 n 行的每个根良基」和「固定行的第 m 个根良基」作实际公式强归纳。
本模块只提供裸二阶算术模型中的图构造辅助层，不宣称对象最终闭句已可推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalDoubleTailGraph

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def zero_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  .app (σ := signature_m) .zero .nil

private def one_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  .app (σ := signature_m) .succ (.cons zero_m .nil)

noncomputable def root_l (n m : num_l ℳ) : num_l ℳ :=
  value_l (succ_l (zero_l ℳ)) (value_l n m)

/-- 两次配对均由原算术公式表示，不调用扩充签名的配对函数。 -/
def root_m {Γ Δ : SortContext signature_m} (n m z : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .existsE .num (.conj
    (PrimitiveFormulas.pair_m (n.weakenBound sort_m.num) (m.weakenBound sort_m.num) (.bvar .here))
    (PrimitiveFormulas.pair_m one_m (.bvar .here) (z.weakenBound sort_m.num)))

theorem root_pure_m {Γ Δ : SortContext signature_m} (n m z : Term signature_m Γ Δ .num)
    (hn : pure_term_m n = true) (hm : pure_term_m m = true) (hz : pure_term_m z = true) :
    pure_m (root_m n m z) = true := by
  simp only [root_m, pure_m, Bool.and_eq_true]
  exact ⟨PrimitiveFormulas.pair_pure_l _ _ _
      (by simpa only [PrimitiveFormulas.weaken_l] using hn)
      (by simpa only [PrimitiveFormulas.weaken_l] using hm) rfl,
    PrimitiveFormulas.pair_pure_l _ _ _ rfl rfl
      (by simpa only [PrimitiveFormulas.weaken_l] using hz)⟩

theorem root_language_m {Γ Δ : SortContext signature_m} (n m z : Term signature_m Γ Δ .num)
    (hn : pure_term_m n = true) (hm : pure_term_m m = true) (hz : pure_term_m z = true) :
    language_m (root_m n m z) = true :=
  pure_language_m _ (root_pure_m n m z hn hm hz)

theorem root_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (n m z : Term signature_m Γ Δ .num) :
    Formula.satisfies η (root_m n m z) ↔ root_l (n.eval η) (m.eval η) = z.eval η := by
  simp only [root_m, Formula.satisfies, SecondOrderPairing.formula_l,
    Term.eval_weakenBound, one_m, zero_m, Term.eval]
  change (∃ p : num_l ℳ, value_l (n.eval η) (m.eval η) = p ∧
    value_l (succ_l (zero_l ℳ)) p = z.eval η) ↔ _
  simp [root_l]

theorem root_injective_l (hℳ : Theory.Models ℳ theory_m) {n m i j : num_l ℳ}
    (h : root_l n m = root_l i j) : n = i ∧ m = j :=
  SecondOrderPairingBounds.injective_l hℳ _ _ _ _
    (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ h).2

def lex_l (i j n m : num_l ℳ) : Prop :=
  SecondOrderOrder.lt_l i n ∨ (i = n ∧ SecondOrderOrder.lt_l j m)

private def lex_m {Γ Δ : SortContext signature_m}
    (i j n m : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .disj (PrimitiveFormulas.lt_m i n)
    (.conj (.equal i n) (PrimitiveFormulas.lt_m j m))

def spec_l (S : set_l ℳ) (r : num_l ℳ) (G : set_l ℳ) : Prop :=
  ∀ x y, relation_l G x y ↔
    (∃ a b, value_l (zero_l ℳ) a = x ∧ value_l (zero_l ℳ) b = y ∧ relation_l S a b) ∨
    (∃ n m, root_l n m = y ∧
      ((∃ a, value_l (zero_l ℳ) a = x ∧ (relation_l S a r ∨ a = r)) ∨
        ∃ i j, root_l i j = x ∧ lex_l i j n m))

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (S : set_l ℳ) (r : num_l ℳ) :
    ∃ G, spec_l S r G := by
  let φ : Formula signature_m [] [.num, .num, .set, .num] := .disj
    (.existsE .num (.existsE .num (.conj
      (PrimitiveFormulas.pair_m zero_m (.bvar (.there .here)) (.fvar .here))
      (.conj (PrimitiveFormulas.pair_m zero_m (.bvar .here) (.fvar (.there .here)))
        (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))))))
    (.existsE .num (.existsE .num (.conj
      (root_m (.bvar (.there .here)) (.bvar .here) (.fvar (.there .here)))
      (.disj
        (.existsE .num (.conj (PrimitiveFormulas.pair_m zero_m (.bvar .here) (.fvar .here))
          (.disj (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar .here)
            (.fvar (.there (.there (.there .here)))))
            (.equal (.bvar .here) (.fvar (.there (.there (.there .here))))))))
        (.existsE .num (.existsE .num (.conj
          (root_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))
          (lex_m (.bvar (.there .here)) (.bvar .here)
            (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))))))))))
  obtain ⟨G, hG⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree r).pushFree S)
  refine ⟨G, fun x y => (hG x y).trans ?_⟩
  simp only [φ, lex_m, Formula.satisfies, root_formula_l, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l, SecondOrderOrder.formula_l, zero_m, Term.eval]
  rfl

theorem fiber_l (hℳ : Theory.Models ℳ theory_m) {S G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l S r G) : SecondOrderTaggedGraph.fiber_l (zero_l ℳ) S G := by
  intro x b
  rw [hG]
  constructor
  · rintro (⟨a, d, ha, hd, h⟩ | ⟨n, m, hn, _⟩)
    · obtain rfl := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hd).2
      exact ⟨a, ha.symm, h⟩
    · exact (nonzero_l hℳ (zero_l ℳ)
        (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hn).1).elim
  · rintro ⟨a, rfl, ha⟩
    exact Or.inl ⟨a, b, rfl, rfl, ha⟩

theorem tail_edge_l (hℳ : Theory.Models ℳ theory_m) {S G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l S r G) (x n m : num_l ℳ) :
    relation_l G x (root_l n m) ↔
      (∃ a, value_l (zero_l ℳ) a = x ∧ (relation_l S a r ∨ a = r)) ∨
        ∃ i j, root_l i j = x ∧ lex_l i j n m := by
  rw [hG]
  constructor
  · rintro (⟨a, b, _, hb, _⟩ | ⟨i, j, hi, h⟩)
    · exact (nonzero_l hℳ (zero_l ℳ)
        (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hb).1.symm).elim
    · obtain ⟨rfl, rfl⟩ := root_injective_l hℳ hi
      exact h
  · exact fun h => Or.inr ⟨n, m, rfl, h⟩

/-- 两层归纳均消费原语言公式及其全部内部数值语义。 -/
theorem wf_l (hℳ : Theory.Models ℳ theory_m) {S G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l S r G) (hS : ∀ a, SecondOrderDomain.wf_l S a) :
    ∀ a, SecondOrderDomain.wf_l G a := by
  classical
  have hBase (a : num_l ℳ) : SecondOrderDomain.wf_l G (value_l (zero_l ℳ) a) :=
    SecondOrderTaggedDomain.wf_l hℳ _ S G (fiber_l hℳ hG) a (hS a)
  let φ : Formula signature_m [] [.num, .set] := .forallE .num (.existsE .num (.conj
    (root_m (.fvar .here) (.bvar (.there .here)) (.bvar .here))
    (GraphTranslation.domain_m (.fvar (.there .here)) (.bvar .here))))
  have hPure : language_m φ = true := by
    change (true && _) = true
    exact GraphTranslation.domain_pure_m _ _ rfl rfl
  have hRead (n : num_l ℳ) : φ.satisfies
      (((Env.empty (M := ℳ)).pushFree G).pushFree n) ↔
        ∀ m, SecondOrderDomain.wf_l G (root_l n m) := by
    simp only [φ, Formula.satisfies, root_formula_l, SecondOrderInterpretation.domain_l, Term.eval]
    change (∀ m : num_l ℳ, ∃ z : num_l ℳ,
      root_l n m = z ∧ SecondOrderDomain.wf_l G z) ↔ _
    simp
  have hTail := SecondOrderListInduction.strong_induct_l hℳ φ hPure
    ((Env.empty (M := ℳ)).pushFree G)
    (fun n => ∀ m, SecondOrderDomain.wf_l G (root_l n m)) hRead (by
      intro n ihOuter
      let ψ : Formula signature_m [] [.num, .num, .set] := .existsE .num (.conj
        (root_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
        (GraphTranslation.domain_m (.fvar (.there (.there .here))) (.bvar .here)))
      have hPureInner : language_m ψ = true := by
        change (true && _) = true
        exact GraphTranslation.domain_pure_m _ _ rfl rfl
      have hReadInner (m : num_l ℳ) : ψ.satisfies
          ((((Env.empty (M := ℳ)).pushFree G).pushFree n).pushFree m) ↔
            SecondOrderDomain.wf_l G (root_l n m) := by
        simp only [ψ, Formula.satisfies, root_formula_l, SecondOrderInterpretation.domain_l, Term.eval]
        change (∃ z : num_l ℳ, root_l n m = z ∧ SecondOrderDomain.wf_l G z) ↔ _
        simp
      apply SecondOrderListInduction.strong_induct_l hℳ ψ hPureInner
        (((Env.empty (M := ℳ)).pushFree G).pushFree n)
        (fun m => SecondOrderDomain.wf_l G (root_l n m)) hReadInner
      intro m ihInner
      apply SecondOrderDomainClosure.intro_l hℳ G _
      intro x hx
      rcases (tail_edge_l hℳ hG x n m).mp hx with ⟨a, ha, _⟩ | ⟨i, j, hij, hlex⟩
      · exact ha ▸ hBase a
      · rcases hlex with hi | ⟨rfl, hj⟩
        · exact hij ▸ ihOuter i hi j
        · exact hij ▸ ihInner j hj)
  intro a
  by_cases hZero : ∃ b, value_l (zero_l ℳ) b = a
  · obtain ⟨b, rfl⟩ := hZero
    exact hBase b
  by_cases hOne : ∃ n m, root_l n m = a
  · obtain ⟨n, m, rfl⟩ := hOne
    exact hTail n m
  exact SecondOrderDomain.leaf_l G a (fun x hx => by
    rcases (hG x a).mp hx with ⟨_, b, _, hb, _⟩ | ⟨n, m, hn, _⟩
    · exact hZero ⟨b, hb⟩
    · exact hOne ⟨n, m, hn⟩)

noncomputable def code_l (hℳ : Theory.Models ℳ theory_m) {S G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l S r G) (hS : ∀ a, SecondOrderDomain.wf_l S a) (n m : num_l ℳ) :
    SecondOrderGraph.code_l ℳ := ⟨G, root_l n m, wf_l hℳ hG hS _⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalDoubleTailGraph
