import BMSConstructibleBridge.SecondOrderLegacyFormulaTranslationDomain

/-! # 全内部公式翻译的输出单值性

实际递归图唯一，并不自动意味着每个输入只有一个输出。本模块另用实际
纯算术公式的内部强归纳证明输出单值；再与精确定义域组合，得到每个合法
内部码的唯一翻译。无 Type 选择函数，也不要求内部长度或码为外部标准数。
求值保持及 Def 双向等价尚未交付。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyFormulaTranslationUnique

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderEvaluationRule (numeral_l)
open SecondOrderTriangularConstructor (constructor_l)
open SecondOrderLegacyFormulaTranslation

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) := t.weakenBound sort_m.num

private theorem atomic_tag_l {t p l q : num_l ℳ} (h : atomic_l t p l q) :
    t = numeral_l ℳ 0 ∨ t = numeral_l ℳ 1 := by
  obtain ⟨_, _, _, _, _, _, _, hTag⟩ := h
  exact hTag.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

private theorem atomic_unique_l (hℳ : Theory.Models ℳ theory_m) {t p l q q' : num_l ℳ}
    (h : atomic_l t p l q) (h' : atomic_l t p l q') : q = q' := by
  obtain ⟨i, j, r, s, hPair, hr, hs, hTag⟩ := h
  obtain ⟨i', j', r', s', hPair', hr', hs', hTag'⟩ := h'
  obtain ⟨hI, hJ⟩ := SecondOrderPairingBounds.injective_l hℳ i' j' i j (hPair'.trans hPair.symm)
  subst i'
  subst j'
  have hR := SecondOrderLegacyAssignmentReversal.unique_l hℳ hr' hr
  have hS := SecondOrderLegacyAssignmentReversal.unique_l hℳ hs' hs
  subst r'
  subst s'
  rcases hTag with ⟨ht, hConstructor⟩ | ⟨ht, hConstructor⟩
  · have hConstructor' : constructor_l (numeral_l ℳ 1) r s q' := by
      simpa [ht, SecondOrderEvaluationEquations.numeral_eq_l hℳ] using hTag'
    exact SecondOrderTriangularConstructor.unique_l hℳ hConstructor hConstructor'
  · have hConstructor' : constructor_l (numeral_l ℳ 0) r s q' := by
      simpa [ht, SecondOrderEvaluationEquations.numeral_eq_l hℳ] using hTag'
    exact SecondOrderTriangularConstructor.unique_l hℳ hConstructor hConstructor'

private theorem negation_unique_l (hℳ : Theory.Models ℳ theory_m) {C : set_l ℳ} {p l q q' : num_l ℳ}
    (hChild : ∀ a b, query_l C p l a → query_l C p l b → a = b)
    (h : negation_l C p l q) (h' : negation_l C p l q') : q = q' := by
  obtain ⟨a, ha, hConstructor⟩ := h
  obtain ⟨b, hb, hConstructor'⟩ := h'
  have hEq := hChild a b ha hb
  subst b
  exact SecondOrderTriangularConstructor.unique_l hℳ hConstructor hConstructor'

private theorem conjunction_unique_l (hℳ : Theory.Models ℳ theory_m) {C : set_l ℳ}
    {t p l q q' : num_l ℳ}
    (ih : ∀ k, SecondOrderOrder.lt_l k (SecondOrderFormulaCode.node_l t p) →
      ∀ a b, query_l C k l a → query_l C k l b → a = b)
    (h : conjunction_l C p l q) (h' : conjunction_l C p l q') : q = q' := by
  obtain ⟨i, j, a, b, d, hPair, ha, hb, hd, hConstructor⟩ := h
  obtain ⟨i', j', a', b', d', hPair', ha', hb', hd', hConstructor'⟩ := h'
  obtain ⟨hI, hJ⟩ := SecondOrderPairingBounds.injective_l hℳ i' j' i j (hPair'.trans hPair.symm)
  subst i'
  subst j'
  have hChildren := SecondOrderFormulaCode.children_l hℳ t i j
  rw [hPair] at hChildren
  have hA := ih i hChildren.1 a' a ha' ha
  have hB := ih j hChildren.2 b' b hb' hb
  subst a'
  subst b'
  have hD := SecondOrderTriangularConstructor.unique_l hℳ hd' hd
  subst d'
  exact SecondOrderTriangularConstructor.unique_l hℳ hConstructor hConstructor'

private theorem existential_unique_l (hℳ : Theory.Models ℳ theory_m) {C : set_l ℳ} {p l q q' : num_l ℳ}
    (hChild : ∀ a b, query_l C p (succ_l l) a → query_l C p (succ_l l) b → a = b)
    (h : existential_l C p l q) (h' : existential_l C p l q') : q = q' := by
  obtain ⟨a, ha, hConstructor⟩ := h
  obtain ⟨b, hb, hConstructor'⟩ := h'
  have hEq := hChild a b ha hb
  subst b
  exact SecondOrderTriangularConstructor.unique_l hℳ hConstructor hConstructor'

theorem cases_unique_l (hℳ : Theory.Models ℳ theory_m) (C : set_l ℳ) (t p l q q' : num_l ℳ)
    (ih : ∀ k, SecondOrderOrder.lt_l k (SecondOrderFormulaCode.node_l t p) →
      ∀ m a b, query_l C k m a → query_l C k m b → a = b)
    (h : cases_l C t p l q) (h' : cases_l C t p l q') : q = q' := by
  classical
  have hp := (SecondOrderFormulaCode.bounds_l hℳ t p).2
  by_cases ht : t = numeral_l ℳ 0 ∨ t = numeral_l ℳ 1
  · have hNot (k : Nat) (hk : k ≠ 0 ∧ k ≠ 1) : t ≠ numeral_l ℳ k := by
      intro hEq
      rcases ht with ht | ht
      · exact hk.1 ((SecondOrderEvaluationEquations.numeral_eq_l hℳ k 0).mp (hEq.symm.trans ht))
      · exact hk.2 ((SecondOrderEvaluationEquations.numeral_eq_l hℳ k 1).mp (hEq.symm.trans ht))
    have hExtract {z : num_l ℳ} (hCases : cases_l C t p l z) : atomic_l t p l z := by
      rcases hCases with hAtom | ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩
      · exact hAtom
      · exact (hNot 2 (by decide) ht).elim
      · exact (hNot 3 (by decide) ht).elim
      · exact (hNot 4 (by decide) ht).elim
    exact atomic_unique_l hℳ (hExtract h) (hExtract h')
  · have hNoAtom (z : num_l ℳ) : ¬atomic_l t p l z := fun hAtom => ht (atomic_tag_l hAtom)
    simp only [cases_l, hNoAtom, false_or] at h h'
    rcases h with ⟨ht, hNeg⟩ | ⟨ht, hConj⟩ | ⟨ht, hExists⟩
    · have hNeg' : negation_l C p l q' := by
        simpa [ht, SecondOrderEvaluationEquations.numeral_eq_l hℳ] using h'
      exact negation_unique_l hℳ (ih p hp l) hNeg hNeg'
    · have hConj' : conjunction_l C p l q' := by
        simpa [ht, SecondOrderEvaluationEquations.numeral_eq_l hℳ] using h'
      exact conjunction_unique_l hℳ (t := t) (fun k hk => ih k hk l) hConj hConj'
    · have hExists' : existential_l C p l q' := by
        simpa [ht, SecondOrderEvaluationEquations.numeral_eq_l hℳ] using h'
      exact existential_unique_l hℳ (ih p hp (succ_l l)) hExists hExists'

def row_m {Γ Δ : SortContext signature_m} (C : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num <| .forallE .num <| .forallE .num <|
    .imp (query_m (up (up (up C))) (up (up (up n)))
      (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
      .imp (query_m (up (up (up C))) (up (up (up n))) (.bvar (.there (.there .here))) (.bvar .here))
        (.equal (.bvar (.there .here)) (.bvar .here))

theorem row_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (C : Term signature_m Γ Δ .set) (n : Term signature_m Γ Δ .num) :
    (row_m C n).satisfies η ↔ ∀ l q q', query_l (C.eval η) (n.eval η) l q →
      query_l (C.eval η) (n.eval η) l q' → q = q' := by
  simp only [row_m, Formula.satisfies, query_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {C : set_l ℳ} (hC : spec_l C) :
    ∀ n l q q', query_l C n l q → query_l C n l q' → q = q' := by
  let φ : Formula signature_m [] [.num, .set] := row_m (.fvar (.there .here)) (.fvar .here)
  apply SecondOrderListInduction.strong_induct_l hℳ φ (pure_language_m _ rfl) (Env.empty.pushFree C)
    (fun n => ∀ l q q', query_l C n l q → query_l C n l q' → q = q')
    (fun n => row_formula_l _ _ _) ?_
  intro n ih l q q' hQuery hQuery'
  rcases (equation_l hℳ hC n l q).mp hQuery with ⟨rfl, rfl⟩ | ⟨t, p, hNode, hCases⟩
  · rcases (equation_l hℳ hC _ l q').mp hQuery' with ⟨_, rfl⟩ | ⟨t, p, hNode, _⟩
    · rfl
    · exact (nonzero_l hℳ (value_l t p) hNode).elim
  · have hCases' := (SecondOrderLegacyFormulaTranslationDomain.target_node_l hℳ hC t p l q').mp
      (hNode.symm ▸ hQuery')
    apply cases_unique_l hℳ C t p l q q' _ hCases hCases'
    intro k hk
    rw [hNode] at hk
    exact ih k hk

theorem exists_unique_l (hℳ : Theory.Models ℳ theory_m) {V C : set_l ℳ}
    (hV : SecondOrderInternalFormulaSyntax.spec_l V) (hC : spec_l C) {n l : num_l ℳ}
    (hn : relation_l V n l) : ∃! q, query_l C n l q := by
  obtain ⟨q, hq⟩ := (SecondOrderLegacyFormulaTranslationDomain.domain_l hℳ hV hC n l).mp hn
  exact ⟨q, hq, fun q' hq' => unique_l hℳ hC n l q' q hq' hq⟩

def sentence_m : Sentence signature_m := .forallE .set <|
  .imp (spec_m (.bvar .here)) <| .forallE .num <| row_m (.bvar (.there .here)) (.bvar .here)

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, spec_formula_l, row_formula_l, Term.eval]
  exact fun _ hC => unique_l hℳ hC

#print axioms unique_l
#print axioms exists_unique_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyFormulaTranslationUnique
