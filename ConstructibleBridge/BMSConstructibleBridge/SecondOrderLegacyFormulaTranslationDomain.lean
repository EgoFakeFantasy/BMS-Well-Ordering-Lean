import BMSConstructibleBridge.SecondOrderLegacyFormulaTranslation
import BMSConstructibleBridge.SecondOrderListInduction

/-! # 内部翻译图的精确定义域

对实际原算术公式作内部强归纳：原五标签码在长度 l 合法，当且仅当递归
翻译图在该输入有目标码。量词分支使用内部后继长度；原子分支由槽反转的
总性与界证书完成。这里覆盖全部内部码，而非仅外部 Formula 的编译像。
尚未断言输出单值、目标合法性或 Sat 求值保持，故仍不是 Def 等价证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyFormulaTranslationDomain

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderEvaluationRule (numeral_l)
open SecondOrderLegacyFormulaTranslation (query_l query_m cases_l point_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) := t.weakenBound sort_m.num

theorem source_node_l (hℳ : Theory.Models ℳ theory_m) {V : set_l ℳ}
    (hV : SecondOrderInternalFormulaSyntax.spec_l V) (t p l : num_l ℳ) :
    relation_l V (SecondOrderFormulaCode.node_l t p) l ↔ SecondOrderInternalFormulaSyntax.cases_l V l t p := by
  rw [hV]
  constructor
  · rintro (hZero | ⟨t', p', hNode, hCases⟩)
    · exact (nonzero_l hℳ (value_l t p) hZero).elim
    · obtain ⟨rfl, rfl⟩ := SecondOrderFormulaCode.injective_l hℳ t' p' t p hNode
      exact hCases
  · intro hCases
    exact Or.inr ⟨t, p, rfl, hCases⟩

theorem target_node_l (hℳ : Theory.Models ℳ theory_m) {C : set_l ℳ}
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) (t p l q : num_l ℳ) :
    query_l C (SecondOrderFormulaCode.node_l t p) l q ↔ cases_l C t p l q := by
  rw [SecondOrderLegacyFormulaTranslation.equation_l hℳ hC]
  constructor
  · rintro (⟨hZero, _⟩ | ⟨t', p', hNode, hCases⟩)
    · exact (nonzero_l hℳ (value_l t p) hZero).elim
    · obtain ⟨rfl, rfl⟩ := SecondOrderFormulaCode.injective_l hℳ t' p' t p hNode
      exact hCases
  · intro hCases
    exact Or.inr ⟨t, p, rfl, hCases⟩

theorem cases_domain_l (hℳ : Theory.Models ℳ theory_m) (V C : set_l ℳ) (t p l : num_l ℳ)
    (ih : ∀ k, SecondOrderOrder.lt_l k (SecondOrderFormulaCode.node_l t p) →
      ∀ m, relation_l V k m ↔ ∃ q, query_l C k m q) :
    (∃ q, cases_l C t p l q) ↔ SecondOrderInternalFormulaSyntax.cases_l V l t p := by
  have hp := (SecondOrderFormulaCode.bounds_l hℳ t p).2
  constructor
  · rintro ⟨q, hCases⟩
    rcases hCases with hAtom | ⟨ht, hNeg⟩ | ⟨ht, hConj⟩ | ⟨ht, hExists⟩
    · obtain ⟨i, j, r, s, hPair, hi, hj, hTag⟩ := hAtom
      exact Or.inl ⟨hTag.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1),
        i, j, hPair, (SecondOrderLegacyAssignmentReversal.bounds_l hℳ hi).1,
        (SecondOrderLegacyAssignmentReversal.bounds_l hℳ hj).1⟩
    · obtain ⟨a, ha, _⟩ := hNeg
      exact Or.inr (Or.inl ⟨ht, (ih p hp l).mpr ⟨a, ha⟩⟩)
    · obtain ⟨i, j, a, b, _, hPair, ha, hb, _, _⟩ := hConj
      have hChildren := SecondOrderFormulaCode.children_l hℳ t i j
      rw [hPair] at hChildren
      exact Or.inr (Or.inr (Or.inl ⟨ht, i, j, hPair,
        (ih i hChildren.1 l).mpr ⟨a, ha⟩, (ih j hChildren.2 l).mpr ⟨b, hb⟩⟩))
    · obtain ⟨a, ha, _⟩ := hExists
      exact Or.inr (Or.inr (Or.inr ⟨ht, (ih p hp (succ_l l)).mpr ⟨a, ha⟩⟩))
  · intro hCases
    rcases hCases with ⟨hTag, hAtom⟩ | ⟨ht, hNeg⟩ | ⟨ht, hConj⟩ | ⟨ht, hExists⟩
    · obtain ⟨i, j, hPair, hi, hj⟩ := hAtom
      obtain ⟨r, hr, _⟩ := SecondOrderLegacyAssignmentReversal.index_exists_l hℳ hi
      obtain ⟨s, hs, _⟩ := SecondOrderLegacyAssignmentReversal.index_exists_l hℳ hj
      rcases hTag with ht | ht
      · obtain ⟨q, hq⟩ := SecondOrderTriangularConstructor.exists_l hℳ (numeral_l ℳ 1) r s
        exact ⟨q, Or.inl ⟨i, j, r, s, hPair, hr, hs, Or.inl ⟨ht, hq⟩⟩⟩
      · obtain ⟨q, hq⟩ := SecondOrderTriangularConstructor.exists_l hℳ (numeral_l ℳ 0) r s
        exact ⟨q, Or.inl ⟨i, j, r, s, hPair, hr, hs, Or.inr ⟨ht, hq⟩⟩⟩
    · obtain ⟨a, ha⟩ := (ih p hp l).mp hNeg
      obtain ⟨q, hq⟩ := SecondOrderTriangularConstructor.exists_l hℳ (numeral_l ℳ 2) a a
      exact ⟨q, Or.inr (Or.inl ⟨ht, a, ha, hq⟩)⟩
    · obtain ⟨i, j, hPair, hi, hj⟩ := hConj
      have hChildren := SecondOrderFormulaCode.children_l hℳ t i j
      rw [hPair] at hChildren
      obtain ⟨a, ha⟩ := (ih i hChildren.1 l).mp hi
      obtain ⟨b, hb⟩ := (ih j hChildren.2 l).mp hj
      obtain ⟨d, hd⟩ := SecondOrderTriangularConstructor.exists_l hℳ (numeral_l ℳ 2) a b
      obtain ⟨q, hq⟩ := SecondOrderTriangularConstructor.exists_l hℳ (numeral_l ℳ 2) d d
      exact ⟨q, Or.inr (Or.inr (Or.inl ⟨ht, i, j, a, b, d, hPair, ha, hb, hd, hq⟩))⟩
    · obtain ⟨a, ha⟩ := (ih p hp (succ_l l)).mp hExists
      obtain ⟨q, hq⟩ := SecondOrderTriangularConstructor.exists_l hℳ (numeral_l ℳ 3) l a
      exact ⟨q, Or.inr (Or.inr (Or.inr ⟨ht, a, ha, hq⟩))⟩

def row_m {Γ Δ : SortContext signature_m} (V C : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num <| .iff (GraphSyntax.edge_m (up V) (up n) (.bvar .here)) <|
    .existsE .num <| query_m (up (up C)) (up (up n)) (.bvar (.there .here)) (.bvar .here)

theorem row_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (V C : Term signature_m Γ Δ .set) (n : Term signature_m Γ Δ .num) :
    (row_m V C n).satisfies η ↔ ∀ l, relation_l (V.eval η) (n.eval η) l ↔
      ∃ q, query_l (C.eval η) (n.eval η) l q := by
  simp only [row_m, Formula.satisfies, SecondOrderPairing.edge_l,
    SecondOrderLegacyFormulaTranslation.query_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem domain_l (hℳ : Theory.Models ℳ theory_m) {V C : set_l ℳ}
    (hV : SecondOrderInternalFormulaSyntax.spec_l V) (hC : SecondOrderLegacyFormulaTranslation.spec_l C) :
    ∀ n l, relation_l V n l ↔ ∃ q, query_l C n l q := by
  let φ : Formula signature_m [] [.num, .set, .set] :=
    row_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  apply SecondOrderListInduction.strong_induct_l hℳ φ (pure_language_m _ rfl)
    ((Env.empty.pushFree C).pushFree V)
    (fun n => ∀ l, relation_l V n l ↔ ∃ q, query_l C n l q)
    (fun n => row_formula_l _ _ _ _) ?_
  intro n ih l
  by_cases hn : n = zero_l ℳ
  · subst n
    have hValid := (hV _ l).mpr (Or.inl rfl)
    have hQuery := (SecondOrderLegacyFormulaTranslation.equation_l hℳ hC _ l (zero_l ℳ)).mpr
      (Or.inl ⟨rfl, rfl⟩)
    exact ⟨fun _ => ⟨_, hQuery⟩, fun _ => hValid⟩
  · obtain ⟨t, p, rfl⟩ := SecondOrderFormulaCode.decode_l hℳ n hn
    exact (source_node_l hℳ hV t p l).trans ((cases_domain_l hℳ V C t p l ih).symm.trans
      (exists_congr (fun q => (target_node_l hℳ hC t p l q).symm)))

def sentence_m : Sentence signature_m := .forallE .set <|
  .imp (SecondOrderMemberDefArithmetic.syntax_m (.bvar .here)) <|
    .existsE .set <| .conj (SecondOrderLegacyFormulaTranslation.spec_m (.bvar .here)) <|
      .forallE .num <| row_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies,
    SecondOrderMemberDefArithmetic.syntax_formula_l, SecondOrderLegacyFormulaTranslation.spec_formula_l,
    row_formula_l, Term.eval]
  intro V hV
  obtain ⟨C, hC, _⟩ := SecondOrderLegacyFormulaTranslation.exists_l hℳ
  exact ⟨C, hC, domain_l hℳ hV hC⟩

#print axioms domain_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyFormulaTranslationDomain
