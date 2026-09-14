import BMSConstructibleBridge.SecondOrderMinimum

/-!
# 内部实数编码的有限迭代历史

历史的长度取整个模型数域，图实数仅在该长度以内满足全函数规格。存在性使用
实际含集合量词的归纳公式，不假定非标准长度能作宿主有限递归。本模块不提供
数值 β 编码，不能当作原始递归证明码生成器的正确性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderHistory

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def succ {Γ Δ : SortContext signature_m} (s : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons s .nil)

/-- 自由槽位为转移图、历史图、初值、末索引；全部内部量词为数量词。 -/
def matrix_m : Formula signature_m [] [.set, .set, .num, .num] :=
  .conj
    (.forallE .num (.imp
      (PrimitiveFormulas.lt_m (.bvar .here) (succ (.fvar (.there (.there (.there .here))))))
      (.existsE .num (.conj
        (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
        (.forallE .num (.imp
          (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar (.there (.there .here))) (.bvar .here))
          (.equal (.bvar .here) (.bvar (.there .here)))))))))
    (.conj (GraphSyntax.edge_m (.fvar (.there .here)) zero (.fvar (.there (.there .here))))
      (.forallE .num (.forallE .num (.forallE .num (.imp
        (PrimitiveFormulas.lt_m (.bvar (.there (.there .here)))
          (.fvar (.there (.there (.there .here)))))
        (.imp (GraphSyntax.edge_m (.fvar (.there .here))
          (.bvar (.there (.there .here))) (.bvar (.there .here)))
          (.imp (GraphSyntax.edge_m (.fvar (.there .here))
            (succ (.bvar (.there (.there .here)))) (.bvar .here))
            (GraphSyntax.edge_m (.fvar .here) (.bvar (.there .here)) (.bvar .here)))))))))

def spec_l (F H : set_l ℳ) (a n : num_l ℳ) : Prop :=
  (∀ i, SecondOrderOrder.lt_l i (succ_l n) → ∃! b, relation_l H i b) ∧
    relation_l H (zero_l ℳ) a ∧
      ∀ i b c, SecondOrderOrder.lt_l i n → relation_l H i b →
        relation_l H (succ_l i) c → relation_l F b c

def formula_m {Γ Δ : SortContext signature_m} (F H : Term signature_m Γ Δ .set)
    (a n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  GraphTranslation.atom_m matrix_m F H a n

theorem pure_m {Γ Δ : SortContext signature_m} (F H : Term signature_m Γ Δ .set)
    (a n : Term signature_m Γ Δ .num) (hF : pure_term_m F = true)
    (hH : pure_term_m H = true) (ha : pure_term_m a = true) (hn : pure_term_m n = true) :
    language_m (formula_m F H a n) = true :=
  GraphTranslation.atom_pure_m matrix_m F H a n (pure_language_m _ rfl) hF hH ha hn

theorem matrix_l (η : Env ℳ [] [.set, .set, .num, .num]) :
    Formula.satisfies η matrix_m ↔ spec_l (η.freeVal .here) (η.freeVal (.there .here))
      (η.freeVal (.there (.there .here))) (η.freeVal (.there (.there (.there .here)))) := by
  simp only [matrix_m, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderOrder.formula_l]
  rfl

theorem formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (F H : Term signature_m Γ Δ .set) (a n : Term signature_m Γ Δ .num) :
    Formula.satisfies η (formula_m F H a n) ↔ spec_l (F.eval η) (H.eval η) (a.eval η) (n.eval η) := by
  rw [formula_m, GraphTranslation.atom_m, Formula.satisfies_substitute, matrix_l]
  rfl

theorem base_l (hℳ : Theory.Models ℳ theory_m) (F : set_l ℳ) (a : num_l ℳ) :
    ∃ H, spec_l F H a (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  let φ : Formula signature_m [] [.num, .num, .num] :=
    .equal (.fvar (.there .here)) (.fvar (.there (.there .here)))
  obtain ⟨H, hH⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((Env.empty (M := ℳ)).pushFree a)
  have h : ∀ i b, relation_l H i b ↔ b = a := hH
  refine ⟨H, fun i _ => ⟨a, (h i a).mpr rfl, fun b hb => (h i b).mp hb⟩,
    (h (zero_l ℳ) a).mpr rfl, ?_⟩
  intro i b c hi _ _
  exact False.elim ((not_lt_of_ge (zero_le_l hℳ i)) hi)

/-- 截取旧历史至末索引，并在其后添加一个数值；新图仍为内部实数。 -/
theorem extend_l (hℳ : Theory.Models ℳ theory_m) (H : set_l ℳ) (n c : num_l ℳ) :
    ∃ K : set_l ℳ, ∀ i b, relation_l K i b ↔
      (SecondOrderOrder.lt_l i (succ_l n) ∧ relation_l H i b) ∨ (i = succ_l n ∧ b = c) := by
  let φ : Formula signature_m [] [.num, .num, .set, .num, .num] :=
    .disj (.conj
      (PrimitiveFormulas.lt_m (.fvar .here) (succ (.fvar (.there (.there (.there .here))))))
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))))
      (.conj (.equal (.fvar .here) (succ (.fvar (.there (.there (.there .here))))))
        (.equal (.fvar (.there .here)) (.fvar (.there (.there (.there (.there .here)))))))
  obtain ⟨K, hK⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((((Env.empty (M := ℳ)).pushFree c).pushFree n).pushFree H)
  refine ⟨K, fun i b => (hK i b).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderOrder.formula_l]
  rfl

theorem step_l (hℳ : Theory.Models ℳ theory_m) (F H : set_l ℳ) (a n : num_l ℳ)
    (hF : ∀ b, ∃ c, relation_l F b c) (hH : spec_l F H a n) :
    ∃ K, spec_l F K a (succ_l n) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have h₀ (i : num_l ℳ) : i < succ_l i := (SecondOrderNaturalGraph.lt_succ_l hℳ i i).mpr le_rfl
  obtain ⟨b, hb, _⟩ := hH.1 n (h₀ n)
  obtain ⟨c, hc⟩ := hF b
  obtain ⟨K, hK⟩ := extend_l hℳ H n c
  have h₁ (i d : num_l ℳ) (hi : i < succ_l n) : relation_l K i d ↔ relation_l H i d := by
    rw [hK]
    change (i < succ_l n ∧ relation_l H i d) ∨ (i = succ_l n ∧ d = c) ↔ _
    simp only [hi, true_and, ne_of_lt hi, false_and, or_false]
  have h₂ (d : num_l ℳ) : relation_l K (succ_l n) d ↔ d = c := by
    rw [hK]
    change (succ_l n < succ_l n ∧ relation_l H (succ_l n) d) ∨ (succ_l n = succ_l n ∧ d = c) ↔ _
    simp only [lt_irrefl, false_and, true_and, false_or]
  refine ⟨K, ?_, ?_, ?_⟩
  · intro i hi
    rcases eq_or_lt_of_le ((SecondOrderNaturalGraph.lt_succ_l hℳ i (succ_l n)).mp hi) with rfl | hi
    · exact ⟨c, (h₂ c).mpr rfl, fun d hd => (h₂ d).mp hd⟩
    · simpa only [h₁ i _ hi] using hH.1 i hi
  · exact (h₁ (zero_l ℳ) a ((SecondOrderNaturalGraph.lt_succ_l hℳ _ n).mpr
      (zero_le_l hℳ n))).mpr hH.2.1
  · intro i d e hi hd he
    rcases eq_or_lt_of_le ((SecondOrderNaturalGraph.lt_succ_l hℳ i n).mp hi) with h | hi
    · subst i
      have h₃ := (hH.1 n (h₀ n)).unique ((h₁ n d (h₀ n)).mp hd) hb
      simpa only [h₃, (h₂ e).mp he] using hc
    · have h₃ : succ_l i < succ_l n := by
        rw [succ_eq_l hℳ i, succ_eq_l hℳ n]
        exact add_lt_add_left hi 1
      exact hH.2.2 i d e hi ((h₁ i d (lt_trans hi (h₀ n))).mp hd) ((h₁ _ e h₃).mp he)

/-- 存在性归纳的正文包含历史实数量词，未把历史族作为额外参数假定。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) (F : set_l ℳ) (a : num_l ℳ)
    (hF : ∀ b, ∃ c, relation_l F b c) (n : num_l ℳ) : ∃ H, spec_l F H a n := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .existsE .set (formula_m (.fvar (.there (.there .here))) (.bvar .here)
      (.fvar (.there .here)) (.fvar .here))
  have hφ : language_m φ = true := pure_m _ _ _ _ rfl rfl rfl rfl
  apply induct_l hℳ φ hφ (((Env.empty (M := ℳ)).pushFree F).pushFree a)
    (fun n => ∃ H, spec_l F H a n) ?_ (base_l hℳ F a) ?_ n
  · intro i
    simp only [φ, Formula.satisfies, formula_l]
    rfl
  · rintro i ⟨H, hH⟩
    exact step_l hℳ F H a i hF hH

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderHistory
