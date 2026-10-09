import BMSConstructibleBridge.SecondOrderLegacyFormulaTranslationUnique
import BMSConstructibleBridge.SecondOrderFunctions

/-! # 原公式翻译的总化数字函数图

输入是原配对值 pair(n,l)，合法原公式读取旧翻译图，非法输入固定为零。
理解公式及其原 Z₂ 推导实例均显式给出；函数性只用 Prop 分情况，不抽取
Type 层选择函数。所得 E 是内部实数图，不宣称其无限图属于 Class。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyTranslationFunction

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 合法性守卫不可省略：非法输入的零不是旧翻译输出。 -/
def point_l (V C : set_l ℳ) (n l q : num_l ℳ) : Prop :=
  (relation_l V n l ∧ SecondOrderLegacyFormulaTranslation.query_l C n l q) ∨
    (¬relation_l V n l ∧ q = zero_l ℳ)

def point_m {Γ Δ : SortContext signature_m} (V C : Term signature_m Γ Δ .set)
    (n l q : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  let r := GraphSyntax.edge_m V n l
  let z : Term signature_m Γ Δ .num := Term.app (σ := signature_m) .zero .nil
  .disj (.conj r (SecondOrderLegacyFormulaTranslation.query_m C n l q))
    (.conj (.neg r) (.equal q z))

theorem point_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (V C : Term signature_m Γ Δ .set) (n l q : Term signature_m Γ Δ .num) :
    (point_m V C n l q).satisfies η ↔
      point_l (V.eval η) (C.eval η) (n.eval η) (l.eval η) (q.eval η) := by
  simp only [point_m, point_l, Formula.satisfies, SecondOrderPairing.edge_l,
    SecondOrderLegacyFormulaTranslation.query_formula_l]
  rfl

/-- 删除非法补零边以后精确恢复原部分翻译，包括输出恰为零的合法输入。 -/
theorem guarded_l (hℳ : Theory.Models ℳ theory_m) {V C : set_l ℳ}
    (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) (n l q : num_l ℳ) :
    (relation_l V n l ∧ point_l V C n l q) ↔
      SecondOrderLegacyFormulaTranslation.query_l C n l q := by
  constructor
  · rintro ⟨hValid, hPoint⟩
    exact hPoint.elim (fun h => h.2) (fun h => (h.1 hValid).elim)
  · intro hQuery
    have hValid := (SecondOrderLegacyFormulaTranslationDomain.domain_l hℳ hV hC n l).mpr ⟨q, hQuery⟩
    exact ⟨hValid, Or.inl ⟨hValid, hQuery⟩⟩

/-- 自由槽位依次为配对输入、输出、原良构图、旧翻译图。 -/
def formula_m : Formula signature_m [] [.num, .num, .set, .set] :=
  .existsE .num <| .existsE .num <|
    let n : Term signature_m [.num, .num] [.num, .num, .set, .set] .num :=
      .bvar (.there .here)
    let l : Term signature_m [.num, .num] [.num, .num, .set, .set] .num := .bvar .here
    .conj (PrimitiveFormulas.pair_m n l (.fvar .here))
      (point_m (.fvar (.there (.there .here)))
        (.fvar (.there (.there (.there .here)))) n l (.fvar (.there .here)))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

def spec_l (V C E : set_l ℳ) : Prop :=
  ∀ i q, relation_l E i q ↔ ∃ n l, value_l n l = i ∧ point_l V C n l q

theorem formula_l (V C : set_l ℳ) (i q : num_l ℳ) :
    formula_m.satisfies (((((Env.empty).pushFree C).pushFree V).pushFree q).pushFree i) ↔
      ∃ n l, value_l n l = i ∧ point_l V C n l q := by
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.formula_l, point_formula_l]
  rfl

/-- 配对单射性把任意坐标读回同一总化逐点规格。 -/
theorem read_l (hℳ : Theory.Models ℳ theory_m) {V C E : set_l ℳ}
    (hE : spec_l V C E) (n l q : num_l ℳ) :
    relation_l E (value_l n l) q ↔ point_l V C n l q := by
  constructor
  · intro h
    obtain ⟨n', l', hPair, hPoint⟩ := (hE _ q).mp h
    obtain ⟨rfl, rfl⟩ := SecondOrderPairingBounds.injective_l hℳ n' l' n l hPair
    exact hPoint
  · intro h
    exact (hE _ q).mpr ⟨n, l, rfl, h⟩

/-- 覆盖全部内部数；反配对总性与旧合法翻译唯一性均在原模型中成立。 -/
theorem function_l (hℳ : Theory.Models ℳ theory_m) {V C E : set_l ℳ}
    (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) (hE : spec_l V C E) :
    SecondOrderFunctions.function_l E := by
  classical
  intro i
  obtain ⟨n, l, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ i
  by_cases hn : relation_l V n l
  · obtain ⟨q, hq, hUnique⟩ :=
      SecondOrderLegacyFormulaTranslationUnique.exists_unique_l hℳ hV hC hn
    refine ⟨q, (read_l hℳ hE n l q).mpr (Or.inl ⟨hn, hq⟩), ?_⟩
    intro q' hq'
    rcases (read_l hℳ hE n l q').mp hq' with h | h
    · exact hUnique q' h.2
    · exact (h.1 hn).elim
  · refine ⟨zero_l ℳ, (read_l hℳ hE n l _).mpr (Or.inr ⟨hn, rfl⟩), ?_⟩
    intro q' hq'
    rcases (read_l hℳ hE n l q').mp hq' with h | h
    · exact (hn h.1).elim
    · exact h.2

/-- 参数无需满足递归规格即可理解逐点图；总函数性另需原合法图规格。 -/
theorem exists_spec_l (hℳ : Theory.Models ℳ theory_m) (V C : set_l ℳ) :
    ∃ E, spec_l V C E := by
  obtain ⟨E, hE⟩ := SecondOrderRelations.comprehension_l hℳ formula_m pure_m
    (((Env.empty).pushFree C).pushFree V)
  exact ⟨E, fun i q => (hE i q).trans (formula_l V C i q)⟩

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (V C : set_l ℳ)
    (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) :
    ∃ E, SecondOrderFunctions.function_l E ∧ spec_l V C E := by
  obtain ⟨E, hE⟩ := exists_spec_l hℳ V C
  exact ⟨E, function_l hℳ hV hC hE, hE⟩

/-- 上述实际配对输入理解公式的原 Z₂ 推导；不是新增图公理。 -/
theorem derives_m : Derives theory_m []
    (SecondOrderArithmetic.comprehension_m (SecondOrderRelations.formula_m formula_m)) :=
  SecondOrderRelations.comprehension_m formula_m pure_m

#print axioms read_l
#print axioms guarded_l
#print axioms function_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyTranslationFunction
