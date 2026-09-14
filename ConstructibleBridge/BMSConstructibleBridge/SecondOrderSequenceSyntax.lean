import BMSConstructibleBridge.SecondOrderSequenceCode

/-!
# 数值函数图的纯读取公式

唯一的实数参数是已存在的内部幂图；码、索引、输出均为模型数。读取公式使用
原配对模板和纯位公式，不添加函数或关系符号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSequenceSyntax

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def template_m : Formula signature_m [] [.set, .num, .num, .num] :=
  .existsE .num (.existsE .num (.conj
    (PrimitiveFormulas.pair_m (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.bvar (.there .here)))
    (.conj (GraphSyntax.edge_m (.fvar .here) (.bvar (.there .here)) (.bvar .here))
      (SecondOrderDigit.formula_m (.fvar (.there .here)) (.bvar .here)))))

private def bind {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c i b : Term signature_m Γ Δ .num) :
    Substitution signature_m [] [.set, .num, .num, .num] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => E
    | .there .here => c
    | .there (.there .here) => i
    | .there (.there (.there .here)) => b)

def formula_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c i b : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  template_m.substitute (bind E c i b)

theorem pure_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c i b : Term signature_m Γ Δ .num) (hE : pure_term_m E = true)
    (hc : pure_term_m c = true) (hi : pure_term_m i = true) (hb : pure_term_m b = true) :
    language_m (formula_m E c i b) = true := by
  refine (SecondOrderSubstitution.form_subst_m template_m _ _ ?_ ?_).trans (pure_language_m _ rfl)
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here => exact hE
    | .there .here => exact hc
    | .there (.there .here) => exact hi
    | .there (.there (.there .here)) => exact hb

theorem template_l (η : Env ℳ [] [.set, .num, .num, .num])
    (hE : SecondOrderBinaryPowers.spec_l (η.freeVal .here)) :
    Formula.satisfies η template_m ↔
      SecondOrderDigit.holds_l (η.freeVal (.there .here))
        (SecondOrderPowers.value_l hE (value_l (η.freeVal (.there (.there .here)))
          (η.freeVal (.there (.there (.there .here)))))) := by
  simp only [template_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l, SecondOrderDigit.formula_l]
  change (∃ z p, value_l (η.freeVal (.there (.there .here)))
    (η.freeVal (.there (.there (.there .here)))) = z ∧
      relation_l (η.freeVal .here) z p ∧ SecondOrderDigit.holds_l (η.freeVal (.there .here)) p) ↔ _
  constructor
  · rintro ⟨z, p, rfl, hp, h⟩
    obtain rfl := (SecondOrderPowers.eq_l hE _ p).mp hp
    exact h
  · intro h
    exact ⟨_, _, rfl, SecondOrderPowers.edge_l hE _, h⟩

/-- 无幂图正确性前提的原始读取规格，便于在复合公式中逐层重写。 -/
def read_l (E : set_l ℳ) (c i b : num_l ℳ) : Prop :=
  ∃ z p, value_l i b = z ∧ relation_l E z p ∧ SecondOrderDigit.holds_l c p

theorem read_eq_l {E : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E) (c i b : num_l ℳ) :
    read_l E c i b ↔ SecondOrderDigit.holds_l c (SecondOrderPowers.value_l hE (value_l i b)) := by
  constructor
  · rintro ⟨z, p, rfl, hp, h⟩
    obtain rfl := (SecondOrderPowers.eq_l hE _ p).mp hp
    exact h
  · intro h
    exact ⟨_, _, rfl, SecondOrderPowers.edge_l hE _, h⟩

theorem raw_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (c i b : Term signature_m Γ Δ .num) :
    Formula.satisfies η (formula_m E c i b) ↔ read_l (E.eval η) (c.eval η) (i.eval η) (b.eval η) := by
  simp only [formula_m, Formula.satisfies_substitute, template_m, Formula.satisfies,
    SecondOrderPairing.formula_l, SecondOrderPairing.edge_l, SecondOrderDigit.formula_l]
  rfl

theorem formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (c i b : Term signature_m Γ Δ .num)
    (hE : SecondOrderBinaryPowers.spec_l (E.eval η)) :
    Formula.satisfies η (formula_m E c i b) ↔
      SecondOrderDigit.holds_l (c.eval η) (SecondOrderPowers.value_l hE (value_l (i.eval η) (b.eval η))) := by
  rw [formula_m, Formula.satisfies_substitute, template_l _ hE]
  rfl

/-- 任意数码的读取关系仍是模型内部实数，并非新增外部函数。 -/
theorem decode_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) (c : num_l ℳ) :
    ∃ H : set_l ℳ, ∀ i b, relation_l H i b ↔
      SecondOrderDigit.holds_l c (SecondOrderPowers.value_l hE (value_l i b)) := by
  let φ : Formula signature_m [] [.num, .num, .set, .num] :=
    formula_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar .here) (.fvar (.there .here))
  obtain ⟨H, hH⟩ := SecondOrderRelations.comprehension_l hℳ φ
    (pure_m _ _ _ _ rfl rfl rfl rfl) (((Env.empty (M := ℳ)).pushFree c).pushFree E)
  refine ⟨H, fun i b => (hH i b).trans ?_⟩
  exact formula_l _ _ _ _ _ hE

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSequenceSyntax
