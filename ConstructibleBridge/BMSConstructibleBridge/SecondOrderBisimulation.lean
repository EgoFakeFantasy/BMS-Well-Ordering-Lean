import BMSConstructibleBridge.SecondOrderRelationOps

/-!
# 任意模型中的内部双模拟

见证必须是模型集合域中的一个实数。等价律使用内部对角、反向和复合构造，
不借用任意外部关系见证；实际等词模板也保留全部原参数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderBisimulation

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

def witness_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} (R S H : set_l ℳ) : Prop :=
  ∀ ⦃a b⦄, relation_l H a b →
    (∀ ⦃c⦄, relation_l R c a → ∃ d, relation_l S d b ∧ relation_l H c d) ∧
    (∀ ⦃d⦄, relation_l S d b → ∃ c, relation_l R c a ∧ relation_l H c d)

def eq_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (R S : set_l ℳ) (a b : num_l ℳ) : Prop :=
  ∃ H : set_l ℳ, witness_l R S H ∧ relation_l H a b

theorem witness_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (η : Env ℳ [] [.set, .set, .set]) :
    Formula.satisfies η GraphSyntax.witness_m ↔
      witness_l (η.freeVal .here) (η.freeVal (.there .here))
        (η.freeVal (.there (.there .here))) := by
  simp only [GraphSyntax.witness_m, Formula.satisfies, SecondOrderPairing.edge_l]
  rfl

theorem eq_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (η : Env ℳ [] [.set, .set, .num, .num]) :
    Formula.satisfies η GraphSyntax.eq_m ↔
      eq_l (η.freeVal .here) (η.freeVal (.there .here))
        (η.freeVal (.there (.there .here))) (η.freeVal (.there (.there (.there .here)))) := by
  rw [GraphSyntax.eq_m, Formula.satisfies]
  apply exists_congr
  intro H
  rw [GraphSyntax.matrix_m, Formula.satisfies, Formula.satisfies_substitute,
    witness_formula_l, SecondOrderPairing.edge_l]
  rfl

theorem refl_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) (a : num_l ℳ) : eq_l R R a a := by
  obtain ⟨H, hH⟩ := SecondOrderRelationOps.diagonal_l hℳ
  refine ⟨H, ?_, (hH a a).mpr rfl⟩
  intro b c h
  obtain rfl := (hH b c).mp h
  exact ⟨fun d h => ⟨d, h, (hH d d).mpr rfl⟩,
    fun d h => ⟨d, h, (hH d d).mpr rfl⟩⟩

/-- 原成员模板保留右图直接子节点与内部双模拟见证，不扩大实数见证域。 -/
theorem mem_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (η : Env ℳ [] [.set, .set, .num, .num]) :
    Formula.satisfies η GraphSyntax.mem_m ↔
      ∃ c, relation_l (η.freeVal (.there .here)) c (η.freeVal (.there (.there (.there .here)))) ∧
        eq_l (η.freeVal .here) (η.freeVal (.there .here)) (η.freeVal (.there (.there .here))) c := by
  simp only [GraphSyntax.mem_m, GraphSyntax.mem_matrix_m, Formula.satisfies,
    Formula.satisfies_substitute, witness_formula_l, SecondOrderPairing.edge_l]
  change (∃ H : set_l ℳ, ∃ c : num_l ℳ,
    witness_l (η.freeVal .here) (η.freeVal (.there .here)) H ∧
      relation_l (η.freeVal (.there .here)) c (η.freeVal (.there (.there (.there .here)))) ∧
      relation_l H (η.freeVal (.there (.there .here))) c) ↔ _
  constructor
  · rintro ⟨H, c, h, h₁, h₂⟩
    exact ⟨c, h₁, H, h, h₂⟩
  · rintro ⟨c, h, H, h₁, h₂⟩
    exact ⟨H, c, h₁, h, h₂⟩

theorem symm_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (R S : set_l ℳ) (a b : num_l ℳ)
    (h : eq_l R S a b) : eq_l S R b a := by
  obtain ⟨H, hH, h⟩ := h
  obtain ⟨K, hK⟩ := SecondOrderRelationOps.converse_l hℳ H
  refine ⟨K, ?_, (hK b a).mpr h⟩
  intro c d h
  have h := hH ((hK c d).mp h)
  constructor
  · intro e h₁
    obtain ⟨f, h₂, h₃⟩ := h.2 h₁
    exact ⟨f, h₂, (hK e f).mpr h₃⟩
  · intro e h₁
    obtain ⟨f, h₂, h₃⟩ := h.1 h₁
    exact ⟨f, h₂, (hK f e).mpr h₃⟩

theorem trans_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (R S T : set_l ℳ) (a b c : num_l ℳ)
    (h : eq_l R S a b) (h₁ : eq_l S T b c) : eq_l R T a c := by
  obtain ⟨H, hH, h⟩ := h
  obtain ⟨K, hK, h₁⟩ := h₁
  obtain ⟨L, hL⟩ := SecondOrderRelationOps.comp_l hℳ H K
  refine ⟨L, ?_, (hL a c).mpr ⟨b, h, h₁⟩⟩
  intro d e h
  obtain ⟨f, h₂, h₃⟩ := (hL d e).mp h
  constructor
  · intro g h₄
    obtain ⟨i, h₅, h₆⟩ := (hH h₂).1 h₄
    obtain ⟨j, h₇, h₈⟩ := (hK h₃).1 h₅
    exact ⟨j, h₇, (hL g j).mpr ⟨i, h₆, h₈⟩⟩
  · intro g h₄
    obtain ⟨i, h₅, h₆⟩ := (hK h₃).2 h₄
    obtain ⟨j, h₇, h₈⟩ := (hH h₂).2 h₅
    exact ⟨j, h₇, (hL j g).mpr ⟨i, h₈, h₆⟩⟩

/-- 最大内部双模拟的每个匹配都仍带有一个内部见证。 -/
theorem match_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (R S : set_l ℳ) (a b : num_l ℳ) (h : eq_l R S a b) :
    (∀ c, relation_l R c a → ∃ d, relation_l S d b ∧ eq_l R S c d) ∧
    (∀ d, relation_l S d b → ∃ c, relation_l R c a ∧ eq_l R S c d) := by
  obtain ⟨H, hH, h⟩ := h
  constructor
  · intro c h₁
    obtain ⟨d, h₂, h₃⟩ := (hH h).1 h₁
    exact ⟨d, h₂, H, hH, h₃⟩
  · intro d h₁
    obtain ⟨c, h₂, h₃⟩ := (hH h).2 h₁
    exact ⟨c, h₂, H, hH, h₃⟩

private def insert : VariableSubstitution signature_m [.set, .set, .num, .num]
    [] [.num, .num, .set, .set]
  | _, .here => .fvar (.there (.there .here))
  | _, .there .here => .fvar (.there (.there (.there .here)))
  | _, .there (.there .here) => .fvar .here
  | _, .there (.there (.there .here)) => .fvar (.there .here)

private def formula : Formula signature_m [] [.num, .num, .set, .set] :=
  GraphSyntax.eq_m.substitute (.map VariableSubstitution.boundId insert)

private theorem pure : language_m formula = true := by
  refine (SecondOrderSubstitution.form_subst_m GraphSyntax.eq_m
    VariableSubstitution.boundId insert ?_ ?_).trans
    (pure_language_m GraphSyntax.matrix_m GraphSyntax.matrix_pure_m)
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here | .there .here | .there (.there .here) | .there (.there (.there .here)) => rfl

/-- 完整二阶理解把存在内部见证的最大关系本身收集为一个内部实数。 -/
theorem maximum_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (R S : set_l ℳ) :
    ∃ H : set_l ℳ, ∀ a b, relation_l H a b ↔ eq_l R S a b := by
  obtain ⟨H, hH⟩ := SecondOrderRelations.comprehension_l hℳ formula pure
    (((Env.empty (M := ℳ)).pushFree S).pushFree R)
  refine ⟨H, fun a b => (hH a b).trans ?_⟩
  rw [formula, Formula.satisfies_substitute, eq_formula_l]
  rfl

/-- 内部最大双模拟满足完整匹配方程，反向由最大关系再添根对构造。 -/
theorem unfold_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (R S : set_l ℳ) (a b : num_l ℳ) :
    eq_l R S a b ↔
      (∀ c, relation_l R c a → ∃ d, relation_l S d b ∧ eq_l R S c d) ∧
      (∀ d, relation_l S d b → ∃ c, relation_l R c a ∧ eq_l R S c d) := by
  refine ⟨match_l R S a b, fun h => ?_⟩
  obtain ⟨H, hH⟩ := maximum_l hℳ R S
  obtain ⟨K, hK⟩ := SecondOrderRelationOps.extend_l hℳ H a b
  refine ⟨K, ?_, (hK a b).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  intro c d h₁
  rcases (hK c d).mp h₁ with h₁ | ⟨rfl, rfl⟩
  · have h₂ := match_l R S c d ((hH c d).mp h₁)
    constructor
    · intro e h₃
      obtain ⟨f, h₄, h₅⟩ := h₂.1 e h₃
      exact ⟨f, h₄, (hK e f).mpr (Or.inl ((hH e f).mpr h₅))⟩
    · intro e h₃
      obtain ⟨f, h₄, h₅⟩ := h₂.2 e h₃
      exact ⟨f, h₄, (hK f e).mpr (Or.inl ((hH f e).mpr h₅))⟩
  · constructor
    · intro c h₁
      obtain ⟨d, h₂, h₃⟩ := h.1 c h₁
      exact ⟨d, h₂, (hK c d).mpr (Or.inl ((hH c d).mpr h₃))⟩
    · intro d h₁
      obtain ⟨c, h₂, h₃⟩ := h.2 d h₁
      exact ⟨c, h₂, (hK c d).mpr (Or.inl ((hH c d).mpr h₃))⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderBisimulation
