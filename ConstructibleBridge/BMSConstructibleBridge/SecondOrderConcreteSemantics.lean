import BMSConstructibleBridge.SecondOrderConcreteFormula

/-!
# 原固定高度矩阵在任意模型中的反例语义

私有member/ternary模板用已有公开edge/iteration模板作定义相等重述，不改变原矩阵。
反例由同一内部实数承载：全函数性、所有当前高度有界、每个相邻对有内部展开指标。
下面不把逐步指标的存在收集成另一条实数序列，也不要求模型数是外部标准自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderConcreteSemantics

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramGeneratedHeight (height_m)
open SecondOrderProgramGeneratedCheck (check_m)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def graph_template_m : Formula signature_m [.set] [.num] :=
  .forallE .num (.existsE .num (.conj
    (GraphSyntax.edge_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
    (.forallE .num (.imp
      (GraphSyntax.edge_m (.bvar (.there (.there (.there .here))))
        (.bvar (.there (.there .here))) (.bvar .here))
      (.equal (.bvar .here) (.bvar (.there .here)))))))

private def bounds_template_m (c : code_m) : Formula signature_m [.set] [.num] :=
  .forallE .num (.forallE .num (.imp
    (GraphSyntax.edge_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
    (FixedHeightPureFormula.bound (graph_m c) (.bvar .here) (.fvar .here))))

private def stop_template_m (c : code_m) : Formula signature_m [.set] [.num] :=
  .existsE .num (.existsE .num (.existsE .num (.conj
    (GraphSyntax.edge_m (.bvar (.there (.there (.there .here))))
      (.bvar (.there (.there .here))) (.bvar (.there .here)))
    (.conj (GraphSyntax.edge_m (.bvar (.there (.there (.there .here))))
      (Term.app (σ := signature_m) .succ (.cons (.bvar (.there (.there .here))) .nil)) (.bvar .here))
      (.forallE .num (.neg (iteration_m (graph_m c) (.bvar (.there .here))
        (.bvar (.there (.there .here))) (.bvar .here)
        (Term.app (σ := signature_m) .succ
          (.cons (Term.app (σ := signature_m) .zero .nil) .nil)))))))))

private theorem iteration_rel_l (c : code_m) {C : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (x i u v : Term signature_m Γ Δ .num) :
    Formula.satisfies η (iteration_m (graph_m c) x i u v) ↔
      relation_l C (value_l (x.eval η) (value_l (i.eval η) (u.eval η))) (v.eval η) := by
  rw [iteration_syntax_l (graph_m c) C hC]
  constructor
  · rintro ⟨a, b, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, _, rfl, rfl, h⟩

/-- 原全函数块就是同一实数在全部内部数上的存在唯一性。 -/
theorem graph_rel_l (η : Env ℳ [.set] [.num]) :
    Formula.satisfies η FixedHeightPureFormula.m_graph ↔ function_l (η.boundVal .here) := by
  change Formula.satisfies η graph_template_m ↔ _
  simp only [graph_template_m, Formula.satisfies, SecondOrderPairing.edge_l]
  rfl

/-- 原全部高度块约束实际高度图的输出；不限制轨迹长度或初始高度。 -/
theorem bounds_rel_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {C : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) (η : Env ℳ [.set] [.num]) :
    letI := order_l hℳ
    Formula.satisfies η (FixedHeightPureFormula.m_allBounds (graph_m c)) ↔
      ∀ i a, relation_l (η.boundVal .here) i a →
        ∃ y, relation_l C a y ∧ y ≤ η.freeVal .here := by
  letI := order_l hℳ
  change Formula.satisfies η (bounds_template_m c) ↔ _
  simp only [bounds_template_m, Formula.satisfies, SecondOrderPairing.edge_l,
    SecondOrderRawHeightFormula.bound_rel_l hℳ c hC]
  rfl

/-- 原停止块要求某个相邻对对所有内部指标都不再给出严格展开见证。 -/
theorem stop_rel_l (c : code_m) {C : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) (η : Env ℳ [.set] [.num]) :
    Formula.satisfies η (FixedHeightPureFormula.m_stop (graph_m c)) ↔
      ∃ i a b, relation_l (η.boundVal .here) i a ∧
        relation_l (η.boundVal .here) (succ_l i) b ∧
        ∀ k, ¬relation_l C (value_l b (value_l a k)) (succ_l (zero_l ℳ)) := by
  change Formula.satisfies η (stop_template_m c) ↔ _
  simp only [stop_template_m, Formula.satisfies, SecondOrderPairing.edge_l,
    iteration_rel_l c hC]
  rfl

/-- 具体程序矩阵在任意原Z₂模型中的真实语义，程序及两张图都不再匿名。 -/
theorem matrix_rel_l (hℳ : Theory.Models ℳ theory_m) {H C : set_l ℳ}
    (hH : graph_semantics_l (graph_m height_m) H)
    (hC : graph_semantics_l (graph_m check_m) C) (η : Env ℳ [.set] [.num]) :
    letI := order_l hℳ
    Formula.satisfies η SecondOrderConcreteFormula.matrix_m ↔
      (function_l (η.boundVal .here) →
        (∀ i a, relation_l (η.boundVal .here) i a →
          ∃ y, relation_l H a y ∧ y ≤ η.freeVal .here) →
        ∃ i a b, relation_l (η.boundVal .here) i a ∧
          relation_l (η.boundVal .here) (succ_l i) b ∧
          ∀ k, ¬relation_l C (value_l b (value_l a k)) (succ_l (zero_l ℳ))) := by
  letI := order_l hℳ
  change Formula.satisfies η (FixedHeightPureFormula.matrix_m (graph_m height_m) (graph_m check_m)) ↔ _
  simp only [FixedHeightPureFormula.matrix_m, Formula.satisfies, graph_rel_l,
    bounds_rel_l hℳ height_m hH, stop_rel_l check_m hC]

/-- 否定原矩阵给出同一内部实数中的全域有界下降反例；不收集指标选择函数。 -/
theorem counterexample_l (hℳ : Theory.Models ℳ theory_m) {H C : set_l ℳ}
    (hH : graph_semantics_l (graph_m height_m) H)
    (hC : graph_semantics_l (graph_m check_m) C) (η : Env ℳ [.set] [.num]) :
    letI := order_l hℳ
    (¬Formula.satisfies η SecondOrderConcreteFormula.matrix_m) ↔
      function_l (η.boundVal .here) ∧
      (∀ i a, relation_l (η.boundVal .here) i a →
        ∃ y, relation_l H a y ∧ y ≤ η.freeVal .here) ∧
      ∀ i a b, relation_l (η.boundVal .here) i a →
        relation_l (η.boundVal .here) (succ_l i) b →
        ∃ k, relation_l C (value_l b (value_l a k)) (succ_l (zero_l ℳ)) := by
  classical
  letI := order_l hℳ
  rw [matrix_rel_l hℳ hH hC]
  simp only [Classical.not_imp, not_exists, not_and, not_forall, Classical.not_not]

#print axioms graph_rel_l
#print axioms bounds_rel_l
#print axioms stop_rel_l
#print axioms matrix_rel_l
#print axioms counterexample_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderConcreteSemantics
