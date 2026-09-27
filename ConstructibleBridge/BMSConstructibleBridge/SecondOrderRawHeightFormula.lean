import BMSConstructibleBridge.SecondOrderProgramZeroRows
import BMSConstructibleBridge.FixedHeightPureFormula

/-!
# 原高度上界模板的任意模型语义

复用 `FixedHeightPureFormula.bound` 的实际 AST，不另写高度谓词。
先对任意原程序证明它精确约束同一程序图的输出；再把原始数组码上的裁剪高度
实例化为全部尾部行全零。此实例的输入是原始数组码，而非生成轨迹码；最终目标
仍须在它之前接上原 `ArithmeticPresentation.decode_l` 的实际程序与内部正确性。
这里没有用原始数组高度替换生成数组解码后的当前高度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRawHeightFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListLookup
open SecondOrderProgramTrimHeight
open SecondOrderProgramZeroRows
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原上界模板在任意模型中约束同一图的输出，保留所有参数环境。 -/
theorem bound_rel_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {C : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (a b : Term signature_m Γ Δ .num) :
    letI := order_l hℳ
    Formula.satisfies η (FixedHeightPureFormula.bound (graph_m c) a b) ↔
      ∃ y, relation_l C (a.eval η) y ∧ y ≤ b.eval η := by
  letI := order_l hℳ
  simp only [FixedHeightPureFormula.bound, Formula.satisfies,
    SecondOrderOrder.formula_l, Term.eval_weakenBound]
  apply exists_congr
  intro y
  rw [hC (η.pushBound y) (a.weakenBound sort_m.num) (.bvar .here)]
  simp only [Term.eval_weakenBound]
  change (relation_l C (a.eval η) y ∧ ¬b.eval η < y) ↔
    (relation_l C (a.eval η) y ∧ y ≤ b.eval η)
  simp only [not_lt]

/-- 已给定同一图的输出时，上界模板精确约束该值。 -/
theorem bound_value_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {C : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (a b : Term signature_m Γ Δ .num) {y : num_l ℳ}
    (hy : relation_l C (a.eval η) y) :
    letI := order_l hℳ
    Formula.satisfies η (FixedHeightPureFormula.bound (graph_m c) a b) ↔ y ≤ b.eval η := by
  letI := order_l hℳ
  rw [bound_rel_l hℳ c hC]
  constructor
  · rintro ⟨z, hz, hb⟩
    exact (function_value_unique_l (function_of_semantics_l hℳ c hC) hz hy) ▸ hb
  · intro hb
    exact ⟨y, hy, hb⟩

/-- 在原始数组码上，实际上界模板精确等价于全部内部尾部行全零。 -/
theorem raw_bound_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (a b : Term signature_m Γ Δ .num) :
    Formula.satisfies η (FixedHeightPureFormula.bound (graph_m trim_m) a b) ↔
      zero_rows_l E (a.eval η) (b.eval η) := by
  obtain ⟨T, hTf, hT⟩ := graph_total_l hℳ trim_m
  obtain ⟨y, hy, _⟩ := hTf (a.eval η)
  exact (bound_value_l hℳ trim_m hT η a b hy).trans
    (trim_bound_iff_zero_rows_l hℳ hT hE hy (b.eval η))

#print axioms bound_rel_l
#print axioms bound_value_l
#print axioms raw_bound_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRawHeightFormula
