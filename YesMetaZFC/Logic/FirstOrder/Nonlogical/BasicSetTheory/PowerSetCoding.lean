import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.IndexOrder
/-!
# 幂集的二值函数编码
本模块建立有限自然数幂集到二值函数空间的规范编码项：
* `binary_value_set_term` 是规范二值集合 `{0, 1}`；
* `chiₘ(n)` 是 `𝒫ₘ(n)` 与 `Mapₘ(n, {0, 1})` 之间的特征函数编码图。
文献记号 `χ`、`Θ₃n₉`、`Θ₁₂₃₆a`--`Θ₁₂₃₆f` 与 `Θ_DY57` 只保留为注释索引。
公共定义直接以有序对投影和特征函数逐点合同刻画图元素，不把纸面分离证明的
辅助公式提升为独立语法或公理。
文献把空集参数单独写成 `{⟨∅, ∅⟩}`。统一规格不需要这个分支：
`Mapₘ(∅, {0, 1})` 的唯一元素就是空映射，因此同一成员公式自然归约到该单点图。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 二值编码规格 -/
/-- 规范二值集合 `{0, 1}`。 -/
def binary_value_set_term : SetTerm :=
  {numₘ(0), numₘ(1)}ₘ
/--
幂集编码图的单元素成员条件。
该公式位于 `membership_specification` 的单元素体中，外层 `bₛ#0` 是候选图元素。
进入逐点全称量词后，`bₛ#1` 仍是该有序对，`bₛ#0` 是自然数中的坐标。
-/
def power_set_bijection_member_condition (natural : SetTerm) :
    SetFormula := (bₛ#0 ∈ₘ (𝒫ₘ(natural) ×ₘ
        Mapₘ(natural, binary_value_set_term))) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ natural) ⟶ₘ (((bₛ#0 ∈ₘ (bₛ#1)₀ₘ) ↔ₘ (⟨bₛ#0, numₘ(1)⟩ₘ ∈ₘ (bₛ#1)₁ₘ)) ∧ₘ
          ((¬ₘ (bₛ#0 ∈ₘ (bₛ#1)₀ₘ)) ↔ₘ (⟨bₛ#0, numₘ(0)⟩ₘ ∈ₘ (bₛ#1)₁ₘ))))
/-- 幂集编码双射图的成员规格。 -/
def power_set_bijection_spec (natural candidate : SetTerm) :
    SetFormula :=
  membership_specification
    candidate (power_set_bijection_member_condition natural)
/-- 对固定自然数参数断言规范编码图存在。 -/
def power_set_bijection_separation_exists (natural : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    power_set_bijection_spec natural bₛ#1
/-- 任意自然数参数上的规范编码图分离实例。 -/
def power_set_bijection_separation_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    power_set_bijection_separation_exists (x#0)
/-- 幂集编码双射函数符号的开放定义实例；文献索引为 `Ξ₅₇`。 -/
def power_set_bijection_definition_instance (natural candidate : SetTerm) :
    SetFormula :=
  is_natural_number_formula natural ⟶ₘ ((candidate ≐ₘ chiₘ(natural)) ↔ₘ
      power_set_bijection_spec natural candidate)
/-- 幂集编码双射函数符号定义公理。 -/
def power_set_bijection_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      power_set_bijection_definition_instance (x#0) (x#1)
/-! ## 理论组合 -/
/-- 加入规范编码图分离实例后的理论。 -/
def power_set_bijection_separation_theory : SetTheory :=
  Theory.insert
    power_set_bijection_separation_axiom
    index_order_theory
/-- 加入规范幂集编码双射函数符号后的理论。 -/
def power_set_bijection_theory : SetTheory :=
  Theory.insert
    power_set_bijection_definition_axiom
    power_set_bijection_separation_theory
/-! ## proof-carrying 项边界 -/
/-- 规范二值集合满足 proof-carrying 项边界。 -/
theorem binary_value_set_term_admissible :
    Term.Admissible
      binary_value_set_term
      SetSort.set :=
  unordered_pair_term_admissible (numₘ(0)) (numₘ(1)) (finite_numeral_term_admissible 0) (finite_numeral_term_admissible 1)
/-- 幂集编码双射项满足 proof-carrying 项边界。 -/
theorem power_set_bijection_term_admissible (natural : SetTerm) (hNatural : Term.Admissible natural SetSort.set) :
    Term.Admissible (chiₘ(natural))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .powerSetBijection [⟨natural, by assumption⟩]
      (by rfl) (by rfl)
/-! ## 良构性与闭理论边界 -/
theorem power_set_bijection_separation_axiom_admissible :
    Formula.Admissible
      power_set_bijection_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem power_set_bijection_definition_axiom_admissible :
    Formula.Admissible
      power_set_bijection_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem power_set_bijection_separation_theory_admissible :
    Theory.Admissible
      power_set_bijection_separation_theory :=
  Theory.admissible_insert
    power_set_bijection_separation_axiom_admissible
    index_order_theory_admissible
theorem power_set_bijection_theory_admissible :
    Theory.Admissible
      power_set_bijection_theory :=
  Theory.admissible_insert
    power_set_bijection_definition_axiom_admissible
    power_set_bijection_separation_theory_admissible
@[derive_close_sentence]
theorem power_set_bijection_separation_theory_sentence
    {formula : SetFormula} (hFormula : power_set_bijection_separation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact power_set_bijection_separation_axiom_admissible
    · native_decide
  · exact index_order_theory_sentence hFormula
@[derive_close_sentence]
theorem power_set_bijection_theory_sentence
    {formula : SetFormula} (hFormula : power_set_bijection_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact power_set_bijection_definition_axiom_admissible
    · native_decide
  · exact power_set_bijection_separation_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem index_order_theory_subset_power_set_bijection_separation_theory
    {formula : SetFormula} (hFormula : index_order_theory formula) :
    power_set_bijection_separation_theory formula :=
  Or.inr hFormula
theorem power_set_bijection_separation_theory_subset_power_set_bijection_theory
    {formula : SetFormula} (hFormula : power_set_bijection_separation_theory formula) :
    power_set_bijection_theory formula :=
  Or.inr hFormula
/-!
## 待证明定理索引
* 定理 3.45：子集与二值特征映射的典型对应；
* 定理 3.46：`chiₘ(n)` 的存在、映射性、双射性和参数一致性；
* 定理 3.48--3.50 中由 `chiₘ(n)` 诱导到幂集上的关系与序性质。
纸面 `ψ₃₈`--`ψ₄₃`、`Θ₃n₉`、`Θ₁₂₃₆a`--`Θ₁₂₃₆f`、`Θ_DY57`
只服务于分离、唯一性和双射证明。后续定理模块应直接消费
`power_set_bijection_spec`，不为这些辅助式增加专用公理。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
