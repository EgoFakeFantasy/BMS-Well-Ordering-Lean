import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.OrderProductMapping
/-!
# 最小差异点与指数序
本模块建立自然离散线性序代数中指数序的公共对象语言接口：
* `min_diffₘ(f, g)` 表示两个同源映射的最小差异点；
* `idx_ordₘ(R, A, S, B)` 表示由源序和目标序诱导的函数空间指数序。
文献中的 `Δ`、`ZhiS`、`Ψ` 与 `Ψ_b` 只作为注释索引。公共定义直接使用
最小差异点条件和已有的 `Mapₘ(source, target)`，不把函数幂记号或纸面辅助
公式提升为新的语法层。
最小差异点是描述符型函数项，因此只需要在其自然 guard 下给出定义合同；
指数序是集合关系，则额外保留一个以函数空间平方为母集的闭分离实例。
后续关于存在性、唯一性、序性质及单点源特殊处理的定理暂留文档索引。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 最小差异点 -/
/-- 两个同源映射的最小差异点规格。 -/
def minimum_difference_spec (sourceRelation sourceCarrier firstFunction secondFunction candidate : SetTerm) :
    SetFormula := (candidate ∈ₘ sourceCarrier) ∧ₘ (((firstFunction ·ₘ candidate) ≠ₘ (secondFunction ·ₘ candidate)) ∧ₘ (∀ₘ[SetSort.set],
        ((bₛ#0 ∈ₘ sourceCarrier) ∧ₘ (⟨bₛ#0, candidate⟩ₘ ∈ₘ sourceRelation)) ⟶ₘ ((firstFunction ·ₘ bₛ#0) ≐ₘ (secondFunction ·ₘ bₛ#0))))
/-- 最小差异点函数符号的开放定义实例；文献索引为 `Ξ₅₂`。 -/
def minimum_difference_definition_instance (sourceRelation sourceCarrier target
      firstFunction secondFunction candidate : SetTerm) :
    SetFormula := (is_well_order_formula sourceRelation sourceCarrier ∧ₘ ((is_mapping_formula firstFunction sourceCarrier target ∧ₘ
          is_mapping_formula secondFunction sourceCarrier target) ∧ₘ (firstFunction ≠ₘ secondFunction))) ⟶ₘ ((candidate ≐ₘ
        min_diffₘ(firstFunction, secondFunction)) ↔ₘ
      minimum_difference_spec
        sourceRelation sourceCarrier
        firstFunction secondFunction candidate)
/-- 最小差异点函数符号定义公理。 -/
def minimum_difference_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4],
            ∀ₘ[SetSort.set, 5],
              minimum_difference_definition_instance (x#0) (x#1) (x#2) (x#3) (x#4) (x#5)
/-! ## 指数序 -/
/--
指数序的最小差异点条件。
当前公式位于 `membership_specification` 的单元素体中，因此 `bₛ#0`
是待判断的函数对；存在量词引入候选差异点后，`bₛ#1` 仍是该函数对。
-/
def index_order_member_condition (sourceRelation sourceCarrier targetRelation : SetTerm) :
    SetFormula := ((((bₛ#0)₀ₘ) ≠ₘ ((bₛ#0)₁ₘ)) ∧ₘ (∃ₘ[SetSort.set], ((bₛ#0 ∈ₘ sourceCarrier) ∧ₘ (((bₛ#1)₀ₘ ·ₘ bₛ#0) ≠ₘ ((bₛ#1)₁ₘ ·ₘ bₛ#0))) ∧ₘ ((∀ₘ[SetSort.set],
              ((bₛ#0 ∈ₘ sourceCarrier) ∧ₘ (⟨bₛ#0, bₛ#1⟩ₘ ∈ₘ sourceRelation)) ⟶ₘ (((bₛ#1)₀ₘ ·ₘ bₛ#0) ≐ₘ ((bₛ#1)₁ₘ ·ₘ bₛ#0))) ∧ₘ (⟨((bₛ#1)₀ₘ ·ₘ bₛ#0),
              ((bₛ#1)₁ₘ ·ₘ bₛ#0)⟩ₘ ∈ₘ targetRelation))))
/-- 指数序的成员规格。 -/
def index_order_spec (sourceRelation sourceCarrier targetRelation targetCarrier candidate : SetTerm) :
    SetFormula :=
  membership_specification
    candidate (((bₛ#0 ∈ₘ (Mapₘ(sourceCarrier, targetCarrier) ×ₘ
            Mapₘ(sourceCarrier, targetCarrier))) ∧ₘ
        index_order_member_condition
          sourceRelation sourceCarrier targetRelation))
/-- 指数序关系的分离存在实例。 -/
def index_order_separation_exists (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    index_order_spec
      sourceRelation sourceCarrier
      targetRelation targetCarrier bₛ#1
/-- 任意源序和目标序上的指数序分离实例。 -/
def index_order_separation_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          index_order_separation_exists (x#0) (x#1) (x#2) (x#3)
/-- 指数序函数符号的开放定义实例。文献索引为 `ZhiS` 的定义层。 -/
def index_order_definition_instance (sourceRelation sourceCarrier targetRelation targetCarrier candidate : SetTerm) :
    SetFormula := (is_well_order_formula sourceRelation sourceCarrier ∧ₘ
      is_well_order_formula targetRelation targetCarrier) ⟶ₘ ((candidate ≐ₘ
        idx_ordₘ(
          sourceRelation, sourceCarrier,
          targetRelation, targetCarrier)) ↔ₘ
      index_order_spec
        sourceRelation sourceCarrier
        targetRelation targetCarrier candidate)
/-- 指数序函数符号定义公理。 -/
def index_order_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4],
            index_order_definition_instance (x#0) (x#1) (x#2) (x#3) (x#4)
/-! ## 理论组合 -/
/-- 加入最小差异点定义公理后的理论。 -/
def minimum_difference_theory : SetTheory :=
  Theory.insert
    minimum_difference_definition_axiom
    order_operator_theory
/-- 加入指数序分离实例后的理论。 -/
def index_order_separation_theory : SetTheory :=
  Theory.insert
    index_order_separation_axiom
    minimum_difference_theory
/-- 加入指数序函数符号后的理论。 -/
def index_order_theory : SetTheory :=
  Theory.insert
    index_order_definition_axiom
    index_order_separation_theory
/-! ## proof-carrying 项边界 -/
/-- 最小差异点项满足 proof-carrying 项边界。 -/
theorem minimum_difference_term_admissible (firstFunction secondFunction : SetTerm) (hFirstFunction : Term.Admissible firstFunction SetSort.set)
    (hSecondFunction : Term.Admissible secondFunction SetSort.set) :
    Term.Admissible (min_diffₘ(firstFunction, secondFunction))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .minimumDifference [⟨firstFunction, by assumption⟩, ⟨secondFunction, by assumption⟩]
      (by rfl) (by rfl)
/-- 指数序项满足 proof-carrying 项边界。 -/
theorem index_order_term_admissible (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm)
    (hSourceRelation : Term.Admissible sourceRelation SetSort.set) (hSourceCarrier : Term.Admissible sourceCarrier SetSort.set)
    (hTargetRelation : Term.Admissible targetRelation SetSort.set) (hTargetCarrier : Term.Admissible targetCarrier SetSort.set) :
    Term.Admissible (idx_ordₘ(
        sourceRelation, sourceCarrier,
        targetRelation, targetCarrier))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .indexOrder [⟨sourceRelation, by assumption⟩, ⟨sourceCarrier, by assumption⟩, ⟨targetRelation, by assumption⟩, ⟨targetCarrier, by assumption⟩]
      (by rfl) (by rfl)
/-! ## 良构性与闭理论边界 -/
theorem minimum_difference_definition_axiom_admissible :
    Formula.Admissible
      minimum_difference_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem index_order_separation_axiom_admissible :
    Formula.Admissible
      index_order_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem index_order_definition_axiom_admissible :
    Formula.Admissible
      index_order_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem minimum_difference_theory_admissible :
    Theory.Admissible minimum_difference_theory :=
  Theory.admissible_insert
    minimum_difference_definition_axiom_admissible
    order_operator_theory_admissible
theorem index_order_separation_theory_admissible :
    Theory.Admissible index_order_separation_theory :=
  Theory.admissible_insert
    index_order_separation_axiom_admissible
    minimum_difference_theory_admissible
theorem index_order_theory_admissible :
    Theory.Admissible index_order_theory :=
  Theory.admissible_insert
    index_order_definition_axiom_admissible
    index_order_separation_theory_admissible
/-! ## 闭理论边界 -/
@[derive_close_sentence]
theorem minimum_difference_theory_sentence
    {formula : SetFormula} (hFormula : minimum_difference_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact minimum_difference_definition_axiom_admissible
    · native_decide
  · exact order_operator_theory_sentence hFormula
@[derive_close_sentence]
theorem index_order_separation_theory_sentence
    {formula : SetFormula} (hFormula : index_order_separation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact index_order_separation_axiom_admissible
    · native_decide
  · exact minimum_difference_theory_sentence hFormula
@[derive_close_sentence]
theorem index_order_theory_sentence
    {formula : SetFormula} (hFormula : index_order_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact index_order_definition_axiom_admissible
    · native_decide
  · exact index_order_separation_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem order_operator_theory_subset_minimum_difference_theory
    {formula : SetFormula} (hFormula : order_operator_theory formula) :
    minimum_difference_theory formula :=
  Or.inr hFormula
theorem minimum_difference_theory_subset_index_order_separation_theory
    {formula : SetFormula} (hFormula : minimum_difference_theory formula) :
    index_order_separation_theory formula :=
  Or.inr hFormula
theorem index_order_separation_theory_subset_index_order_theory
    {formula : SetFormula} (hFormula : index_order_separation_theory formula) :
    index_order_theory formula :=
  Or.inr hFormula
/-!
## 待证明定理索引
* 定理 3.41：指数序关系的存在性与唯一性，包括单点源的特殊分支；
* 定理 3.42：指数序保持线性序、序同构与自然离散线性序；
* 定理 3.43：自然离散线性序上的指数序限制性质。
`Ψ` 与 `Ψ_b` 已压缩为 `index_order_member_condition` 的直接现代规格，
不再作为公共函数或独立公理出现。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
