import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.WellOrderComparison
/-!
# 序数、自然数与良序比较映射
本模块吸收文献中良序比较之后的定义设施：
* 两个良序之间的规范比较映射；
* 序数谓词与自然数谓词；
* 序数非空子集的成员序最小元合同；
* 自然数非空子集的成员序最大元合同。
文献记号 `QR`、`XuS`、`ZRS`、`min_∈` 与 `max_∈` 只保留为索引。公共接口使用
`wo_compareₘ`、`is_ordinal_formula`、`is_natural_number_formula`，并把成员序
极值直接表示为已有的 `minₘ(εₘ(ordinal), subset)` 与
`maxₘ(εₘ(natural), subset)`。因此这里只增加确实不可由现有 AST 表示的比较映射
函数符号以及两个谓词符号。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 良序比较映射 -/
/--
良序比较映射的开放定义实例。
文献索引为 `Ξ₄₃`。候选映射满足最大序同构规格，并以源载体为完整定义域。
-/
def well_order_comparison_map_definition_instance (sourceRelation sourceCarrier targetRelation targetCarrier candidate :
      SetTerm) :
    SetFormula := (is_well_order_formula sourceRelation sourceCarrier ∧ₘ
      is_well_order_formula targetRelation targetCarrier) ⟶ₘ ((candidate ≐ₘ
        wo_compareₘ(
          sourceRelation, sourceCarrier,
          targetRelation, targetCarrier)) ↔ₘ (maximal_order_isomorphism_spec
          sourceRelation sourceCarrier
          targetRelation targetCarrier candidate ∧ₘ (sourceCarrier ≐ₘ domₘ(candidate))))
/-- 良序比较映射函数符号定义公理。 -/
def well_order_comparison_map_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4],
            well_order_comparison_map_definition_instance (x#0) (x#1) (x#2) (x#3) (x#4)
/-! ## 序数与自然数谓词 -/
/-- 序数条件：传递集上的成员关系构成良序。文献索引为 `XuS`。 -/
def is_ordinal_condition (set : SetTerm) :
    SetFormula :=
  is_transitive_set_formula set ∧ₘ
    is_well_order_formula (εₘ(set)) set
/-- 序数谓词的开放定义实例。 -/
def is_ordinal_definition_instance (set : SetTerm) :
    SetFormula :=
  is_ordinal_formula set ↔ₘ
    is_ordinal_condition set
/-- 序数谓词定义公理。 -/
def is_ordinal_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_ordinal_definition_instance (x#0)
/--
自然数条件：传递集上的成员关系构成自然离散线性序。文献索引为 `ZRS`。
-/
def is_natural_number_condition (set : SetTerm) :
    SetFormula :=
  is_transitive_set_formula set ∧ₘ
    is_natural_discrete_linear_order_formula (εₘ(set)) set
/-- 自然数谓词的开放定义实例。 -/
def is_natural_number_definition_instance (set : SetTerm) :
    SetFormula :=
  is_natural_number_formula set ↔ₘ
    is_natural_number_condition set
/-- 自然数谓词定义公理。 -/
def is_natural_number_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_natural_number_definition_instance (x#0)
/-! ## 成员序极值的文献合同 -/
/--
`candidate` 是 `subset` 在成员序下的最小元。
该写法忠实对应文献中的 `candidate ∈ S(element)`，同时保留候选必须属于子集。
-/
def ordinal_membership_minimum_spec (subset candidate : SetTerm) :
    SetFormula := (candidate ∈ₘ subset) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ subset) ⟶ₘ (candidate ∈ₘ Sₘ(bₛ#0)))
/--
序数非空子集最小元的开放合同。
算子项复用 `minₘ(εₘ(ordinal), subset)`，不再为文献的特化记号增加新函数符号。
-/
def ordinal_membership_minimum_definition_instance (ordinal subset candidate : SetTerm) :
    SetFormula := (is_ordinal_formula ordinal ∧ₘ ((subset ⊆ₘ ordinal) ∧ₘ (¬ₘ (subset ≐ₘ ∅ₘ)))) ⟶ₘ ((candidate ≐ₘ minεₘ(ordinal, subset)) ↔ₘ
      ordinal_membership_minimum_spec subset candidate)
/-- 序数非空子集最小元合同公理。文献索引为 `Ξ₄₆`。 -/
def ordinal_membership_minimum_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ordinal_membership_minimum_definition_instance (x#0) (x#1) (x#2)
/-- `candidate` 是 `subset` 在成员序下的最大元。 -/
def natural_membership_maximum_spec (subset candidate : SetTerm) :
    SetFormula := (candidate ∈ₘ subset) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ subset) ⟶ₘ (bₛ#0 ∈ₘ Sₘ(candidate)))
/--
自然数非空子集最大元的开放合同。
算子项复用 `maxₘ(εₘ(natural), subset)`，不再为文献的特化记号增加新函数符号。
-/
def natural_membership_maximum_definition_instance (natural subset candidate : SetTerm) :
    SetFormula := (is_natural_number_formula natural ∧ₘ ((subset ⊆ₘ natural) ∧ₘ (¬ₘ (subset ≐ₘ ∅ₘ)))) ⟶ₘ ((candidate ≐ₘ maxεₘ(natural, subset)) ↔ₘ
      natural_membership_maximum_spec subset candidate)
/-- 自然数非空子集最大元合同公理。文献索引为 `Ξ₄₇`。 -/
def natural_membership_maximum_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        natural_membership_maximum_definition_instance (x#0) (x#1) (x#2)
/-! ## 理论组合 -/
/-- 加入规范良序比较映射后的理论。 -/
def well_order_comparison_map_theory : SetTheory :=
  Theory.insert
    well_order_comparison_map_definition_axiom
    well_order_comparison_theory
/-- 加入序数谓词后的理论。 -/
def ordinal_predicate_theory : SetTheory :=
  Theory.insert
    is_ordinal_definition_axiom
    well_order_comparison_map_theory
/-- 加入自然数谓词后的理论。 -/
def natural_number_predicate_theory : SetTheory :=
  Theory.insert
    is_natural_number_definition_axiom
    ordinal_predicate_theory
/-- 加入序数成员序最小元合同后的理论。 -/
def ordinal_membership_minimum_theory : SetTheory :=
  Theory.insert
    ordinal_membership_minimum_definition_axiom
    natural_number_predicate_theory
/-- 序数与自然数定义设施的最终理论。 -/
def ordinal_natural_theory : SetTheory :=
  Theory.insert
    natural_membership_maximum_definition_axiom
    ordinal_membership_minimum_theory
/-! ## proof-carrying 项边界 -/
/-- 良序比较映射项满足 proof-carrying 项边界。 -/
theorem well_order_comparison_map_term_admissible (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm)
    (hSourceRelation : Term.Admissible sourceRelation SetSort.set) (hSourceCarrier : Term.Admissible sourceCarrier SetSort.set)
    (hTargetRelation : Term.Admissible targetRelation SetSort.set) (hTargetCarrier : Term.Admissible targetCarrier SetSort.set) :
    Term.Admissible (well_order_comparison_map_term
        sourceRelation sourceCarrier
        targetRelation targetCarrier)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .wellOrderComparisonMap [⟨sourceRelation, by assumption⟩, ⟨sourceCarrier, by assumption⟩, ⟨targetRelation, by assumption⟩, ⟨targetCarrier, by assumption⟩]
      (by rfl) (by rfl)
/-- 序数成员序最小元项满足 proof-carrying 项边界。 -/
theorem ordinal_membership_minimum_term_admissible (ordinal subset : SetTerm) (hOrdinal : Term.Admissible ordinal SetSort.set)
    (hSubset : Term.Admissible subset SetSort.set) :
    Term.Admissible (minεₘ(ordinal, subset))
      SetSort.set :=
  minimum_term_admissible (εₘ(ordinal)) subset (membership_relation_term_admissible ordinal hOrdinal)
    hSubset
/-- 自然数成员序最大元项满足 proof-carrying 项边界。 -/
theorem natural_membership_maximum_term_admissible (natural subset : SetTerm) (hNatural : Term.Admissible natural SetSort.set)
    (hSubset : Term.Admissible subset SetSort.set) :
    Term.Admissible (maxεₘ(natural, subset))
      SetSort.set :=
  maximum_term_admissible (εₘ(natural)) subset (membership_relation_term_admissible natural hNatural)
    hSubset
/-! ## 公共良构性边界 -/
theorem well_order_comparison_map_definition_axiom_admissible :
    Formula.Admissible
      well_order_comparison_map_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_ordinal_definition_axiom_admissible :
    Formula.Admissible
      is_ordinal_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_natural_number_definition_axiom_admissible :
    Formula.Admissible
      is_natural_number_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem ordinal_membership_minimum_definition_axiom_admissible :
    Formula.Admissible
      ordinal_membership_minimum_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem natural_membership_maximum_definition_axiom_admissible :
    Formula.Admissible
      natural_membership_maximum_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem well_order_comparison_map_theory_admissible :
    Theory.Admissible
      well_order_comparison_map_theory :=
  Theory.admissible_insert
    well_order_comparison_map_definition_axiom_admissible
    well_order_comparison_theory_admissible
theorem ordinal_predicate_theory_admissible :
    Theory.Admissible
      ordinal_predicate_theory :=
  Theory.admissible_insert
    is_ordinal_definition_axiom_admissible
    well_order_comparison_map_theory_admissible
theorem natural_number_predicate_theory_admissible :
    Theory.Admissible
      natural_number_predicate_theory :=
  Theory.admissible_insert
    is_natural_number_definition_axiom_admissible
    ordinal_predicate_theory_admissible
theorem ordinal_membership_minimum_theory_admissible :
    Theory.Admissible
      ordinal_membership_minimum_theory :=
  Theory.admissible_insert
    ordinal_membership_minimum_definition_axiom_admissible
    natural_number_predicate_theory_admissible
theorem ordinal_natural_theory_admissible :
    Theory.Admissible
      ordinal_natural_theory :=
  Theory.admissible_insert
    natural_membership_maximum_definition_axiom_admissible
    ordinal_membership_minimum_theory_admissible
/-! ## 闭理论边界 -/
@[derive_close_sentence]
theorem well_order_comparison_map_theory_sentence
    {formula : SetFormula} (hFormula : well_order_comparison_map_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact well_order_comparison_map_definition_axiom_admissible
    · native_decide
  · exact well_order_comparison_theory_sentence hFormula
@[derive_close_sentence]
theorem ordinal_predicate_theory_sentence
    {formula : SetFormula} (hFormula : ordinal_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_ordinal_definition_axiom_admissible
    · native_decide
  · exact well_order_comparison_map_theory_sentence hFormula
@[derive_close_sentence]
theorem natural_number_predicate_theory_sentence
    {formula : SetFormula} (hFormula : natural_number_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_natural_number_definition_axiom_admissible
    · native_decide
  · exact ordinal_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem ordinal_membership_minimum_theory_sentence
    {formula : SetFormula} (hFormula : ordinal_membership_minimum_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact ordinal_membership_minimum_definition_axiom_admissible
    · native_decide
  · exact natural_number_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem ordinal_natural_theory_sentence
    {formula : SetFormula} (hFormula : ordinal_natural_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact natural_membership_maximum_definition_axiom_admissible
    · native_decide
  · exact ordinal_membership_minimum_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem well_order_comparison_theory_subset_well_order_comparison_map_theory
    {formula : SetFormula} (hFormula : well_order_comparison_theory formula) :
    well_order_comparison_map_theory formula :=
  Or.inr hFormula
theorem well_order_comparison_map_theory_subset_ordinal_predicate_theory
    {formula : SetFormula} (hFormula : well_order_comparison_map_theory formula) :
    ordinal_predicate_theory formula :=
  Or.inr hFormula
theorem ordinal_predicate_theory_subset_natural_number_predicate_theory
    {formula : SetFormula} (hFormula : ordinal_predicate_theory formula) :
    natural_number_predicate_theory formula :=
  Or.inr hFormula
theorem natural_number_predicate_theory_subset_ordinal_membership_minimum_theory
    {formula : SetFormula} (hFormula : natural_number_predicate_theory formula) :
    ordinal_membership_minimum_theory formula :=
  Or.inr hFormula
theorem ordinal_membership_minimum_theory_subset_ordinal_natural_theory
    {formula : SetFormula} (hFormula : ordinal_membership_minimum_theory formula) :
    ordinal_natural_theory formula :=
  Or.inr hFormula
/-!
## 待证明定理索引
本轮截图中的结论暂留为后续证明任务：
* 推论 3.5：两个良序若不满足反向可嵌入，则存在向前的序嵌入；
* 定理 3.26：规范比较映射在源载体未被完全覆盖时，其逆给出反向比较映射；
* 定理 3.27：有限数是自然数、自然数是序数，以及序数/自然数非空子集极值的
  存在性。
这些结果依赖前一模块中的最大序同构定理和比较定理。当前模块只建立它们消费的
定义公理、项记号、理论链与良构性边界，不以 `sorry` 或额外公理伪装证明。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
