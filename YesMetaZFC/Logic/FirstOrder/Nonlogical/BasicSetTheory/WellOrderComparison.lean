import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.OrderOperators
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Intersection
/-!
# 良序初始段与比较基础设施
本模块只落地良序比较阶段真正新增的两个对象语言算子：
* 指定点的严格初始段 `segₘ(point, relation, carrier)`；
* 关系在子集上的限制 `rel_restrictₘ(relation, subset)`。
初始段算子拥有独立的分离实例，其成员条件是
`element ∈ carrier ∧ ⟨element, point⟩ₘ ∈ relation`。关系限制采用现代的通用
定义，直接等于 `relation ∩ₘ (subset ×ₘ subset)`，不把文献中仅针对良序初始段
的使用条件固化为公共算子的额外护栏。
文献记号 `W[...]`、`Θ_qndn` 与本轮各个证明辅助式只在注释中保留为索引。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 严格初始段算子 -/
/-- 当前元素严格位于 `point` 之前。 -/
def strict_initial_segment_member_condition (point relation : SetTerm) :
    SetFormula :=
  ⟨bₛ#0, point⟩ₘ ∈ₘ relation
/-- `candidate` 是指定点在载体中的严格初始段。 -/
def strict_initial_segment_spec (point relation carrier candidate : SetTerm) :
    SetFormula :=
  membership_specification
    candidate ((bₛ#0 ∈ₘ carrier) ∧ₘ
      strict_initial_segment_member_condition
        point relation)
/-- 对固定点、关系和载体断言严格初始段存在。 -/
def strict_initial_segment_separation_exists (point relation carrier : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ carrier) ∧ₘ (⟨bₛ#0, point⟩ₘ ∈ₘ relation))
/-- 任意点、关系和载体上的严格初始段分离实例。 -/
def strict_initial_segment_separation_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        strict_initial_segment_separation_exists (x#0) (x#1) (x#2)
/--
严格初始段算子的开放定义实例。
文献索引为 `Θ_qndn` 与 `Ξ₄₁`。只有当 `relation` 良序 `carrier` 且 `point`
属于载体时，定义公理才规定该原子项的外延。
-/
def initial_segment_definition_instance (point relation carrier candidate : SetTerm) :
    SetFormula := (is_well_order_formula relation carrier ∧ₘ (point ∈ₘ carrier)) ⟶ₘ ((candidate ≐ₘ segₘ(point, relation, carrier)) ↔ₘ
      strict_initial_segment_spec
        point relation carrier candidate)
/-- 严格初始段函数符号定义公理。 -/
def initial_segment_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          initial_segment_definition_instance (x#0) (x#1) (x#2) (x#3)
/-! ## 关系限制算子 -/
/-- 关系限制的规范见证。 -/
abbrev relation_restriction_witness_term (relation subset : SetTerm) :
    SetTerm :=
  relation ∩ₘ (subset ×ₘ subset)
/--
关系限制函数符号的开放定义实例。
文献 `Ξ₄₂` 只对良序的初始段写出该等式。公共接口解除这一章节性护栏，把关系
在任意集合上的限制统一定义为与相应笛卡尔平方的交集。
-/
def relation_restriction_definition_instance (relation subset : SetTerm) :
    SetFormula :=
  rel_restrictₘ(relation, subset) ≐ₘ
    relation_restriction_witness_term relation subset
/-- 关系限制函数符号定义公理。 -/
def relation_restriction_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      relation_restriction_definition_instance (x#0) (x#1)
/-! ## 最大序同构候选规格 -/
/--
一对点之前的严格初始段彼此序同构。
这是文献 `ψ₁₅` 的现代原子化版本。公共公式直接使用有序对投影，不再为两个坐标
额外引入存在量词。
-/
def corresponding_initial_segments_condition (sourceRelation sourceCarrier targetRelation targetCarrier pair : SetTerm) :
    SetFormula :=
  is_order_isomorphic_formula (rel_restrictₘ(
      sourceRelation,
      segₘ((pair)₀ₘ, sourceRelation, sourceCarrier))) (segₘ((pair)₀ₘ, sourceRelation, sourceCarrier)) (rel_restrictₘ(
      targetRelation,
      segₘ((pair)₁ₘ, targetRelation, targetCarrier))) (segₘ((pair)₁ₘ, targetRelation, targetCarrier))
/--
两个良序之间的最大序同构候选规格。
文献索引为 `Θ_zdxtg`。候选关系恰由两边初始段序同构的点对组成；其存在性、
函数性和最大性仍属于后续定理层。
-/
def maximal_order_isomorphism_spec (sourceRelation sourceCarrier targetRelation targetCarrier candidate :
      SetTerm) :
    SetFormula :=
  is_well_order_formula sourceRelation sourceCarrier ∧ₘ (is_well_order_formula targetRelation targetCarrier ∧ₘ
      membership_specification
        candidate ((bₛ#0 ∈ₘ (sourceCarrier ×ₘ targetCarrier)) ∧ₘ
          corresponding_initial_segments_condition
            sourceRelation sourceCarrier
            targetRelation targetCarrier bₛ#0))
/-! ## 理论组合 -/
/--
良序比较算子的公共基座。
序算子理论给出良序、关系像和笛卡尔积；二元交理论给出限制关系规范见证的
外延合同。
-/
def well_order_comparison_base_theory :
    SetTheory :=
  fun formula =>
    order_operator_theory formula ∨
      binary_intersection_operator_theory formula
/-- 加入严格初始段分离实例后的理论。 -/
def strict_initial_segment_separation_theory :
    SetTheory :=
  Theory.insert
    strict_initial_segment_separation_axiom
    well_order_comparison_base_theory
/-- 加入严格初始段原子项后的理论。 -/
def initial_segment_operator_theory : SetTheory :=
  Theory.insert
    initial_segment_definition_axiom
    strict_initial_segment_separation_theory
/-- 加入关系限制原子项后的良序比较基础理论。 -/
def well_order_comparison_theory : SetTheory :=
  Theory.insert
    relation_restriction_definition_axiom
    initial_segment_operator_theory
/-! ## proof-carrying 项边界 -/
/-- 严格初始段项满足 proof-carrying 项边界。 -/
theorem initial_segment_term_admissible (point relation carrier : SetTerm) (hPoint : Term.Admissible point SetSort.set)
    (hRelation : Term.Admissible relation SetSort.set) (hCarrier : Term.Admissible carrier SetSort.set) :
    Term.Admissible (initial_segment_term point relation carrier)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .initialSegment [⟨point, by assumption⟩, ⟨relation, by assumption⟩, ⟨carrier, by assumption⟩]
      (by rfl) (by rfl)
/-- 关系限制项满足 proof-carrying 项边界。 -/
theorem relation_restriction_term_admissible (relation subset : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hSubset : Term.Admissible subset SetSort.set) :
    Term.Admissible (relation_restriction_term relation subset)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .relationRestriction [⟨relation, by assumption⟩, ⟨subset, by assumption⟩]
      (by rfl) (by rfl)
/-- 关系限制的规范见证满足 proof-carrying 项边界。 -/
theorem relation_restriction_witness_term_admissible (relation subset : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hSubset : Term.Admissible subset SetSort.set) :
    Term.Admissible (relation_restriction_witness_term relation subset)
      SetSort.set :=
  binary_intersection_term_admissible
    relation (subset ×ₘ subset)
    hRelation (cartesian_product_term_admissible
      subset subset hSubset hSubset)
/-! ## 公共良构性边界 -/
theorem initial_segment_definition_axiom_admissible :
    Formula.Admissible
      initial_segment_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem strict_initial_segment_separation_axiom_admissible :
    Formula.Admissible
      strict_initial_segment_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem relation_restriction_definition_axiom_admissible :
    Formula.Admissible
      relation_restriction_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem well_order_comparison_base_theory_admissible :
    Theory.Admissible
      well_order_comparison_base_theory := by
  intro formula hFormula
  rcases hFormula with hFormula | hFormula
  · exact order_operator_theory_admissible
      formula hFormula
  · exact binary_intersection_operator_theory_admissible
      formula hFormula
theorem strict_initial_segment_separation_theory_admissible :
    Theory.Admissible
      strict_initial_segment_separation_theory :=
  Theory.admissible_insert
    strict_initial_segment_separation_axiom_admissible
    well_order_comparison_base_theory_admissible
theorem initial_segment_operator_theory_admissible :
    Theory.Admissible
      initial_segment_operator_theory :=
  Theory.admissible_insert
    initial_segment_definition_axiom_admissible
    strict_initial_segment_separation_theory_admissible
theorem well_order_comparison_theory_admissible :
    Theory.Admissible
      well_order_comparison_theory :=
  Theory.admissible_insert
    relation_restriction_definition_axiom_admissible
    initial_segment_operator_theory_admissible
/-! ## 闭理论边界 -/
@[derive_close_sentence]
theorem well_order_comparison_base_theory_sentence
    {formula : SetFormula} (hFormula : well_order_comparison_base_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with hFormula | hFormula
  · exact order_operator_theory_sentence hFormula
  · exact binary_intersection_operator_theory_sentence
      hFormula
@[derive_close_sentence]
theorem strict_initial_segment_separation_theory_sentence
    {formula : SetFormula} (hFormula :
      strict_initial_segment_separation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact strict_initial_segment_separation_axiom_admissible
    · native_decide
  · exact well_order_comparison_base_theory_sentence
      hFormula
@[derive_close_sentence]
theorem initial_segment_operator_theory_sentence
    {formula : SetFormula} (hFormula : initial_segment_operator_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact initial_segment_definition_axiom_admissible
    · native_decide
  · exact strict_initial_segment_separation_theory_sentence
      hFormula
@[derive_close_sentence]
theorem well_order_comparison_theory_sentence
    {formula : SetFormula} (hFormula : well_order_comparison_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact relation_restriction_definition_axiom_admissible
    · native_decide
  · exact initial_segment_operator_theory_sentence
      hFormula
/-! ## 理论嵌入 -/
theorem order_operator_theory_subset_well_order_comparison_base_theory
    {formula : SetFormula} (hFormula : order_operator_theory formula) :
    well_order_comparison_base_theory formula :=
  Or.inl hFormula
theorem binary_intersection_operator_theory_subset_well_order_comparison_base_theory
    {formula : SetFormula} (hFormula : binary_intersection_operator_theory formula) :
    well_order_comparison_base_theory formula :=
  Or.inr hFormula
theorem well_order_comparison_base_theory_subset_strict_initial_segment_separation_theory
    {formula : SetFormula} (hFormula : well_order_comparison_base_theory formula) :
    strict_initial_segment_separation_theory formula :=
  Or.inr hFormula
theorem strict_initial_segment_separation_theory_subset_initial_segment_operator_theory
    {formula : SetFormula} (hFormula : strict_initial_segment_separation_theory formula) :
    initial_segment_operator_theory formula :=
  Or.inr hFormula
theorem initial_segment_operator_theory_subset_well_order_comparison_theory
    {formula : SetFormula} (hFormula : initial_segment_operator_theory formula) :
    well_order_comparison_theory formula :=
  Or.inr hFormula
/-!
## 待证明定理索引
本轮截图中的主要结果暂留为文档索引：
* 3.18：良序刚性，即良序到自身的序同构逐点恒等；
* 3.19：两个良序之间的序同构映射唯一；
* 3.20：指定点严格初始段的存在性与唯一性；
* 3.21：向下封闭的真子集由唯一切点给出；
* 3.22--3.23：`maximal_order_isomorphism_spec` 的存在性与唯一性；
* 3.24：最大序同构映射的定义域和值域边界；
* 3.25：良序的可比较性。
文献辅助式 `Θ_box`、`Θ_tgys`、`Θ_qd`、`Θ_687`、
`Θ_688`、`Θ_dy`、`Θ_dya`、`Θ_bs`、`Θ_ds`、`Θ_bxa` 与 `Θ_bxb`
服务于上述证明的纸面分段。它们不增加语言符号，本轮不作为独立公理或带
`sorry` 的定理声明；后续正式证明比较定理时再按可复用的数学结构拆分。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
