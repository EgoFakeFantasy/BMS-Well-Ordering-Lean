import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.FiniteOrdinal
/-!
# 映像、限制与序算子
本模块只落地这一轮截图中仍属于基础设施的四个算子：
* 映像 `imgₘ(function, subset)`；
* 函数限制 `restrictₘ(function, subset)`；
* 良序上的最小元 `minₘ(relation, subset)`；
* 自然离散线性序上的最大元 `maxₘ(relation, subset)`。
它们复用前一层的映射、良序和自然离散线性序接口。截图中的映像存在性、
限制映射性质、序同构继承、有限序的极值递归等内容只保留在文档索引中。
文献 `ψ₁₃` 描述的是关系像成员条件。本模块为它建立独立的关系像分离层，不再
沿用早期实现中“初始段”的误名。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 关系像分离实例 -/
/--
当前元素是 `source` 中某个点经 `relation` 得到的像。
该条件作为 `membership_specification` 的体使用；进入存在 binder 后，
`bₛ#0` 是原像见证，`bₛ#1` 是当前待筛选元素。文献索引为 `ψ₁₃`。
-/
def relation_image_member_condition (relation source : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set], (bₛ#0 ∈ₘ source) ∧ₘ (⟨bₛ#0, bₛ#1⟩ₘ ∈ₘ relation)
/-- 从目标集合中分离关系像的存在公式。 -/
def relation_image_separation_exists (relation source target : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ target) ∧ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ source) ∧ₘ (⟨bₛ#0, bₛ#1⟩ₘ ∈ₘ relation)))
/-- 任意关系、原像集合和目标母集上的关系像分离实例。 -/
def relation_image_separation_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        relation_image_separation_exists (x#0) (x#1) (x#2)
/-! ## 映像 -/
/-- 映像成员条件：目标元素属于 `target` 且由 `subset` 中的点映到。 -/
def image_spec (function subset target candidate : SetTerm) :
    SetFormula :=
  membership_specification
    candidate ((bₛ#0 ∈ₘ target) ∧ₘ
      relation_image_member_condition function subset)
/-- 映像函数符号的开放定义实例。 -/
def image_definition_instance (function source target subset candidate : SetTerm) :
    SetFormula :=
  is_mapping_formula function source target ⟶ₘ (((¬ₘ (subset ≐ₘ ∅ₘ)) ∧ₘ (subset ⊆ₘ source)) ⟶ₘ ((candidate ≐ₘ imgₘ(function, subset)) ↔ₘ
        image_spec function subset target candidate))
/-- 映像函数符号定义公理。 -/
def image_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4],
            image_definition_instance (x#0) (x#1) (x#2) (x#3) (x#4)
/-! ## 函数限制 -/
/--
限制关系的成员条件。
在 `membership_specification` 的当前元素下，`bₛ#1` 是限制集中的第一坐标，
`bₛ#0` 是第二坐标，`bₛ#2` 是当前有序对。
-/
def restriction_member_condition (subset : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∃ₘ[SetSort.set], (bₛ#1 ∈ₘ subset) ∧ₘ (bₛ#2 ≐ₘ ⟨bₛ#1, bₛ#0⟩ₘ)
/-- 函数限制的成员规格。 -/
def restriction_spec (function subset candidate : SetTerm) :
    SetFormula :=
  membership_specification
    candidate ((bₛ#0 ∈ₘ function) ∧ₘ
      restriction_member_condition subset)
/-- 函数限制符号的开放定义实例。 -/
def restriction_definition_instance (function source target subset candidate : SetTerm) :
    SetFormula :=
  is_mapping_formula function source target ⟶ₘ (((¬ₘ (subset ≐ₘ ∅ₘ)) ∧ₘ (subset ⊆ₘ source)) ⟶ₘ ((candidate ≐ₘ restrictₘ(function, subset)) ↔ₘ
        restriction_spec function subset candidate))
/-- 函数限制符号定义公理。 -/
def restriction_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4],
            restriction_definition_instance (x#0) (x#1) (x#2) (x#3) (x#4)
/-! ## 最小元与最大元 -/
/-- 候选元是子集在严格序下的最小元。 -/
def minimum_spec (relation subset candidate : SetTerm) :
    SetFormula := (candidate ∈ₘ subset) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ subset) ⟶ₘ ((¬ₘ (candidate ≐ₘ bₛ#0)) ⟶ₘ (⟨candidate, bₛ#0⟩ₘ ∈ₘ relation)))
/-- 良序上的最小元定义实例。 -/
def minimum_linear_order_definition_instance (relation carrier subset candidate : SetTerm) :
    SetFormula := ((is_well_order_formula relation carrier) ∧ₘ ((subset ⊆ₘ carrier) ∧ₘ (¬ₘ (subset ≐ₘ ∅ₘ)))) ⟶ₘ ((candidate ≐ₘ minₘ(relation, subset)) ↔ₘ
      minimum_spec relation subset candidate)
/-- 良序上的最小元定义公理。 -/
def minimum_linear_order_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          minimum_linear_order_definition_instance (x#0) (x#1) (x#2) (x#3)
/-- 自然离散线性序上的最小元定义实例。 -/
def minimum_natural_order_definition_instance (relation carrier subset candidate : SetTerm) :
    SetFormula := ((is_natural_discrete_linear_order_formula relation carrier) ∧ₘ ((subset ⊆ₘ carrier) ∧ₘ (¬ₘ (subset ≐ₘ ∅ₘ)))) ⟶ₘ
    ((candidate ≐ₘ minₘ(relation, subset)) ↔ₘ
      minimum_spec relation subset candidate)
/-- 自然离散线性序上的最小元定义公理。 -/
def minimum_natural_order_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          minimum_natural_order_definition_instance (x#0) (x#1) (x#2) (x#3)
/-- 候选元是子集在严格序下的最大元。 -/
def maximum_spec (relation subset candidate : SetTerm) :
    SetFormula := (candidate ∈ₘ subset) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ subset) ⟶ₘ ((¬ₘ (candidate ≐ₘ bₛ#0)) ⟶ₘ (⟨bₛ#0, candidate⟩ₘ ∈ₘ relation)))
/-- 自然离散线性序上的最大元定义实例。 -/
def maximum_natural_order_definition_instance (relation carrier subset candidate : SetTerm) :
    SetFormula := ((is_natural_discrete_linear_order_formula relation carrier) ∧ₘ ((subset ⊆ₘ carrier) ∧ₘ (¬ₘ (subset ≐ₘ ∅ₘ)))) ⟶ₘ
    ((candidate ≐ₘ maxₘ(relation, subset)) ↔ₘ
      maximum_spec relation subset candidate)
/-- 自然离散线性序上的最大元定义公理。 -/
def maximum_natural_order_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          maximum_natural_order_definition_instance (x#0) (x#1) (x#2) (x#3)
/-! ## 理论组合 -/
/-- 加入关系像分离实例后的理论。 -/
def relation_image_separation_theory : SetTheory :=
  Theory.insert
    relation_image_separation_axiom
    finite_ordinal_theory
/-- 映像函数符号理论。 -/
def image_operator_theory : SetTheory :=
  Theory.insert
    image_definition_axiom
    relation_image_separation_theory
/-- 函数限制符号理论。 -/
def restriction_operator_theory : SetTheory :=
  Theory.insert
    restriction_definition_axiom
    image_operator_theory
/-- 良序最小元算子理论。 -/
def minimum_linear_order_theory : SetTheory :=
  Theory.insert
    minimum_linear_order_definition_axiom
    restriction_operator_theory
/-- 自然离散线性序最小元算子理论。 -/
def minimum_natural_order_theory : SetTheory :=
  Theory.insert
    minimum_natural_order_definition_axiom
    minimum_linear_order_theory
/-- 自然离散线性序最大元算子理论。 -/
def order_operator_theory : SetTheory :=
  Theory.insert
    maximum_natural_order_definition_axiom
    minimum_natural_order_theory
/-! ## proof-carrying 项边界 -/
/-- 映像项满足 proof-carrying 项边界。 -/
theorem image_term_admissible (function subset : SetTerm) (hFunction : Term.Admissible function SetSort.set) (hSubset : Term.Admissible subset SetSort.set) :
    Term.Admissible (image_term function subset)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .image [⟨function, by assumption⟩, ⟨subset, by assumption⟩]
      (by rfl) (by rfl)
/-- 函数限制项满足 proof-carrying 项边界。 -/
theorem restriction_term_admissible (function subset : SetTerm) (hFunction : Term.Admissible function SetSort.set)
    (hSubset : Term.Admissible subset SetSort.set) :
    Term.Admissible (restriction_term function subset)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .restriction [⟨function, by assumption⟩, ⟨subset, by assumption⟩]
      (by rfl) (by rfl)
/-- 最小元项满足 proof-carrying 项边界。 -/
theorem minimum_term_admissible (relation subset : SetTerm) (hRelation : Term.Admissible relation SetSort.set) (hSubset : Term.Admissible subset SetSort.set) :
    Term.Admissible (minimum_term relation subset)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .minimum [⟨relation, by assumption⟩, ⟨subset, by assumption⟩]
      (by rfl) (by rfl)
/-- 最大元项满足 proof-carrying 项边界。 -/
theorem maximum_term_admissible (relation subset : SetTerm) (hRelation : Term.Admissible relation SetSort.set) (hSubset : Term.Admissible subset SetSort.set) :
    Term.Admissible (maximum_term relation subset)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .maximum [⟨relation, by assumption⟩, ⟨subset, by assumption⟩]
      (by rfl) (by rfl)
/-! ## 公共良构性边界 -/
theorem relation_image_separation_axiom_admissible :
    Formula.Admissible
      relation_image_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem image_definition_axiom_admissible :
    Formula.Admissible image_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem restriction_definition_axiom_admissible :
    Formula.Admissible restriction_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem minimum_linear_order_definition_axiom_admissible :
    Formula.Admissible
      minimum_linear_order_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem minimum_natural_order_definition_axiom_admissible :
    Formula.Admissible
      minimum_natural_order_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem maximum_natural_order_definition_axiom_admissible :
    Formula.Admissible
      maximum_natural_order_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem relation_image_separation_theory_admissible :
    Theory.Admissible
      relation_image_separation_theory :=
  Theory.admissible_insert
    relation_image_separation_axiom_admissible
    finite_ordinal_theory_admissible
theorem image_operator_theory_admissible :
    Theory.Admissible image_operator_theory :=
  Theory.admissible_insert
    image_definition_axiom_admissible
    relation_image_separation_theory_admissible
theorem restriction_operator_theory_admissible :
    Theory.Admissible restriction_operator_theory :=
  Theory.admissible_insert
    restriction_definition_axiom_admissible
    image_operator_theory_admissible
theorem minimum_linear_order_theory_admissible :
    Theory.Admissible minimum_linear_order_theory :=
  Theory.admissible_insert
    minimum_linear_order_definition_axiom_admissible
    restriction_operator_theory_admissible
theorem minimum_natural_order_theory_admissible :
    Theory.Admissible minimum_natural_order_theory :=
  Theory.admissible_insert
    minimum_natural_order_definition_axiom_admissible
    minimum_linear_order_theory_admissible
theorem order_operator_theory_admissible :
    Theory.Admissible order_operator_theory :=
  Theory.admissible_insert
    maximum_natural_order_definition_axiom_admissible
    minimum_natural_order_theory_admissible
/-! ## 闭理论边界 -/
@[derive_close_sentence]
theorem relation_image_separation_theory_sentence
    {formula : SetFormula} (hFormula : relation_image_separation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact relation_image_separation_axiom_admissible
    · native_decide
  · exact finite_ordinal_theory_sentence hFormula
@[derive_close_sentence]
theorem image_operator_theory_sentence
    {formula : SetFormula} (hFormula : image_operator_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact image_definition_axiom_admissible
    · native_decide
  · exact relation_image_separation_theory_sentence
      hFormula
@[derive_close_sentence]
theorem restriction_operator_theory_sentence
    {formula : SetFormula} (hFormula : restriction_operator_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact restriction_definition_axiom_admissible
    · native_decide
  · exact image_operator_theory_sentence hFormula
@[derive_close_sentence]
theorem minimum_linear_order_theory_sentence
    {formula : SetFormula} (hFormula : minimum_linear_order_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact minimum_linear_order_definition_axiom_admissible
    · native_decide
  · exact restriction_operator_theory_sentence hFormula
@[derive_close_sentence]
theorem minimum_natural_order_theory_sentence
    {formula : SetFormula} (hFormula : minimum_natural_order_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact minimum_natural_order_definition_axiom_admissible
    · native_decide
  · exact minimum_linear_order_theory_sentence hFormula
@[derive_close_sentence]
theorem order_operator_theory_sentence
    {formula : SetFormula} (hFormula : order_operator_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact maximum_natural_order_definition_axiom_admissible
    · native_decide
  · exact minimum_natural_order_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem finite_ordinal_theory_subset_relation_image_separation_theory
    {formula : SetFormula} (hFormula : finite_ordinal_theory formula) :
    relation_image_separation_theory formula :=
  Or.inr hFormula
theorem relation_image_separation_theory_subset_image_operator_theory
    {formula : SetFormula} (hFormula : relation_image_separation_theory formula) :
    image_operator_theory formula :=
  Or.inr hFormula
theorem image_operator_theory_subset_restriction_operator_theory
    {formula : SetFormula} (hFormula : image_operator_theory formula) :
    restriction_operator_theory formula :=
  Or.inr hFormula
theorem restriction_operator_theory_subset_minimum_linear_order_theory
    {formula : SetFormula} (hFormula : restriction_operator_theory formula) :
    minimum_linear_order_theory formula :=
  Or.inr hFormula
theorem minimum_linear_order_theory_subset_minimum_natural_order_theory
    {formula : SetFormula} (hFormula : minimum_linear_order_theory formula) :
    minimum_natural_order_theory formula :=
  Or.inr hFormula
theorem minimum_natural_order_theory_subset_order_operator_theory
    {formula : SetFormula} (hFormula : minimum_natural_order_theory formula) :
    order_operator_theory formula :=
  Or.inr hFormula
/-!
## 待证明定理索引
本轮截图中的主要内容暂留为文档索引：
* 3.6--3.8：映像、限制映射以及单射/满射/双射闭性；
* 3.9：线性序同构下的限制与结构保持；
* 3.10--3.11：非空子集最小元/最大元的存在唯一性；
* 3.16：限制映射存在性；
* 3.17：良序、自然离散线性序与后继的关系；
* `Θ_Lo*` 系列：关系、定义域和值域在成员关系限制下的线性序合同。
这些结果不在当前基础设施层声明为 `axiom` 或带 `sorry` 的定理。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
