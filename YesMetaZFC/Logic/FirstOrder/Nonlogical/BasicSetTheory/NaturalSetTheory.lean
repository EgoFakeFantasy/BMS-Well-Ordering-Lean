import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Infinity
/-!
# 自然数集合基础设施
本模块吸收无穷公理之后的自然数集合定义层。
公共接口采用现代数学命名：
* `unboundedₘ(subset, relation, carrier)` 表示关系载体中的无界子集；
* `boundedₘ(subset, relation, carrier)` 表示关系载体中的有界子集；
* `ord_typeₘ(relation, carrier)` 表示自然离散线性序的有限序型；
* `nat_subset_typeₘ(subset)` 表示自然数子集的序型，非有界时取 `ωₘ`。
文献中的 `WuJ`、`YuJ`、`XuXn`、`ZrBS` 只保留为注释索引，不进入公共
命名。截图中的自然数集合推论、有限数逐项刻画、非压缩映像引理以及鸽巢原理
同样暂留为后续证明层的文档索引。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 有界与无界子集 -/
/-- 子集在关系载体中无界；文献索引为 `WuJ`。 -/
def unbounded_subset_condition (subset relation carrier : SetTerm) :
    SetFormula := (subset ⊆ₘ carrier) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ carrier) ⟶ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ subset) ∧ₘ (⟨bₛ#1, bₛ#0⟩ₘ ∈ₘ relation)))
/-- 无界子集谓词的开放定义实例。 -/
def unbounded_subset_definition_instance (subset relation carrier : SetTerm) :
    SetFormula :=
  unboundedₘ(subset, relation, carrier) ↔ₘ
    unbounded_subset_condition subset relation carrier
/-- 无界子集谓词定义公理。 -/
def unbounded_subset_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        unbounded_subset_definition_instance (x#0) (x#1) (x#2)
/-- 子集在关系载体中有界；文献索引为 `YuJ`。 -/
def bounded_subset_condition (subset relation carrier : SetTerm) :
    SetFormula := (subset ⊆ₘ carrier) ∧ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ carrier) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ subset) ⟶ₘ (⟨bₛ#0, bₛ#1⟩ₘ ∈ₘ relation)))
/-- 有界子集谓词的开放定义实例。 -/
def bounded_subset_definition_instance (subset relation carrier : SetTerm) :
    SetFormula :=
  boundedₘ(subset, relation, carrier) ↔ₘ
    bounded_subset_condition subset relation carrier
/-- 有界子集谓词定义公理。 -/
def bounded_subset_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        bounded_subset_definition_instance (x#0) (x#1) (x#2)
/-! ## 自然离散线性序的序型 -/
/--
关系 `relation` 在 `carrier` 上的自然序型条件。
文献中的 `XuTG` 是关系同构谓词，而不是带函数参数的序同构映射谓词。
因此这里使用四参数的 `is_order_isomorphic_formula`。
-/
def natural_order_type_condition (relation carrier candidate : SetTerm) :
    SetFormula := (candidate ∈ₘ ωₘ) ∧ₘ
    is_order_isomorphic_formula
      relation carrier (εₘ(ωₘ)) candidate
/-- 自然序型函数项的开放定义实例；文献函数记号为 `XuXn`。 -/
def natural_order_type_definition_instance (relation carrier candidate : SetTerm) :
    SetFormula :=
  is_natural_discrete_linear_order_formula relation carrier ⟶ₘ ((candidate ≐ₘ ord_typeₘ(relation, carrier)) ↔ₘ
      natural_order_type_condition relation carrier candidate)
/-- 自然序型函数符号定义公理。 -/
def natural_order_type_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        natural_order_type_definition_instance (x#0) (x#1) (x#2)
/-! ## 自然数子集的序型 -/
/--
自然数子集的序型条件。
有界子集的序型仍落在 `ωₘ` 中，并与其成员关系同构；无界子集的序型则为
`ωₘ`。外层 `subset ⊆ₘ ωₘ` 前件把函数项的定义域明确限制在自然数子集上。
-/
def natural_subset_type_condition (subset candidate : SetTerm) :
    SetFormula := (candidate ∈ₘ Sₘ(ωₘ)) ∧ₘ ((boundedₘ(subset, εₘ(ωₘ), ωₘ)) ⟶ₘ ((candidate ∈ₘ ωₘ) ∧ₘ
        is_order_isomorphic_formula (εₘ(ωₘ)) subset (εₘ(candidate)) candidate)) ∧ₘ ((¬ₘ boundedₘ(subset, εₘ(ωₘ), ωₘ)) ⟶ₘ (candidate ≐ₘ ωₘ))
/-- 自然数子集序型函数项的开放定义实例；文献函数记号为 `ZrBS`。 -/
def natural_subset_type_definition_instance (subset candidate : SetTerm) :
    SetFormula := (subset ⊆ₘ ωₘ) ⟶ₘ ((candidate ≐ₘ nat_subset_typeₘ(subset)) ↔ₘ
      natural_subset_type_condition subset candidate)
/-- 自然数子集序型函数符号定义公理。 -/
def natural_subset_type_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      natural_subset_type_definition_instance (x#0) (x#1)
/-! ## 理论组合 -/
/-- 加入无界子集谓词后的理论。 -/
def unbounded_subset_theory : SetTheory :=
  Theory.insert
    unbounded_subset_definition_axiom
    infinity_theory
/-- 加入有界子集谓词后的理论。 -/
def bounded_subset_theory : SetTheory :=
  Theory.insert
    bounded_subset_definition_axiom
    unbounded_subset_theory
/-- 加入自然序型函数项后的理论。 -/
def natural_order_type_theory : SetTheory :=
  Theory.insert
    natural_order_type_definition_axiom
    bounded_subset_theory
/-- 加入自然数子集序型函数项后的理论。 -/
def natural_subset_type_theory : SetTheory :=
  Theory.insert
    natural_subset_type_definition_axiom
    natural_order_type_theory
/-- 自然数集合定义层的稳定公共入口。 -/
def natural_set_theory : SetTheory :=
  natural_subset_type_theory
/-! ## proof-carrying 项边界 -/
/-- 自然序型项满足 proof-carrying 项边界。 -/
theorem natural_order_type_term_admissible (relation carrier : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hCarrier : Term.Admissible carrier SetSort.set) :
    Term.Admissible (ord_typeₘ(relation, carrier))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .naturalOrderType [⟨relation, by assumption⟩, ⟨carrier, by assumption⟩]
      (by rfl) (by rfl)
/-- 自然数子集序型项满足 proof-carrying 项边界。 -/
theorem natural_subset_type_term_admissible (subset : SetTerm) (hSubset : Term.Admissible subset SetSort.set) :
    Term.Admissible (nat_subset_typeₘ(subset))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .naturalSubsetType [⟨subset, by assumption⟩]
      (by rfl) (by rfl)
/-! ## 良构性与闭理论边界 -/
theorem unbounded_subset_definition_axiom_admissible :
    Formula.Admissible
      unbounded_subset_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem bounded_subset_definition_axiom_admissible :
    Formula.Admissible
      bounded_subset_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem natural_order_type_definition_axiom_admissible :
    Formula.Admissible
      natural_order_type_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem natural_subset_type_definition_axiom_admissible :
    Formula.Admissible
      natural_subset_type_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem unbounded_subset_theory_admissible :
    Theory.Admissible unbounded_subset_theory :=
  Theory.admissible_insert
    unbounded_subset_definition_axiom_admissible
    infinity_theory_admissible
theorem bounded_subset_theory_admissible :
    Theory.Admissible bounded_subset_theory :=
  Theory.admissible_insert
    bounded_subset_definition_axiom_admissible
    unbounded_subset_theory_admissible
theorem natural_order_type_theory_admissible :
    Theory.Admissible natural_order_type_theory :=
  Theory.admissible_insert
    natural_order_type_definition_axiom_admissible
    bounded_subset_theory_admissible
theorem natural_subset_type_theory_admissible :
    Theory.Admissible natural_subset_type_theory :=
  Theory.admissible_insert
    natural_subset_type_definition_axiom_admissible
    natural_order_type_theory_admissible
theorem natural_set_theory_admissible :
    Theory.Admissible natural_set_theory :=
  natural_subset_type_theory_admissible
/-! ## 闭理论边界 -/
@[derive_close_sentence]
theorem unbounded_subset_theory_sentence
    {formula : SetFormula} (hFormula : unbounded_subset_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact unbounded_subset_definition_axiom_admissible
    · native_decide
  · exact infinity_theory_sentence hFormula
@[derive_close_sentence]
theorem bounded_subset_theory_sentence
    {formula : SetFormula} (hFormula : bounded_subset_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact bounded_subset_definition_axiom_admissible
    · native_decide
  · exact unbounded_subset_theory_sentence hFormula
@[derive_close_sentence]
theorem natural_order_type_theory_sentence
    {formula : SetFormula} (hFormula : natural_order_type_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact natural_order_type_definition_axiom_admissible
    · native_decide
  · exact bounded_subset_theory_sentence hFormula
@[derive_close_sentence]
theorem natural_subset_type_theory_sentence
    {formula : SetFormula} (hFormula : natural_subset_type_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact natural_subset_type_definition_axiom_admissible
    · native_decide
  · exact natural_order_type_theory_sentence hFormula
@[derive_close_sentence]
theorem natural_set_theory_sentence
    {formula : SetFormula} (hFormula : natural_set_theory formula) :
    Formula.Sentence formula :=
  natural_subset_type_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem infinity_theory_subset_unbounded_subset_theory
    {formula : SetFormula} (hFormula : infinity_theory formula) :
    unbounded_subset_theory formula :=
  Or.inr hFormula
theorem unbounded_subset_theory_subset_bounded_subset_theory
    {formula : SetFormula} (hFormula : unbounded_subset_theory formula) :
    bounded_subset_theory formula :=
  Or.inr hFormula
theorem bounded_subset_theory_subset_natural_order_type_theory
    {formula : SetFormula} (hFormula : bounded_subset_theory formula) :
    natural_order_type_theory formula :=
  Or.inr hFormula
theorem natural_order_type_theory_subset_natural_subset_type_theory
    {formula : SetFormula} (hFormula : natural_order_type_theory formula) :
    natural_subset_type_theory formula :=
  Or.inr hFormula
/-!
## 待证明定理索引
以下内容暂留为后续证明任务：
* 定理 5.1 与 5.6--5.7：`ωₘ` 的成员性质、有限自然数刻画以及序相关推论；
* 定理 5.11：`WuJ`/`YuJ` 与有穷性、后继和幂集运算的关系；
* 章节中的 `ψ₄₉`--`ψ₅₉`：为分离实例服务的一次性辅助公式；
* `Γ₃₀`--`Γ₃₆`：自然数集合后续证明阶段的累计理论；
* 鸽巢原理及其后续自然离散线性序推论。
这些结果应在本模块的定义公理和理论链之上，按需使用 `prove_auto` 或手工证明；
它们不提前伪装成已经完成的定理。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
