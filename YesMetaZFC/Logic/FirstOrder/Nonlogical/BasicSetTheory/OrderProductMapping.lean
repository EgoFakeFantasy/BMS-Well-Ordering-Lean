import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalOrderAlgebra
/-!
# 映射直积与指数序基础设施
本模块吸收自然离散线性序章节中序积之后的映射直积设施。公共对象语言接口
使用 `map_prodₘ(function₁, function₂)` 表示两个映射的直积；文献中的 `⊗`
只保留为索引注释，以免与带载体的词典序积 `ord_prodₘ` 发生歧义。
映射直积的成员直接由源集合中的两个坐标生成：
`⟨⟨x, y⟩, ⟨f(x), g(y)⟩⟩`。
目标集合只出现在映射守卫中，因此由 `is_mapping_formula` 保证生成的值位于
目标直积。分离公理使用源直积与目标直积作为母集，并把这个直接成员条件
封装为公共规格。
文献指数序部分的 `Ψ`、`ψ₂₅`--`ψ₃₃` 与 `Γ₂₂` 都是第一分歧点定理的
证明中间式，包含纸面上的函数幂、递归截断和最小元展开。本模块不把这些
冗余中间量提升为公共签名；后续 `IndexOrder` 模块直接提供最小差异点和指数序
公共规格。定理 3.39、3.40 先保留为后续证明任务。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 映射直积 -/
/--
映射直积的单元素成员条件。
该公式作为 `membership_specification` 的体使用。两层存在量词引入第一、
第二个源坐标，因此在最内层 `bₛ#2` 仍然指向外层待判断的关系元素。
-/
def mapping_product_member_condition (firstFunction firstSource secondFunction secondSource : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∃ₘ[SetSort.set], ((bₛ#1 ∈ₘ firstSource) ∧ₘ (bₛ#0 ∈ₘ secondSource)) ∧ₘ (bₛ#2 ≐ₘ
          ⟨⟨bₛ#1, bₛ#0⟩ₘ,
            ⟨firstFunction ·ₘ bₛ#1,
              secondFunction ·ₘ bₛ#0⟩ₘ⟩ₘ)
/-- 映射直积的成员规格。 -/
def mapping_product_spec (firstFunction firstSource secondFunction secondSource candidate : SetTerm) :
    SetFormula :=
  membership_specification
    candidate (mapping_product_member_condition
      firstFunction firstSource secondFunction secondSource)
/-- 映射直积的分离存在实例。 -/
def mapping_product_separation_exists (firstFunction firstSource firstTarget
      secondFunction secondSource secondTarget : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ ((firstSource ×ₘ secondSource) ×ₘ (firstTarget ×ₘ secondTarget))) ∧ₘ
          mapping_product_member_condition
            firstFunction firstSource
            secondFunction secondSource)
/-- 任意两个映射的直积分离实例。 -/
def mapping_product_separation_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4],
            ∀ₘ[SetSort.set, 5],
              mapping_product_separation_exists (x#0) (x#1) (x#2) (x#3) (x#4) (x#5)
/--
映射直积函数符号的开放定义实例。文献索引为 `Ξ₅₁`。
只有当两个输入确实是相应源到目标的映射时，函数项才由成员规格确定。
-/
def mapping_product_definition_instance (firstFunction firstSource firstTarget
      secondFunction secondSource secondTarget candidate : SetTerm) :
    SetFormula := (is_mapping_formula firstFunction firstSource firstTarget ∧ₘ
      is_mapping_formula secondFunction secondSource secondTarget) ⟶ₘ ((candidate ≐ₘ
        map_prodₘ(firstFunction, secondFunction)) ↔ₘ
      mapping_product_spec
        firstFunction firstSource
        secondFunction secondSource candidate)
/-- 映射直积函数符号定义公理。 -/
def mapping_product_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4],
            ∀ₘ[SetSort.set, 5],
              ∀ₘ[SetSort.set, 6],
                mapping_product_definition_instance (x#4) (x#0) (x#2) (x#5) (x#1) (x#3) (x#6)
/-! ## 理论组合 -/
/-- 加入映射直积分离实例后的理论。 -/
def mapping_product_separation_theory : SetTheory :=
  Theory.insert
    mapping_product_separation_axiom
    order_product_theory
/-- 加入映射直积函数符号后的理论；文献索引为 `Γ₂₁b`。 -/
def mapping_product_theory : SetTheory :=
  Theory.insert
    mapping_product_definition_axiom
    mapping_product_separation_theory
/-! ## proof-carrying 项边界 -/
/-- 映射直积函数项满足 proof-carrying 项边界。 -/
theorem mapping_product_term_admissible (firstFunction secondFunction : SetTerm) (hFirstFunction : Term.Admissible firstFunction SetSort.set)
    (hSecondFunction : Term.Admissible secondFunction SetSort.set) :
    Term.Admissible (map_prodₘ(firstFunction, secondFunction))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .mappingProduct [⟨firstFunction, by assumption⟩, ⟨secondFunction, by assumption⟩]
      (by rfl) (by rfl)
/-! ## 良构性与闭理论边界 -/
theorem mapping_product_separation_axiom_admissible :
    Formula.Admissible
      mapping_product_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem mapping_product_definition_axiom_admissible :
    Formula.Admissible
      mapping_product_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem mapping_product_separation_theory_admissible :
    Theory.Admissible
      mapping_product_separation_theory :=
  Theory.admissible_insert
    mapping_product_separation_axiom_admissible
    order_product_theory_admissible
theorem mapping_product_theory_admissible :
    Theory.Admissible mapping_product_theory :=
  Theory.admissible_insert
    mapping_product_definition_axiom_admissible
    mapping_product_separation_theory_admissible
@[derive_close_sentence]
theorem mapping_product_separation_theory_sentence
    {formula : SetFormula} (hFormula : mapping_product_separation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact mapping_product_separation_axiom_admissible
    · native_decide
  · exact order_product_theory_sentence hFormula
@[derive_close_sentence]
theorem mapping_product_theory_sentence
    {formula : SetFormula} (hFormula : mapping_product_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact mapping_product_definition_axiom_admissible
    · native_decide
  · exact mapping_product_separation_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem order_product_theory_subset_mapping_product_separation_theory
    {formula : SetFormula} (hFormula : order_product_theory formula) :
    mapping_product_separation_theory formula :=
  Or.inr hFormula
theorem mapping_product_separation_theory_subset_mapping_product_theory
    {formula : SetFormula} (hFormula : mapping_product_separation_theory formula) :
    mapping_product_theory formula :=
  Or.inr hFormula
/-!
## 待证明定理索引
* 定理 3.39：映射直积保持线性序同构的闭性；
* 定理 3.40：非空良序集合上的两个不同映射存在第一分歧点。
指数序证明中的 `Ψ`、`ψ₂₅`--`ψ₃₃` 与 `Γ₂₂` 不建立公共函数符号或公共理论层。
`IndexOrder` 模块使用最小差异点条件直接给出同等数学强度的现代规格。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
