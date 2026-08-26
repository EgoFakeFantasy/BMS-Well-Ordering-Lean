import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Foundation
/-!
# 自然离散线性序下的代数运算
本模块建立自然离散线性序章节的两个运算设施：
* 带载体的线性序和；
* 带载体的词典序积。
文献中的 `⊕` 与 `⊗` 省略了载体参数；公共对象语言接口将四个决定性参数
`(relation₁, carrier₁, relation₂, carrier₂)` 全部保留在函数项中。序和直接使用
`relation₁ ∪ relation₂ ∪ (carrier₁ × carrier₂)` 作为规范项，序积直接使用笛卡尔
平方上的词典序成员条件。
文献辅助式 `ψ₂₀`、`Θ_zdx`、`ψ₂₁`、`ψ₂₂`、`ψ₂₃`、`ψ₂₄` 与 `Θ₈₈₅`、`Θ₉₆₄`
中，词典序坐标条件和序积成员条件属于公共定义规格；其余是纸面分离证明的中间式。
当前模块只保留序积定义真正需要的闭分离实例，不把后续映射闭性证明的辅助式提前
注入理论。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 线性序和 -/
/-- 两个线性序及其载体不交的条件。 -/
def order_sum_guard (firstRelation firstCarrier secondRelation secondCarrier : SetTerm) :
    SetFormula :=
  is_linear_order_formula firstRelation firstCarrier ∧ₘ (is_linear_order_formula secondRelation secondCarrier ∧ₘ ((firstCarrier ∩ₘ secondCarrier) ≐ₘ ∅ₘ))
/-- 线性序和的规范关系项。 -/
def order_sum_witness (firstRelation firstCarrier secondRelation secondCarrier : SetTerm) :
    SetTerm := (firstRelation ∪ₘ secondRelation) ∪ₘ (firstCarrier ×ₘ secondCarrier)
/-- 线性序和函数符号的开放定义实例。文献索引为 `Ξ₄₉`。 -/
def order_sum_definition_instance (firstRelation firstCarrier secondRelation secondCarrier : SetTerm) :
    SetFormula :=
  order_sum_guard
      firstRelation firstCarrier secondRelation secondCarrier ⟶ₘ (ord_sumₘ(
      firstRelation, firstCarrier,
      secondRelation, secondCarrier) ≐ₘ
      order_sum_witness
        firstRelation firstCarrier secondRelation secondCarrier)
/-- 线性序和函数符号定义公理。 -/
def order_sum_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          order_sum_definition_instance (x#0) (x#1) (x#2) (x#3)
/-! ## 词典序积 -/
/--
两个积点之间的词典序坐标条件。
这正是文献 `Θ_zdx` 的现代析取写法：
第一坐标严格递增，或第一坐标相等且第二坐标严格递增。
-/
def order_product_coordinate_condition (firstRelation secondRelation left right : SetTerm) :
    SetFormula := (⟨(left)₀ₘ, (right)₀ₘ⟩ₘ ∈ₘ firstRelation) ∨ₘ (((left)₀ₘ ≐ₘ (right)₀ₘ) ∧ₘ (⟨(left)₁ₘ, (right)₁ₘ⟩ₘ ∈ₘ secondRelation))
/--
词典序积的点态成员条件。
该定义作为 `membership_specification` 的单元素 body 使用，因此外层当前元素是
`bₛ#2`，两个存在量词分别引入候选的左右积点 `bₛ#1` 与 `bₛ#0`。
-/
def order_product_member_condition (firstRelation firstCarrier secondRelation secondCarrier : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∃ₘ[SetSort.set], ((bₛ#1 ∈ₘ (firstCarrier ×ₘ secondCarrier)) ∧ₘ (bₛ#0 ∈ₘ (firstCarrier ×ₘ secondCarrier))) ∧ₘ ((bₛ#2 ≐ₘ ⟨bₛ#1, bₛ#0⟩ₘ) ∧ₘ
          order_product_coordinate_condition
            firstRelation secondRelation bₛ#1 bₛ#0)
/-- 词典序积关系的成员规格。 -/
def order_product_spec (firstRelation firstCarrier secondRelation secondCarrier candidate : SetTerm) :
    SetFormula :=
  membership_specification
    candidate (order_product_member_condition
      firstRelation firstCarrier secondRelation secondCarrier)
/-- 对固定参数断言词典序积关系存在。 -/
def order_product_exists (firstRelation firstCarrier secondRelation secondCarrier : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    order_product_spec
      firstRelation firstCarrier
      secondRelation secondCarrier bₛ#1
/--
词典序积所需的闭分离实例。
该公理对应文献 `Z₂[ψ₂₁]` 的现代特化：母集固定为积载体的笛卡尔平方，具体
成员条件由 `order_product_member_condition` 给出。
-/
def order_product_separation_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          order_product_exists (x#0) (x#1) (x#2) (x#3)
/-- 词典序积函数符号的开放定义实例。文献索引为 `Ξ₅₀`。 -/
def order_product_definition_instance (firstRelation firstCarrier secondRelation secondCarrier candidate : SetTerm) :
    SetFormula := (is_linear_order_formula firstRelation firstCarrier ∧ₘ
      is_linear_order_formula secondRelation secondCarrier) ⟶ₘ ((candidate ≐ₘ
        ord_prodₘ(
          firstRelation, firstCarrier,
          secondRelation, secondCarrier)) ↔ₘ
      order_product_spec
        firstRelation firstCarrier
        secondRelation secondCarrier candidate)
/-- 词典序积函数符号定义公理。 -/
def order_product_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4],
            order_product_definition_instance (x#0) (x#1) (x#2) (x#3) (x#4)
/-! ## 理论组合 -/
/--
自然离散线性序代数的基础理论。
文献中的 `Γ₁₉` 在现代接口中由 `foundation_theory` 承担；纸面 `Z₂[ψ₂₀]`
不再单独注入，因为序和规范项已经由现有并集与笛卡尔积函数符号直接表达。
-/
def natural_order_algebra_base_theory : SetTheory :=
  foundation_theory
/-- 加入线性序和函数符号后的理论。 -/
def order_sum_theory : SetTheory :=
  Theory.insert
    order_sum_definition_axiom
    natural_order_algebra_base_theory
/-- 加入词典序积分离实例后的理论。 -/
def order_product_separation_theory : SetTheory :=
  Theory.insert
    order_product_separation_axiom
    order_sum_theory
/-- 加入词典序积函数符号后的理论。 -/
def order_product_theory : SetTheory :=
  Theory.insert
    order_product_definition_axiom
    order_product_separation_theory
/-! ## proof-carrying 项边界 -/
/-- 线性序和的规范见证满足 proof-carrying 项边界。 -/
theorem order_sum_witness_admissible (firstRelation firstCarrier secondRelation secondCarrier : SetTerm)
    (hFirstRelation : Term.Admissible firstRelation SetSort.set) (hFirstCarrier : Term.Admissible firstCarrier SetSort.set)
    (hSecondRelation : Term.Admissible secondRelation SetSort.set) (hSecondCarrier : Term.Admissible secondCarrier SetSort.set) :
    Term.Admissible (order_sum_witness
        firstRelation firstCarrier
        secondRelation secondCarrier)
      SetSort.set :=
  binary_union_term_admissible (firstRelation ∪ₘ secondRelation) (firstCarrier ×ₘ secondCarrier) (binary_union_term_admissible
      firstRelation secondRelation
      hFirstRelation hSecondRelation) (cartesian_product_term_admissible
      firstCarrier secondCarrier
      hFirstCarrier hSecondCarrier)
/-- 线性序和项满足 proof-carrying 项边界。 -/
theorem order_sum_term_admissible (firstRelation firstCarrier secondRelation secondCarrier : SetTerm)
    (hFirstRelation : Term.Admissible firstRelation SetSort.set) (hFirstCarrier : Term.Admissible firstCarrier SetSort.set)
    (hSecondRelation : Term.Admissible secondRelation SetSort.set) (hSecondCarrier : Term.Admissible secondCarrier SetSort.set) :
    Term.Admissible (ord_sumₘ(
        firstRelation, firstCarrier,
        secondRelation, secondCarrier))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .orderSum [⟨firstRelation, by assumption⟩, ⟨firstCarrier, by assumption⟩, ⟨secondRelation, by assumption⟩, ⟨secondCarrier, by assumption⟩]
      (by rfl) (by rfl)
/-- 词典序积项满足 proof-carrying 项边界。 -/
theorem order_product_term_admissible (firstRelation firstCarrier secondRelation secondCarrier : SetTerm)
    (hFirstRelation : Term.Admissible firstRelation SetSort.set) (hFirstCarrier : Term.Admissible firstCarrier SetSort.set)
    (hSecondRelation : Term.Admissible secondRelation SetSort.set) (hSecondCarrier : Term.Admissible secondCarrier SetSort.set) :
    Term.Admissible (ord_prodₘ(
        firstRelation, firstCarrier,
        secondRelation, secondCarrier))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .orderProduct [⟨firstRelation, by assumption⟩, ⟨firstCarrier, by assumption⟩, ⟨secondRelation, by assumption⟩, ⟨secondCarrier, by assumption⟩]
      (by rfl) (by rfl)
/-! ## 公共良构性边界 -/
theorem order_sum_definition_axiom_admissible :
    Formula.Admissible
      order_sum_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem order_product_definition_axiom_admissible :
    Formula.Admissible
      order_product_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem order_product_separation_axiom_admissible :
    Formula.Admissible
      order_product_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem natural_order_algebra_base_theory_admissible :
    Theory.Admissible
      natural_order_algebra_base_theory :=
  foundation_theory_admissible
theorem order_sum_theory_admissible :
    Theory.Admissible order_sum_theory :=
  Theory.admissible_insert
    order_sum_definition_axiom_admissible
    natural_order_algebra_base_theory_admissible
theorem order_product_separation_theory_admissible :
    Theory.Admissible order_product_separation_theory :=
  Theory.admissible_insert
    order_product_separation_axiom_admissible
    order_sum_theory_admissible
theorem order_product_theory_admissible :
    Theory.Admissible order_product_theory :=
  Theory.admissible_insert
    order_product_definition_axiom_admissible
    order_product_separation_theory_admissible
/-! ## 闭理论边界 -/
@[derive_close_sentence]
theorem natural_order_algebra_base_theory_sentence
    {formula : SetFormula} (hFormula : natural_order_algebra_base_theory formula) :
    Formula.Sentence formula :=
  foundation_theory_sentence hFormula
@[derive_close_sentence]
theorem order_sum_theory_sentence
    {formula : SetFormula} (hFormula : order_sum_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact order_sum_definition_axiom_admissible
    · native_decide
  · exact natural_order_algebra_base_theory_sentence hFormula
@[derive_close_sentence]
theorem order_product_separation_theory_sentence
    {formula : SetFormula} (hFormula : order_product_separation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact order_product_separation_axiom_admissible
    · native_decide
  · exact order_sum_theory_sentence hFormula
@[derive_close_sentence]
theorem order_product_theory_sentence
    {formula : SetFormula} (hFormula : order_product_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact order_product_definition_axiom_admissible
    · native_decide
  · exact order_product_separation_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem foundation_theory_subset_natural_order_algebra_base_theory
    {formula : SetFormula} (hFormula : foundation_theory formula) :
    natural_order_algebra_base_theory formula :=
  hFormula
theorem natural_order_algebra_base_theory_subset_order_sum_theory
    {formula : SetFormula} (hFormula : natural_order_algebra_base_theory formula) :
    order_sum_theory formula :=
  Or.inr hFormula
theorem order_sum_theory_subset_order_product_separation_theory
    {formula : SetFormula} (hFormula : order_sum_theory formula) :
    order_product_separation_theory formula :=
  Or.inr hFormula
theorem order_product_separation_theory_subset_order_product_theory
    {formula : SetFormula} (hFormula : order_product_separation_theory formula) :
    order_product_theory formula :=
  Or.inr hFormula
/-!
## 待证明定理索引
本轮图片中的结论暂留为后续证明任务：
* 定理 3.32：不交线性序的序和存在性与唯一性；
* 定理 3.33：序和定义合同，以及线性序、良序、自然离散线性序闭性；
* 问题 3.3：序和一般不交换；
* 定理 3.34：序和对关系、序同构和序同构关系的闭性；
* 定理 3.35：线性序积存在性；
* 定理 3.36：词典序积特征定理；
* 推论 3.8：词典序积关系的直接成员刻画；
* 定理 3.37：词典序积的线性序、良序和自然离散线性序闭性；
* 定理 3.38：词典序积对映射、满射、单射和双射的闭性。
纸面 `ψ₂₀`、`ψ₂₂`、`ψ₂₃`、`ψ₂₄` 与 `Θ₈₈₅`、`Θ₉₆₄` 只服务于上述定理的
分离与复合证明，不进入公共签名或理论公理。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
