import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.FunctionProperties
/-!
# 自然离散线性序
本模块建立自然离散线性序章节的对象语言基础设施。线性序、序同构、序同构关系、
序嵌入、序可嵌入关系以及自然离散线性序都使用现代公共命名。
文献中的 `XiXn`、`TGYS`、`XuTG`、`QRYS`、`XuQR`、`Zrlx` 与
`Θ_excd`、`Θ_exbj`、`Θ_exxb`、`Θ₃₇`、`Θ₃₈` 只保留为注释索引。
本模块不提前声明截图中的引理和定理；它只提供公式规格、定义公理、理论链、
闭句边界与 proof-carrying 良构性接口。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 线性序 -/
/-- 线性序的自反排除条件。 -/
def linear_order_irreflexive_condition (relation carrier : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ carrier) ⟶ₘ
      ¬ₘ (⟨bₛ#0, bₛ#0⟩ₘ ∈ₘ relation)
/--
线性序的传递条件。文献索引为 `Θ_excd`。
-/
def linear_order_transitive_condition (relation carrier : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set],
    ∀ₘ[SetSort.set],
      ∀ₘ[SetSort.set], ((bₛ#2 ∈ₘ carrier) ∧ₘ ((bₛ#1 ∈ₘ carrier) ∧ₘ (bₛ#0 ∈ₘ carrier))) ⟶ₘ (((⟨bₛ#2, bₛ#1⟩ₘ ∈ₘ relation) ∧ₘ (⟨bₛ#1, bₛ#0⟩ₘ ∈ₘ relation)) ⟶ₘ
            (⟨bₛ#2, bₛ#0⟩ₘ ∈ₘ relation))
/--
线性序的可比性条件。文献索引为 `Θ_exbj`。
在自反排除条件下，它等价于不同元素之间必有一个方向成立。
-/
def linear_order_connex_condition (relation carrier : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set],
    ∀ₘ[SetSort.set], ((bₛ#1 ∈ₘ carrier) ∧ₘ (bₛ#0 ∈ₘ carrier)) ⟶ₘ (¬ₘ (⟨bₛ#1, bₛ#0⟩ₘ ∈ₘ relation) ⟶ₘ (¬ₘ (bₛ#1 ≐ₘ bₛ#0) ⟶ₘ (⟨bₛ#0, bₛ#1⟩ₘ ∈ₘ relation)))
/-- `relation` 在 `carrier` 上构成严格线性序。文献索引为 `XiXn`。 -/
def is_linear_order_condition (relation carrier : SetTerm) :
    SetFormula :=
  is_relation_formula relation ∧ₘ ((relation ⊆ₘ (carrier ×ₘ carrier)) ∧ₘ ((linear_order_irreflexive_condition relation carrier ∧ₘ
          linear_order_transitive_condition relation carrier) ∧ₘ
        linear_order_connex_condition relation carrier))
/-- 线性序谓词的开放定义实例。 -/
def is_linear_order_definition_instance (relation carrier : SetTerm) :
    SetFormula :=
  is_linear_order_formula relation carrier ↔ₘ
    is_linear_order_condition relation carrier
/-- 线性序谓词定义公理。 -/
def is_linear_order_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      is_linear_order_definition_instance (x#0) (x#1)
/-! ## 序同构与序嵌入 -/
/--
序保持条件。文献索引为 `Θ_exxb`。
它把源序上的有序对与目标序上函数值的有序对逐点对应起来。
-/
def order_preservation_condition (function sourceRelation sourceCarrier targetRelation : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set],
    ∀ₘ[SetSort.set], ((bₛ#1 ∈ₘ sourceCarrier) ∧ₘ (bₛ#0 ∈ₘ sourceCarrier)) ⟶ₘ ((⟨bₛ#1, bₛ#0⟩ₘ ∈ₘ sourceRelation) ↔ₘ (⟨function ·ₘ bₛ#1, function ·ₘ bₛ#0⟩ₘ ∈ₘ
            targetRelation))
/-- `function` 是两个线性序之间的序同构映射。文献索引为 `TGYS`。 -/
def is_order_isomorphism_condition (function sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  is_linear_order_formula sourceRelation sourceCarrier ∧ₘ ((is_linear_order_formula targetRelation targetCarrier ∧ₘ
        (is_bijection_formula function sourceCarrier targetCarrier)) ∧ₘ
      order_preservation_condition
        function sourceRelation sourceCarrier targetRelation)
/-- 序同构映射谓词的开放定义实例。 -/
def is_order_isomorphism_definition_instance (function sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  is_order_isomorphism_formula
      function sourceRelation sourceCarrier targetRelation targetCarrier ↔ₘ
    is_order_isomorphism_condition
      function sourceRelation sourceCarrier targetRelation targetCarrier
/-- 序同构映射谓词定义公理。 -/
def is_order_isomorphism_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4],
            is_order_isomorphism_definition_instance (x#0) (x#1) (x#2) (x#3) (x#4)
/-- 两个线性序关系同构。文献索引为 `XuTG`。 -/
def is_order_isomorphic_condition (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    is_order_isomorphism_formula
      bₛ#0 sourceRelation sourceCarrier targetRelation targetCarrier
/-- 序同构关系谓词的开放定义实例。 -/
def is_order_isomorphic_definition_instance (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  is_order_isomorphic_formula
      sourceRelation sourceCarrier targetRelation targetCarrier ↔ₘ
    is_order_isomorphic_condition
      sourceRelation sourceCarrier targetRelation targetCarrier
/-- 序同构关系谓词定义公理。 -/
def is_order_isomorphic_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          is_order_isomorphic_definition_instance (x#0) (x#1) (x#2) (x#3)
/-- `function` 是两个线性序之间的序嵌入。文献索引为 `QRYS`。 -/
def is_order_embedding_condition (function sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  is_linear_order_formula sourceRelation sourceCarrier ∧ₘ ((is_linear_order_formula targetRelation targetCarrier ∧ₘ
        (is_injective_formula function sourceCarrier targetCarrier)) ∧ₘ
      order_preservation_condition
        function sourceRelation sourceCarrier targetRelation)
/-- 序嵌入映射谓词的开放定义实例。 -/
def is_order_embedding_definition_instance (function sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  is_order_embedding_formula
      function sourceRelation sourceCarrier targetRelation targetCarrier ↔ₘ
    is_order_embedding_condition
      function sourceRelation sourceCarrier targetRelation targetCarrier
/-- 序嵌入映射谓词定义公理。 -/
def is_order_embedding_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          ∀ₘ[SetSort.set, 4],
            is_order_embedding_definition_instance (x#0) (x#1) (x#2) (x#3) (x#4)
/-- 两个线性序关系可嵌入。文献索引为 `XuQR`。 -/
def is_order_embeddable_condition (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    is_order_embedding_formula
      bₛ#0 sourceRelation sourceCarrier targetRelation targetCarrier
/-- 序可嵌入关系谓词的开放定义实例。 -/
def is_order_embeddable_definition_instance (sourceRelation sourceCarrier targetRelation targetCarrier : SetTerm) :
    SetFormula :=
  is_order_embeddable_formula
      sourceRelation sourceCarrier targetRelation targetCarrier ↔ₘ
    is_order_embeddable_condition
      sourceRelation sourceCarrier targetRelation targetCarrier
/-- 序可嵌入关系谓词定义公理。 -/
def is_order_embeddable_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        ∀ₘ[SetSort.set, 3],
          is_order_embeddable_definition_instance (x#0) (x#1) (x#2) (x#3)
/-! ## 自然离散线性序 -/
/-- 非空子集存在最大元的条件。文献索引为 `Θ₃₇`。 -/
def natural_order_greatest_element_condition (relation carrier : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], ((bₛ#0 ∈ₘ 𝒫ₘ(carrier)) ∧ₘ (¬ₘ (bₛ#0 ≐ₘ ∅ₘ))) ⟶ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#2) ⟶ₘ
              ((¬ₘ (bₛ#1 ≐ₘ bₛ#0)) ⟶ₘ (⟨bₛ#1, bₛ#0⟩ₘ ∈ₘ relation))))
/-- 非空子集存在最小元的条件。文献索引为 `Θ₃₈`。 -/
def natural_order_least_element_condition (relation carrier : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], ((bₛ#0 ∈ₘ 𝒫ₘ(carrier)) ∧ₘ (¬ₘ (bₛ#0 ≐ₘ ∅ₘ))) ⟶ₘ (∃ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#2) ⟶ₘ
              ((¬ₘ (bₛ#1 ≐ₘ bₛ#0)) ⟶ₘ (⟨bₛ#0, bₛ#1⟩ₘ ∈ₘ relation))))
/-- 自然离散线性序条件。文献索引为 `Zrlx`。 -/
def is_natural_discrete_linear_order_condition (relation carrier : SetTerm) :
    SetFormula :=
  is_linear_order_formula relation carrier ∧ₘ (natural_order_greatest_element_condition relation carrier ∧ₘ
      natural_order_least_element_condition relation carrier)
/-- 自然离散线性序谓词的开放定义实例。 -/
def is_natural_discrete_linear_order_definition_instance (relation carrier : SetTerm) :
    SetFormula :=
  is_natural_discrete_linear_order_formula relation carrier ↔ₘ
    is_natural_discrete_linear_order_condition relation carrier
/-- 自然离散线性序谓词定义公理。 -/
def is_natural_discrete_linear_order_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      is_natural_discrete_linear_order_definition_instance (x#0) (x#1)
/-! ## 理论组合 -/
/-- 在线性序谓词定义上加入线性序基础。 -/
def linear_order_theory : SetTheory :=
  Theory.insert
    is_linear_order_definition_axiom
    membership_relation_operator_theory
/-- 加入序同构映射谓词。 -/
def order_isomorphism_theory : SetTheory :=
  Theory.insert
    is_order_isomorphism_definition_axiom
    linear_order_theory
/-- 加入序同构关系谓词。 -/
def order_isomorphic_theory : SetTheory :=
  Theory.insert
    is_order_isomorphic_definition_axiom
    order_isomorphism_theory
/-- 加入序嵌入映射谓词。 -/
def order_embedding_theory : SetTheory :=
  Theory.insert
    is_order_embedding_definition_axiom
    order_isomorphic_theory
/-- 加入序可嵌入关系谓词。 -/
def order_embeddable_theory : SetTheory :=
  Theory.insert
    is_order_embeddable_definition_axiom
    order_embedding_theory
/-- 加入自然离散线性序谓词。 -/
def natural_discrete_linear_order_theory : SetTheory :=
  Theory.insert
    is_natural_discrete_linear_order_definition_axiom
    order_embeddable_theory
/-! ## 公共良构性边界 -/
theorem is_linear_order_definition_axiom_admissible :
    Formula.Admissible
      is_linear_order_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_order_isomorphism_definition_axiom_admissible :
    Formula.Admissible
      is_order_isomorphism_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_order_isomorphic_definition_axiom_admissible :
    Formula.Admissible
      is_order_isomorphic_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_order_embedding_definition_axiom_admissible :
    Formula.Admissible
      is_order_embedding_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_order_embeddable_definition_axiom_admissible :
    Formula.Admissible
      is_order_embeddable_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_natural_discrete_linear_order_definition_axiom_admissible :
    Formula.Admissible
      is_natural_discrete_linear_order_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem linear_order_theory_admissible :
    Theory.Admissible linear_order_theory :=
  Theory.admissible_insert
    is_linear_order_definition_axiom_admissible
    membership_relation_operator_theory_admissible
theorem order_isomorphism_theory_admissible :
    Theory.Admissible order_isomorphism_theory :=
  Theory.admissible_insert
    is_order_isomorphism_definition_axiom_admissible
    linear_order_theory_admissible
theorem order_isomorphic_theory_admissible :
    Theory.Admissible order_isomorphic_theory :=
  Theory.admissible_insert
    is_order_isomorphic_definition_axiom_admissible
    order_isomorphism_theory_admissible
theorem order_embedding_theory_admissible :
    Theory.Admissible order_embedding_theory :=
  Theory.admissible_insert
    is_order_embedding_definition_axiom_admissible
    order_isomorphic_theory_admissible
theorem order_embeddable_theory_admissible :
    Theory.Admissible order_embeddable_theory :=
  Theory.admissible_insert
    is_order_embeddable_definition_axiom_admissible
    order_embedding_theory_admissible
theorem natural_discrete_linear_order_theory_admissible :
    Theory.Admissible natural_discrete_linear_order_theory :=
  Theory.admissible_insert
    is_natural_discrete_linear_order_definition_axiom_admissible
    order_embeddable_theory_admissible
/-! ## 闭理论边界 -/
@[derive_close_sentence]
theorem linear_order_theory_sentence
    {formula : SetFormula} (hFormula : linear_order_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_linear_order_definition_axiom_admissible
    · native_decide
  · exact membership_relation_operator_theory_sentence hFormula
@[derive_close_sentence]
theorem order_isomorphism_theory_sentence
    {formula : SetFormula} (hFormula : order_isomorphism_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_order_isomorphism_definition_axiom_admissible
    · native_decide
  · exact linear_order_theory_sentence hFormula
@[derive_close_sentence]
theorem order_isomorphic_theory_sentence
    {formula : SetFormula} (hFormula : order_isomorphic_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_order_isomorphic_definition_axiom_admissible
    · native_decide
  · exact order_isomorphism_theory_sentence hFormula
@[derive_close_sentence]
theorem order_embedding_theory_sentence
    {formula : SetFormula} (hFormula : order_embedding_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_order_embedding_definition_axiom_admissible
    · native_decide
  · exact order_isomorphic_theory_sentence hFormula
@[derive_close_sentence]
theorem order_embeddable_theory_sentence
    {formula : SetFormula} (hFormula : order_embeddable_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_order_embeddable_definition_axiom_admissible
    · native_decide
  · exact order_embedding_theory_sentence hFormula
@[derive_close_sentence]
theorem natural_discrete_linear_order_theory_sentence
    {formula : SetFormula} (hFormula : natural_discrete_linear_order_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_natural_discrete_linear_order_definition_axiom_admissible
    · native_decide
  · exact order_embeddable_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem membership_relation_operator_theory_subset_linear_order_theory
    {formula : SetFormula} (hFormula : membership_relation_operator_theory formula) :
    linear_order_theory formula :=
  Or.inr hFormula
theorem linear_order_theory_subset_order_isomorphism_theory
    {formula : SetFormula} (hFormula : linear_order_theory formula) :
    order_isomorphism_theory formula :=
  Or.inr hFormula
theorem order_isomorphism_theory_subset_order_isomorphic_theory
    {formula : SetFormula} (hFormula : order_isomorphism_theory formula) :
    order_isomorphic_theory formula :=
  Or.inr hFormula
theorem order_isomorphic_theory_subset_order_embedding_theory
    {formula : SetFormula} (hFormula : order_isomorphic_theory formula) :
    order_embedding_theory formula :=
  Or.inr hFormula
theorem order_embedding_theory_subset_order_embeddable_theory
    {formula : SetFormula} (hFormula : order_embedding_theory formula) :
    order_embeddable_theory formula :=
  Or.inr hFormula
theorem order_embeddable_theory_subset_natural_discrete_linear_order_theory
    {formula : SetFormula} (hFormula : order_embeddable_theory formula) :
    natural_discrete_linear_order_theory formula :=
  Or.inr hFormula
/-!
## 待证明定理索引
以下内容对应截图中的后续数学结果，当前只保留文档索引：
* 3.1：恒等映射是序同构；序同构的逆与序同构的复合仍保持序结构；
* 3.2：序嵌入的基本性质与序同构关系；
* 3.3：自然离散线性序条件的对偶性；
* 线性序谓词、序同构、序嵌入和自然离散性之间的后续派生合同。
这些结果将在本模块的定义公理和理论链之上按需使用 `prove_auto` 或手工证明。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
