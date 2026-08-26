import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.SymmetricDifference
/-!
# 基本有穷理论
本模块建立集合有穷性与基数比较的定义设施：
* `finiteₘ(set)`：集合承载某个自然离散线性序；
* `left ≈ₘ right`：两个集合之间存在双射；
* `left ≼ₘ right`：空集平凡成立，否则存在从左到右的单射；
* `left ≺ₘ right`：左侧不强于右侧，且两侧不等势；
* `dedekind_finiteₘ(set)`：集合上的每个自单射都是满射。
文献记号 `YuQn`、`|x| = |y|`、`|x| ≤ |y|`、`|x| < |y|` 只保留为索引。
严格比较直接建立在原子化的弱比较和等势关系上，避免重复展开单射、满射和空集
分支。
文献 `Ξ_DFP` 被拆成可复用的一元戴德金有限谓词，以及闭公式
`dedekind_finiteness_principle`。后者只是后续证明目标，不作为额外公理插入
`basic_finite_theory`。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 有穷性 -/
/-- 有穷集条件：存在一个以该集合为载体的自然离散线性序。 -/
def is_finite_condition (set : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    is_natural_discrete_linear_order_formula bₛ#0 set
/-- 有穷集谓词的开放定义实例；文献索引为 `Ξ₄₈`。 -/
def is_finite_definition_instance (set : SetTerm) :
    SetFormula :=
  finiteₘ(set) ↔ₘ
    is_finite_condition set
/-- 有穷集谓词定义公理。 -/
def is_finite_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_finite_definition_instance (x#0)
/-! ## 等势与基数比较 -/
/-- 两个集合等势，当且仅当存在它们之间的双射。 -/
def is_equinumerous_condition (left right : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    is_bijection_formula bₛ#0 left right
/-- 等势关系的开放定义实例；文献索引为 `Ξ₅₉`。 -/
def is_equinumerous_definition_instance (left right : SetTerm) :
    SetFormula := (left ≈ₘ right) ↔ₘ
    is_equinumerous_condition left right
/-- 等势关系定义公理。 -/
def is_equinumerous_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      is_equinumerous_definition_instance (x#0) (x#1)
/--
基数不强于条件。
空源集时条件平凡成立；非空时要求存在从 `left` 到 `right` 的单射。
这保留文献 `Ξ₆₁` 的数学强度，同时避免为唯一空映射另设分支公理。
-/
def cardinality_leq_condition (left right : SetTerm) :
    SetFormula := (left ≠ₘ ∅ₘ) ⟶ₘ (∃ₘ[SetSort.set],
      is_injective_formula bₛ#0 left right)
/-- 基数不强于关系的开放定义实例；文献索引为 `Ξ₆₁`。 -/
def cardinality_leq_definition_instance (left right : SetTerm) :
    SetFormula := (left ≼ₘ right) ↔ₘ
    cardinality_leq_condition left right
/-- 基数不强于关系定义公理。 -/
def cardinality_leq_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      cardinality_leq_definition_instance (x#0) (x#1)
/--
基数严格弱于条件。
采用文献定义 4.5 的数学表述：左侧不强于右侧，并且两者不等势。文献 `Ξ₆₀`
对空集和单射、满射的机械展开不进入公共接口。
-/
def cardinality_strict_less_condition (left right : SetTerm) :
    SetFormula := (left ≼ₘ right) ∧ₘ
    ¬ₘ (left ≈ₘ right)
/-- 基数严格弱于关系的开放定义实例；文献索引为 `Ξ₆₀`。 -/
def cardinality_strict_less_definition_instance (left right : SetTerm) :
    SetFormula := (left ≺ₘ right) ↔ₘ
    cardinality_strict_less_condition left right
/-- 基数严格弱于关系定义公理。 -/
def cardinality_strict_less_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      cardinality_strict_less_definition_instance (x#0) (x#1)
/-! ## 戴德金有限 -/
/-- 戴德金有限条件：集合上的每个自单射都是满射。 -/
def is_dedekind_finite_condition (set : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set],
    is_injective_formula bₛ#0 set set ⟶ₘ
      is_surjective_formula bₛ#0 set set
/-- 戴德金有限谓词的开放定义实例。 -/
def is_dedekind_finite_definition_instance (set : SetTerm) :
    SetFormula :=
  dedekind_finiteₘ(set) ↔ₘ
    is_dedekind_finite_condition set
/-- 戴德金有限谓词定义公理。 -/
def is_dedekind_finite_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_dedekind_finite_definition_instance (x#0)
/--
有穷集都是戴德金有限集的闭命题。
它对应文献 `Ξ_DFP`，但在现代理论链中应作为定理证明，而不是作为基本公理加入。
-/
def dedekind_finiteness_principle : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    finiteₘ(x#0) ⟶ₘ
      dedekind_finiteₘ(x#0)
/-! ## 理论组合 -/
/-- 加入有穷集谓词后的理论；对应文献 `Γ₁₈b` 的定义部分。 -/
def finite_predicate_theory : SetTheory :=
  Theory.insert
    is_finite_definition_axiom
    symmetric_difference_theory
/-- 加入等势关系后的理论。 -/
def equinumerous_predicate_theory : SetTheory :=
  Theory.insert
    is_equinumerous_definition_axiom
    finite_predicate_theory
/-- 加入基数不强于关系后的理论。 -/
def cardinality_leq_predicate_theory : SetTheory :=
  Theory.insert
    cardinality_leq_definition_axiom
    equinumerous_predicate_theory
/-- 加入基数严格弱于关系后的理论。 -/
def cardinality_strict_less_predicate_theory : SetTheory :=
  Theory.insert
    cardinality_strict_less_definition_axiom
    cardinality_leq_predicate_theory
/-- 加入戴德金有限谓词后的基本有穷理论。 -/
def dedekind_finite_predicate_theory : SetTheory :=
  Theory.insert
    is_dedekind_finite_definition_axiom
    cardinality_strict_less_predicate_theory
/-- 基本有穷理论的稳定公共入口。 -/
def basic_finite_theory : SetTheory :=
  dedekind_finite_predicate_theory
/-! ## 良构性边界 -/
theorem is_finite_definition_axiom_admissible :
    Formula.Admissible
      is_finite_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_equinumerous_definition_axiom_admissible :
    Formula.Admissible
      is_equinumerous_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem cardinality_leq_definition_axiom_admissible :
    Formula.Admissible
      cardinality_leq_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem cardinality_strict_less_definition_axiom_admissible :
    Formula.Admissible
      cardinality_strict_less_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_dedekind_finite_definition_axiom_admissible :
    Formula.Admissible
      is_dedekind_finite_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem dedekind_finiteness_principle_admissible :
    Formula.Admissible
      dedekind_finiteness_principle := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_predicate_theory_admissible :
    Theory.Admissible finite_predicate_theory :=
  Theory.admissible_insert
    is_finite_definition_axiom_admissible
    symmetric_difference_theory_admissible
theorem equinumerous_predicate_theory_admissible :
    Theory.Admissible equinumerous_predicate_theory :=
  Theory.admissible_insert
    is_equinumerous_definition_axiom_admissible
    finite_predicate_theory_admissible
theorem cardinality_leq_predicate_theory_admissible :
    Theory.Admissible cardinality_leq_predicate_theory :=
  Theory.admissible_insert
    cardinality_leq_definition_axiom_admissible
    equinumerous_predicate_theory_admissible
theorem cardinality_strict_less_predicate_theory_admissible :
    Theory.Admissible
      cardinality_strict_less_predicate_theory :=
  Theory.admissible_insert
    cardinality_strict_less_definition_axiom_admissible
    cardinality_leq_predicate_theory_admissible
theorem dedekind_finite_predicate_theory_admissible :
    Theory.Admissible
      dedekind_finite_predicate_theory :=
  Theory.admissible_insert
    is_dedekind_finite_definition_axiom_admissible
    cardinality_strict_less_predicate_theory_admissible
theorem basic_finite_theory_admissible :
    Theory.Admissible basic_finite_theory :=
  dedekind_finite_predicate_theory_admissible
/-! ## 闭理论边界 -/
@[derive_close_sentence]
theorem finite_predicate_theory_sentence
    {formula : SetFormula} (hFormula : finite_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_finite_definition_axiom_admissible
    · native_decide
  · exact symmetric_difference_theory_sentence hFormula
@[derive_close_sentence]
theorem equinumerous_predicate_theory_sentence
    {formula : SetFormula} (hFormula : equinumerous_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_equinumerous_definition_axiom_admissible
    · native_decide
  · exact finite_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem cardinality_leq_predicate_theory_sentence
    {formula : SetFormula} (hFormula : cardinality_leq_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact cardinality_leq_definition_axiom_admissible
    · native_decide
  · exact equinumerous_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem cardinality_strict_less_predicate_theory_sentence
    {formula : SetFormula} (hFormula : cardinality_strict_less_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact cardinality_strict_less_definition_axiom_admissible
    · native_decide
  · exact cardinality_leq_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem dedekind_finite_predicate_theory_sentence
    {formula : SetFormula} (hFormula : dedekind_finite_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_dedekind_finite_definition_axiom_admissible
    · native_decide
  · exact cardinality_strict_less_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem basic_finite_theory_sentence
    {formula : SetFormula} (hFormula : basic_finite_theory formula) :
    Formula.Sentence formula :=
  dedekind_finite_predicate_theory_sentence hFormula
theorem dedekind_finiteness_principle_sentence :
    Formula.Sentence
      dedekind_finiteness_principle := by
  constructor
  · exact dedekind_finiteness_principle_admissible
  · native_decide
/-! ## 理论嵌入 -/
theorem symmetric_difference_theory_subset_finite_predicate_theory
    {formula : SetFormula} (hFormula : symmetric_difference_theory formula) :
    finite_predicate_theory formula :=
  Or.inr hFormula
theorem finite_predicate_theory_subset_equinumerous_predicate_theory
    {formula : SetFormula} (hFormula : finite_predicate_theory formula) :
    equinumerous_predicate_theory formula :=
  Or.inr hFormula
theorem equinumerous_predicate_theory_subset_cardinality_leq_predicate_theory
    {formula : SetFormula} (hFormula : equinumerous_predicate_theory formula) :
    cardinality_leq_predicate_theory formula :=
  Or.inr hFormula
theorem cardinality_leq_predicate_theory_subset_cardinality_strict_less_predicate_theory
    {formula : SetFormula} (hFormula : cardinality_leq_predicate_theory formula) :
    cardinality_strict_less_predicate_theory formula :=
  Or.inr hFormula
theorem cardinality_strict_less_predicate_theory_subset_dedekind_finite_predicate_theory
    {formula : SetFormula} (hFormula : cardinality_strict_less_predicate_theory formula) :
    dedekind_finite_predicate_theory formula :=
  Or.inr hFormula
theorem dedekind_finite_predicate_theory_subset_basic_finite_theory
    {formula : SetFormula} (hFormula : dedekind_finite_predicate_theory formula) :
    basic_finite_theory formula :=
  hFormula
/-!
## 待证明定理索引
本轮截图中的结论暂不声明为已证明定理：
* 定理 4.1--4.3：有穷集对空集、单点集、后继、自然数、并、积、幂和幂集的闭性；
* 定理 4.4：等势关系的自反、对称、传递以及等式相容性；
* 定理 4.5：非空集合到任意目标集的常值映射存在；
* 定理 4.6--4.8 与推论 4.1：基数弱比较、康托尔不等式和幂集基数结论；
* 文献 `Ξ_DFP`：由有穷性推出戴德金有限性。
纸面 `ψ_cv`、`Z₂[ψ_cv]`、`ψ₆₂` 与 `Z₂[ψ₆₂]` 是具体定理证明所需的分离实例，
不属于本轮定义层。后续证明时应按需构造 proof-carrying `SetPredicate`，而不是
把这些一次性辅助式加入基础理论。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
