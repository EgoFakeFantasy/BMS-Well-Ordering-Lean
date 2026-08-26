import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.HereditarilyFinite
/-!
# 有限序列合并与有限折叠
本模块是一阶形式系统层使用的有限序列基础设施。集合论模块只提供对象语言中的
函数、自然数、有限序列空间与集合构造；这里进一步加入：
* 两个任意有限序列的顺序合并；
* 给定源集上的非空有限序列空间；
* 对有限序列族作顺序合并的有限折叠。
文献中的 `XuLe`、`YXXL`、`Ξ₁₀₀`、`Ξ₁₀₁`、`Ξ₁₀₃`、`ψ₁₃₃`、
`Θ₂₀₆₀`、`*` 与 `⊕` 仅作为本注释中的检索索引。公共接口使用
`finite_sequence_*` 命名，并以 `⌢ₘ`、`seq₊_spaceₘ`、`flattenₘ`
表示相应对象语言项。
有限折叠采用空序列作初值的累积器。这样无需文献为一元序列单独选择特殊函数
`f₀`，并且递归规格直接覆盖空族、单元素族与一般有限族。
本模块只建立定义公理、理论链、记号与 proof-carrying 良构性边界。合并的
存在唯一性、结合律、空间闭性以及折叠递归定理留给后续证明模块。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
/-! ## 有限序列与顺序合并 -/
/--
一个集合编码对象是有限序列，当且仅当它是函数，且定义域是某个自然数。
这里不固定值域，因而可同时服务于符号序列、公式序列和有限序列族。
-/
def finite_sequence_condition (sequence : SetTerm) :
    SetFormula :=
  is_function_formula sequence ∧ₘ (domₘ(sequence) ∈ₘ ωₘ)
/-- 合并结果在左序列定义域上的点态条件。 -/
def finite_sequence_concatenation_left_condition (left candidate index : SetTerm) :
    SetFormula := (index ∈ₘ domₘ(left)) ⟶ₘ ((index ∈ₘ domₘ(candidate)) ∧ₘ ((candidate ·ₘ index) ≐ₘ (left ·ₘ index)))
/-- 合并结果在平移后的右序列定义域上的点态条件。 -/
def finite_sequence_concatenation_right_condition (left right candidate index : SetTerm) :
    SetFormula := (index ∈ₘ domₘ(right)) ⟶ₘ ((((domₘ(left) +ₘ index) ∈ₘ
        domₘ(candidate))) ∧ₘ ((candidate ·ₘ (domₘ(left) +ₘ index)) ≐ₘ (right ·ₘ index)))
/--
`candidate` 是 `left` 与 `right` 的顺序合并。
定义域长度为两段长度之和；前段照抄 `left`，后段将 `right` 的指标平移
`dom(left)` 后照抄。
-/
def finite_sequence_concatenation_spec (left right candidate : SetTerm) :
    SetFormula :=
  finite_sequence_condition candidate ∧ₘ ((domₘ(candidate) ≐ₘ (domₘ(left) +ₘ domₘ(right))) ∧ₘ ((∀ₘ[SetSort.set],
          finite_sequence_concatenation_left_condition
            left candidate bₛ#0) ∧ₘ (∀ₘ[SetSort.set],
          finite_sequence_concatenation_right_condition
            left right candidate bₛ#0)))
/-- 有限序列顺序合并函数符号的开放定义实例；文献索引为 `Ξ₁₀₀`、`Ξ₁₀₃`。 -/
def finite_sequence_concatenation_definition_instance (left right candidate : SetTerm) :
    SetFormula := (finite_sequence_condition left ∧ₘ
      finite_sequence_condition right) ⟶ₘ ((candidate ≐ₘ (left ⌢ₘ right)) ↔ₘ
      finite_sequence_concatenation_spec
        left right candidate)
/-- 有限序列顺序合并定义公理。 -/
def finite_sequence_concatenation_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        finite_sequence_concatenation_definition_instance (x#0) (x#1) (x#2)
/-! ## 非空有限序列空间 -/
/-- `sequence` 是取值于 `source` 的非空有限序列。 -/
def nonempty_finite_sequence_member_condition (source sequence : SetTerm) :
    SetFormula := (sequence ∈ₘ seq_spaceₘ(source)) ∧ₘ (numₘ(0) ∈ₘ domₘ(sequence))
/-- `candidate` 收集所有取值于 `source` 的非空有限序列。 -/
def nonempty_finite_sequence_space_spec (source candidate : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ candidate) ↔ₘ
      nonempty_finite_sequence_member_condition
        source bₛ#0
/-- 对固定源集断言非空有限序列空间存在。 -/
def nonempty_finite_sequence_space_separation_exists (source : SetTerm) :
    SetFormula :=
  ∃ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ bₛ#1) ↔ₘ ((bₛ#0 ∈ₘ seq_spaceₘ(source)) ∧ₘ (numₘ(0) ∈ₘ domₘ(bₛ#0)))
/-- 任意源集上的非空有限序列空间分离公理。 -/
def nonempty_finite_sequence_space_separation_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    nonempty_finite_sequence_space_separation_exists (x#0)
/-- 非空有限序列空间函数符号的开放定义实例；文献索引为 `Ξ₁₀₁`。 -/
def nonempty_finite_sequence_space_definition_instance (source candidate : SetTerm) :
    SetFormula := (source ≠ₘ ∅ₘ) ⟶ₘ ((candidate ≐ₘ seq₊_spaceₘ(source)) ↔ₘ
      nonempty_finite_sequence_space_spec
        source candidate)
/-- 非空有限序列空间定义公理。 -/
def nonempty_finite_sequence_space_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      nonempty_finite_sequence_space_definition_instance (x#0) (x#1)
/-! ## 有限序列族的有限折叠 -/
/-- `family` 是一个以自然数为定义域的有限函数，并且每个值仍是有限序列。 -/
def finite_sequence_family_condition (family : SetTerm) :
    SetFormula :=
  finite_sequence_condition family ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ domₘ(family)) ⟶ₘ
        finite_sequence_condition (family ·ₘ bₛ#0))
/-- 累积器在指标 `index` 处执行一次序列合并。 -/
def finite_sequence_flatten_step_condition (family accumulator index : SetTerm) :
    SetFormula := (index ∈ₘ domₘ(family)) ⟶ₘ ((accumulator ·ₘ Sₘ(index)) ≐ₘ ((accumulator ·ₘ index) ⌢ₘ (family ·ₘ index)))
/--
有限折叠的规格。
存在一个定义域为 `S(dom(family))` 的累积器：零位为空序列，每一步把当前结果
与 `family(index)` 合并，最终结果取累积器在 `dom(family)` 处的值。
-/
def finite_sequence_flatten_spec (family result : SetTerm) :
    SetFormula :=
  finite_sequence_condition result ∧ₘ (∃ₘ[SetSort.set],
      finite_sequence_condition bₛ#0 ∧ₘ ((domₘ(bₛ#0) ≐ₘ Sₘ(domₘ(family))) ∧ₘ (((bₛ#0 ·ₘ numₘ(0)) ≐ₘ ∅ₘ) ∧ₘ ((∀ₘ[SetSort.set],
                finite_sequence_flatten_step_condition
                  family bₛ#1 bₛ#0) ∧ₘ (result ≐ₘ (bₛ#0 ·ₘ domₘ(family)))))))
/-- 有限序列族折叠函数符号的开放定义实例；文献符号 `⊕` 仅保留为索引。 -/
def finite_sequence_flatten_definition_instance (family result : SetTerm) :
    SetFormula :=
  finite_sequence_family_condition family ⟶ₘ ((result ≐ₘ flattenₘ(family)) ↔ₘ
      finite_sequence_flatten_spec family result)
/-- 有限序列族折叠定义公理。 -/
def finite_sequence_flatten_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      finite_sequence_flatten_definition_instance (x#0) (x#1)
/-! ## 理论组合 -/
/-- 加入有限序列顺序合并后的理论。 -/
def finite_sequence_concatenation_theory :
    SetTheory :=
  Theory.insert
    finite_sequence_concatenation_definition_axiom
    hereditarily_finite_theory
/-- 加入非空有限序列空间分离实例后的理论。 -/
def nonempty_finite_sequence_space_separation_theory :
    SetTheory :=
  Theory.insert
    nonempty_finite_sequence_space_separation_axiom
    finite_sequence_concatenation_theory
/-- 加入非空有限序列空间函数符号后的理论。 -/
def nonempty_finite_sequence_space_theory :
    SetTheory :=
  Theory.insert
    nonempty_finite_sequence_space_definition_axiom
    nonempty_finite_sequence_space_separation_theory
/-- 加入有限序列族折叠函数符号后的理论。 -/
def finite_sequence_flatten_theory :
    SetTheory :=
  Theory.insert
    finite_sequence_flatten_definition_axiom
    nonempty_finite_sequence_space_theory
/-- 一阶形式系统有限序列层的稳定理论入口。 -/
def finite_sequence_formal_system_theory :
    SetTheory :=
  finite_sequence_flatten_theory
/-! ## proof-carrying 项边界 -/
theorem finite_sequence_concatenation_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (left ⌢ₘ right) SetSort.set := by
  simpa using
    set_function_application_admissible
      .finiteSequenceConcatenation [⟨left, by assumption⟩, ⟨right, by assumption⟩]
      (by rfl) (by rfl)
/-- 有限序列条件保持公式 admissibility。 -/
theorem finite_sequence_condition_admissible (sequence : SetTerm) (hSequence : Term.Admissible
      sequence SetSort.set) :
    Formula.Admissible (finite_sequence_condition sequence) := by
  exact Formula.Admissible.conj (is_function_formula_admissible hSequence) (membership_formula_admissible (domain_term_admissible sequence hSequence)
      omega_term_admissible)
/-- 两个参数的已证明等式可组合为有限序列拼接项等式。 -/
theorem finite_sequence_concatenation_term_congr_of_equalities
    {T : SetTheory} {Γ : Context signature} (left_first right_first left_second right_second : SetTerm) (hLeftFirst : Term.Admissible left_first SetSort.set)
    (hRightFirst : Term.Admissible right_first SetSort.set) (hLeftSecond : Term.Admissible left_second SetSort.set)
    (hRightSecond : Term.Admissible right_second SetSort.set) (hFirstEquality : Γ ⊢ₘ[T] left_first ≐ₘ right_first)
    (hSecondEquality : Γ ⊢ₘ[T] left_second ≐ₘ right_second) :
    Γ ⊢ₘ[T] (left_first ⌢ₘ left_second) ≐ₘ (right_first ⌢ₘ right_second) := by
  exact Metatheory.Derives.binary_term_constructor_congr_of_equalities
    (fun left right => left ⌢ₘ right)
    (fun left right hLeft hRight =>
      finite_sequence_concatenation_term_admissible
        left right hLeft hRight)
    (by intros; simp [Term.substituteFree])
    left_first right_first left_second right_second
    hLeftFirst hRightFirst hLeftSecond hRightSecond
    hFirstEquality hSecondEquality
theorem nonempty_finite_sequence_space_term_admissible (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    Term.Admissible (seq₊_spaceₘ(source))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .nonemptyFiniteSequenceSpace [⟨source, by assumption⟩]
      (by rfl) (by rfl)
theorem finite_sequence_flatten_term_admissible (sequence : SetTerm) (hSequence : Term.Admissible sequence SetSort.set) :
    Term.Admissible (flattenₘ(sequence))
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .finiteSequenceFlatten [⟨sequence, by assumption⟩]
      (by rfl) (by rfl)
/-! ## 良构性与理论边界 -/
theorem finite_sequence_concatenation_definition_axiom_admissible :
    Formula.Admissible
      finite_sequence_concatenation_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem nonempty_finite_sequence_space_separation_axiom_admissible :
    Formula.Admissible
      nonempty_finite_sequence_space_separation_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem nonempty_finite_sequence_space_definition_axiom_admissible :
    Formula.Admissible
      nonempty_finite_sequence_space_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_sequence_flatten_definition_axiom_admissible :
    Formula.Admissible
      finite_sequence_flatten_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_sequence_concatenation_theory_admissible :
    Theory.Admissible finite_sequence_concatenation_theory :=
  Theory.admissible_insert
    finite_sequence_concatenation_definition_axiom_admissible
    hereditarily_finite_theory_admissible
theorem nonempty_finite_sequence_space_separation_theory_admissible :
    Theory.Admissible
      nonempty_finite_sequence_space_separation_theory :=
  Theory.admissible_insert
    nonempty_finite_sequence_space_separation_axiom_admissible
    finite_sequence_concatenation_theory_admissible
theorem nonempty_finite_sequence_space_theory_admissible :
    Theory.Admissible
      nonempty_finite_sequence_space_theory :=
  Theory.admissible_insert
    nonempty_finite_sequence_space_definition_axiom_admissible
    nonempty_finite_sequence_space_separation_theory_admissible
theorem finite_sequence_flatten_theory_admissible :
    Theory.Admissible finite_sequence_flatten_theory :=
  Theory.admissible_insert
    finite_sequence_flatten_definition_axiom_admissible
    nonempty_finite_sequence_space_theory_admissible
theorem finite_sequence_formal_system_theory_admissible :
    Theory.Admissible finite_sequence_formal_system_theory :=
  finite_sequence_flatten_theory_admissible
/-! ## 闭理论边界 -/
@[derive_close_sentence]
theorem finite_sequence_concatenation_theory_sentence
    {formula : SetFormula} (hFormula : finite_sequence_concatenation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact finite_sequence_concatenation_definition_axiom_admissible
    · native_decide
  · exact hereditarily_finite_theory_sentence hFormula
@[derive_close_sentence]
theorem nonempty_finite_sequence_space_separation_theory_sentence
    {formula : SetFormula} (hFormula :
      nonempty_finite_sequence_space_separation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact nonempty_finite_sequence_space_separation_axiom_admissible
    · native_decide
  · exact finite_sequence_concatenation_theory_sentence hFormula
@[derive_close_sentence]
theorem nonempty_finite_sequence_space_theory_sentence
    {formula : SetFormula} (hFormula : nonempty_finite_sequence_space_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact nonempty_finite_sequence_space_definition_axiom_admissible
    · native_decide
  · exact
      nonempty_finite_sequence_space_separation_theory_sentence
        hFormula
@[derive_close_sentence]
theorem finite_sequence_flatten_theory_sentence
    {formula : SetFormula} (hFormula : finite_sequence_flatten_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact finite_sequence_flatten_definition_axiom_admissible
    · native_decide
  · exact nonempty_finite_sequence_space_theory_sentence hFormula
@[derive_close_sentence]
theorem finite_sequence_formal_system_theory_sentence
    {formula : SetFormula} (hFormula : finite_sequence_formal_system_theory formula) :
    Formula.Sentence formula :=
  finite_sequence_flatten_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem hereditarily_finite_theory_subset_finite_sequence_concatenation_theory
    {formula : SetFormula} (hFormula : hereditarily_finite_theory formula) :
    finite_sequence_concatenation_theory formula :=
  Or.inr hFormula
theorem finite_sequence_concatenation_theory_subset_nonempty_sequence_separation_theory
    {formula : SetFormula} (hFormula : finite_sequence_concatenation_theory formula) :
    nonempty_finite_sequence_space_separation_theory formula :=
  Or.inr hFormula
theorem nonempty_sequence_separation_theory_subset_nonempty_sequence_space_theory
    {formula : SetFormula} (hFormula :
      nonempty_finite_sequence_space_separation_theory formula) :
    nonempty_finite_sequence_space_theory formula :=
  Or.inr hFormula
theorem nonempty_sequence_space_theory_subset_finite_sequence_flatten_theory
    {formula : SetFormula} (hFormula : nonempty_finite_sequence_space_theory formula) :
    finite_sequence_flatten_theory formula :=
  Or.inr hFormula
/-! ## 待证明定理索引 -/
/-!
后续证明层按需承载以下内容：
* 有限序列顺序合并的存在性、唯一性与点态求值合同；
* `seq_spaceₘ(source)` 及 `seq₊_spaceₘ(source)` 对合并的闭性；
* 合并结合律，以及文献定义 9.1、9.2、9.5 的闭式接口；
* `flattenₘ` 的存在唯一性、空族/单元素族递归式和结果闭性；
* 公式、项、证明对象等具体语法对象的有限序列空间实例。
这些定理只消费本模块的定义公理，不把文献一次性的变量编号或递归构造过程
写进公共 API。
-/
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
