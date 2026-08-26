import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Successor
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.NaturalDiscreteLinearOrder
/-!
# 良序与有限自然数基础设施
本模块吸收文献中自然离散线性序之后的良序与有限数内容。
数字项不再作为十个独立的对象语言常量加入签名，而是统一递归为
`∅ₘ` 与 `Sₘ` 的项。文献中的 `0` 到 `9` 兼容合同因此只是现有项记号
的 proof-carrying 别名合同，不增加新的数学强度。
文献中的 `ZX` 与 `Ξ_sz0` 到 `Ξ_sz9` 只在注释和公共命名中作为索引；
截图中的有限数值定理暂不伪造为已证明声明。文献 `ψ₁₃` 实际描述关系像，
其分离实例归入 `OrderOperators`，不再以“初始段”误名留在本模块。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 良序 -/
/-- 良序条件：线性序加上每个非空子集都有最小元。文献索引为 `ZX`。 -/
def well_order_condition (relation carrier : SetTerm) :
    SetFormula :=
  is_linear_order_formula relation carrier ∧ₘ
    natural_order_least_element_condition relation carrier
/-- 良序谓词的开放定义实例。 -/
def well_order_definition_instance (relation carrier : SetTerm) :
    SetFormula :=
  is_well_order_formula relation carrier ↔ₘ
    well_order_condition relation carrier
/-- 良序谓词定义公理。 -/
def well_order_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      well_order_definition_instance (x#0) (x#1)
/-- 良序层理论。 -/
def well_order_theory : SetTheory :=
  Theory.insert
    well_order_definition_axiom
    natural_discrete_linear_order_theory
/-! ## 有限自然数项与文献兼容合同 -/
/-- 由空集和后继递归生成的有限自然数项。 -/
def finite_numeral_term : Nat → SetTerm
  | 0 => empty_set_term
  | n + 1 => successor_term (finite_numeral_term n)
/-- 文献数字项的现代公共记号。 -/
scoped notation:max "numₘ(" n ")" =>
  finite_numeral_term n
/--
有限自然数的兼容合同。
当前语法没有独立数字常量，因此文献左侧数字记号与右侧的规范项都归约到
同一个 `finite_numeral_term`。该公式保留文献理论层的接口，但不引入假数字常量。
-/
def finite_numeral_alias_contract (number : Nat) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ≐ₘ finite_numeral_term number) ↔ₘ (bₛ#0 ≐ₘ finite_numeral_term number)
/-- 文献 `0` 的现代兼容合同。 -/
def finite_numeral_contract_0 : SetFormula :=
  finite_numeral_alias_contract 0
/-- 文献 `1` 的现代兼容合同。 -/
def finite_numeral_contract_1 : SetFormula :=
  finite_numeral_alias_contract 1
/-- 文献 `2` 的现代兼容合同。 -/
def finite_numeral_contract_2 : SetFormula :=
  finite_numeral_alias_contract 2
/-- 文献 `3` 的现代兼容合同。 -/
def finite_numeral_contract_3 : SetFormula :=
  finite_numeral_alias_contract 3
/-- 文献 `4` 的现代兼容合同。 -/
def finite_numeral_contract_4 : SetFormula :=
  finite_numeral_alias_contract 4
/-- 文献 `5` 的现代兼容合同。 -/
def finite_numeral_contract_5 : SetFormula :=
  finite_numeral_alias_contract 5
/-- 文献 `6` 的现代兼容合同。 -/
def finite_numeral_contract_6 : SetFormula :=
  finite_numeral_alias_contract 6
/-- 文献 `7` 的现代兼容合同。 -/
def finite_numeral_contract_7 : SetFormula :=
  finite_numeral_alias_contract 7
/-- 文献 `8` 的现代兼容合同。 -/
def finite_numeral_contract_8 : SetFormula :=
  finite_numeral_alias_contract 8
/-- 文献 `9` 的现代兼容合同。 -/
def finite_numeral_contract_9 : SetFormula :=
  finite_numeral_alias_contract 9
/-- 加入有限自然数兼容合同后的理论。 -/
def finite_natural_theory : SetTheory :=
  Theory.insert finite_numeral_contract_9 (Theory.insert finite_numeral_contract_8 (Theory.insert finite_numeral_contract_7
        (Theory.insert finite_numeral_contract_6 (Theory.insert finite_numeral_contract_5 (Theory.insert finite_numeral_contract_4
              (Theory.insert finite_numeral_contract_3 (Theory.insert finite_numeral_contract_2 (Theory.insert finite_numeral_contract_1
                    (Theory.insert finite_numeral_contract_0
                      well_order_theory)))))))))
/-- 有限序数基础理论。 -/
def finite_ordinal_theory : SetTheory :=
  finite_natural_theory
/-! ## proof-carrying 良构性 -/
/-- 良序定义公理满足公共良构性边界。 -/
theorem well_order_definition_axiom_admissible :
    Formula.Admissible
      well_order_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 良序理论仍然 admissible。 -/
theorem well_order_theory_admissible :
    Theory.Admissible well_order_theory :=
  Theory.admissible_insert
    well_order_definition_axiom_admissible
    natural_discrete_linear_order_theory_admissible
/-- 有限自然数项满足 proof-carrying 项边界。 -/
theorem finite_numeral_term_admissible (number : Nat) :
    Term.Admissible (finite_numeral_term number)
      SetSort.set := by
  induction number with
  | zero =>
      exact empty_set_term_admissible
  | succ number ih =>
      simpa [finite_numeral_term] using
        successor_term_admissible (finite_numeral_term number)
          ih
/--
有限 numeral 的计算证书。登记后，量词实例化等内核接口可直接接受
`numₘ(number)`，无需调用方传递 admissibility 证明。
-/
@[term_check]
theorem finite_numeral_term_check (number : Nat) :
    Term.CheckCertificate (finite_numeral_term number)
      SetSort.set :=
  Term.check_admissible_complete
    (finite_numeral_term_admissible number)
/-- 标准有限 numeral 不含对象语言自由变量。 -/
theorem finite_numeral_term_freeSupport (number : Nat) :
    Term.freeSupport (numₘ(number) : SetTerm) = [] := by
  induction number with
  | zero =>
      rfl
  | succ number ih =>
      simp [finite_numeral_term, successor_term,
        Term.freeSupport, Term.freeSupportList, ih]
theorem finite_numeral_contract_0_admissible :
    Formula.Admissible finite_numeral_contract_0 := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_numeral_contract_1_admissible :
    Formula.Admissible finite_numeral_contract_1 := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_numeral_contract_2_admissible :
    Formula.Admissible finite_numeral_contract_2 := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_numeral_contract_3_admissible :
    Formula.Admissible finite_numeral_contract_3 := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_numeral_contract_4_admissible :
    Formula.Admissible finite_numeral_contract_4 := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_numeral_contract_5_admissible :
    Formula.Admissible finite_numeral_contract_5 := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_numeral_contract_6_admissible :
    Formula.Admissible finite_numeral_contract_6 := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_numeral_contract_7_admissible :
    Formula.Admissible finite_numeral_contract_7 := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_numeral_contract_8_admissible :
    Formula.Admissible finite_numeral_contract_8 := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_numeral_contract_9_admissible :
    Formula.Admissible finite_numeral_contract_9 := by
  apply Formula.check_admissible_sound
  native_decide
theorem finite_natural_theory_admissible :
    Theory.Admissible finite_natural_theory :=
  Theory.admissible_insert
    finite_numeral_contract_9_admissible (Theory.admissible_insert
      finite_numeral_contract_8_admissible (Theory.admissible_insert
        finite_numeral_contract_7_admissible (Theory.admissible_insert
          finite_numeral_contract_6_admissible (Theory.admissible_insert
            finite_numeral_contract_5_admissible (Theory.admissible_insert
              finite_numeral_contract_4_admissible (Theory.admissible_insert
                finite_numeral_contract_3_admissible (Theory.admissible_insert
                  finite_numeral_contract_2_admissible (Theory.admissible_insert
                    finite_numeral_contract_1_admissible (Theory.admissible_insert
                      finite_numeral_contract_0_admissible
                      well_order_theory_admissible)))))))))
/-- 有限序数基础理论仍然 admissible。 -/
theorem finite_ordinal_theory_admissible :
    Theory.Admissible finite_ordinal_theory :=
  finite_natural_theory_admissible
/-! ## 闭理论边界 -/
@[derive_close_sentence]
theorem well_order_theory_sentence
    {formula : SetFormula} (hFormula : well_order_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact well_order_definition_axiom_admissible
    · native_decide
  · exact natural_discrete_linear_order_theory_sentence hFormula
@[derive_close_sentence]
theorem finite_natural_theory_sentence
    {formula : SetFormula} (hFormula : finite_natural_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact finite_numeral_contract_9_admissible
    · native_decide
  · rcases hFormula with rfl | hFormula
    · constructor
      · exact finite_numeral_contract_8_admissible
      · native_decide
    · rcases hFormula with rfl | hFormula
      · constructor
        · exact finite_numeral_contract_7_admissible
        · native_decide
      · rcases hFormula with rfl | hFormula
        · constructor
          · exact finite_numeral_contract_6_admissible
          · native_decide
        · rcases hFormula with rfl | hFormula
          · constructor
            · exact finite_numeral_contract_5_admissible
            · native_decide
          · rcases hFormula with rfl | hFormula
            · constructor
              · exact finite_numeral_contract_4_admissible
              · native_decide
            · rcases hFormula with rfl | hFormula
              · constructor
                · exact finite_numeral_contract_3_admissible
                · native_decide
              · rcases hFormula with rfl | hFormula
                · constructor
                  · exact finite_numeral_contract_2_admissible
                  · native_decide
                · rcases hFormula with rfl | hFormula
                  · constructor
                    · exact finite_numeral_contract_1_admissible
                    · native_decide
                  · rcases hFormula with rfl | hFormula
                    · constructor
                      · exact finite_numeral_contract_0_admissible
                      · native_decide
                    · exact well_order_theory_sentence hFormula
@[derive_close_sentence]
theorem finite_ordinal_theory_sentence
    {formula : SetFormula} (hFormula : finite_ordinal_theory formula) :
    Formula.Sentence formula :=
  finite_natural_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem natural_discrete_linear_order_theory_subset_well_order_theory
    {formula : SetFormula} (hFormula : natural_discrete_linear_order_theory formula) :
    well_order_theory formula :=
  Or.inr hFormula
theorem well_order_theory_subset_finite_natural_theory
    {formula : SetFormula} (hFormula : well_order_theory formula) :
    finite_natural_theory formula :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hFormula)))))))))
theorem finite_natural_theory_subset_finite_ordinal_theory
    {formula : SetFormula} (hFormula : finite_natural_theory formula) :
    finite_ordinal_theory formula :=
  hFormula
/-!
## 待证明定理索引
* 3.3--3.4：有限序数上的后继、传递集和成员关系限制；
* 3.5--3.14：有限自然数 `0` 到 `9` 及其后继项的成员刻画；
* 3.15：映像存在性转入 `OrderOperators` 的关系像分离层；
* 后续有限序数的唯一性、有限序同构和自然数递归性质。
这些结果暂时只作为文档索引，后续在 `finite_ordinal_theory` 上按需证明。
-/
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
