import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ProjectRelationElimination.Hilbert
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Occurrence
import YesMetaZFC.SetTheory.Axioms.ZFC

/-!
# ZFC 的内部 FormalSystem 实例

本模块把仓库公开的 `SetTheory.ZFC` 实例化到通用内部理论构造器。quotation 与
Hilbert 演绎编码当前依赖完整替换强度，因此使用 ZFC 作为公开基础理论，避免把该
联合理论误标为较弱的 KPω。

旧 Rosser 证明谓词专用的有限截断分离链已经移除；本适配层只导出基础实例与
quotation 基础设施实际使用的理论包含关系。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

/-- ZFC 与全部编码定义尚未 Hilbert 归约时的联合理论。 -/
def fs_zfc_support_raw_theory : SetTheory :=
  fs_internal_project_raw_theory
    _root_.YesMetaZFC.SetTheory.ZFC

/-- ZFC 在 FormalSystem 扩展签名上的内部 Hilbert 理论。 -/
def fs_zfc_support_theory : SetTheory :=
  fs_internal_project_theory
    _root_.YesMetaZFC.SetTheory.ZFC

/-- ZFC 的 raw 内部理论只含 admissible 闭句。 -/
@[derive_close_sentence]
theorem fs_zfc_support_raw_theory_sentence
    {formula : SetFormula} (hFormula : fs_zfc_support_raw_theory formula) :
    Formula.Sentence formula :=
  fs_internal_project_raw_theory_sentence hFormula

/-- ZFC 的内部 Hilbert 理论自动承载 quotation 编码。 -/
theorem fs_zfc_support_theory_extends_code_naming :
    GodelQuotation.fs_extends_code_naming fs_zfc_support_theory :=
  fs_internal_project_theory_extends_code_naming
    _root_.YesMetaZFC.SetTheory.ZFC

/-- ZFC 内部理论在 Hilbert 意义下扩张翻译后的 ZFC 基础理论。 -/
theorem fs_zfc_support_theory_extends_project_base :
    Theory.hilbert_extends fs_zfc_support_theory
      (Theory.hilbertize SetSort.set
        (fs_project_base_theory _root_.YesMetaZFC.SetTheory.ZFC)) :=
  fs_internal_theory_extends_base
    (fs_project_base_theory _root_.YesMetaZFC.SetTheory.ZFC)

/-! ## raw 编码理论到标准 ZFC 的内部化接口 -/

/-- 标准 ZFC raw 理论逐字包含 Gödel quotation 定义理论。 -/
theorem fs_zfc_support_raw_contains_godel_quotation
    {formula : SetFormula}
    (hFormula : GodelQuotation.godel_quotation_theory formula) :
    fs_zfc_support_raw_theory formula :=
  Or.inl <| Or.inl <| Or.inl <| Or.inr <| Or.inr hFormula

/-- 标准 ZFC raw 理论逐字包含 Gödel 配对定义理论。 -/
theorem fs_zfc_support_raw_contains_godel_pairing
    {formula : SetFormula}
    (hFormula : godel_pairing_theory formula) :
    fs_zfc_support_raw_theory formula :=
  Or.inl <| Or.inl <| Or.inr hFormula

/-- 标准 ZFC raw 理论逐字包含标准有限序列语义。 -/
theorem fs_zfc_support_raw_contains_standard_sequence_semantics
    {formula : SetFormula}
    (hFormula : GodelQuotation.standard_sequence_semantics_theory formula) :
    fs_zfc_support_raw_theory formula :=
  fs_zfc_support_raw_contains_godel_quotation (Or.inl hFormula)

/-- 标准 ZFC raw 理论逐字包含对象自然数有限上界层。 -/
theorem fs_zfc_support_raw_contains_natural_addition_bound
    {formula : SetFormula}
    (hFormula : natural_addition_bound_theory formula) :
    fs_zfc_support_raw_theory formula :=
  fs_zfc_support_raw_contains_standard_sequence_semantics <|
    Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr hFormula

/-- 标准 ZFC raw 理论逐字包含有限序列空间定义理论。 -/
theorem fs_zfc_support_raw_contains_finite_sequence_space
    {formula : SetFormula}
    (hFormula : finite_sequence_space_theory formula) :
    fs_zfc_support_raw_theory formula :=
  fs_zfc_support_raw_contains_standard_sequence_semantics
    (Or.inr <| Or.inr <| Or.inl hFormula)

/-- 标准 ZFC raw 理论逐字包含函数求值联合理论。 -/
theorem fs_zfc_support_raw_contains_function_application
    {formula : SetFormula}
    (hFormula : function_application_theory formula) :
    fs_zfc_support_raw_theory formula :=
  fs_zfc_support_raw_contains_standard_sequence_semantics
    (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hFormula)

/-- 标准 ZFC raw 理论逐字包含映射谓词定义理论。 -/
theorem fs_zfc_support_raw_contains_mapping_predicate
    {formula : SetFormula}
    (hFormula : mapping_predicate_theory formula) :
    fs_zfc_support_raw_theory formula :=
  fs_zfc_support_raw_contains_function_application
    (mapping_predicate_theory_subset_function_application_theory
      hFormula)

/-- 标准 ZFC raw 理论逐字包含对象层无穷理论。 -/
theorem fs_zfc_support_raw_contains_infinity
    {formula : SetFormula} (hFormula : infinity_theory formula) :
    fs_zfc_support_raw_theory formula :=
  fs_zfc_support_raw_contains_standard_sequence_semantics
    (Or.inr <| Or.inr <| Or.inr <| Or.inl hFormula)

/-- 标准 ZFC raw 理论逐字包含空集符号定义理论。 -/
theorem fs_zfc_support_raw_contains_empty_set_symbol
    {formula : SetFormula} (hFormula : empty_set_symbol_theory formula) :
    fs_zfc_support_raw_theory formula :=
  fs_zfc_support_raw_contains_standard_sequence_semantics
    (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hFormula)

/-- 标准 ZFC raw 理论逐字包含后继算子定义层。 -/
theorem fs_zfc_support_raw_contains_successor_operator
    {formula : SetFormula} (hFormula : successor_operator_theory formula) :
    fs_zfc_support_raw_theory formula :=
  fs_zfc_support_raw_contains_standard_sequence_semantics
    (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inl hFormula)

/-- 标准 ZFC raw 理论逐字包含关系平面理论。 -/
theorem fs_zfc_support_raw_contains_relation_plane
    {formula : SetFormula} (hFormula : relation_plane_theory formula) :
    fs_zfc_support_raw_theory formula :=
  fs_zfc_support_raw_contains_standard_sequence_semantics
    (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
        relation_plane_theory_subset_function_application_theory hFormula)

/-- 标准 ZFC raw 理论逐字包含完整 Hilbert 逻辑规则编码理论。 -/
theorem fs_zfc_support_raw_contains_logical_rules
    {formula : SetFormula} (hFormula : logical_rule_encoding_theory formula) :
    fs_zfc_support_raw_theory formula :=
  Or.inl <| Or.inr hFormula

/--
标准 ZFC raw 理论逐字包含 quotation 出现性联合理论。
标准序列分支已经属于 quotation 定义理论；出现性分支沿表达式编码、可代入性、
逻辑公理码和完整逻辑规则编码链进入 raw 理论。
-/
theorem fs_zfc_support_raw_contains_quotation_occurrence
    {formula : SetFormula}
    (hFormula : GodelQuotation.quotation_occurrence_theory formula) :
    fs_zfc_support_raw_theory formula := by
  rcases hFormula with hStandard | hOccurrence
  · exact fs_zfc_support_raw_contains_godel_quotation (Or.inl hStandard)
  · exact fs_zfc_support_raw_contains_logical_rules <|
      logical_axiom_code_theory_subset_logical_rule_encoding_theory <|
        equality_axiom_schema_theory_subset_logical_axiom_code_theory <|
          quantifier_axiom_schema_theory_subset_equality_axiom_schema_theory <|
            propositional_axiom_schema_theory_subset_quantifier_axiom_schema_theory <|
              substitutability_theory_subset_propositional_axiom_schema_theory <|
                expression_encoding_theory_subset_substitutability_theory
                  hOccurrence

/-- 标准 ZFC raw 理论逐字包含对象子集关系的定义理论。 -/
theorem fs_zfc_support_raw_contains_subset_theory
    {formula : SetFormula} (hFormula : subset_theory formula) :
    fs_zfc_support_raw_theory formula :=
  Or.inr <| Or.inl hFormula

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
