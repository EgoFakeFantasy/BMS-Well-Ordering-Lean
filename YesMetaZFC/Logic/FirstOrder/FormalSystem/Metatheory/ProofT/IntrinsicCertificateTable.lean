import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FixedAxiomTable
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSchemaClosure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.StructuredCertificateCondition

/-!
# ProofT 内在证书表装配

固定公理表与带依赖 witness 的 schema 分支在同一公式模板中合成。二元模板只保留
formula、certificate 两个自由槽位；旧层为嵌套量词预留的 base 编号不再进入接口。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace IntrinsicCertificateTable

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open StructuredCertificateCondition

set_option autoImplicit false

abbrev binary_free : SetContext := [SetSort.set, SetSort.set]

def formula_slot : SetOpenTerm binary_free :=
  .fvar .here

def certificate_slot : SetOpenTerm binary_free :=
  .fvar (.there .here)

/-- 固定表在二元内在模板中的条件。 -/
def fixed_condition_template
    (table : FixedAxiomTable) : FormulaTemplate.Binary where
  body := table.condition formula_slot certificate_slot

/-- schema 分支表在二元内在模板中的条件。 -/
def schema_condition_template
    (branches : List (BoundedBinaryBranch binary_free)) :
    FormulaTemplate.Binary where
  body := bounded_binary_condition_list branches
    formula_slot certificate_slot

/-- 固定表与 schema 分支的总二元条件模板。 -/
def condition_template
    (table : FixedAxiomTable)
    (branches : List (BoundedBinaryBranch binary_free)) :
    FormulaTemplate.Binary where
  body :=
      (fixed_condition_template table).body ∨ₘ
      (schema_condition_template branches).body

theorem condition_template_body
    (table : FixedAxiomTable)
    (branches : List (BoundedBinaryBranch binary_free)) :
    (condition_template table branches).body =
      table.condition formula_slot certificate_slot ∨ₘ
        bounded_binary_condition_list branches
          formula_slot certificate_slot :=
  rfl

/-- 从固定表、schema 分支、公式条件和逻辑条件直接组装 checked verifier。 -/
def checked_verifier
    (table : FixedAxiomTable)
    (branches : List (BoundedBinaryBranch binary_free))
    (formulaCondition : FormulaTemplate.Unary)
    (logicalCondition : LogicalCondition) :
    CheckedVerifier where
  formula_condition := formulaCondition
  condition := condition_template table branches
  logical_condition := logicalCondition

@[simp] theorem checked_verifier_formula_condition
    (table : FixedAxiomTable)
    (branches : List (BoundedBinaryBranch binary_free))
    (formulaCondition : FormulaTemplate.Unary)
    (logicalCondition : LogicalCondition) :
    (checked_verifier table branches formulaCondition logicalCondition).formula_condition =
      formulaCondition :=
  rfl

@[simp] theorem checked_verifier_condition
    (table : FixedAxiomTable)
    (branches : List (BoundedBinaryBranch binary_free))
    (formulaCondition : FormulaTemplate.Unary)
    (logicalCondition : LogicalCondition) :
    (checked_verifier table branches formulaCondition logicalCondition).condition =
      condition_template table branches :=
  rfl

@[simp] theorem checked_verifier_logical_condition
    (table : FixedAxiomTable)
    (branches : List (BoundedBinaryBranch binary_free))
    (formulaCondition : FormulaTemplate.Unary)
    (logicalCondition : LogicalCondition) :
    (checked_verifier table branches formulaCondition logicalCondition).logical_condition =
      logicalCondition :=
  rfl

end IntrinsicCertificateTable
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
