import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta0Support
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCertificateTable
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicFixedTable
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalCertificate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicSchemaCertificate

/-!
# ZFC 的内在 checked verifier

这里是新内核的唯一 ZFC 装配点：八条固定公理使用直接结构码，schema presentation
由分支表参数化，逻辑条件来自十二类内在证书。普通 ZFC 选择分离与收集；replacement
presentation 选择分离与替换。旧 token verifier 不再参与新证明图接口。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC
namespace IntrinsicVerifier

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open StructuredCertificateCondition
open IntrinsicCertificateTable
open IntrinsicLogicalCertificate
open IntrinsicSchemaCertificate

set_option autoImplicit false

def formula_condition_template : FormulaTemplate.Unary where
  body := formula_payload_condition
    (.fvar .here : SetOpenTerm [SetSort.set])

theorem formula_condition_template_delta0 :
    Formula.IsDelta0 set_levy_bound
      formula_condition_template.body := by
  simpa [formula_condition_template] using
    formula_payload_condition_delta0
      (.fvar .here : SetOpenTerm [SetSort.set])

def checked_verifier_for
    (branches : List (BoundedBinaryBranch schema_free)) : CheckedVerifier :=
  IntrinsicCertificateTable.checked_verifier
    fixed_table branches
    formula_condition_template logical_condition_template

theorem checked_verifier_for_formula_condition_body_delta0
    (branches : List (BoundedBinaryBranch schema_free)) :
    Formula.IsDelta0 set_levy_bound
      (checked_verifier_for branches).formula_condition.body := by
  change Formula.IsDelta0 set_levy_bound
    formula_condition_template.body
  exact formula_condition_template_delta0

theorem checked_verifier_for_condition_body_delta0
    (branches : List (BoundedBinaryBranch schema_free)) :
    Formula.IsDelta0 set_levy_bound
      (checked_verifier_for branches).condition.body := by
  change Formula.IsDelta0 set_levy_bound
    (IntrinsicCertificateTable.condition_template
      fixed_table branches).body
  have hFixed : Formula.IsDelta0 set_levy_bound
      (fixed_table.condition
        (formula_slot : SetOpenTerm IntrinsicCertificateTable.binary_free)
        (certificate_slot : SetOpenTerm IntrinsicCertificateTable.binary_free)) :=
    FixedAxiomTable.condition_delta0 fixed_table
      (formula_slot : SetOpenTerm IntrinsicCertificateTable.binary_free)
      (certificate_slot : SetOpenTerm IntrinsicCertificateTable.binary_free)
  have hSchema : Formula.IsDelta0 set_levy_bound
      (bounded_binary_condition_list branches
        (formula_slot : SetOpenTerm IntrinsicCertificateTable.binary_free)
        (certificate_slot : SetOpenTerm IntrinsicCertificateTable.binary_free)) :=
    bounded_binary_condition_list_delta0 branches
      (formula_slot : SetOpenTerm IntrinsicCertificateTable.binary_free)
      (certificate_slot : SetOpenTerm IntrinsicCertificateTable.binary_free)
  have hTemplate : Formula.IsDelta0 set_levy_bound
      (IntrinsicCertificateTable.condition_template
        fixed_table branches).body := by
    simpa [IntrinsicCertificateTable.condition_template,
      IntrinsicCertificateTable.fixed_condition_template,
      IntrinsicCertificateTable.schema_condition_template] using
      Formula.IsDelta0.disj hFixed hSchema
  exact hTemplate

theorem checked_verifier_for_condition_body_neg
    {T : SetTheory}
    (branches : List (BoundedBinaryBranch schema_free))
    {Γ : Context signature IntrinsicCertificateTable.binary_free}
    (hFixedReject :
      Γ ⊢ₘ[T] ¬ₘ
        (fixed_table.condition
          (formula_slot : SetOpenTerm IntrinsicCertificateTable.binary_free)
          (certificate_slot : SetOpenTerm IntrinsicCertificateTable.binary_free)))
    (hSchemaReject :
      ∀ branch, branch ∈ branches →
        Γ ⊢ₘ[T] ¬ₘ
          branch.condition_closed
            (formula_slot : SetOpenTerm IntrinsicCertificateTable.binary_free)
            (certificate_slot : SetOpenTerm IntrinsicCertificateTable.binary_free)) :
    Γ ⊢ₘ[T] ¬ₘ (checked_verifier_for branches).condition.body := by
  change Γ ⊢ₘ[T] ¬ₘ
    (fixed_table.condition
      (formula_slot : SetOpenTerm IntrinsicCertificateTable.binary_free)
      (certificate_slot : SetOpenTerm IntrinsicCertificateTable.binary_free) ∨ₘ
      bounded_binary_condition_list branches
        (formula_slot : SetOpenTerm IntrinsicCertificateTable.binary_free)
        (certificate_slot : SetOpenTerm IntrinsicCertificateTable.binary_free))
  exact IntrinsicSchema.disj_neg hFixedReject
    (bounded_binary_condition_list_neg hSchemaReject)

theorem checked_verifier_for_logical_condition_body_delta0
    (branches : List (BoundedBinaryBranch schema_free)) :
    Formula.IsDelta0 set_levy_bound
      (checked_verifier_for branches).logical_condition.body := by
  change Formula.IsDelta0 set_levy_bound
    logical_condition_template.body
  exact logical_condition_template_delta0

def delta0_checked_verifier_for
    (branches : List (BoundedBinaryBranch schema_free)) :
    Delta0CheckedVerifier where
  toCheckedVerifier := checked_verifier_for branches
  formula_condition_delta0 :=
    checked_verifier_for_formula_condition_body_delta0 branches
  condition_delta0 :=
    checked_verifier_for_condition_body_delta0 branches
  logical_condition_delta0 :=
    checked_verifier_for_logical_condition_body_delta0 branches

def checked_verifier : CheckedVerifier :=
  checked_verifier_for schema_branches

theorem checked_verifier_formula_condition_body_delta0 :
    Formula.IsDelta0 set_levy_bound
      checked_verifier.formula_condition.body :=
  checked_verifier_for_formula_condition_body_delta0 schema_branches

theorem checked_verifier_condition_body_delta0 :
    Formula.IsDelta0 set_levy_bound
      checked_verifier.condition.body :=
  checked_verifier_for_condition_body_delta0 schema_branches

theorem checked_verifier_logical_condition_body_delta0 :
    Formula.IsDelta0 set_levy_bound
      checked_verifier.logical_condition.body :=
  checked_verifier_for_logical_condition_body_delta0 schema_branches

def delta0_checked_verifier : Delta0CheckedVerifier :=
  delta0_checked_verifier_for schema_branches

def replacement_checked_verifier : CheckedVerifier :=
  checked_verifier_for replacement_schema_branches

theorem replacement_checked_verifier_formula_condition_body_delta0 :
    Formula.IsDelta0 set_levy_bound
      replacement_checked_verifier.formula_condition.body :=
  checked_verifier_for_formula_condition_body_delta0
    replacement_schema_branches

theorem replacement_checked_verifier_condition_body_delta0 :
    Formula.IsDelta0 set_levy_bound
      replacement_checked_verifier.condition.body :=
  checked_verifier_for_condition_body_delta0 replacement_schema_branches

theorem replacement_checked_verifier_logical_condition_body_delta0 :
    Formula.IsDelta0 set_levy_bound
      replacement_checked_verifier.logical_condition.body :=
  checked_verifier_for_logical_condition_body_delta0
    replacement_schema_branches

def replacement_delta0_checked_verifier : Delta0CheckedVerifier :=
  delta0_checked_verifier_for replacement_schema_branches

end IntrinsicVerifier
end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
