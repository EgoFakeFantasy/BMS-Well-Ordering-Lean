import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Rosser
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedProofInternalization
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifierSupport

/-!
# ZFC Rosser 句法实例

本模块只固定当前 ZFC proof presentation 的公开变量编号，并把通用 `ProofT`
Rosser 谓词实例化到 ZFC 对象 verifier。自由变量支撑和 Hilbert 化交换律均直接
复用通用定理；对角句由最终的 `ProofT.RosserPresentation` 统一生成。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation

set_option autoImplicit false

/-- Rosser 自由代码变量。内部证明码条件从 `880` 起分配。 -/
def fs_zfc_rosser_code_id : FreeVarId := 840

/-- Rosser 左证明码的存在见证编号。 -/
def fs_zfc_rosser_proof_code_id : FreeVarId := 841

/-- Rosser 右侧较小证明码的全称编号。 -/
def fs_zfc_rosser_smaller_code_id : FreeVarId := 842

/-- 当前 ZFC verifier 的完整 Rosser 支撑合同。 -/
private def fs_zfc_rosser_support :
    ProofT.RosserVerifierSupport
      fs_zfc_object_certificate_verifier where
  toVerifierSupport :=
    ProofT.ZFC.verifier_support
  formula_freeSupport_subset := by
    intro formula freeVariable hMember
    simpa [fs_zfc_object_certificate_verifier] using
      fs_formula_replay_condition_freeSupport_subset
        formula freeVariable hMember

/-- ZFC Rosser 证明码谓词的对象公式体。 -/
def fs_zfc_rosser_predicate : SetFormula :=
  ProofT.rosser_predicate
    fs_zfc_object_certificate_verifier
    fs_zfc_rosser_code_id
    fs_zfc_rosser_proof_code_id
    fs_zfc_rosser_smaller_code_id
    ProofT.condition_base

/-- ZFC Rosser 句体是证明码谓词的否定。 -/
def fs_zfc_rosser_sentence_body : SetFormula :=
  ProofT.rosser_sentence_body
    fs_zfc_object_certificate_verifier
    fs_zfc_rosser_code_id
    fs_zfc_rosser_proof_code_id
    fs_zfc_rosser_smaller_code_id
    ProofT.condition_base

/-- 把 Rosser 证明码谓词实例化到一个具体公式码。 -/
def fs_zfc_rosser_predicate_at
    (formulaCode : SetTerm) : SetFormula :=
  ProofT.rosser_predicate_at
    fs_zfc_object_certificate_verifier
    fs_zfc_rosser_code_id
    fs_zfc_rosser_proof_code_id
    fs_zfc_rosser_smaller_code_id
    ProofT.condition_base
    formulaCode

/-- 对角固定点右侧实际使用的 Hilbert 化 Rosser 谓词。 -/
def fs_zfc_rosser_predicate_instance
    (formulaCode : SetTerm) : SetFormula :=
  ProofT.rosser_predicate_instance
    fs_zfc_object_certificate_verifier
    fs_zfc_rosser_code_id
    fs_zfc_rosser_proof_code_id
    fs_zfc_rosser_smaller_code_id
    ProofT.condition_base
    formulaCode

theorem fs_zfc_rosser_predicate_admissible :
    Formula.Admissible fs_zfc_rosser_predicate := by
  exact ProofT.rosser_predicate_admissible
    fs_zfc_object_certificate_verifier
    fs_zfc_rosser_code_id
    fs_zfc_rosser_proof_code_id
    fs_zfc_rosser_smaller_code_id
    ProofT.condition_base

theorem fs_zfc_rosser_sentence_body_admissible :
    Formula.Admissible fs_zfc_rosser_sentence_body := by
  exact ProofT.rosser_sentence_body_admissible
    fs_zfc_object_certificate_verifier
    fs_zfc_rosser_code_id
    fs_zfc_rosser_proof_code_id
    fs_zfc_rosser_smaller_code_id
    ProofT.condition_base

theorem fs_zfc_rosser_predicate_at_admissible
    (formulaCode : SetTerm)
    (hFormulaCode :
      Term.Admissible formulaCode SetSort.set) :
    Formula.Admissible
      (fs_zfc_rosser_predicate_at formulaCode) := by
  exact Formula.Admissible.substituteFree
    SetSort.set fs_zfc_rosser_code_id
    fs_zfc_rosser_predicate_admissible hFormulaCode

theorem fs_zfc_rosser_predicate_instance_admissible
    (formulaCode : SetTerm)
    (hFormulaCode :
      Term.Admissible formulaCode SetSort.set) :
    Formula.Admissible
      (fs_zfc_rosser_predicate_instance formulaCode) := by
  exact Formula.Admissible.substituteFree
    SetSort.set fs_zfc_rosser_code_id
    (Formula.Admissible.hilbertize
      fs_zfc_rosser_predicate_admissible)
    hFormulaCode

theorem fs_zfc_rosser_predicate_instance_eq_hilbertize
    (formulaCode : SetTerm) :
    fs_zfc_rosser_predicate_instance formulaCode =
      Formula.hilbertize SetSort.set
        (fs_zfc_rosser_predicate_at formulaCode) := by
  exact ProofT.rosser_predicate_instance_eq_hilbertize
    fs_zfc_object_certificate_verifier
    fs_zfc_rosser_code_id
    fs_zfc_rosser_proof_code_id
    fs_zfc_rosser_smaller_code_id
    ProofT.condition_base
    formulaCode

theorem fs_zfc_rosser_predicate_only_code_variable :
    fs_only_code_variable_formula
      fs_zfc_rosser_code_id fs_zfc_rosser_predicate := by
  exact ProofT.rosser_predicate_only_code_variable
    fs_zfc_object_certificate_verifier
    fs_zfc_rosser_code_id
    fs_zfc_rosser_proof_code_id
    fs_zfc_rosser_smaller_code_id
    ProofT.condition_base
    fs_zfc_rosser_support

theorem fs_zfc_rosser_sentence_body_only_code_variable :
    fs_only_code_variable_formula
      fs_zfc_rosser_code_id fs_zfc_rosser_sentence_body := by
  exact ProofT.rosser_sentence_body_only_code_variable
    fs_zfc_object_certificate_verifier
    fs_zfc_rosser_code_id
    fs_zfc_rosser_proof_code_id
    fs_zfc_rosser_smaller_code_id
    ProofT.condition_base
    fs_zfc_rosser_support

theorem fs_zfc_support_theory_sentence :
    ∀ formula, fs_zfc_support_theory formula →
      Formula.Sentence formula := by
  intro formula hFormula
  simpa [fs_zfc_support_theory] using
    (fs_internal_project_theory_sentence
      (base := _root_.YesMetaZFC.SetTheory.ZFC)
      hFormula)

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
