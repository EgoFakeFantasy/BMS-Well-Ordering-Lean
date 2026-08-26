import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CheckedSyntax

/-!
# ZFC verifier 的 checked syntax 实例

本模块只把 separation+collection verifier 代入通用 `ProofT` 行条件。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory

set_option autoImplicit false

/-- 当前 ZFC verifier 的逐行条件。 -/
def ProofT.ZFC.line_condition
    (sequence certificates index : SetTerm) : SetFormula :=
  ProofT.line_condition
    fs_zfc_object_certificate_verifier
    sequence certificates index

/-- 当前 ZFC verifier 的证明序列条件。 -/
def ProofT.ZFC.sequence_condition
    (sequence certificates : SetTerm) : SetFormula :=
  ProofT.sequence_condition
    fs_zfc_object_certificate_verifier
    sequence certificates

/-- 当前 ZFC verifier 的逐行条件保持 admissibility。 -/
theorem ProofT.ZFC.line_condition_admissible
    (sequence certificates index : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible
      (ProofT.ZFC.line_condition sequence certificates index) :=
  ProofT.line_condition_admissible
    fs_zfc_object_certificate_verifier
    sequence certificates index
    hSequence hCertificates hIndex

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
