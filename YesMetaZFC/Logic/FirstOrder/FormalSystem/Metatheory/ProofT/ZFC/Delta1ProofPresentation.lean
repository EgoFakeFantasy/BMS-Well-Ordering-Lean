import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta1ProofPresentation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedProofInternalization
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ProofRelationRejection

/-!
# ZFC 的 `Delta1ProofPresentation` 实例

本模块把现有 ZFC checked replay、对象证明码成功内部化与失败拒绝整理为一个
可审计实例；Rosser 终局不再直接依赖三条彼此分散的 ZFC 定理。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC

open Nonlogical.BasicSetTheory
open Rosser

set_option autoImplicit false

/-- ZFC 支持理论按定义对再次 Hilbert 化封闭。 -/
private theorem hilbert_closed :
    ∀ formula, fs_zfc_support_theory formula →
      fs_zfc_support_theory
        (Formula.hilbertize SetSort.set formula) := by
  intro formula hFormula
  simpa [fs_zfc_support_theory] using
    fs_internal_project_theory_hilbert_closed
      _root_.YesMetaZFC.SetTheory.ZFC
      (Formula.hilbertize SetSort.set formula)
      (Theory.hilbertize_mem
        (anchorSort := SetSort.set) hFormula)

/-- 当前 ZFC 支持理论的 checked 证明表示。 -/
def proof_presentation :
    ProofT.Delta1ProofPresentation
      fs_zfc_support_raw_theory fs_zfc_support_theory where
  enumeration :=
    ProofCode.fs_zfc_support_enumeration
  hilbert_closed :=
    hilbert_closed
  verifier :=
    fs_zfc_object_certificate_verifier
  base :=
    ProofT.condition_base
  realize := by
    intro formula code hQuote hDerives
    exact
      fs_zfc_support_raw_certified_code_condition_of_derives_at_quote
        ProofCode.fs_zfc_support_enumeration
        fs_zfc_object_certificate_verifier
        ProofT.ZFC.verifier_transport
        (fun hVerifier => by
          simpa [fs_zfc_object_certificate_verifier] using
            fs_zfc_support_raw_object_certificate_condition_of_verifier
              hVerifier)
        hilbert_closed hQuote hDerives
  reject :=
    ProofT.ZFC.code_neg_of_terminal_unchecked

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
