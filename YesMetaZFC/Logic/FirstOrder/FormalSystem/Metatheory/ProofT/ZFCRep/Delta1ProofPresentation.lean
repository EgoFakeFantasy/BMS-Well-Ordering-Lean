import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta1ProofPresentation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedProofInternalization
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFCRep.ProofRelationRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCReplacementObjectCertificateReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCReplacementVerifierSubstitution

/-!
# replacement 插件的 `Delta1ProofPresentation`

该实例以 ZFC 内部理论为对象证明宿主，并把启用 separation 与 replacement
插件后的 Hilbert 枚举及 checked replay 正负两面内部化到同一个对象 verifier。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFCRep

open Nonlogical.BasicSetTheory
open Rosser

set_option autoImplicit false

/-- separation+replacement 支持理论按定义对再次 Hilbert 化封闭。 -/
private theorem hilbert_closed :
    ∀ formula,
      ProofCode.fs_zfc_replacement_support_theory formula →
        ProofCode.fs_zfc_replacement_support_theory
          (Formula.hilbertize SetSort.set formula) :=
  ProofCode.fs_zfc_replacement_support_theory_hilbert_closed

/--
separation+replacement 理论的 checked `Delta1` 证明表示。

这里的对象证明宿主是 `fs_zfc_support_raw_theory`；被枚举、回放并用于 Rosser
关系的 Hilbert 理论则是 `fs_zfc_replacement_support_theory`。
-/
def proof_presentation :
    ProofT.Delta1ProofPresentation
      fs_zfc_support_raw_theory
      ProofCode.fs_zfc_replacement_support_theory where
  enumeration :=
    ProofCode.fs_zfc_replacement_support_enumeration
  hilbert_closed :=
    hilbert_closed
  verifier :=
    fs_zfc_replacement_object_certificate_verifier
  base :=
    ProofT.condition_base
  realize := by
    intro formula code hQuote hDerives
    exact
      fs_zfc_support_raw_certified_code_condition_of_derives_at_quote
        ProofCode.fs_zfc_replacement_support_enumeration
        fs_zfc_replacement_object_certificate_verifier
        ProofT.ZFCRep.verifier_transport
        (fun hVerifier => by
          simpa [fs_zfc_replacement_object_certificate_verifier] using
            fs_zfc_support_raw_replacement_object_certificate_condition_of_verifier
              hVerifier)
        hilbert_closed hQuote hDerives
  reject :=
    ProofT.ZFCRep.code_neg_of_terminal_unchecked

end ZFCRep
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
