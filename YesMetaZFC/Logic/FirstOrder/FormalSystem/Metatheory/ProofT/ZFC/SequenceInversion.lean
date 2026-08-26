import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCProofSequenceConditionRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceInversion

/-!
# 有限序列编码反演核心的 ZFC 实现

本模块只把现有自然数序列与二维证明序列的完整对象层反演证明包装成公共
`ProofT.SequenceInversion`。上层不再依赖这些证明所在的 ZFC 专用模块。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC

set_option autoImplicit false

/-- 当前 ZFC raw 支持理论实现两层有限序列编码的规范反演。 -/
def sequence_inversion :
    ProofT.SequenceInversion
      fs_zfc_support_raw_theory where
  nat_unique :=
    fs_zfc_support_raw_nat_sequence_code_condition_unique_of_code_equality
  proof_unique :=
    fs_zfc_support_raw_proof_sequence_code_condition_unique_of_code_equality

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
