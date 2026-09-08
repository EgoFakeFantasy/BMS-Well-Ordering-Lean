import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Core
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicProofRows
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatSequenceInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProofSequenceInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceInversion

/-!
# ProofT 内在证明支撑合同

内在 witness、有限行反演和终端反证共享同一组对象算术、序列反演及行承载能力。
这里将三类能力捆绑为一个明确合同，避免下游在每个定理中重复传递并手工对齐支撑参数。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory

set_option autoImplicit false

/-- 内在证明码反演所需的统一支撑。 -/
structure IntrinsicProofSupport (T : SetTheory) where
  certificate_core : CertificateCore T
  sequence_inversion : SequenceInversion T
  row_support : IntrinsicProofRowSupport T

/--
从最小证书核心和证明行承载合同直接构造完整的内在反演支撑。

自然数序列与二维证明序列的唯一性均由对应的内在反演定理给出，调用方不再
重复手工传递两份相同的支撑参数。
-/
theorem IntrinsicProofSupport.ofCoreAndRows
    {T : SetTheory}
    (C : CertificateCore T)
    (R : IntrinsicProofRowSupport T) :
    IntrinsicProofSupport T where
  certificate_core := C
  sequence_inversion :=
    { nat_unique := by
        intro free Γ sequence code tokens hCondition hCodeEquality
        exact nat_sequence_code_condition_unique_of_code_equality
          C R.toFiniteSequenceSpaceSupport sequence code tokens
          hCondition hCodeEquality
      proof_unique := by
        intro free Γ sequence code rows hCondition hCodeEquality
        exact proof_sequence_code_condition_unique_of_code_equality
          C R sequence code rows hCondition hCodeEquality }
  row_support := R

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
