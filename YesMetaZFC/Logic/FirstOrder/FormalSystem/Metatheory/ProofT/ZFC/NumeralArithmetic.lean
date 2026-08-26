import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NumeralArithmetic

/-! # ZFC 的标准 numeral 算术实例 -/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation

set_option autoImplicit false

/-- ZFC raw 支持理论继承标准有限序列语义中的 numeral 互异性。 -/
def numeral_arithmetic :
    ProofT.NumeralArithmetic
      fs_zfc_support_raw_theory where
  numeral_ne := fun hNe =>
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_sequence_finite_numeral_ne hNe)

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
