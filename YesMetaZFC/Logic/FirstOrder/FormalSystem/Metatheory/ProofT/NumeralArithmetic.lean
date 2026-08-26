import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Infinity

/-!
# `ProofT` 的标准 numeral 算术

固定公理表的证书标签拒绝只需要区分两个外部自然数对应的对象 numeral。该接口
独立于自然数切分、quotation 和序列编码，避免有限表 verifier 依赖完整 `Core`。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 对象理论能够判定不同标准 numeral 互异。 -/
structure NumeralArithmetic (T : SetTheory) where
  numeral_ne :
    ∀ {left right : Nat},
      left ≠ right →
      Derives T [] (
        ¬ₘ (numₘ(left) ≐ₘ numₘ(right)))

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
