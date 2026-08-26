import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.Failure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.NamedFormulaPayload

/-!
# 具名公式 payload 的定长失败视图

本模块把固定长度的具名公式 payload 完整分解为三种互斥计算结果：

* 原始自然数序列长度错误；
* 序列长度正确，但某个公式字段解码失败；
* 全部字段成功解码，并保留结果长度。

该视图只依赖可计算解码器，不携带对象理论假设。逻辑证书的各个固定 arity
分支可共享这一层，而无需重复展开 `List.mapM`。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace Rosser

open Nonlogical.BasicSetTheory
open ProofCode
open GodelQuotation

set_option autoImplicit false

/-- 具名公式 payload 在固定 arity 下的两类失败。 -/
inductive FSNamedFormulaPayloadArityFailure
    (freeBase code arity : Nat) : Prop
  | length_mismatch
      (hLength :
        (nat_sequence_decode code).length ≠ arity) :
      FSNamedFormulaPayloadArityFailure freeBase code arity
  | component_failure
      (index : Nat)
      (hIndex :
        index < (nat_sequence_decode code).length)
      (hLength :
        (nat_sequence_decode code).length = arity)
      (hDecode :
        fs_named_formula_token_code_decode freeBase
            (nat_sequence_decode code)[index] =
          none) :
      FSNamedFormulaPayloadArityFailure freeBase code arity

/-- 具名公式 payload 在固定 arity 下的完整计算视图。 -/
inductive FSNamedFormulaPayloadArityView
    (freeBase code arity : Nat) : Prop
  | failure
      (hFailure :
        FSNamedFormulaPayloadArityFailure
          freeBase code arity) :
      FSNamedFormulaPayloadArityView freeBase code arity
  | decoded
      (formulas : List SetFormula)
      (hDecode :
        fs_named_formula_payload_decode freeBase code =
          some formulas)
      (hLength : formulas.length = arity) :
      FSNamedFormulaPayloadArityView freeBase code arity

/--
任意具名公式 payload 对固定 arity 都落入长度错误、字段失败或整体成功之一。
-/
theorem fs_named_formula_payload_arity_view
    (freeBase code arity : Nat) :
    FSNamedFormulaPayloadArityView freeBase code arity := by
  by_cases hLength :
      (nat_sequence_decode code).length = arity
  · cases hDecode :
      fs_named_formula_payload_decode freeBase code with
    | none =>
        have hMap :
            (nat_sequence_decode code).mapM
                (fs_named_formula_token_code_decode freeBase) =
              none := by
          simpa [fs_named_formula_payload_decode] using hDecode
        rcases fs_mapM_failure_of_none hMap with
          ⟨index, hIndex, hFailure⟩
        exact
          .failure <|
            .component_failure index hIndex hLength hFailure
    | some formulas =>
        have hResultLength :
            formulas.length =
              (nat_sequence_decode code).length :=
          GodelQuotation.fs_option_mapM_length <| by
            simpa [fs_named_formula_payload_decode] using hDecode
        exact
          .decoded formulas hDecode
            (hResultLength.trans hLength)
  · exact .failure (.length_mismatch hLength)

end Rosser
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
