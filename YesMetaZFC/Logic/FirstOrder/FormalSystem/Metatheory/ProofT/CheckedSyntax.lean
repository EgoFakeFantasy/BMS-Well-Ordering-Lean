import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CertifiedProofCodeEncoding

/-!
# ProofT checked replay 的对象语法

本模块集中管理 checked replay 的外层 binder 分配，并导出精确的逐行条件与
证明序列条件。编号表、fresh-base 算法与 verifier 合同都不依赖具体 ZFC 公理，
PA 或 KPω realization 可以直接复用同一对象语法。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- Rosser 证明谓词与 checked replay 共用的固定编号基点。 -/
def ProofT.condition_base : FreeVarId := 880

abbrev ProofT.lc_sequence_id : FreeVarId := 891
abbrev ProofT.lc_formula_trace_id : FreeVarId := 892
abbrev ProofT.lc_last_index_id : FreeVarId := 893
abbrev ProofT.lc_line_index_id : FreeVarId := 894
abbrev ProofT.lc_code_trace_id : FreeVarId := 895
abbrev ProofT.lc_code_index_id : FreeVarId := 896
abbrev ProofT.lc_base_id : FreeVarId :=
  CertifiedProof.logical_certificate_body_base_with_ids
    ProofT.lc_sequence_id
    ProofT.lc_formula_trace_id
    ProofT.lc_last_index_id

abbrev ProofT.line_index_id : FreeVarId := 900
abbrev ProofT.mp_implication_id : FreeVarId := 901
abbrev ProofT.mp_premise_id : FreeVarId := 902
abbrev ProofT.certificate_code_id : FreeVarId := 903

/--
schema verifier 的内部新鲜编号起点。

`900` 至 `903` 保留给行位置和证书见证；若公开输入含有更高自由变量，则继续取
真实新鲜上界。该算法只描述 ProofT 的 binder 布局，不携带集合论公理强度。
-/
def ProofT.schema_base
    (terms : List SetTerm) : FreeVarId :=
  max 904 <|
    FreshVariable.fresh_id SetSort.set
      (terms.map fun term => term ≐ₘ term)

/--
checked replay 对对象 verifier 的完整运输合同。

公式词法条件必须复用公共 quotation replay；理论证书条件则须在 schema 内部保留
边界 `904` 以下保持闭项替换。该合同恰好覆盖逐行运输与四见证闭合，不暴露具体
schema 插件。
-/
structure ProofT.VerifierTransport
    (verifier : ObjectCertificateVerifier) where
  formula_condition :
    verifier.formula_condition =
      GodelQuotation.fs_formula_replay_condition
  substitute_closed :
    ∀ (formula certificate replacement
        formulaResult certificateResult : SetTerm)
      (sourceId : FreeVarId),
      sourceId < 904 →
      GodelQuotation.Numbered.CodeBoundary replacement →
      Term.substituteFree SetSort.set sourceId replacement formula =
        formulaResult →
      Term.substituteFree SetSort.set sourceId replacement certificate =
        certificateResult →
      ProofT.schema_base [formula, certificate] = 904 →
      ProofT.schema_base
          [formulaResult, certificateResult] = 904 →
      Formula.substituteFree SetSort.set sourceId replacement
          (verifier.condition formula certificate) =
        verifier.condition formulaResult certificateResult

/-- checked replay 的精确逐行合法性条件。 -/
def ProofT.line_condition
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm) : SetFormula :=
  CertifiedProof.line_condition_with_ids
    verifier
    sequence certificates index
    ProofT.certificate_code_id
    ProofT.lc_sequence_id ProofT.lc_formula_trace_id
    ProofT.lc_last_index_id ProofT.lc_line_index_id
    ProofT.lc_code_trace_id ProofT.lc_code_index_id
    ProofT.mp_implication_id ProofT.mp_premise_id

/-- checked replay 的精确证明序列条件。 -/
def ProofT.sequence_condition
    (verifier : ObjectCertificateVerifier)
    (sequence certificates : SetTerm) : SetFormula :=
  CertifiedProof.sequence_condition_with_ids
    verifier
    sequence certificates
    ProofT.line_index_id ProofT.certificate_code_id
    ProofT.lc_sequence_id ProofT.lc_formula_trace_id
    ProofT.lc_last_index_id ProofT.lc_line_index_id
    ProofT.lc_code_trace_id ProofT.lc_code_index_id
    ProofT.mp_implication_id ProofT.mp_premise_id

/-- 参数化 verifier 的逐行条件保持 admissibility。 -/
theorem ProofT.line_condition_admissible
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible
      (ProofT.line_condition
        verifier sequence certificates index) := by
  exact CertifiedProof.line_condition_with_ids_admissible
    verifier sequence certificates index
    ProofT.certificate_code_id
    ProofT.lc_sequence_id ProofT.lc_formula_trace_id
    ProofT.lc_last_index_id ProofT.lc_line_index_id
    ProofT.lc_code_trace_id ProofT.lc_code_index_id
    ProofT.mp_implication_id ProofT.mp_premise_id
    hSequence hCertificates hIndex

/--
负向规范见证消去所需的 verifier 支撑合同。

条件公式不得引入两个公开输入之外的自由变量；该合同与 substitution replay
正交，因此作为独立能力保存。
-/
structure ProofT.VerifierSupport
    (verifier : ObjectCertificateVerifier) where
  freeSupport_subset :
    ∀ formula certificate freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (verifier.condition formula certificate) →
        freeVariable ∈ Term.freeSupport formula ∨
          freeVariable ∈ Term.freeSupport certificate

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
