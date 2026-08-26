import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.Base
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceConditionRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCFormulaBinderRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCFormulaSignatureRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCodeDecodeRejection

/-!
# 逻辑基础证书的单字段反向核

本模块只反演一个 payload 字段。对象层同时给出公式码谓词与自然数序列条件时，
字段代码被唯一地锁定为数值字段解出的标准 token 串。该接口只使用二元数值码
等式，不反演完整 transcript，也不引入新的对象理论公理。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation
open Rosser

set_option autoImplicit false

namespace CertifiedProof

/--
单个 payload 字段的二元数值码反演。

该接口只消费对象层自然数序列码关系；不需要公式 decoder，也不需要展开公式构造
轨迹。数值字段一旦等于标准自然数 `code`，公式字段就唯一等于该数解出的 token
序列。
-/
theorem
    fs_zfc_support_raw_logical_formula_payload_component_code_eq_standard
    {Γ : Context signature}
    (componentCode numericCode : SetTerm)
    (code : Nat)
    (traceId indexId : FreeVarId)
    (hIds : traceId ≠ indexId)
    (hComponentCode : Term.Admissible componentCode SetSort.set)
    (hNumericCode : Term.Admissible numericCode SetSort.set)
    (hTraceFreshSequence :
      (SetSort.set, traceId) ∉ Term.freeSupport componentCode)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉ Term.freeSupport componentCode)
    (hIndexFreshCode :
      (SetSort.set, indexId) ∉ Term.freeSupport numericCode)
    (hTraceFreshContext :
      ∀ proposition, proposition ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport proposition)
    (hComponent :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_formula_payload_component_condition_with_ids
          componentCode numericCode traceId indexId)
    (hNumericEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numericCode ≐ₘ numₘ(code)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      componentCode ≐ₘ
        standard_token_sequence (nat_sequence_decode code) := by
  have hSequenceCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        nat_sequence_code_condition_with_ids
          componentCode numericCode traceId indexId :=
    FirstOrder.Derives.conjElimRight hComponent
  have hCodeEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numericCode ≐ₘ
          numₘ(nat_sequence_code_value
            (nat_sequence_decode code)) := by
    simpa [nat_sequence_code_value_decode] using hNumericEquality
  exact
    fs_zfc_support_raw_nat_sequence_code_condition_unique_of_code_equality
      componentCode numericCode
      (nat_sequence_decode code)
      traceId indexId
      hComponentCode hNumericCode
      hIds hTraceFreshSequence hIndexFreshSequence
      hIndexFreshCode hTraceFreshContext
      hSequenceCondition hCodeEquality

/--
共享命名 decoder 拒绝一个 payload 字段时，该字段条件在对象层推出矛盾。

证明先用二元自然数序列关系把字段锁定为标准 token 串，再按有限签名与 binder
布尔检查分支。两类词法失败直接与 replay 条件冲突；词法检查均通过时，通用公式
解码拒绝定理否定 `FormulaCodeₘ` 成员，而 payload 的公式码谓词给出该成员。
-/
theorem
    fs_zfc_support_raw_logical_formula_payload_component_falsum_of_named_decode_none
    {Γ : Context signature}
    (componentCode numericCode : SetTerm)
    (freeBase code : Nat)
    (traceId indexId : FreeVarId)
    (hIds : traceId ≠ indexId)
    (hComponentCode : Term.Admissible componentCode SetSort.set)
    (hNumericCode : Term.Admissible numericCode SetSort.set)
    (hTraceFreshSequence :
      (SetSort.set, traceId) ∉ Term.freeSupport componentCode)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉ Term.freeSupport componentCode)
    (hIndexFreshCode :
      (SetSort.set, indexId) ∉ Term.freeSupport numericCode)
    (hTraceFreshContext :
      ∀ proposition, proposition ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport proposition)
    (hComponent :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_formula_payload_component_condition_with_ids
          componentCode numericCode traceId indexId)
    (hNumericEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numericCode ≐ₘ numₘ(code))
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] (nat_sequence_decode code) =
        none) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  let tokens : List Nat := nat_sequence_decode code
  let standardCode : SetTerm :=
    standard_token_sequence tokens
  have hStandardBoundary :
      GodelQuotation.Numbered.CodeBoundary standardCode := by
    exact
      ⟨standard_token_sequence_admissible tokens,
        standard_token_sequence_freeSupport_nil tokens⟩
  have hComponentEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        componentCode ≐ₘ standardCode := by
    simpa [tokens, standardCode] using
      fs_zfc_support_raw_logical_formula_payload_component_code_eq_standard
        componentCode numericCode code traceId indexId
        hIds hComponentCode hNumericCode
        hTraceFreshSequence hIndexFreshSequence hIndexFreshCode
        hTraceFreshContext hComponent hNumericEquality
  have hFormulaFields :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        formula_codeₘ(componentCode) ∧ₘ
          fs_formula_replay_condition componentCode :=
    FirstOrder.Derives.conjElimLeft hComponent
  have hComponentReplay :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        fs_formula_replay_condition componentCode :=
    FirstOrder.Derives.conjElimRight hFormulaFields
  have hReplayTransport :=
    fs_formula_replay_condition_iff_of_equality
      componentCode standardCode
      hComponentCode hStandardBoundary.1
      hComponentEquality
  have hStandardReplay :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        fs_formula_replay_condition standardCode :=
    FirstOrder.Derives.iffElimRight
      hReplayTransport hComponentReplay
  rcases fs_formula_tokens_or_bad_index tokens with
    hTokens | ⟨tokenIndex, hTokenIndex, hToken⟩
  · cases hBinderCheck :
        fs_formula_binder_tokens_check tokens with
    | false =>
        have hReplayNot :
            Derives fs_zfc_support_raw_theory [] (
              ¬ₘ fs_formula_replay_condition standardCode) := by
          simpa [standardCode] using
            fs_zfc_support_raw_standard_token_sequence_replay_neg_of_binder_check
              tokens hBinderCheck
        exact FirstOrder.Derives.negElim
          hStandardReplay
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Γ) (by simp)
            hReplayNot)
    | true =>
        have hBinders : FSFormulaBinderTokens tokens := by
          simpa [FSFormulaBinderTokens] using hBinderCheck
        have hFormulaPredicate :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              formula_codeₘ(componentCode) :=
          FirstOrder.Derives.conjElimLeft hFormulaFields
        have hDefinition :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              is_formula_code_definition_instance
                componentCode := by
          apply FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Γ) (by simp)
          exact
            fs_zfc_support_raw_derives_of_godel_quotation
              (gq_formula_code_definition_instance
                componentCode hComponentCode)
        have hComponentMember :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              componentCode ∈ₘ FormulaCodeₘ :=
          FirstOrder.Derives.iffElimRight
            hDefinition hFormulaPredicate
        have hStandardMember :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              standardCode ∈ₘ FormulaCodeₘ :=
          FirstOrder.Derives.iffElimRight
            (membership_left_iff_of_equality
              componentCode standardCode FormulaCodeₘ
              hComponentCode hStandardBoundary.1
              formula_code_set_term_admissible
              hComponentEquality)
            hComponentMember
        have hStandardMemberNot :
            Derives fs_zfc_support_raw_theory [] (
              ¬ₘ (standardCode ∈ₘ FormulaCodeₘ)) := by
          apply
            fs_zfc_support_raw_derives_of_godel_quotation
          simpa [tokens, standardCode] using
            gq_standard_formula_code_not_of_decode_none
              freeBase [] tokens hTokens hBinders
              (by simpa [tokens] using hDecode)
        exact FirstOrder.Derives.negElim
          hStandardMember
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Γ) (by simp)
            hStandardMemberNot)
  · have hStandardSignature :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_formula_signature_condition standardCode := by
      simpa [fs_formula_replay_condition] using
        FirstOrder.Derives.conjElimLeft hStandardReplay
    have hSignatureNot :
        Derives fs_zfc_support_raw_theory [] (
          ¬ₘ fs_formula_signature_condition standardCode) := by
      simpa [standardCode] using
        fs_zfc_support_raw_standard_token_sequence_signature_neg_of_token
          tokens tokenIndex hTokenIndex hToken
    exact FirstOrder.Derives.negElim
      hStandardSignature
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        hSignatureNot)

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
