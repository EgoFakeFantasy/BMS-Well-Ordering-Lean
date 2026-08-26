import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.PairingInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceConditionRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateBaseInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.NamedFormulaPayloadFailure

/-!
# 逻辑 payload 失败的对象层反演

本模块只消费基础逻辑证书共有的二元关系：证书配对、自然数序列码关系与序列
定义域。它不展开完整逻辑 transcript，也不依赖具体 Hilbert 公理构造器。
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
地面证书中的 payload 长度若与分支 arity 不同，则该分支在对象层推出矛盾。

证明只恢复 payload 的标准自然数序列，并比较两个定义域 numeral。
-/
theorem fs_zfc_support_raw_logical_payload_length_falsum
    {Γ : Context signature}
    (raw tag arity : Nat)
    (payload sequence : SetTerm)
    (traceId indexId : FreeVarId)
    (hPayload : Term.Admissible payload SetSort.set)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hTraceNeIndex : traceId ≠ indexId)
    (hTraceFreshSequence :
      (SetSort.set, traceId) ∉ Term.freeSupport sequence)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉ Term.freeSupport sequence)
    (hIndexFreshPayload :
      (SetSort.set, indexId) ∉ Term.freeSupport payload)
    (hTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport formula)
    (hPair :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(raw) ≐ₘ
          godel_pairₘ(⟨numₘ(tag), payload⟩ₘ))
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        nat_sequence_code_condition_with_ids
          sequence payload traceId indexId)
    (hDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ numₘ(arity))
    (hLength :
      (nat_sequence_decode
        (godel_unpair_value raw).2).length ≠ arity) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  let payloadCode : Nat := (godel_unpair_value raw).2
  let tokens : List Nat := nat_sequence_decode payloadCode
  have hPayloadNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        payload ∈ₘ ωₘ :=
    (fs_zfc_support_raw_nat_sequence_code_condition_parts
      sequence payload traceId indexId hCondition).2.1
  have hPayloadEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        payload ≐ₘ numₘ(payloadCode) := by
    simpa [payloadCode] using
      ProofT.pair_right_unique
        ProofT.ZFC.pairing_core
        raw tag payload hPayload hPayloadNatural hPair
  have hPayloadCodeEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        payload ≐ₘ numₘ(nat_sequence_code_value tokens) := by
    simpa [tokens, payloadCode, nat_sequence_code_value_decode] using
      hPayloadEquality
  have hSequenceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence ≐ₘ standard_token_sequence tokens :=
    fs_zfc_support_raw_nat_sequence_code_condition_unique_of_code_equality
      sequence payload tokens traceId indexId
      hSequence hPayload hTraceNeIndex
      hTraceFreshSequence hIndexFreshSequence
      hIndexFreshPayload hTraceFreshContext
      hCondition hPayloadCodeEquality
  have hDecodedDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ numₘ(tokens.length) :=
    GodelQuotation.gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      sequence tokens hSequenceEquality
      (hCode := Term.check_admissible_complete hSequence)
  have hNumeralEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(tokens.length) ≐ₘ numₘ(arity) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hDecodedDomain)
      hDomain
  exact fs_zfc_support_raw_falsum_of_numeral_equality
    (by simpa [tokens, payloadCode] using hLength)
    hNumeralEquality

/--
地面证书与对象序列关系唯一确定第 `componentIndex` 个数值字段。

这是 payload 反演的公共二元核心：它不读取组件公式条件，也不调用任何 decoder。
-/
theorem fs_zfc_support_raw_logical_payload_component_numeric_eq
    {Γ : Context signature}
    (raw tag componentIndex : Nat)
    (payload sequence numericCode : SetTerm)
    (traceId indexId : FreeVarId)
    (hPayload : Term.Admissible payload SetSort.set)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hTraceNeIndex : traceId ≠ indexId)
    (hTraceFreshSequence :
      (SetSort.set, traceId) ∉ Term.freeSupport sequence)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉ Term.freeSupport sequence)
    (hIndexFreshPayload :
      (SetSort.set, indexId) ∉ Term.freeSupport payload)
    (hTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport formula)
    (hPair :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(raw) ≐ₘ
          godel_pairₘ(⟨numₘ(tag), payload⟩ₘ))
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        nat_sequence_code_condition_with_ids
          sequence payload traceId indexId)
    (hNumericAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numericCode ≐ₘ
          (sequence ·ₘ numₘ(componentIndex)))
    (hComponentIndex :
      componentIndex <
        (nat_sequence_decode
          (godel_unpair_value raw).2).length) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      numericCode ≐ₘ
        numₘ((nat_sequence_decode
          (godel_unpair_value raw).2)[componentIndex]) := by
  let payloadCode : Nat := (godel_unpair_value raw).2
  let tokens : List Nat := nat_sequence_decode payloadCode
  let componentValue : Nat := tokens[componentIndex]
  have hPayloadNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        payload ∈ₘ ωₘ :=
    (fs_zfc_support_raw_nat_sequence_code_condition_parts
      sequence payload traceId indexId hCondition).2.1
  have hPayloadEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        payload ≐ₘ numₘ(payloadCode) := by
    simpa [payloadCode] using
      ProofT.pair_right_unique
        ProofT.ZFC.pairing_core
        raw tag payload hPayload hPayloadNatural hPair
  have hPayloadCodeEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        payload ≐ₘ numₘ(nat_sequence_code_value tokens) := by
    simpa [tokens, payloadCode, nat_sequence_code_value_decode] using
      hPayloadEquality
  have hSequenceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence ≐ₘ standard_token_sequence tokens :=
    fs_zfc_support_raw_nat_sequence_code_condition_unique_of_code_equality
      sequence payload tokens traceId indexId
      hSequence hPayload hTraceNeIndex
      hTraceFreshSequence hIndexFreshSequence
      hIndexFreshPayload hTraceFreshContext
      hCondition hPayloadCodeEquality
  have hSequenceAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (sequence ·ₘ numₘ(componentIndex)) ≐ₘ
          (standard_token_sequence tokens ·ₘ
            numₘ(componentIndex)) :=
    function_application_term_congr_function_of_equality
      sequence (standard_token_sequence tokens)
      (numₘ(componentIndex))
      hSequence
      (standard_token_sequence_admissible tokens)
      (finite_numeral_term_admissible componentIndex)
      hSequenceEquality
  have hGet :
      tokens[componentIndex]? = some componentValue := by
    simp [componentValue]
  have hStandardAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (standard_token_sequence tokens ·ₘ
            numₘ(componentIndex)) ≐ₘ
          numₘ(componentValue) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_standard_sequence
          (standard_token_sequence_apply_getElem?
            tokens hGet)
  simpa [componentValue, tokens, payloadCode] using
    Metatheory.Derives.equality_trans hNumericAt <|
      Metatheory.Derives.equality_trans
        hSequenceAt hStandardAt

/--
地面 payload 的第 `componentIndex` 个公式字段等于该数值字段解出的标准 token 串。

该接口仍不要求 decoder 成功；它只组合数值字段唯一性与组件自身的序列关系。
-/
theorem fs_zfc_support_raw_logical_payload_component_code_eq_standard
    {Γ : Context signature}
    (raw tag componentIndex : Nat)
    (payload sequence componentCode numericCode : SetTerm)
    (traceId indexId : FreeVarId)
    (hPayload : Term.Admissible payload SetSort.set)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hComponentCode : Term.Admissible componentCode SetSort.set)
    (hNumericCode : Term.Admissible numericCode SetSort.set)
    (hTraceNeIndex : traceId ≠ indexId)
    (hTraceFreshSequence :
      (SetSort.set, traceId) ∉ Term.freeSupport sequence)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉ Term.freeSupport sequence)
    (hIndexFreshPayload :
      (SetSort.set, indexId) ∉ Term.freeSupport payload)
    (hTraceFreshComponent :
      (SetSort.set, traceId) ∉ Term.freeSupport componentCode)
    (hIndexFreshComponent :
      (SetSort.set, indexId) ∉ Term.freeSupport componentCode)
    (hIndexFreshNumeric :
      (SetSort.set, indexId) ∉ Term.freeSupport numericCode)
    (hTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport formula)
    (hPair :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(raw) ≐ₘ
          godel_pairₘ(⟨numₘ(tag), payload⟩ₘ))
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        nat_sequence_code_condition_with_ids
          sequence payload traceId indexId)
    (hNumericAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numericCode ≐ₘ
          (sequence ·ₘ numₘ(componentIndex)))
    (hComponent :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_formula_payload_component_condition_with_ids
          componentCode numericCode traceId indexId)
    (hComponentIndex :
      componentIndex <
        (nat_sequence_decode
          (godel_unpair_value raw).2).length) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      componentCode ≐ₘ
        standard_token_sequence
          (nat_sequence_decode
            ((nat_sequence_decode
              (godel_unpair_value raw).2)[componentIndex])) := by
  have hNumericEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numericCode ≐ₘ
          numₘ((nat_sequence_decode
            (godel_unpair_value raw).2)[componentIndex]) :=
    fs_zfc_support_raw_logical_payload_component_numeric_eq
      raw tag componentIndex payload sequence numericCode
      traceId indexId hPayload hSequence hTraceNeIndex
      hTraceFreshSequence hIndexFreshSequence
      hIndexFreshPayload hTraceFreshContext
      hPair hCondition hNumericAt hComponentIndex
  exact
    fs_zfc_support_raw_logical_formula_payload_component_code_eq_standard
      componentCode numericCode
      ((nat_sequence_decode
        (godel_unpair_value raw).2)[componentIndex])
      traceId indexId hTraceNeIndex
      hComponentCode hNumericCode
      hTraceFreshComponent hIndexFreshComponent hIndexFreshNumeric
      hTraceFreshContext hComponent hNumericEquality

/--
地面 payload 的某个字段若被具名公式 decoder 拒绝，则该字段条件推出矛盾。

索引只用于从已经恢复的标准 payload 序列读取数值字段；不反演任何额外 trace。
-/
theorem fs_zfc_support_raw_logical_payload_component_falsum
    {Γ : Context signature}
    (raw tag freeBase componentIndex : Nat)
    (payload sequence componentCode numericCode : SetTerm)
    (traceId indexId : FreeVarId)
    (hPayload : Term.Admissible payload SetSort.set)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hComponentCode : Term.Admissible componentCode SetSort.set)
    (hNumericCode : Term.Admissible numericCode SetSort.set)
    (hTraceNeIndex : traceId ≠ indexId)
    (hTraceFreshSequence :
      (SetSort.set, traceId) ∉ Term.freeSupport sequence)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉ Term.freeSupport sequence)
    (hIndexFreshPayload :
      (SetSort.set, indexId) ∉ Term.freeSupport payload)
    (hTraceFreshComponent :
      (SetSort.set, traceId) ∉ Term.freeSupport componentCode)
    (hIndexFreshComponent :
      (SetSort.set, indexId) ∉ Term.freeSupport componentCode)
    (hIndexFreshNumeric :
      (SetSort.set, indexId) ∉ Term.freeSupport numericCode)
    (hTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport formula)
    (hPair :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(raw) ≐ₘ
          godel_pairₘ(⟨numₘ(tag), payload⟩ₘ))
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        nat_sequence_code_condition_with_ids
          sequence payload traceId indexId)
    (hNumericAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numericCode ≐ₘ
          (sequence ·ₘ numₘ(componentIndex)))
    (hComponent :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_formula_payload_component_condition_with_ids
          componentCode numericCode traceId indexId)
    (hComponentIndex :
      componentIndex <
        (nat_sequence_decode
          (godel_unpair_value raw).2).length)
    (hDecode :
      fs_named_formula_token_code_decode freeBase
          (nat_sequence_decode
            (godel_unpair_value raw).2)[componentIndex] =
        none) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hNumericEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numericCode ≐ₘ
          numₘ((nat_sequence_decode
            (godel_unpair_value raw).2)[componentIndex]) :=
    fs_zfc_support_raw_logical_payload_component_numeric_eq
      raw tag componentIndex payload sequence numericCode
      traceId indexId hPayload hSequence hTraceNeIndex
      hTraceFreshSequence hIndexFreshSequence
      hIndexFreshPayload hTraceFreshContext
      hPair hCondition hNumericAt hComponentIndex
  apply
    fs_zfc_support_raw_logical_formula_payload_component_falsum_of_named_decode_none
      componentCode numericCode freeBase
      ((nat_sequence_decode
        (godel_unpair_value raw).2)[componentIndex])
      traceId indexId hTraceNeIndex
      hComponentCode hNumericCode
      hTraceFreshComponent hIndexFreshComponent
      hIndexFreshNumeric hTraceFreshContext
      hComponent hNumericEquality
  exact hDecode

/-! ## 有限 witness 的公共拒绝提升 -/

/-- 将打开 body 的反证逐层提升过有限存在 witness。 -/
theorem fs_zfc_support_raw_exists_assignments_imp_falsum
    (assignments : List (FreeVarId × SetTerm))
    (body : SetFormula)
    (hBody :
      Derives fs_zfc_support_raw_theory [] (
        body ⟶ₘ Formula.falsum)) :
    Derives fs_zfc_support_raw_theory [] (
      Formula.existsFreeAssignments
          SetSort.set assignments body ⟶ₘ
        Formula.falsum) := by
  induction assignments with
  | nil =>
      simpa [Formula.existsFreeAssignments] using hBody
  | cons assignment assignments ih =>
      rcases assignment with ⟨eigen, witness⟩
      apply FirstOrder.Derives.exists_imp_of_imp
        (T := fs_zfc_support_raw_theory)
        (Γ := ([] : Context signature))
        (sort := SetSort.set)
        (eigen := eigen)
        (body :=
          Formula.existsFreeAssignments
            SetSort.set assignments body)
        (conclusion := Formula.falsum)
      · intro formula hFormula
        rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
        exact List.not_mem_nil
      · intro formula hFormula
        exact False.elim (List.not_mem_nil hFormula)
      · exact List.not_mem_nil
      · simpa [Formula.existsFreeAssignments] using ih

/-- 将有限对象存在量词下的蕴含提升到闭结论。 -/
theorem fs_zfc_support_raw_exists_assignments_imp_closed
    (assignments : List (FreeVarId × SetTerm))
    (body conclusion : SetFormula)
    (hConclusionClosed :
      Formula.freeSupport conclusion = [])
    (hBody :
      Derives fs_zfc_support_raw_theory [] (
        body ⟶ₘ conclusion)) :
    Derives fs_zfc_support_raw_theory [] (
      Formula.existsFreeAssignments
          SetSort.set assignments body ⟶ₘ
        conclusion) := by
  induction assignments with
  | nil =>
      simpa [Formula.existsFreeAssignments] using hBody
  | cons assignment assignments ih =>
      rcases assignment with ⟨eigen, witness⟩
      apply FirstOrder.Derives.exists_imp_of_imp
        (T := fs_zfc_support_raw_theory)
        (Γ := ([] : Context signature))
        (sort := SetSort.set)
        (eigen := eigen)
        (body :=
          Formula.existsFreeAssignments
            SetSort.set assignments body)
        (conclusion := conclusion)
      · intro formula hFormula
        rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
        exact List.not_mem_nil
      · intro formula hFormula
        exact False.elim (List.not_mem_nil hFormula)
      · rw [hConclusionClosed]
        exact List.not_mem_nil
      · simpa [Formula.existsFreeAssignments] using ih

/--
将有限对象存在量词下的蕴含提升到对全部 witness 变量新鲜的结论。

这比闭结论版本弱，允许终端适配器保留开放的 transcript 公式码。
-/
theorem fs_zfc_support_raw_exists_assignments_imp_fresh
    (assignments : List (FreeVarId × SetTerm))
    (body conclusion : SetFormula)
    (hConclusionFresh :
      ∀ eigen witness,
        (eigen, witness) ∈ assignments →
          (SetSort.set, eigen) ∉
            Formula.freeSupport conclusion)
    (hBody :
      Derives fs_zfc_support_raw_theory [] (
        body ⟶ₘ conclusion)) :
    Derives fs_zfc_support_raw_theory [] (
      Formula.existsFreeAssignments
          SetSort.set assignments body ⟶ₘ
        conclusion) := by
  induction assignments with
  | nil =>
      simpa [Formula.existsFreeAssignments] using hBody
  | cons assignment assignments ih =>
      rcases assignment with ⟨eigen, witness⟩
      apply FirstOrder.Derives.exists_imp_of_imp
        (T := fs_zfc_support_raw_theory)
        (Γ := ([] : Context signature))
        (sort := SetSort.set)
        (eigen := eigen)
        (body :=
          Formula.existsFreeAssignments
            SetSort.set assignments body)
        (conclusion := conclusion)
      · intro formula hFormula
        rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
        exact List.not_mem_nil
      · intro formula hFormula
        exact False.elim (List.not_mem_nil hFormula)
      · exact hConclusionFresh eigen witness (by simp)
      · simpa [Formula.existsFreeAssignments] using
          ih (fun tailEigen tailWitness hMember =>
            hConclusionFresh tailEigen tailWitness (by simp [hMember]))

/-- 将有限 witness 下的 body 反证闭合为对象层分支否定。 -/
theorem fs_zfc_support_raw_exists_assignments_neg
    (assignments : List (FreeVarId × SetTerm))
    (body : SetFormula)
    (hBody :
      Derives fs_zfc_support_raw_theory [] (
        body ⟶ₘ Formula.falsum)) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ Formula.existsFreeAssignments
        SetSort.set assignments body) := by
  let condition : SetFormula :=
    Formula.existsFreeAssignments
      SetSort.set assignments body
  have hConditionImp :
      Derives fs_zfc_support_raw_theory [] (
        condition ⟶ₘ Formula.falsum) := by
    simpa [condition] using
      fs_zfc_support_raw_exists_assignments_imp_falsum
        assignments body hBody
  have hCondition :
      Formula.Admissible condition :=
    Formula.Admissible.imp_left hConditionImp.admissible
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete hCondition)
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := [condition]) (by simp)
      hConditionImp)
    (FirstOrder.Derives.assumption
      (by simp [condition])
      (Formula.check_admissible_complete hCondition))

/--
对象分支若唯一推出一个规范候选码，而当前公式码又等于不同的规范行，则该分支
为假。该接口与具体逻辑 tag 无关。
-/
theorem fs_zfc_support_raw_neg_of_candidate_code_ne
    (condition : SetFormula)
    (formulaCode : SetTerm)
    (row expectedTokens : List Nat)
    (hExpected :
      Derives fs_zfc_support_raw_theory [] (
        condition ⟶ₘ
          formulaCode ≐ₘ standard_token_sequence expectedTokens))
    (hFormulaToRow :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ standard_token_sequence row))
    (hRowNe : row ≠ expectedTokens) :
    Derives fs_zfc_support_raw_theory [] (¬ₘ condition) := by
  have hCondition :
      Formula.Admissible condition :=
    Formula.Admissible.imp_left hExpected.admissible
  apply FirstOrder.Derives.negIntro
    (hBodyCheck := Formula.check_admissible_complete hCondition)
  let Γ : Context signature := [condition]
  have hConditionAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hCondition)
  have hFormulaExpected :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        formulaCode ≐ₘ standard_token_sequence expectedTokens :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) hExpected)
      hConditionAt
  have hFormulaToRowAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        formulaCode ≐ₘ standard_token_sequence row :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) hFormulaToRow
  have hRowsEqual :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence row ≐ₘ
          standard_token_sequence expectedTokens :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hFormulaToRowAt)
      hFormulaExpected
  exact FirstOrder.Derives.negElim hRowsEqual <|
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_standard_sequence <|
          standard_token_sequence_ne hRowNe

/-- 从按原自由变量关闭的存在链可容许性恢复开放 body 的可容许性。 -/
theorem fs_zfc_admissible_body_of_exists_assignments
    (assignments : List (FreeVarId × SetTerm))
    (body : SetFormula)
    (hCondition :
      Formula.Admissible
        (Formula.existsFreeAssignments
          SetSort.set assignments body)) :
    Formula.Admissible body := by
  induction assignments with
  | nil =>
      simpa [Formula.existsFreeAssignments] using hCondition
  | cons assignment assignments ih =>
      rcases assignment with ⟨eigen, witness⟩
      have hOpened :=
        Formula.Admissible.exists_openAt
          (term := (x#eigen : SetTerm))
          SetSort.set hCondition
          (set_variable_admissible eigen)
      apply ih
      simpa [Formula.existsFreeAssignments,
        Formula.openAt_closeFreeAt] using hOpened

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
