import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalPropositionalQuotation

/-!
# 命题逻辑证书公式 mismatch 的对象层拒绝

本模块处理 payload 已成功解码、但当前证明行不等于对应命题公理实例的分支。
证明只恢复 payload 中实际出现的数值字段与原始 token 串，再用公理码 quotation
把对象见证计算到同一批 token；不使用解码公式的 canonical re-quotation。
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

/-- 对象变量项的自由支持只含自身。 -/
private theorem fs_zfc_prop_mismatch_set_variable_fresh
    (source target : FreeVarId)
    (hNe : source ≠ target) :
    (SetSort.set, source) ∉
      Term.freeSupport (x#target) := by
  intro hMember
  change
    (SetSort.set, source) ∈
      [(SetSort.set, target)] at hMember
  exact hNe <| congrArg Prod.snd <|
    List.mem_singleton.mp hMember

/-- 对象变量在闭 numeral 上的函数应用不增加自由变量。 -/
private theorem fs_zfc_prop_mismatch_application_numeral_fresh
    (source target : FreeVarId)
    (value : Nat)
    (hNe : source ≠ target) :
    (SetSort.set, source) ∉
      Term.freeSupport (x#target ·ₘ numₘ(value)) := by
  intro hMember
  simp [Term.freeSupport, Term.freeSupportList,
    finite_numeral_term_freeSupport] at hMember
  exact
    fs_zfc_prop_mismatch_set_variable_fresh
      source target hNe hMember

/--
在空背景中把一个打开见证的蕴含提升过一层存在量词；结论必须是闭公式。

该接口用于把证书分支唯一决定的候选公式码提升到闭结论。
-/
private theorem fs_zfc_prop_mismatch_exists_imp_closed
    (eigen : FreeVarId)
    (body conclusion : SetFormula)
    (hConclusionClosed :
      Formula.freeSupport conclusion = [])
    (hImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          body ⟶ₘ conclusion) :
    ([] : Context signature)
      ⊢ₘ[fs_zfc_support_raw_theory]
        (∃ₘ[SetSort.set, eigen], body) ⟶ₘ
          conclusion := by
  apply FirstOrder.Derives.exists_imp_of_imp
    (T := fs_zfc_support_raw_theory)
    (Γ := ([] : Context signature))
    (sort := SetSort.set)
    (eigen := eigen)
    (body := body)
    (conclusion := conclusion)
  · intro proposition hProposition
    rw [(fs_zfc_support_raw_theory_sentence hProposition).2]
    exact List.not_mem_nil
  · intro proposition hProposition
    exact False.elim (List.not_mem_nil hProposition)
  · rw [hConclusionClosed]
    exact List.not_mem_nil
  · exact hImp

/--
一元命题公理分支唯一决定其候选标准公式码。

`hConstructorStandard` 是具体公理构造器的可计算 quotation；其输入严格是 payload
字段解出的原始 token 串，而不是 decoder 结果的重新 quotation。
-/
theorem fs_zfc_support_raw_logical_unary_base_certificate_eq_standard_imp
    (raw tag componentValue : Nat)
    (expectedTokens : List Nat)
    (constructor : SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId componentId traceId indexId : FreeVarId)
    (hTraceFresh :
      traceId ∉ [payloadId, sequenceId, componentId])
    (hIndexFresh :
      indexId ∉ [payloadId, sequenceId, componentId])
    (hTraceNeIndex : traceId ≠ indexId)
    (hConstructorAdmissible :
      ∀ component,
        Term.Admissible component SetSort.set →
          Term.Admissible (constructor component) SetSort.set)
    (hConstructorSupport :
      ∀ component freeVariable,
        freeVariable ∈ Term.freeSupport (constructor component) →
          freeVariable ∈ Term.freeSupport component)
    (hConstructorSubstitute :
      ∀ parameter replacement component,
        Term.substituteFree SetSort.set parameter replacement
            (constructor component) =
          constructor
            (Term.substituteFree SetSort.set parameter replacement
              component))
    (hFormulaCode :
      Term.Admissible formulaCode SetSort.set)
    (hCertificate :
      Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        [payloadId, sequenceId, componentId, traceId, indexId]
        [formulaCode, certificate])
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hPayloadCodes :
      nat_sequence_decode
          (godel_unpair_value raw).2 =
        [componentValue])
    (hConstructorStandard :
      Derives fs_zfc_support_raw_theory [] (
        constructor
            (standard_token_sequence
              (nat_sequence_decode componentValue)) ≐ₘ
          standard_token_sequence expectedTokens)) :
    Derives fs_zfc_support_raw_theory [] (
      logical_unary_base_certificate_condition_with_ids
          tag constructor formulaCode certificate
          payloadId sequenceId componentId traceId indexId ⟶ₘ
        formulaCode ≐ₘ standard_token_sequence expectedTokens) := by
  let body : SetFormula :=
    logical_certificate_conjunction [
      certificate ≐ₘ
        godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
      nat_sequence_code_condition_with_ids
        (x#sequenceId) (x#payloadId) traceId indexId,
      domₘ(x#sequenceId) ≐ₘ numₘ(1),
      logical_formula_payload_component_condition_with_ids
        (x#componentId) (x#sequenceId ·ₘ numₘ(0))
        traceId indexId,
      formulaCode ≐ₘ constructor (x#componentId)]
  let target : SetFormula :=
    formulaCode ≐ₘ standard_token_sequence expectedTokens
  have hPayload :
      Term.Admissible (x#payloadId) SetSort.set :=
    set_variable_admissible payloadId
  have hSequence :
      Term.Admissible (x#sequenceId) SetSort.set :=
    set_variable_admissible sequenceId
  have hComponent :
      Term.Admissible (x#componentId) SetSort.set :=
    set_variable_admissible componentId
  have hNumeric :
      Term.Admissible
        (x#sequenceId ·ₘ numₘ(0)) SetSort.set :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(0)) hSequence
      (finite_numeral_term_admissible 0)
  have hTracePayload : traceId ≠ payloadId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hTraceSequence : traceId ≠ sequenceId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hTraceComponent : traceId ≠ componentId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hIndexPayload : indexId ≠ payloadId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hIndexSequence : indexId ≠ sequenceId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hIndexComponent : indexId ≠ componentId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hBody :
      Formula.Admissible body := by
    dsimp [body]
    apply logical_certificate_conjunction_admissible
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with rfl | rfl | rfl | rfl | rfl
    · exact Formula.Admissible.equal hCertificate <|
        godel_pairing_term_admissible _ <|
          ordered_pair_term_admissible _ _
            (finite_numeral_term_admissible tag) hPayload
    · exact nat_sequence_code_condition_with_ids_admissible
        (x#sequenceId) (x#payloadId) traceId indexId
        hSequence hPayload
    · exact Formula.Admissible.equal
        (domain_term_admissible (x#sequenceId) hSequence)
        (finite_numeral_term_admissible 1)
    · exact
        logical_formula_payload_component_condition_with_ids_admissible
          (x#componentId) (x#sequenceId ·ₘ numₘ(0))
          traceId indexId hComponent hNumeric
    · exact Formula.Admissible.equal hFormulaCode
        (hConstructorAdmissible (x#componentId) hComponent)
  have hBodyImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          body ⟶ₘ target := by
    nd_apply FirstOrder.Derives.impIntro
      (hAntecedentCheck :=
        Formula.check_admissible_complete hBody)
    let Γ : Context signature := [body]
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete hBody)
    have hPairField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ) := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hRestOne :=
      FirstOrder.Derives.conjElimRight hBodyAt
    have hSequenceField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          nat_sequence_code_condition_with_ids
            (x#sequenceId) (x#payloadId) traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestOne
    have hRestTwo :=
      FirstOrder.Derives.conjElimRight hRestOne
    have hComponentField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          logical_formula_payload_component_condition_with_ids
            (x#componentId) (x#sequenceId ·ₘ numₘ(0))
            traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight hRestTwo
    have hFormulaField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          formulaCode ≐ₘ constructor (x#componentId) := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight hRestTwo
    have hCertificateCodeAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          certificate ≐ₘ numₘ(raw) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) hCertificateCode
    have hPair :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ) :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm hCertificateCodeAt)
        hPairField
    have hTraceFreshContext :
        ∀ proposition, proposition ∈ Γ →
          (SetSort.set, traceId) ∉
            Formula.freeSupport proposition := by
      intro proposition hProposition
      have hEquality : proposition = body :=
        List.mem_singleton.mp <| by
          simpa [Γ] using hProposition
      subst proposition
      intro hMember
      rcases logical_certificate_conjunction_freeSupport
          _ (SetSort.set, traceId) hMember with
        ⟨field, hField, hFieldSupport⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
      rcases hField with rfl | rfl | rfl | rfl | rfl
      · have hCases :
            (SetSort.set, traceId) ∈ Term.freeSupport certificate ∨
              traceId = payloadId := by
          simpa [Formula.freeSupport, Term.freeSupport,
            Term.freeSupportList,
            finite_numeral_term_freeSupport] using hFieldSupport
        rcases hCases with hCertificateMember | hPayload
        · exact False.elim <|
            hReservedFresh certificate (by simp) traceId (by simp)
              hCertificateMember
        · exact hTracePayload hPayload
      · rcases nat_sequence_code_condition_with_ids_freeSupport_subset
            (x#sequenceId) (x#payloadId) traceId indexId
            (SetSort.set, traceId) hFieldSupport with
          hMember | hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId sequenceId hTraceSequence) hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId payloadId hTracePayload) hMember
      · simp [Formula.freeSupport, Term.freeSupport,
          Term.freeSupportList,
          finite_numeral_term_freeSupport] at hFieldSupport
        exact hTraceSequence hFieldSupport
      · rcases
            logical_formula_payload_component_condition_with_ids_freeSupport_subset
              (x#componentId) (x#sequenceId ·ₘ numₘ(0))
              traceId indexId (SetSort.set, traceId)
              hFieldSupport with
          hMember | hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId componentId hTraceComponent) hMember
        · simp [Term.freeSupport, Term.freeSupportList,
            finite_numeral_term_freeSupport] at hMember
          exact hTraceSequence hMember
      · have hConstructorMember :
            (SetSort.set, traceId) ∈
              Term.freeSupport
                (constructor (x#componentId)) := by
          have hCases :
              (SetSort.set, traceId) ∈ Term.freeSupport formulaCode ∨
                (SetSort.set, traceId) ∈
                  Term.freeSupport (constructor (x#componentId)) := by
            simpa [Formula.freeSupport] using hFieldSupport
          rcases hCases with hFormulaMember | hConstructorMember
          · exact False.elim <|
              hReservedFresh formulaCode (by simp) traceId (by simp)
                hFormulaMember
          · exact hConstructorMember
        exact
          (fs_zfc_prop_mismatch_set_variable_fresh
            traceId componentId hTraceComponent) <|
            hConstructorSupport
              (x#componentId) (SetSort.set, traceId)
              hConstructorMember
    have hComponentEqualityRaw :=
      fs_zfc_support_raw_logical_payload_component_code_eq_standard
        raw tag 0
        (x#payloadId) (x#sequenceId) (x#componentId)
        (x#sequenceId ·ₘ numₘ(0))
        traceId indexId hPayload hSequence hComponent hNumeric
        hTraceNeIndex
        (fs_zfc_prop_mismatch_set_variable_fresh
          traceId sequenceId hTraceSequence)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId sequenceId hIndexSequence)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId payloadId hIndexPayload)
        (fs_zfc_prop_mismatch_set_variable_fresh
          traceId componentId hTraceComponent)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId componentId hIndexComponent)
        (fs_zfc_prop_mismatch_application_numeral_fresh
          indexId sequenceId 0 hIndexSequence)
        hTraceFreshContext hPair hSequenceField
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (x#sequenceId ·ₘ numₘ(0)))
        hComponentField
        (by simp [hPayloadCodes])
    have hComponentEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          (x#componentId) ≐ₘ
            standard_token_sequence
              (nat_sequence_decode componentValue) := by
      simpa [hPayloadCodes] using hComponentEqualityRaw
    have hConstructorEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          constructor (x#componentId) ≐ₘ
            constructor
              (standard_token_sequence
                (nat_sequence_decode componentValue)) :=
      Metatheory.Derives.unary_term_constructor_congr_of_equality
        constructor hConstructorAdmissible hConstructorSubstitute
        (x#componentId)
        (standard_token_sequence
          (nat_sequence_decode componentValue))
        hComponent
        (standard_token_sequence_admissible
          (nat_sequence_decode componentValue))
        hComponentEquality
    have hConstructorStandardAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          constructor
              (standard_token_sequence
                (nat_sequence_decode componentValue)) ≐ₘ
            standard_token_sequence expectedTokens :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) hConstructorStandard
    have hFormulaExpected :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          formulaCode ≐ₘ
            standard_token_sequence expectedTokens :=
      Metatheory.Derives.equality_trans hFormulaField <|
        Metatheory.Derives.equality_trans hConstructorEquality
          hConstructorStandardAt
    simpa [target] using hFormulaExpected
  have hWrapped :=
    fs_zfc_support_raw_exists_assignments_imp_fresh
      [(payloadId, x#payloadId), (sequenceId, x#sequenceId),
        (componentId, x#componentId)]
      body target
      (by
        intro eigen witness hMember
        have hEigen :
            eigen ∈ [payloadId, sequenceId, componentId] := by
          simpa using
            List.mem_map_of_mem (f := Prod.fst) hMember
        have hReserved :
            eigen ∈
              [payloadId, sequenceId, componentId, traceId, indexId] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hEigen ⊢
          rcases hEigen with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
        simpa [target, Formula.freeSupport,
          standard_token_sequence_freeSupport_nil] using
            hReservedFresh formulaCode (by simp) eigen hReserved)
      hBodyImp
  simpa [target, logical_unary_base_certificate_condition_with_ids,
    body, Formula.existsFreeAssignments] using hWrapped

/--
二元命题公理分支唯一决定其候选标准公式码。

两个组件分别由 payload 的第 0、1 个原始数值字段恢复；构造器等式只通过
二元项构造同余传输，不读取 decoder 输出的 canonical quotation。
-/
theorem fs_zfc_support_raw_logical_binary_base_certificate_eq_standard_imp
    (raw tag leftValue rightValue : Nat)
    (expectedTokens : List Nat)
    (constructor : SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId leftId rightId traceId indexId : FreeVarId)
    (hTraceFresh :
      traceId ∉ [payloadId, sequenceId, leftId, rightId])
    (hIndexFresh :
      indexId ∉ [payloadId, sequenceId, leftId, rightId])
    (hTraceNeIndex : traceId ≠ indexId)
    (hConstructorAdmissible :
      ∀ left right,
        Term.Admissible left SetSort.set →
        Term.Admissible right SetSort.set →
          Term.Admissible (constructor left right) SetSort.set)
    (hConstructorSupport :
      ∀ left right freeVariable,
        freeVariable ∈
            Term.freeSupport (constructor left right) →
          freeVariable ∈ Term.freeSupport left ∨
            freeVariable ∈ Term.freeSupport right)
    (hConstructorSubstitute :
      ∀ parameter replacement left right,
        Term.substituteFree SetSort.set parameter replacement
            (constructor left right) =
          constructor
            (Term.substituteFree SetSort.set parameter replacement left)
            (Term.substituteFree SetSort.set parameter replacement right))
    (hFormulaCode :
      Term.Admissible formulaCode SetSort.set)
    (hCertificate :
      Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        [payloadId, sequenceId, leftId, rightId, traceId, indexId]
        [formulaCode, certificate])
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hPayloadCodes :
      nat_sequence_decode
          (godel_unpair_value raw).2 =
        [leftValue, rightValue])
    (hConstructorStandard :
      Derives fs_zfc_support_raw_theory [] (
        constructor
            (standard_token_sequence
              (nat_sequence_decode leftValue))
            (standard_token_sequence
              (nat_sequence_decode rightValue)) ≐ₘ
          standard_token_sequence expectedTokens)) :
    Derives fs_zfc_support_raw_theory [] (
      logical_binary_base_certificate_condition_with_ids
          tag constructor formulaCode certificate
          payloadId sequenceId leftId rightId traceId indexId ⟶ₘ
        formulaCode ≐ₘ standard_token_sequence expectedTokens) := by
  let body : SetFormula :=
    logical_certificate_conjunction [
      certificate ≐ₘ
        godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
      nat_sequence_code_condition_with_ids
        (x#sequenceId) (x#payloadId) traceId indexId,
      domₘ(x#sequenceId) ≐ₘ numₘ(2),
      logical_formula_payload_component_condition_with_ids
        (x#leftId) (x#sequenceId ·ₘ numₘ(0))
        traceId indexId,
      logical_formula_payload_component_condition_with_ids
        (x#rightId) (x#sequenceId ·ₘ numₘ(1))
        traceId indexId,
      formulaCode ≐ₘ constructor (x#leftId) (x#rightId)]
  let target : SetFormula :=
    formulaCode ≐ₘ standard_token_sequence expectedTokens
  have hPayload :
      Term.Admissible (x#payloadId) SetSort.set :=
    set_variable_admissible payloadId
  have hSequence :
      Term.Admissible (x#sequenceId) SetSort.set :=
    set_variable_admissible sequenceId
  have hLeft :
      Term.Admissible (x#leftId) SetSort.set :=
    set_variable_admissible leftId
  have hRight :
      Term.Admissible (x#rightId) SetSort.set :=
    set_variable_admissible rightId
  have hNumericLeft :
      Term.Admissible
        (x#sequenceId ·ₘ numₘ(0)) SetSort.set :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(0)) hSequence
      (finite_numeral_term_admissible 0)
  have hNumericRight :
      Term.Admissible
        (x#sequenceId ·ₘ numₘ(1)) SetSort.set :=
    function_application_term_admissible
      (x#sequenceId) (numₘ(1)) hSequence
      (finite_numeral_term_admissible 1)
  have hTracePayload : traceId ≠ payloadId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hTraceSequence : traceId ≠ sequenceId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hTraceLeft : traceId ≠ leftId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hTraceRight : traceId ≠ rightId := by
    intro h
    apply hTraceFresh
    simp [h]
  have hIndexPayload : indexId ≠ payloadId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hIndexSequence : indexId ≠ sequenceId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hIndexLeft : indexId ≠ leftId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hIndexRight : indexId ≠ rightId := by
    intro h
    apply hIndexFresh
    simp [h]
  have hBody :
      Formula.Admissible body := by
    dsimp [body]
    apply logical_certificate_conjunction_admissible
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Formula.Admissible.equal hCertificate <|
        godel_pairing_term_admissible _ <|
          ordered_pair_term_admissible _ _
            (finite_numeral_term_admissible tag) hPayload
    · exact nat_sequence_code_condition_with_ids_admissible
        (x#sequenceId) (x#payloadId) traceId indexId
        hSequence hPayload
    · exact Formula.Admissible.equal
        (domain_term_admissible (x#sequenceId) hSequence)
        (finite_numeral_term_admissible 2)
    · exact
        logical_formula_payload_component_condition_with_ids_admissible
          (x#leftId) (x#sequenceId ·ₘ numₘ(0))
          traceId indexId hLeft hNumericLeft
    · exact
        logical_formula_payload_component_condition_with_ids_admissible
          (x#rightId) (x#sequenceId ·ₘ numₘ(1))
          traceId indexId hRight hNumericRight
    · exact Formula.Admissible.equal hFormulaCode
        (hConstructorAdmissible
          (x#leftId) (x#rightId) hLeft hRight)
  have hBodyImp :
      ([] : Context signature)
        ⊢ₘ[fs_zfc_support_raw_theory]
          body ⟶ₘ target := by
    nd_apply FirstOrder.Derives.impIntro
      (hAntecedentCheck :=
        Formula.check_admissible_complete hBody)
    let Γ : Context signature := [body]
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete hBody)
    have hPairField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ) := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hRestOne :=
      FirstOrder.Derives.conjElimRight hBodyAt
    have hSequenceField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          nat_sequence_code_condition_with_ids
            (x#sequenceId) (x#payloadId) traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestOne
    have hRestTwo :=
      FirstOrder.Derives.conjElimRight hRestOne
    have hDomainField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(x#sequenceId) ≐ₘ numₘ(2) := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestTwo
    have hRestThree :=
      FirstOrder.Derives.conjElimRight hRestTwo
    have hLeftField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          logical_formula_payload_component_condition_with_ids
            (x#leftId) (x#sequenceId ·ₘ numₘ(0))
            traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestThree
    have hRightField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          logical_formula_payload_component_condition_with_ids
            (x#rightId) (x#sequenceId ·ₘ numₘ(1))
            traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight hRestThree
    have hFormulaField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          formulaCode ≐ₘ constructor (x#leftId) (x#rightId) := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight hRestThree
    have hCertificateCodeAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          certificate ≐ₘ numₘ(raw) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) hCertificateCode
    have hPair :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ) :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm hCertificateCodeAt)
        hPairField
    have hTraceFreshContext :
        ∀ proposition, proposition ∈ Γ →
          (SetSort.set, traceId) ∉
            Formula.freeSupport proposition := by
      intro proposition hProposition
      have hEquality : proposition = body :=
        List.mem_singleton.mp <| by
          simpa [Γ] using hProposition
      subst proposition
      intro hMember
      rcases logical_certificate_conjunction_freeSupport
          _ (SetSort.set, traceId) hMember with
        ⟨field, hField, hFieldSupport⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
      rcases hField with rfl | rfl | rfl | rfl | rfl | rfl
      · have hCases :
            (SetSort.set, traceId) ∈ Term.freeSupport certificate ∨
              traceId = payloadId := by
          simpa [Formula.freeSupport, Term.freeSupport,
            Term.freeSupportList,
            finite_numeral_term_freeSupport] using hFieldSupport
        rcases hCases with hCertificateMember | hPayload
        · exact False.elim <|
            hReservedFresh certificate (by simp) traceId (by simp)
              hCertificateMember
        · exact hTracePayload hPayload
      · rcases nat_sequence_code_condition_with_ids_freeSupport_subset
            (x#sequenceId) (x#payloadId) traceId indexId
            (SetSort.set, traceId) hFieldSupport with
          hMember | hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId sequenceId hTraceSequence) hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId payloadId hTracePayload) hMember
      · simp [Formula.freeSupport, Term.freeSupport,
          Term.freeSupportList,
          finite_numeral_term_freeSupport] at hFieldSupport
        exact hTraceSequence hFieldSupport
      · rcases
            logical_formula_payload_component_condition_with_ids_freeSupport_subset
              (x#leftId) (x#sequenceId ·ₘ numₘ(0))
              traceId indexId (SetSort.set, traceId)
              hFieldSupport with
          hMember | hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId leftId hTraceLeft) hMember
        · exact
            (fs_zfc_prop_mismatch_application_numeral_fresh
              traceId sequenceId 0 hTraceSequence) hMember
      · rcases
            logical_formula_payload_component_condition_with_ids_freeSupport_subset
              (x#rightId) (x#sequenceId ·ₘ numₘ(1))
              traceId indexId (SetSort.set, traceId)
              hFieldSupport with
          hMember | hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId rightId hTraceRight) hMember
        · exact
            (fs_zfc_prop_mismatch_application_numeral_fresh
              traceId sequenceId 1 hTraceSequence) hMember
      · have hConstructorMember :
            (SetSort.set, traceId) ∈
              Term.freeSupport
                (constructor (x#leftId) (x#rightId)) := by
          have hCases :
              (SetSort.set, traceId) ∈ Term.freeSupport formulaCode ∨
                (SetSort.set, traceId) ∈
                  Term.freeSupport
                    (constructor (x#leftId) (x#rightId)) := by
            simpa [Formula.freeSupport] using hFieldSupport
          rcases hCases with hFormulaMember | hConstructorMember
          · exact False.elim <|
              hReservedFresh formulaCode (by simp) traceId (by simp)
                hFormulaMember
          · exact hConstructorMember
        rcases hConstructorSupport
            (x#leftId) (x#rightId)
            (SetSort.set, traceId) hConstructorMember with
          hMember | hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId leftId hTraceLeft) hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId rightId hTraceRight) hMember
    have hLeftEqualityRaw :=
      fs_zfc_support_raw_logical_payload_component_code_eq_standard
        raw tag 0
        (x#payloadId) (x#sequenceId) (x#leftId)
        (x#sequenceId ·ₘ numₘ(0))
        traceId indexId hPayload hSequence hLeft hNumericLeft
        hTraceNeIndex
        (fs_zfc_prop_mismatch_set_variable_fresh
          traceId sequenceId hTraceSequence)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId sequenceId hIndexSequence)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId payloadId hIndexPayload)
        (fs_zfc_prop_mismatch_set_variable_fresh
          traceId leftId hTraceLeft)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId leftId hIndexLeft)
        (fs_zfc_prop_mismatch_application_numeral_fresh
          indexId sequenceId 0 hIndexSequence)
        hTraceFreshContext hPair hSequenceField
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (x#sequenceId ·ₘ numₘ(0)))
        hLeftField
        (by simp [hPayloadCodes])
    have hRightEqualityRaw :=
      fs_zfc_support_raw_logical_payload_component_code_eq_standard
        raw tag 1
        (x#payloadId) (x#sequenceId) (x#rightId)
        (x#sequenceId ·ₘ numₘ(1))
        traceId indexId hPayload hSequence hRight hNumericRight
        hTraceNeIndex
        (fs_zfc_prop_mismatch_set_variable_fresh
          traceId sequenceId hTraceSequence)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId sequenceId hIndexSequence)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId payloadId hIndexPayload)
        (fs_zfc_prop_mismatch_set_variable_fresh
          traceId rightId hTraceRight)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId rightId hIndexRight)
        (fs_zfc_prop_mismatch_application_numeral_fresh
          indexId sequenceId 1 hIndexSequence)
        hTraceFreshContext hPair hSequenceField
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (x#sequenceId ·ₘ numₘ(1)))
        hRightField
        (by simp [hPayloadCodes])
    have hLeftEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          (x#leftId) ≐ₘ
            standard_token_sequence
              (nat_sequence_decode leftValue) := by
      simpa [hPayloadCodes] using hLeftEqualityRaw
    have hRightEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          (x#rightId) ≐ₘ
            standard_token_sequence
              (nat_sequence_decode rightValue) := by
      simpa [hPayloadCodes] using hRightEqualityRaw
    have hConstructorEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          constructor (x#leftId) (x#rightId) ≐ₘ
            constructor
              (standard_token_sequence
                (nat_sequence_decode leftValue))
              (standard_token_sequence
                (nat_sequence_decode rightValue)) :=
      Metatheory.Derives.binary_term_constructor_congr_of_equalities
        constructor hConstructorAdmissible hConstructorSubstitute
        (x#leftId)
        (standard_token_sequence
          (nat_sequence_decode leftValue))
        (x#rightId)
        (standard_token_sequence
          (nat_sequence_decode rightValue))
        hLeft
        (standard_token_sequence_admissible
          (nat_sequence_decode leftValue))
        hRight
        (standard_token_sequence_admissible
          (nat_sequence_decode rightValue))
        hLeftEquality hRightEquality
    have hConstructorStandardAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          constructor
              (standard_token_sequence
                (nat_sequence_decode leftValue))
              (standard_token_sequence
                (nat_sequence_decode rightValue)) ≐ₘ
            standard_token_sequence expectedTokens :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) hConstructorStandard
    have hFormulaExpected :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          formulaCode ≐ₘ
            standard_token_sequence expectedTokens :=
      Metatheory.Derives.equality_trans hFormulaField <|
        Metatheory.Derives.equality_trans hConstructorEquality
          hConstructorStandardAt
    simpa [target] using hFormulaExpected
  have hWrapped :=
    fs_zfc_support_raw_exists_assignments_imp_fresh
      [(payloadId, x#payloadId), (sequenceId, x#sequenceId),
        (leftId, x#leftId), (rightId, x#rightId)]
      body target
      (by
        intro eigen witness hMember
        have hEigen :
            eigen ∈ [payloadId, sequenceId, leftId, rightId] := by
          simpa using
            List.mem_map_of_mem (f := Prod.fst) hMember
        have hReserved :
            eigen ∈
              [payloadId, sequenceId, leftId, rightId, traceId, indexId] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hEigen ⊢
          rcases hEigen with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        simpa [target, Formula.freeSupport,
          standard_token_sequence_freeSupport_nil] using
            hReservedFresh formulaCode (by simp) eigen hReserved)
      hBodyImp
  simpa [target, logical_binary_base_certificate_condition_with_ids,
    body, Formula.existsFreeAssignments] using hWrapped

/-- 二元候选唯一性与标准行互异时，导出该证书分支的对象层否定。 -/
theorem fs_zfc_support_raw_logical_binary_base_certificate_neg_of_row_mismatch
    (raw tag leftValue rightValue : Nat)
    (row expectedTokens : List Nat)
    (constructor : SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId leftId rightId traceId indexId : FreeVarId)
    (hTraceFresh :
      traceId ∉ [payloadId, sequenceId, leftId, rightId])
    (hIndexFresh :
      indexId ∉ [payloadId, sequenceId, leftId, rightId])
    (hTraceNeIndex : traceId ≠ indexId)
    (hConstructorAdmissible :
      ∀ left right,
        Term.Admissible left SetSort.set →
        Term.Admissible right SetSort.set →
          Term.Admissible (constructor left right) SetSort.set)
    (hConstructorSupport :
      ∀ left right freeVariable,
        freeVariable ∈
            Term.freeSupport (constructor left right) →
          freeVariable ∈ Term.freeSupport left ∨
            freeVariable ∈ Term.freeSupport right)
    (hConstructorSubstitute :
      ∀ parameter replacement left right,
        Term.substituteFree SetSort.set parameter replacement
            (constructor left right) =
          constructor
            (Term.substituteFree SetSort.set parameter replacement left)
            (Term.substituteFree SetSort.set parameter replacement right))
    (hFormulaCode :
      Term.Admissible formulaCode SetSort.set)
    (hCertificate :
      Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        [payloadId, sequenceId, leftId, rightId, traceId, indexId]
        [formulaCode, certificate])
    (hFormulaToRow :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ standard_token_sequence row))
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hPayloadCodes :
      nat_sequence_decode
          (godel_unpair_value raw).2 =
        [leftValue, rightValue])
    (hConstructorStandard :
      Derives fs_zfc_support_raw_theory [] (
        constructor
            (standard_token_sequence
              (nat_sequence_decode leftValue))
            (standard_token_sequence
              (nat_sequence_decode rightValue)) ≐ₘ
          standard_token_sequence expectedTokens))
    (hRowNe : row ≠ expectedTokens) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_binary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId leftId rightId traceId indexId) := by
  let condition :=
    logical_binary_base_certificate_condition_with_ids
      tag constructor formulaCode certificate
      payloadId sequenceId leftId rightId traceId indexId
  have hExpected :=
    fs_zfc_support_raw_logical_binary_base_certificate_eq_standard_imp
      raw tag leftValue rightValue expectedTokens constructor
      formulaCode certificate payloadId sequenceId leftId rightId
      traceId indexId hTraceFresh hIndexFresh hTraceNeIndex
      hConstructorAdmissible hConstructorSupport hConstructorSubstitute
      hFormulaCode hCertificate hReservedFresh hCertificateCode hPayloadCodes
      hConstructorStandard
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

/-- 具名双公式 payload 唯一给出可解码的候选标准公式码。 -/
theorem
    fs_zfc_support_raw_logical_binary_base_certificate_candidate_of_named_payload
    (raw tag freeBase : Nat)
    (left right expected : SetFormula)
    (tokenConstructor : List Nat → List Nat → List Nat)
    (constructor : SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId leftId rightId traceId indexId : FreeVarId)
    (hTraceFresh :
      traceId ∉ [payloadId, sequenceId, leftId, rightId])
    (hIndexFresh :
      indexId ∉ [payloadId, sequenceId, leftId, rightId])
    (hTraceNeIndex : traceId ≠ indexId)
    (hConstructorAdmissible :
      ∀ leftTerm rightTerm,
        Term.Admissible leftTerm SetSort.set →
        Term.Admissible rightTerm SetSort.set →
          Term.Admissible (constructor leftTerm rightTerm) SetSort.set)
    (hConstructorSupport :
      ∀ leftTerm rightTerm freeVariable,
        freeVariable ∈
            Term.freeSupport (constructor leftTerm rightTerm) →
          freeVariable ∈ Term.freeSupport leftTerm ∨
            freeVariable ∈ Term.freeSupport rightTerm)
    (hConstructorSubstitute :
      ∀ parameter replacement leftTerm rightTerm,
        Term.substituteFree SetSort.set parameter replacement
            (constructor leftTerm rightTerm) =
          constructor
            (Term.substituteFree SetSort.set parameter replacement leftTerm)
            (Term.substituteFree SetSort.set parameter replacement rightTerm))
    (hFormulaCode :
      Term.Admissible formulaCode SetSort.set)
    (hCertificate :
      Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        [payloadId, sequenceId, leftId, rightId, traceId, indexId]
        [formulaCode, certificate])
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hPayload :
      fs_named_formula_payload_decode
          freeBase (godel_unpair_value raw).2 =
        some [left, right])
    (hExpectedDecode :
      ∀ leftTokens rightTokens,
        fs_named_hilbert_tokens_decode_with_env
            freeBase [] leftTokens =
          some left →
        fs_named_hilbert_tokens_decode_with_env
            freeBase [] rightTokens =
          some right →
        fs_named_hilbert_tokens_decode_with_env
            freeBase [] (tokenConstructor leftTokens rightTokens) =
          some expected)
    (hConstructorStandard :
      ∀ leftTokens rightTokens,
        Derives fs_zfc_support_raw_theory [] (
          constructor
              (standard_token_sequence leftTokens)
              (standard_token_sequence rightTokens) ≐ₘ
            standard_token_sequence
              (tokenConstructor leftTokens rightTokens))) :
    ∃ expectedTokens,
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] expectedTokens =
        some expected ∧
      Derives fs_zfc_support_raw_theory [] (
        logical_binary_base_certificate_condition_with_ids
            tag constructor formulaCode certificate
            payloadId sequenceId leftId rightId traceId indexId ⟶ₘ
          formulaCode ≐ₘ standard_token_sequence expectedTokens) := by
  rcases fs_named_formula_payload_decode_two hPayload with
    ⟨leftCode, rightCode, hCodes, hLeftCode, hRightCode⟩
  let leftTokens := nat_sequence_decode leftCode
  let rightTokens := nat_sequence_decode rightCode
  let expectedTokens := tokenConstructor leftTokens rightTokens
  have hLeftDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] leftTokens =
        some left := by
    simpa [leftTokens, fs_named_formula_token_code_decode] using hLeftCode
  have hRightDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] rightTokens =
        some right := by
    simpa [rightTokens, fs_named_formula_token_code_decode] using hRightCode
  refine ⟨expectedTokens, ?_, ?_⟩
  · simpa [expectedTokens] using
      hExpectedDecode leftTokens rightTokens hLeftDecode hRightDecode
  · exact
      fs_zfc_support_raw_logical_binary_base_certificate_eq_standard_imp
        raw tag leftCode rightCode expectedTokens constructor
        formulaCode certificate
        payloadId sequenceId leftId rightId traceId indexId
        hTraceFresh hIndexFresh hTraceNeIndex
        hConstructorAdmissible hConstructorSupport hConstructorSubstitute
        hFormulaCode hCertificate hReservedFresh hCertificateCode
        (by simp [hCodes])
        (by
          simpa [leftTokens, rightTokens, expectedTokens] using
            hConstructorStandard leftTokens rightTokens)

/--
把具名双公式 payload 的公式错配压到原始 token 行错配。

该适配器只负责宿主 decoder 与对象 quotation 的对齐；对象层反证仍完全由上面的
二元通用拒绝定理给出。
-/
theorem
    fs_zfc_support_raw_logical_binary_base_certificate_neg_of_named_mismatch
    (raw tag freeBase : Nat)
    (row : List Nat)
    (formula left right expected : SetFormula)
    (tokenConstructor : List Nat → List Nat → List Nat)
    (constructor : SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId leftId rightId traceId indexId : FreeVarId)
    (hTraceFresh :
      traceId ∉ [payloadId, sequenceId, leftId, rightId])
    (hIndexFresh :
      indexId ∉ [payloadId, sequenceId, leftId, rightId])
    (hTraceNeIndex : traceId ≠ indexId)
    (hConstructorAdmissible :
      ∀ leftTerm rightTerm,
        Term.Admissible leftTerm SetSort.set →
        Term.Admissible rightTerm SetSort.set →
          Term.Admissible (constructor leftTerm rightTerm) SetSort.set)
    (hConstructorSupport :
      ∀ leftTerm rightTerm freeVariable,
        freeVariable ∈
            Term.freeSupport (constructor leftTerm rightTerm) →
          freeVariable ∈ Term.freeSupport leftTerm ∨
            freeVariable ∈ Term.freeSupport rightTerm)
    (hConstructorSubstitute :
      ∀ parameter replacement leftTerm rightTerm,
        Term.substituteFree SetSort.set parameter replacement
            (constructor leftTerm rightTerm) =
          constructor
            (Term.substituteFree SetSort.set parameter replacement leftTerm)
            (Term.substituteFree SetSort.set parameter replacement rightTerm))
    (hFormulaCode :
      Term.Admissible formulaCode SetSort.set)
    (hCertificate :
      Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        [payloadId, sequenceId, leftId, rightId, traceId, indexId]
        [formulaCode, certificate])
    (hFormulaToRow :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ standard_token_sequence row))
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hRowDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] row =
        some formula)
    (hPayload :
      fs_named_formula_payload_decode
          freeBase (godel_unpair_value raw).2 =
        some [left, right])
    (hExpectedDecode :
      ∀ leftTokens rightTokens,
        fs_named_hilbert_tokens_decode_with_env
            freeBase [] leftTokens =
          some left →
        fs_named_hilbert_tokens_decode_with_env
            freeBase [] rightTokens =
          some right →
        fs_named_hilbert_tokens_decode_with_env
            freeBase [] (tokenConstructor leftTokens rightTokens) =
          some expected)
    (hConstructorStandard :
      ∀ leftTokens rightTokens,
        Derives fs_zfc_support_raw_theory [] (
          constructor
              (standard_token_sequence leftTokens)
              (standard_token_sequence rightTokens) ≐ₘ
            standard_token_sequence
              (tokenConstructor leftTokens rightTokens)))
    (hMismatch : formula ≠ expected) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_binary_base_certificate_condition_with_ids
        tag constructor formulaCode certificate
        payloadId sequenceId leftId rightId traceId indexId) := by
  rcases fs_named_formula_payload_decode_two hPayload with
    ⟨leftCode, rightCode, hCodes, hLeftCode, hRightCode⟩
  let leftTokens := nat_sequence_decode leftCode
  let rightTokens := nat_sequence_decode rightCode
  let expectedTokens := tokenConstructor leftTokens rightTokens
  have hLeftDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] leftTokens =
        some left := by
    simpa [leftTokens, fs_named_formula_token_code_decode] using hLeftCode
  have hRightDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] rightTokens =
        some right := by
    simpa [rightTokens, fs_named_formula_token_code_decode] using hRightCode
  have hRowNe : row ≠ expectedTokens := by
    intro hEquality
    rw [hEquality] at hRowDecode
    apply hMismatch
    exact Option.some.inj <|
      hRowDecode.symm.trans <| by
        simpa [expectedTokens] using
          hExpectedDecode leftTokens rightTokens
            hLeftDecode hRightDecode
  exact
    fs_zfc_support_raw_logical_binary_base_certificate_neg_of_row_mismatch
      raw tag leftCode rightCode row expectedTokens constructor
      formulaCode certificate
      payloadId sequenceId leftId rightId traceId indexId
      hTraceFresh hIndexFresh hTraceNeIndex
      hConstructorAdmissible hConstructorSupport hConstructorSubstitute
      hFormulaCode hCertificate hReservedFresh hFormulaToRow hCertificateCode
      (by simp [hCodes])
      (by
        simpa [leftTokens, rightTokens, expectedTokens] using
          hConstructorStandard leftTokens rightTokens)
      hRowNe

/--
三元命题公理分支唯一决定其候选标准公式码。

三个组件只从 payload 的原始数值字段恢复；具体构造器只需给出支持投影与三元
等式合同，因而该接口不依赖某个固定 Hilbert 公理模式。
-/
theorem fs_zfc_support_raw_logical_ternary_base_certificate_eq_standard_imp
    (raw tag firstValue secondValue thirdValue : Nat)
    (expectedTokens : List Nat)
    (constructor : SetTerm → SetTerm → SetTerm → SetTerm)
    (formulaCode certificate : SetTerm)
    (payloadId sequenceId firstId secondId thirdId traceId indexId :
      FreeVarId)
    (hTraceFresh :
      traceId ∉
        [payloadId, sequenceId, firstId, secondId, thirdId])
    (hIndexFresh :
      indexId ∉
        [payloadId, sequenceId, firstId, secondId, thirdId])
    (hTraceNeIndex : traceId ≠ indexId)
    (hConstructorAdmissible :
      ∀ first second third,
        Term.Admissible first SetSort.set →
        Term.Admissible second SetSort.set →
        Term.Admissible third SetSort.set →
          Term.Admissible (constructor first second third) SetSort.set)
    (hConstructorSupport :
      ∀ first second third freeVariable,
        freeVariable ∈
            Term.freeSupport (constructor first second third) →
          freeVariable ∈ Term.freeSupport first ∨
            freeVariable ∈ Term.freeSupport second ∨
              freeVariable ∈ Term.freeSupport third)
    (hConstructorCongruence :
      ∀ {Γ : Context signature}
        (firstLeft firstRight secondLeft secondRight
          thirdLeft thirdRight : SetTerm),
        Term.Admissible firstLeft SetSort.set →
        Term.Admissible firstRight SetSort.set →
        Term.Admissible secondLeft SetSort.set →
        Term.Admissible secondRight SetSort.set →
        Term.Admissible thirdLeft SetSort.set →
        Term.Admissible thirdRight SetSort.set →
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          firstLeft ≐ₘ firstRight →
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          secondLeft ≐ₘ secondRight →
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          thirdLeft ≐ₘ thirdRight →
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          constructor firstLeft secondLeft thirdLeft ≐ₘ
            constructor firstRight secondRight thirdRight)
    (hFormulaCode :
      Term.Admissible formulaCode SetSort.set)
    (hCertificate :
      Term.Admissible certificate SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        [payloadId, sequenceId, firstId, secondId, thirdId, traceId, indexId]
        [formulaCode, certificate])
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hPayloadCodes :
      nat_sequence_decode (godel_unpair_value raw).2 =
        [firstValue, secondValue, thirdValue])
    (hConstructorStandard :
      Derives fs_zfc_support_raw_theory [] (
        constructor
            (standard_token_sequence
              (nat_sequence_decode firstValue))
            (standard_token_sequence
              (nat_sequence_decode secondValue))
            (standard_token_sequence
              (nat_sequence_decode thirdValue)) ≐ₘ
          standard_token_sequence expectedTokens)) :
    Derives fs_zfc_support_raw_theory [] (
      logical_ternary_base_certificate_condition_with_ids
          tag constructor formulaCode certificate
          payloadId sequenceId firstId secondId thirdId traceId indexId ⟶ₘ
        formulaCode ≐ₘ standard_token_sequence expectedTokens) := by
  let body : SetFormula :=
    logical_certificate_conjunction [
      certificate ≐ₘ
        godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ),
      nat_sequence_code_condition_with_ids
        (x#sequenceId) (x#payloadId) traceId indexId,
      domₘ(x#sequenceId) ≐ₘ numₘ(3),
      logical_formula_payload_component_condition_with_ids
        (x#firstId) (x#sequenceId ·ₘ numₘ(0)) traceId indexId,
      logical_formula_payload_component_condition_with_ids
        (x#secondId) (x#sequenceId ·ₘ numₘ(1)) traceId indexId,
      logical_formula_payload_component_condition_with_ids
        (x#thirdId) (x#sequenceId ·ₘ numₘ(2)) traceId indexId,
      formulaCode ≐ₘ
        constructor (x#firstId) (x#secondId) (x#thirdId)]
  let assignments : List (FreeVarId × SetTerm) :=
    [(payloadId, x#payloadId), (sequenceId, x#sequenceId),
      (firstId, x#firstId), (secondId, x#secondId),
      (thirdId, x#thirdId)]
  let target : SetFormula :=
    formulaCode ≐ₘ standard_token_sequence expectedTokens
  have hCondition :=
    logical_ternary_base_certificate_condition_with_ids_admissible
      tag constructor formulaCode certificate
      payloadId sequenceId firstId secondId thirdId traceId indexId
      hConstructorAdmissible hFormulaCode hCertificate
  have hBody : Formula.Admissible body := by
    apply fs_zfc_admissible_body_of_exists_assignments
      assignments body
    simpa [assignments, body,
      logical_ternary_base_certificate_condition_with_ids,
      Formula.existsFreeAssignments] using hCondition
  have hBodyImp :
      Derives fs_zfc_support_raw_theory [] (
        body ⟶ₘ target) := by
    apply FirstOrder.Derives.impIntro
      (hAntecedentCheck :=
        Formula.check_admissible_complete hBody)
    let Γ : Context signature := [body]
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete hBody)
    have hRestOne := FirstOrder.Derives.conjElimRight hBodyAt
    have hRestTwo := FirstOrder.Derives.conjElimRight hRestOne
    have hRestThree := FirstOrder.Derives.conjElimRight hRestTwo
    have hRestFour := FirstOrder.Derives.conjElimRight hRestThree
    have hRestFive := FirstOrder.Derives.conjElimRight hRestFour
    have hPairField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          certificate ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ) := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hSequenceField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          nat_sequence_code_condition_with_ids
            (x#sequenceId) (x#payloadId) traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestOne
    have hFirstField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          logical_formula_payload_component_condition_with_ids
            (x#firstId) (x#sequenceId ·ₘ numₘ(0))
            traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestThree
    have hSecondField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          logical_formula_payload_component_condition_with_ids
            (x#secondId) (x#sequenceId ·ₘ numₘ(1))
            traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestFour
    have hThirdField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          logical_formula_payload_component_condition_with_ids
            (x#thirdId) (x#sequenceId ·ₘ numₘ(2))
            traceId indexId := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimLeft hRestFive
    have hFormulaField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          formulaCode ≐ₘ
            constructor (x#firstId) (x#secondId) (x#thirdId) := by
      simpa [Γ, body, logical_certificate_conjunction] using
        FirstOrder.Derives.conjElimRight hRestFive
    have hTracePayload : traceId ≠ payloadId := by
      intro h
      apply hTraceFresh
      simp [h]
    have hTraceSequence : traceId ≠ sequenceId := by
      intro h
      apply hTraceFresh
      simp [h]
    have hTraceFirst : traceId ≠ firstId := by
      intro h
      apply hTraceFresh
      simp [h]
    have hTraceSecond : traceId ≠ secondId := by
      intro h
      apply hTraceFresh
      simp [h]
    have hTraceThird : traceId ≠ thirdId := by
      intro h
      apply hTraceFresh
      simp [h]
    have hIndexPayload : indexId ≠ payloadId := by
      intro h
      apply hIndexFresh
      simp [h]
    have hIndexSequence : indexId ≠ sequenceId := by
      intro h
      apply hIndexFresh
      simp [h]
    have hIndexFirst : indexId ≠ firstId := by
      intro h
      apply hIndexFresh
      simp [h]
    have hIndexSecond : indexId ≠ secondId := by
      intro h
      apply hIndexFresh
      simp [h]
    have hIndexThird : indexId ≠ thirdId := by
      intro h
      apply hIndexFresh
      simp [h]
    have hPayload :
        Term.Admissible (x#payloadId) SetSort.set :=
      set_variable_admissible payloadId
    have hSequence :
        Term.Admissible (x#sequenceId) SetSort.set :=
      set_variable_admissible sequenceId
    have hFirst :
        Term.Admissible (x#firstId) SetSort.set :=
      set_variable_admissible firstId
    have hSecond :
        Term.Admissible (x#secondId) SetSort.set :=
      set_variable_admissible secondId
    have hThird :
        Term.Admissible (x#thirdId) SetSort.set :=
      set_variable_admissible thirdId
    have hNumeric (value : Nat) :
        Term.Admissible
          (x#sequenceId ·ₘ numₘ(value)) SetSort.set :=
      function_application_term_admissible
        (x#sequenceId) (numₘ(value)) hSequence
        (finite_numeral_term_admissible value)
    have hCertificateCodeAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          certificate ≐ₘ numₘ(raw) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) hCertificateCode
    have hPair :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            godel_pairₘ(⟨numₘ(tag), x#payloadId⟩ₘ) :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm hCertificateCodeAt)
        hPairField
    have hTraceFreshContext :
        ∀ proposition, proposition ∈ Γ →
          (SetSort.set, traceId) ∉
            Formula.freeSupport proposition := by
      intro proposition hProposition
      have hEquality : proposition = body :=
        List.mem_singleton.mp <| by
          simpa [Γ] using hProposition
      subst proposition
      intro hMember
      rcases logical_certificate_conjunction_freeSupport
          _ (SetSort.set, traceId) hMember with
        ⟨field, hField, hFieldSupport⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
      rcases hField with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have hCases :
            (SetSort.set, traceId) ∈ Term.freeSupport certificate ∨
              traceId = payloadId := by
          simpa [Formula.freeSupport, Term.freeSupport,
            Term.freeSupportList,
            finite_numeral_term_freeSupport] using hFieldSupport
        rcases hCases with hCertificateMember | hPayload
        · exact False.elim <|
            hReservedFresh certificate (by simp) traceId (by simp)
              hCertificateMember
        · exact hTracePayload hPayload
      · rcases nat_sequence_code_condition_with_ids_freeSupport_subset
            (x#sequenceId) (x#payloadId) traceId indexId
            (SetSort.set, traceId) hFieldSupport with
          hMember | hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId sequenceId hTraceSequence) hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId payloadId hTracePayload) hMember
      · simp [Formula.freeSupport, Term.freeSupport,
          Term.freeSupportList,
          finite_numeral_term_freeSupport] at hFieldSupport
        exact hTraceSequence hFieldSupport
      · rcases
            logical_formula_payload_component_condition_with_ids_freeSupport_subset
              (x#firstId) (x#sequenceId ·ₘ numₘ(0))
              traceId indexId (SetSort.set, traceId)
              hFieldSupport with hMember | hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId firstId hTraceFirst) hMember
        · exact
            (fs_zfc_prop_mismatch_application_numeral_fresh
              traceId sequenceId 0 hTraceSequence) hMember
      · rcases
            logical_formula_payload_component_condition_with_ids_freeSupport_subset
              (x#secondId) (x#sequenceId ·ₘ numₘ(1))
              traceId indexId (SetSort.set, traceId)
              hFieldSupport with hMember | hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId secondId hTraceSecond) hMember
        · exact
            (fs_zfc_prop_mismatch_application_numeral_fresh
              traceId sequenceId 1 hTraceSequence) hMember
      · rcases
            logical_formula_payload_component_condition_with_ids_freeSupport_subset
              (x#thirdId) (x#sequenceId ·ₘ numₘ(2))
              traceId indexId (SetSort.set, traceId)
              hFieldSupport with hMember | hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId thirdId hTraceThird) hMember
        · exact
            (fs_zfc_prop_mismatch_application_numeral_fresh
              traceId sequenceId 2 hTraceSequence) hMember
      · have hConstructorMember :
            (SetSort.set, traceId) ∈
              Term.freeSupport
                (constructor (x#firstId) (x#secondId) (x#thirdId)) := by
          have hCases :
              (SetSort.set, traceId) ∈ Term.freeSupport formulaCode ∨
                (SetSort.set, traceId) ∈
                  Term.freeSupport
                    (constructor (x#firstId) (x#secondId) (x#thirdId)) := by
            simpa [Formula.freeSupport] using hFieldSupport
          rcases hCases with hFormulaMember | hConstructorMember
          · exact False.elim <|
              hReservedFresh formulaCode (by simp) traceId (by simp)
                hFormulaMember
          · exact hConstructorMember
        rcases hConstructorSupport
            (x#firstId) (x#secondId) (x#thirdId)
            (SetSort.set, traceId) hConstructorMember with
          hMember | hMember | hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId firstId hTraceFirst) hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId secondId hTraceSecond) hMember
        · exact
            (fs_zfc_prop_mismatch_set_variable_fresh
              traceId thirdId hTraceThird) hMember
    have hFirstEqualityRaw :=
      fs_zfc_support_raw_logical_payload_component_code_eq_standard
        raw tag 0 (x#payloadId) (x#sequenceId) (x#firstId)
        (x#sequenceId ·ₘ numₘ(0)) traceId indexId
        hPayload hSequence hFirst (hNumeric 0) hTraceNeIndex
        (fs_zfc_prop_mismatch_set_variable_fresh
          traceId sequenceId hTraceSequence)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId sequenceId hIndexSequence)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId payloadId hIndexPayload)
        (fs_zfc_prop_mismatch_set_variable_fresh
          traceId firstId hTraceFirst)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId firstId hIndexFirst)
        (fs_zfc_prop_mismatch_application_numeral_fresh
          indexId sequenceId 0 hIndexSequence)
        hTraceFreshContext hPair hSequenceField
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) (x#sequenceId ·ₘ numₘ(0)))
        hFirstField (by simp [hPayloadCodes])
    have hSecondEqualityRaw :=
      fs_zfc_support_raw_logical_payload_component_code_eq_standard
        raw tag 1 (x#payloadId) (x#sequenceId) (x#secondId)
        (x#sequenceId ·ₘ numₘ(1)) traceId indexId
        hPayload hSequence hSecond (hNumeric 1) hTraceNeIndex
        (fs_zfc_prop_mismatch_set_variable_fresh
          traceId sequenceId hTraceSequence)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId sequenceId hIndexSequence)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId payloadId hIndexPayload)
        (fs_zfc_prop_mismatch_set_variable_fresh
          traceId secondId hTraceSecond)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId secondId hIndexSecond)
        (fs_zfc_prop_mismatch_application_numeral_fresh
          indexId sequenceId 1 hIndexSequence)
        hTraceFreshContext hPair hSequenceField
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) (x#sequenceId ·ₘ numₘ(1)))
        hSecondField (by simp [hPayloadCodes])
    have hThirdEqualityRaw :=
      fs_zfc_support_raw_logical_payload_component_code_eq_standard
        raw tag 2 (x#payloadId) (x#sequenceId) (x#thirdId)
        (x#sequenceId ·ₘ numₘ(2)) traceId indexId
        hPayload hSequence hThird (hNumeric 2) hTraceNeIndex
        (fs_zfc_prop_mismatch_set_variable_fresh
          traceId sequenceId hTraceSequence)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId sequenceId hIndexSequence)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId payloadId hIndexPayload)
        (fs_zfc_prop_mismatch_set_variable_fresh
          traceId thirdId hTraceThird)
        (fs_zfc_prop_mismatch_set_variable_fresh
          indexId thirdId hIndexThird)
        (fs_zfc_prop_mismatch_application_numeral_fresh
          indexId sequenceId 2 hIndexSequence)
        hTraceFreshContext hPair hSequenceField
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) (x#sequenceId ·ₘ numₘ(2)))
        hThirdField (by simp [hPayloadCodes])
    have hFirstEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#firstId ≐ₘ standard_token_sequence
            (nat_sequence_decode firstValue) := by
      simpa [hPayloadCodes] using hFirstEqualityRaw
    have hSecondEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#secondId ≐ₘ standard_token_sequence
            (nat_sequence_decode secondValue) := by
      simpa [hPayloadCodes] using hSecondEqualityRaw
    have hThirdEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#thirdId ≐ₘ standard_token_sequence
            (nat_sequence_decode thirdValue) := by
      simpa [hPayloadCodes] using hThirdEqualityRaw
    have hConstructorEquality :=
      hConstructorCongruence
        (x#firstId)
        (standard_token_sequence (nat_sequence_decode firstValue))
        (x#secondId)
        (standard_token_sequence (nat_sequence_decode secondValue))
        (x#thirdId)
        (standard_token_sequence (nat_sequence_decode thirdValue))
        hFirst
        (standard_token_sequence_admissible
          (nat_sequence_decode firstValue))
        hSecond
        (standard_token_sequence_admissible
          (nat_sequence_decode secondValue))
        hThird
        (standard_token_sequence_admissible
          (nat_sequence_decode thirdValue))
        hFirstEquality hSecondEquality hThirdEquality
    have hConstructorStandardAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          constructor
              (standard_token_sequence
                (nat_sequence_decode firstValue))
              (standard_token_sequence
                (nat_sequence_decode secondValue))
              (standard_token_sequence
                (nat_sequence_decode thirdValue)) ≐ₘ
            standard_token_sequence expectedTokens :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          hConstructorStandard
    have hFormulaExpected :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          formulaCode ≐ₘ
            standard_token_sequence expectedTokens :=
      Metatheory.Derives.equality_trans hFormulaField <|
        Metatheory.Derives.equality_trans hConstructorEquality
          hConstructorStandardAt
    simpa [target] using hFormulaExpected
  have hImp :=
    fs_zfc_support_raw_exists_assignments_imp_fresh
      assignments body target
      (by
        intro eigen witness hMember
        have hEigen :
            eigen ∈
              [payloadId, sequenceId, firstId, secondId, thirdId] := by
          simpa [assignments] using
            List.mem_map_of_mem (f := Prod.fst) hMember
        have hReserved :
            eigen ∈
              [payloadId, sequenceId, firstId, secondId, thirdId, traceId,
                indexId] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hEigen ⊢
          rcases hEigen with h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        simpa [target, Formula.freeSupport,
          standard_token_sequence_freeSupport_nil] using
            hReservedFresh formulaCode (by simp) eigen hReserved)
      hBodyImp
  simpa [target, assignments, body,
    logical_ternary_base_certificate_condition_with_ids,
    Formula.existsFreeAssignments] using hImp

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
