import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalFirstOrderFailureAdapter
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Occurrence.Object
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoderFreeSupport

/-!
# 无关全称逻辑公理的失败适配

本模块只把 tag 9 的宿主检查失败转换成对象证书条件的否定。成功反演仍由既有
二元配对、公式字段与 canonical closure 接口承担；这里不公开 trace。
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
tag 9 的有效具名 payload 唯一决定对象分支的规范候选公式码。

该接口只保留终局失败适配器需要的函数性方向；公式是否与当前宿主公式错配由
调用方使用 `fs_logical_base_axiom_check = false` 判定。
-/
theorem fs_zfc_support_raw_logical_vacuous_forall_candidate
    (raw freeBase payloadCode eigen bodyCode : Nat)
    (sourceFormula : SetFormula)
    (formulaCode : SetTerm)
    (base : FreeVarId)
    (hBaseLower : 700 ≤ base)
    (hRawBound : raw < freeBase)
    (hRawPayload :
      (godel_unpair_value raw).2 = payloadCode)
    (hPayload :
      godel_unpair_value payloadCode = (eigen, bodyCode))
    (hBodyDecode :
      fs_named_formula_token_code_decode freeBase bodyCode =
        some sourceFormula)
    (hFormulaCode :
      Term.Admissible formulaCode SetSort.set)
    (hFormulaFresh :
      ∀ id,
        id ∈
          [base + 40, base + 52, base + 53, base + 54,
            base + 55, base + 56, base + 57] →
        (SetSort.set, id) ∉ Term.freeSupport formulaCode) :
    ∃ expectedTokens,
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] expectedTokens =
        some (Formula.imp sourceFormula
          (Formula.forallE SetSort.set
            (Formula.closeFreeAt
              SetSort.set eigen 0 sourceFormula))) ∧
      Derives fs_zfc_support_raw_theory [] (
        logical_vacuous_forall_certificate_condition_with_ids
            formulaCode (numₘ(raw))
            (base + 52) (base + 53) (base + 54) (base + 55)
            (base + 56) (base + 57) (base + 40) (base + 41) ⟶ₘ
          formulaCode ≐ₘ
            standard_token_sequence expectedTokens) := by
  let payloadId := base + 52
  let eigenId := base + 53
  let bodyNumericId := base + 54
  let sourceId := base + 55
  let variableId := base + 56
  let universalId := base + 57
  let traceId := base + 40
  let indexId := base + 41
  let bodyTokens := nat_sequence_decode bodyCode
  have hEigenBound : eigen < freeBase := by
    have hEigenPayload : eigen ≤ payloadCode := by
      simpa [hPayload] using
        godel_unpair_value_left_le payloadCode
    have hPayloadRaw : payloadCode ≤ raw := by
      simpa [hRawPayload] using
        godel_unpair_value_right_le raw
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans hEigenPayload hPayloadRaw) hRawBound
  have hBodyNamed :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] bodyTokens =
        some sourceFormula := by
    simpa [fs_named_formula_token_code_decode,
      bodyTokens] using hBodyDecode
  rcases
      fs_named_hilbert_tokens_decode_with_env_binder_close
        freeBase eigen [] bodyTokens sourceFormula
        hEigenBound hBodyNamed with
    ⟨shiftedTokens, hShift, hClosedBodyDecode⟩
  let closedTokens :=
    Numbered.universal_tokens 1
      (substitute_tokens shiftedTokens
        (Numbered.variable_token (free_name eigen))
        [Numbered.variable_token (bound_name 0)])
  let expectedTokens :=
    Numbered.implication_tokens bodyTokens closedTokens
  let candidate :=
    Formula.imp sourceFormula
      (Formula.forallE SetSort.set
        (Formula.closeFreeAt SetSort.set eigen 0 sourceFormula))
  have hClosedDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] closedTokens =
        some (Formula.forallE SetSort.set
          (Formula.closeFreeAt SetSort.set eigen 0 sourceFormula)) := by
    apply fs_named_hilbert_tokens_decode_with_env_universal
    simpa [closedTokens, bound_name] using hClosedBodyDecode
  have hExpectedDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] expectedTokens =
        some candidate :=
    fs_named_hilbert_tokens_decode_with_env_implication
      freeBase [] hBodyNamed hClosedDecode
  refine ⟨expectedTokens, by simpa [candidate] using hExpectedDecode, ?_⟩
  let fields : List SetFormula := [
    numₘ(raw) ≐ₘ godel_pairₘ(⟨numₘ(9), x#payloadId⟩ₘ),
    x#payloadId ≐ₘ
      godel_pairₘ(⟨x#eigenId, x#bodyNumericId⟩ₘ),
    x#eigenId ∈ₘ ωₘ,
    logical_formula_payload_component_condition_with_ids
      (x#sourceId) (x#bodyNumericId) traceId indexId,
    x#variableId ≐ₘ var_codeₘ(numₘ(2) *ₘ x#eigenId),
    ¬ₘ ((x#variableId) ∈ₘ varsₘ(x#sourceId)),
    canonical_forall_closure_code_condition
      (x#sourceId) (x#variableId) (x#universalId),
    formulaCode ≐ₘ
      imp_codeₘ(x#sourceId, x#universalId)]
  let body := logical_certificate_conjunction fields
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, x#payloadId), (eigenId, x#eigenId),
    (bodyNumericId, x#bodyNumericId), (sourceId, x#sourceId),
    (variableId, x#variableId), (universalId, x#universalId)]
  have hCondition :=
    logical_vacuous_forall_certificate_condition_with_ids_admissible
      formulaCode (numₘ(raw))
      payloadId eigenId bodyNumericId sourceId variableId universalId
      traceId indexId hFormulaCode
      (finite_numeral_term_admissible raw)
  have hBody : Formula.Admissible body :=
    fs_zfc_admissible_body_of_exists_assignments assignments body <| by
      simpa [assignments, body, fields, payloadId, eigenId,
        bodyNumericId, sourceId, variableId, universalId,
        traceId, indexId,
        logical_vacuous_forall_certificate_condition_with_ids,
        Formula.existsFreeAssignments] using hCondition
  have hTraceIndex : traceId ≠ indexId := by
    simp [traceId, indexId]
  have hTraceFreshBody :
      (SetSort.set, traceId) ∉ Formula.freeSupport body := by
    intro hMember
    have hConditionMember :
        (SetSort.set, traceId) ∈
          Formula.freeSupport
            (Formula.existsFreeAssignments
              SetSort.set assignments body) :=
      fs_zfc_fo_failure_mem_exists_assignments
        assignments body (SetSort.set, traceId)
        (by
          intro assignment hAssignment
          simp only [assignments, List.mem_cons,
            List.not_mem_nil, or_false] at hAssignment
          rcases hAssignment with rfl | rfl | rfl | rfl | rfl | rfl
          all_goals
            simp [traceId, payloadId, eigenId, bodyNumericId,
              sourceId, variableId, universalId])
        hMember
    rcases
        logical_vacuous_forall_certificate_condition_with_ids_freeSupport_subset
          formulaCode (numₘ(raw))
          payloadId eigenId bodyNumericId sourceId variableId universalId
          traceId indexId (SetSort.set, traceId)
          (by
            simpa [assignments, body, fields,
              logical_vacuous_forall_certificate_condition_with_ids,
              Formula.existsFreeAssignments] using hConditionMember) with
      hFormula | hCertificate
    · exact hFormulaFresh traceId (by simp [traceId]) hFormula
    · simp [finite_numeral_term_freeSupport] at hCertificate
  apply
    fs_zfc_support_raw_exists_assignments_imp_fresh
      assignments body
      (formulaCode ≐ₘ standard_token_sequence expectedTokens)
  · intro id _ hId
    simp only [assignments, List.mem_cons,
      List.not_mem_nil, or_false] at hId
    rcases hId with hId | hId | hId | hId | hId | hId
    all_goals
      cases hId
      simpa [Formula.freeSupport,
        standard_token_sequence_freeSupport_nil] using
        hFormulaFresh _ (by simp [payloadId, eigenId,
          bodyNumericId, sourceId, variableId, universalId])
  · apply FirstOrder.Derives.impIntro
      (hAntecedentCheck := Formula.check_admissible_complete hBody)
    let Γ : Context signature := [body]
    have hAt : Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ]) (Formula.check_admissible_complete hBody)
    have hField :
        ∀ field, field ∈ fields →
          Γ ⊢ₘ[fs_zfc_support_raw_theory] field := by
      intro field hMember
      exact fs_zfc_fo_failure_conjunction_elim
        fields field hMember (by simpa [Γ, body] using hAt)
    have hPair :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            godel_pairₘ(⟨numₘ(9), x#payloadId⟩ₘ) :=
      hField _ (by simp [fields])
    have hPayloadPair :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#payloadId ≐ₘ
            godel_pairₘ(⟨x#eigenId, x#bodyNumericId⟩ₘ) :=
      hField _ (by simp [fields])
    have hEigenNatural :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] x#eigenId ∈ₘ ωₘ :=
      hField _ (by simp [fields])
    have hComponent :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          logical_formula_payload_component_condition_with_ids
            (x#sourceId) (x#bodyNumericId) traceId indexId :=
      hField _ (by simp [fields])
    have hVariableField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#variableId ≐ₘ
            var_codeₘ(numₘ(2) *ₘ x#eigenId) :=
      hField _ (by simp [fields])
    have hClosure :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_forall_closure_code_condition
            (x#sourceId) (x#variableId) (x#universalId) :=
      hField _ (by simp [fields])
    have hFormulaField :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          formulaCode ≐ₘ
            imp_codeₘ(x#sourceId, x#universalId) :=
      hField _ (by simp [fields])
    have hBodyNatural :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#bodyNumericId ∈ₘ ωₘ :=
      (fs_zfc_support_raw_nat_sequence_code_condition_parts
        (x#sourceId) (x#bodyNumericId) traceId indexId
        (FirstOrder.Derives.conjElimRight hComponent)).2.1
    have hPayloadNatural :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] x#payloadId ∈ₘ ωₘ :=
      fs_zfc_support_raw_godel_pairing_mem_omega_of_equality
        (x#payloadId) (x#eigenId) (x#bodyNumericId)
        (set_variable_admissible payloadId)
        (set_variable_admissible eigenId)
        (set_variable_admissible bodyNumericId)
        hEigenNatural hBodyNatural hPayloadPair
    have hPayloadEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#payloadId ≐ₘ numₘ(payloadCode) := by
      simpa [hRawPayload] using
        ProofT.pair_right_unique
          ProofT.ZFC.pairing_core
          raw 9 (x#payloadId)
          (set_variable_admissible payloadId)
          hPayloadNatural hPair
    have hPayloadGround :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(payloadCode) ≐ₘ
            godel_pairₘ(⟨x#eigenId, x#bodyNumericId⟩ₘ) :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm hPayloadEquality)
        hPayloadPair
    have hEigenEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#eigenId ≐ₘ numₘ(eigen) := by
      simpa [hPayload] using
        ProofT.pair_left_unique
          ProofT.ZFC.pairing_core
          payloadCode (x#eigenId) (x#bodyNumericId)
          (set_variable_admissible eigenId)
          (set_variable_admissible bodyNumericId)
          hEigenNatural hBodyNatural hPayloadGround
    have hPayloadGround' :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(payloadCode) ≐ₘ
            godel_pairₘ(⟨numₘ(eigen), x#bodyNumericId⟩ₘ) :=
      Metatheory.Derives.equality_trans hPayloadGround <|
        godel_pairing_term_congr_of_equalities
          (x#eigenId) (numₘ(eigen))
          (x#bodyNumericId) (x#bodyNumericId)
          (set_variable_admissible eigenId)
          (finite_numeral_term_admissible eigen)
          (set_variable_admissible bodyNumericId)
          (set_variable_admissible bodyNumericId)
          hEigenEquality
          (FirstOrder.Derives.eq_refl_m (x#bodyNumericId))
    have hBodyNumericEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#bodyNumericId ≐ₘ numₘ(bodyCode) := by
      simpa [hPayload] using
        ProofT.pair_right_unique
          ProofT.ZFC.pairing_core
          payloadCode eigen (x#bodyNumericId)
          (set_variable_admissible bodyNumericId)
          hBodyNatural hPayloadGround'
    have hTraceFreshContext :
        ∀ formula, formula ∈ Γ →
          (SetSort.set, traceId) ∉ Formula.freeSupport formula := by
      intro formula hFormula
      simp only [Γ, List.mem_singleton] at hFormula
      subst formula
      exact hTraceFreshBody
    have hSourceEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#sourceId ≐ₘ standard_token_sequence bodyTokens :=
      fs_zfc_support_raw_logical_formula_payload_component_code_eq_standard
        (x#sourceId) (x#bodyNumericId) bodyCode
        traceId indexId hTraceIndex
        (set_variable_admissible sourceId)
        (set_variable_admissible bodyNumericId)
        (fs_zfc_fo_failure_set_variable_fresh traceId sourceId <| by
          simp [traceId, sourceId])
        (fs_zfc_fo_failure_set_variable_fresh indexId sourceId <| by
          simp [indexId, sourceId])
        (fs_zfc_fo_failure_set_variable_fresh indexId bodyNumericId <| by
          simp [indexId, bodyNumericId])
        hTraceFreshContext hComponent hBodyNumericEquality
    have hVariableCongruence :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          var_codeₘ(numₘ(2) *ₘ x#eigenId) ≐ₘ
            var_codeₘ(numₘ(2) *ₘ numₘ(eigen)) :=
      Metatheory.Derives.unary_term_constructor_congr_of_equality
        (fun term => var_codeₘ(numₘ(2) *ₘ term))
        (fun term hTerm =>
          variable_code_term_admissible _ <|
            natural_multiplication_term_admissible
              (numₘ(2)) term
              (finite_numeral_term_admissible 2) hTerm)
        (by
          intros
          simp [Term.substituteFree,
            Term.substituteFree_eq_self_of_not_mem,
            finite_numeral_term_freeSupport])
        (x#eigenId) (numₘ(eigen))
        (set_variable_admissible eigenId)
        (finite_numeral_term_admissible eigen)
        hEigenEquality
    have hVariableArithmetic :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          var_codeₘ(numₘ(2) *ₘ numₘ(eigen)) ≐ₘ
            var_codeₘ(numₘ(2 * eigen)) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          Metatheory.Derives.equality_symm
            (fs_zfc_support_raw_variable_code_term_numeral_mul eigen)
    have hVariableNamed :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#variableId ≐ₘ
            Numbered.named_variable_code (free_name eigen) := by
      simpa [Numbered.named_variable_code, free_name] using
        Metatheory.Derives.equality_trans hVariableField <|
          Metatheory.Derives.equality_trans
            hVariableCongruence hVariableArithmetic
    have hVariableStandard :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#variableId ≐ₘ standard_token_sequence
            [Numbered.variable_token (free_name eigen)] :=
      Metatheory.Derives.equality_trans hVariableNamed <|
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            fs_zfc_support_raw_derives_of_godel_quotation <|
              named_variable_code_eq_standard_token_sequence
                (free_name eigen)
    have hFreshVariable
        (id offset : Nat) (hUpper : id ≤ 470) :
        (SetSort.set, id) ∉
          Term.freeSupport (x#(base + offset)) :=
      fs_zfc_fo_failure_set_variable_fresh id (base + offset) <| by
        apply Nat.ne_of_lt
        exact Nat.lt_of_le_of_lt hUpper <|
          Nat.lt_of_lt_of_le (by decide : 470 < 700) <|
            Nat.le_trans hBaseLower
              (Nat.le_add_right base offset)
    have hFunctional :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_canonical_forall_closure_unique_imp
            bodyTokens shiftedTokens eigen hShift
            (x#sourceId) (x#variableId) (x#universalId)
            (Term.check_certificate_of_admissible <|
              set_variable_admissible sourceId)
            (Term.check_certificate_of_admissible <|
              set_variable_admissible variableId)
            (Term.check_certificate_of_admissible <|
              set_variable_admissible universalId)
            (by
              intro id _ hUpper
              exact hFreshVariable id 55
                (Nat.le_trans hUpper (by decide)))
            (by
              intro id _ hUpper
              exact hFreshVariable id 56
                (Nat.le_trans hUpper (by decide)))
            (by
              intro id hId
              exact hFreshVariable id 55 <| by
                rcases hId with rfl | rfl <;> decide)
            (by
              intro id hId
              exact hFreshVariable id 56 <| by
                rcases hId with rfl | rfl <;> decide)
            (by
              intro id hId
              exact hFreshVariable id 57 <| by
                rcases hId with rfl | rfl <;> decide)
            (by
              intro id hId
              exact hFreshVariable id 56 <| by
                rcases hId with rfl | rfl <;> decide)
    have hClosedEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#universalId ≐ₘ
            standard_token_sequence closedTokens := by
      simpa [closedTokens] using
        FirstOrder.Derives.impElim
          (FirstOrder.Derives.impElim
            (FirstOrder.Derives.impElim
              hFunctional hSourceEquality)
            hVariableStandard)
          hClosure
    have hImplicationEquality :=
      fs_zfc_support_raw_implication_code_eq_standard
        bodyTokens closedTokens
        (x#sourceId) (x#universalId)
        (Term.check_certificate_of_admissible <|
          set_variable_admissible sourceId)
        (Term.check_certificate_of_admissible <|
          set_variable_admissible universalId)
        hSourceEquality hClosedEquality
    simpa [fields, expectedTokens] using
      Metatheory.Derives.equality_trans
        hFormulaField hImplicationEquality

/--
tag 9 的两类结构失败直接否定对象分支：正文不能具名解码，或 eigen 在正文中
自由出现。公式最终错配不在此处理，而由候选函数性出口保留给 tail 回折。
-/
theorem fs_zfc_support_raw_logical_vacuous_forall_neg_of_structural_failure
    (raw freeBase payloadCode eigen bodyCode : Nat)
    (formulaCode : SetTerm)
    (base : FreeVarId)
    (hRawPayload :
      (godel_unpair_value raw).2 = payloadCode)
    (hPayload :
      godel_unpair_value payloadCode = (eigen, bodyCode))
    (hEigenBound : eigen < freeBase)
    (hFormulaCode :
      Term.Admissible formulaCode SetSort.set)
    (hTraceFresh :
      (SetSort.set, base + 40) ∉
        Term.freeSupport formulaCode)
    (hFailure :
      fs_named_formula_token_code_decode freeBase bodyCode = none ∨
        ∃ sourceFormula,
          fs_named_formula_token_code_decode freeBase bodyCode =
              some sourceFormula ∧
            (SetSort.set, eigen) ∈
              Formula.freeSupport sourceFormula) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_vacuous_forall_certificate_condition_with_ids
        formulaCode (numₘ(raw))
        (base + 52) (base + 53) (base + 54) (base + 55)
        (base + 56) (base + 57) (base + 40) (base + 41)) := by
  let payloadId := base + 52
  let eigenId := base + 53
  let bodyNumericId := base + 54
  let sourceId := base + 55
  let variableId := base + 56
  let universalId := base + 57
  let traceId := base + 40
  let indexId := base + 41
  let bodyTokens := nat_sequence_decode bodyCode
  let fields : List SetFormula := [
    numₘ(raw) ≐ₘ godel_pairₘ(⟨numₘ(9), x#payloadId⟩ₘ),
    x#payloadId ≐ₘ
      godel_pairₘ(⟨x#eigenId, x#bodyNumericId⟩ₘ),
    x#eigenId ∈ₘ ωₘ,
    logical_formula_payload_component_condition_with_ids
      (x#sourceId) (x#bodyNumericId) traceId indexId,
    x#variableId ≐ₘ var_codeₘ(numₘ(2) *ₘ x#eigenId),
    ¬ₘ ((x#variableId) ∈ₘ varsₘ(x#sourceId)),
    canonical_forall_closure_code_condition
      (x#sourceId) (x#variableId) (x#universalId),
    formulaCode ≐ₘ
      imp_codeₘ(x#sourceId, x#universalId)]
  let body := logical_certificate_conjunction fields
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, x#payloadId), (eigenId, x#eigenId),
    (bodyNumericId, x#bodyNumericId), (sourceId, x#sourceId),
    (variableId, x#variableId), (universalId, x#universalId)]
  have hCondition :=
    logical_vacuous_forall_certificate_condition_with_ids_admissible
      formulaCode (numₘ(raw))
      payloadId eigenId bodyNumericId sourceId variableId universalId
      traceId indexId hFormulaCode
      (finite_numeral_term_admissible raw)
  have hBody : Formula.Admissible body :=
    fs_zfc_admissible_body_of_exists_assignments assignments body <| by
      simpa [assignments, body, fields, payloadId, eigenId,
        bodyNumericId, sourceId, variableId, universalId,
        traceId, indexId,
        logical_vacuous_forall_certificate_condition_with_ids,
        Formula.existsFreeAssignments] using hCondition
  have hTraceIndex : traceId ≠ indexId := by
    simp [traceId, indexId]
  have hTraceFreshBody :
      (SetSort.set, traceId) ∉ Formula.freeSupport body := by
    intro hMember
    have hConditionMember :
        (SetSort.set, traceId) ∈
          Formula.freeSupport
            (Formula.existsFreeAssignments
              SetSort.set assignments body) :=
      fs_zfc_fo_failure_mem_exists_assignments
        assignments body (SetSort.set, traceId)
        (by
          intro assignment hAssignment
          simp only [assignments, List.mem_cons,
            List.not_mem_nil, or_false] at hAssignment
          rcases hAssignment with rfl | rfl | rfl | rfl | rfl | rfl
          all_goals
            simp [traceId, payloadId, eigenId, bodyNumericId,
              sourceId, variableId, universalId])
        hMember
    rcases
        logical_vacuous_forall_certificate_condition_with_ids_freeSupport_subset
          formulaCode (numₘ(raw))
          payloadId eigenId bodyNumericId sourceId variableId universalId
          traceId indexId (SetSort.set, traceId)
          (by
            simpa [assignments, body, fields,
              logical_vacuous_forall_certificate_condition_with_ids,
              Formula.existsFreeAssignments] using hConditionMember) with
      hFormula | hCertificate
    · exact hTraceFresh hFormula
    · simp [finite_numeral_term_freeSupport] at hCertificate
  apply fs_zfc_support_raw_exists_assignments_neg assignments body
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck := Formula.check_admissible_complete hBody)
  let Γ : Context signature := [body]
  have hAt : Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
    FirstOrder.Derives.assumption
      (by simp [Γ]) (Formula.check_admissible_complete hBody)
  have hField :
      ∀ field, field ∈ fields →
        Γ ⊢ₘ[fs_zfc_support_raw_theory] field := by
    intro field hMember
    exact fs_zfc_fo_failure_conjunction_elim
      fields field hMember (by simpa [Γ, body] using hAt)
  have hPair :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(raw) ≐ₘ
          godel_pairₘ(⟨numₘ(9), x#payloadId⟩ₘ) :=
    hField _ (by simp [fields])
  have hPayloadPair :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#payloadId ≐ₘ
          godel_pairₘ(⟨x#eigenId, x#bodyNumericId⟩ₘ) :=
    hField _ (by simp [fields])
  have hEigenNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] x#eigenId ∈ₘ ωₘ :=
    hField _ (by simp [fields])
  have hComponent :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_formula_payload_component_condition_with_ids
          (x#sourceId) (x#bodyNumericId) traceId indexId :=
    hField _ (by simp [fields])
  have hVariableField :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#variableId ≐ₘ
          var_codeₘ(numₘ(2) *ₘ x#eigenId) :=
    hField _ (by simp [fields])
  have hNonmember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ¬ₘ ((x#variableId) ∈ₘ varsₘ(x#sourceId)) :=
    hField _ (by simp [fields])
  have hBodyNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#bodyNumericId ∈ₘ ωₘ :=
    (fs_zfc_support_raw_nat_sequence_code_condition_parts
      (x#sourceId) (x#bodyNumericId) traceId indexId
      (FirstOrder.Derives.conjElimRight hComponent)).2.1
  have hPayloadNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] x#payloadId ∈ₘ ωₘ :=
    fs_zfc_support_raw_godel_pairing_mem_omega_of_equality
      (x#payloadId) (x#eigenId) (x#bodyNumericId)
      (set_variable_admissible payloadId)
      (set_variable_admissible eigenId)
      (set_variable_admissible bodyNumericId)
      hEigenNatural hBodyNatural hPayloadPair
  have hPayloadEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#payloadId ≐ₘ numₘ(payloadCode) := by
    simpa [hRawPayload] using
      ProofT.pair_right_unique
        ProofT.ZFC.pairing_core
        raw 9 (x#payloadId)
        (set_variable_admissible payloadId)
        hPayloadNatural hPair
  have hPayloadGround :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(payloadCode) ≐ₘ
          godel_pairₘ(⟨x#eigenId, x#bodyNumericId⟩ₘ) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hPayloadEquality)
      hPayloadPair
  have hEigenEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#eigenId ≐ₘ numₘ(eigen) := by
    simpa [hPayload] using
      ProofT.pair_left_unique
        ProofT.ZFC.pairing_core
        payloadCode (x#eigenId) (x#bodyNumericId)
        (set_variable_admissible eigenId)
        (set_variable_admissible bodyNumericId)
        hEigenNatural hBodyNatural hPayloadGround
  have hPayloadGround' :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(payloadCode) ≐ₘ
          godel_pairₘ(⟨numₘ(eigen), x#bodyNumericId⟩ₘ) :=
    Metatheory.Derives.equality_trans hPayloadGround <|
      godel_pairing_term_congr_of_equalities
        (x#eigenId) (numₘ(eigen))
        (x#bodyNumericId) (x#bodyNumericId)
        (set_variable_admissible eigenId)
        (finite_numeral_term_admissible eigen)
        (set_variable_admissible bodyNumericId)
        (set_variable_admissible bodyNumericId)
        hEigenEquality
        (FirstOrder.Derives.eq_refl_m (x#bodyNumericId))
  have hBodyNumericEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#bodyNumericId ≐ₘ numₘ(bodyCode) := by
    simpa [hPayload] using
      ProofT.pair_right_unique
        ProofT.ZFC.pairing_core
        payloadCode eigen (x#bodyNumericId)
        (set_variable_admissible bodyNumericId)
        hBodyNatural hPayloadGround'
  have hTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    simp only [Γ, List.mem_singleton] at hFormula
    subst formula
    exact hTraceFreshBody
  rcases hFailure with hDecodeNone |
      ⟨sourceFormula, hBodyDecode, hMember⟩
  · exact
      fs_zfc_support_raw_logical_formula_payload_component_falsum_of_named_decode_none
        (x#sourceId) (x#bodyNumericId) freeBase bodyCode
        traceId indexId hTraceIndex
        (set_variable_admissible sourceId)
        (set_variable_admissible bodyNumericId)
        (fs_zfc_fo_failure_set_variable_fresh traceId sourceId <| by
          simp [traceId, sourceId])
        (fs_zfc_fo_failure_set_variable_fresh indexId sourceId <| by
          simp [indexId, sourceId])
        (fs_zfc_fo_failure_set_variable_fresh indexId bodyNumericId <| by
          simp [indexId, bodyNumericId])
        hTraceFreshContext hComponent hBodyNumericEquality
        (by
          simpa [fs_named_formula_token_code_decode,
            bodyTokens] using hDecodeNone)
  · have hSourceEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#sourceId ≐ₘ standard_token_sequence bodyTokens :=
      fs_zfc_support_raw_logical_formula_payload_component_code_eq_standard
        (x#sourceId) (x#bodyNumericId) bodyCode
        traceId indexId hTraceIndex
        (set_variable_admissible sourceId)
        (set_variable_admissible bodyNumericId)
        (fs_zfc_fo_failure_set_variable_fresh traceId sourceId <| by
          simp [traceId, sourceId])
        (fs_zfc_fo_failure_set_variable_fresh indexId sourceId <| by
          simp [indexId, sourceId])
        (fs_zfc_fo_failure_set_variable_fresh indexId bodyNumericId <| by
          simp [indexId, bodyNumericId])
        hTraceFreshContext hComponent hBodyNumericEquality
    have hVariableCongruence :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          var_codeₘ(numₘ(2) *ₘ x#eigenId) ≐ₘ
            var_codeₘ(numₘ(2) *ₘ numₘ(eigen)) :=
      Metatheory.Derives.unary_term_constructor_congr_of_equality
        (fun term => var_codeₘ(numₘ(2) *ₘ term))
        (fun term hTerm =>
          variable_code_term_admissible _ <|
            natural_multiplication_term_admissible
              (numₘ(2)) term
              (finite_numeral_term_admissible 2) hTerm)
        (by
          intros
          simp [Term.substituteFree,
            Term.substituteFree_eq_self_of_not_mem,
            finite_numeral_term_freeSupport])
        (x#eigenId) (numₘ(eigen))
        (set_variable_admissible eigenId)
        (finite_numeral_term_admissible eigen)
        hEigenEquality
    have hVariableArithmetic :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          var_codeₘ(numₘ(2) *ₘ numₘ(eigen)) ≐ₘ
            var_codeₘ(numₘ(2 * eigen)) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          Metatheory.Derives.equality_symm
            (fs_zfc_support_raw_variable_code_term_numeral_mul eigen)
    have hVariableNamed :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#variableId ≐ₘ
            Numbered.named_variable_code (free_name eigen) := by
      simpa [Numbered.named_variable_code, free_name] using
        Metatheory.Derives.equality_trans hVariableField <|
          Metatheory.Derives.equality_trans
            hVariableCongruence hVariableArithmetic
    have hBodyNamed :
        fs_named_hilbert_tokens_decode_with_env
            freeBase [] bodyTokens =
          some sourceFormula := by
      simpa [fs_named_formula_token_code_decode,
        bodyTokens] using hBodyDecode
    have hToken :=
      fs_named_hilbert_tokens_decode_with_env_low_fvar_mem
        freeBase [] hBodyNamed hMember hEigenBound
    let standardSource := standard_token_sequence bodyTokens
    let namedVariable :=
      Numbered.named_variable_code (free_name eigen)
    have hSourceFormula :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          formula_codeₘ(x#sourceId) :=
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimLeft hComponent
    have hSourceMember :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#sourceId ∈ₘ FormulaCodeₘ :=
      FirstOrder.Derives.iffElimRight
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            fs_zfc_support_raw_derives_of_godel_quotation <|
              gq_formula_code_definition_instance
                (x#sourceId) (set_variable_admissible sourceId))
        hSourceFormula
    have hStandardFormula :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          standardSource ∈ₘ FormulaCodeₘ :=
      FirstOrder.Derives.iffElimRight
        (membership_left_iff_of_equality
          (x#sourceId) standardSource FormulaCodeₘ
          (set_variable_admissible sourceId)
          (standard_token_sequence_admissible bodyTokens)
          formula_code_set_term_admissible
          (by simpa [standardSource] using hSourceEquality))
        hSourceMember
    have hStandardUnion :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          standardSource ∈ₘ (TermCodeₘ ∪ₘ FormulaCodeₘ) :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            fs_zfc_support_raw_derives_of_godel_quotation <|
              gq_weaken_relation_plane <|
                mem_binary_union_right
                  TermCodeₘ FormulaCodeₘ standardSource
                  term_code_set_term_admissible
                  formula_code_set_term_admissible
                  (standard_token_sequence_admissible bodyTokens))
        hStandardFormula
    have hNamedMember :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          namedVariable ∈ₘ VarSymₘ :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation <| by
            simpa [namedVariable] using
              named_variable_code_mem_variable_symbols
                (free_name eigen)
    have hOccurrence :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          variable_symbol_occurs_condition
            namedVariable standardSource :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          FirstOrder.Derives.theory_weaken
            (fun _ h =>
              fs_zfc_support_raw_contains_quotation_occurrence h) <| by
                simpa [namedVariable, standardSource] using
                  standard_token_sequence_variable_symbol_occurs
                    bodyTokens (free_name eigen) hToken
    have hStandardCollection :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          namedVariable ∈ₘ varsₘ(standardSource) := by
      have hFunctional :=
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            fs_zfc_support_raw_derives_of_godel_quotation <|
              gq_variable_collection_member_of_occurrence_imp
                standardSource namedVariable
                ⟨standard_token_sequence_admissible bodyTokens,
                  standard_token_sequence_freeSupport_nil bodyTokens⟩
                ⟨variable_code_term_admissible _
                    (finite_numeral_term_admissible _),
                  named_variable_code_freeSupport _⟩
      exact FirstOrder.Derives.impElim
        (FirstOrder.Derives.impElim
          (FirstOrder.Derives.impElim hFunctional hStandardUnion)
          hNamedMember)
        hOccurrence
    have hObjectVariableCollection :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#variableId ∈ₘ varsₘ(standardSource) :=
      FirstOrder.Derives.iffElimLeft
        (membership_left_iff_of_equality
          (x#variableId) namedVariable (varsₘ(standardSource))
          (set_variable_admissible variableId)
          (variable_code_term_admissible _
            (finite_numeral_term_admissible _))
          (variable_collection_term_admissible standardSource
            (standard_token_sequence_admissible bodyTokens))
          (by simpa [namedVariable] using hVariableNamed))
        hStandardCollection
    have hCollectionEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          varsₘ(x#sourceId) ≐ₘ varsₘ(standardSource) :=
      Metatheory.Derives.unary_term_constructor_congr_of_equality
        (fun source => varsₘ(source))
        (fun source hSource =>
          variable_collection_term_admissible source hSource)
        (by intros; simp [Term.substituteFree])
        (x#sourceId) standardSource
        (set_variable_admissible sourceId)
        (standard_token_sequence_admissible bodyTokens)
        (by simpa [standardSource] using hSourceEquality)
    have hObjectMember :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          x#variableId ∈ₘ varsₘ(x#sourceId) :=
      FirstOrder.Derives.iffElimLeft
        (membership_right_iff_of_equality
          (x#variableId)
          (varsₘ(x#sourceId)) (varsₘ(standardSource))
          (set_variable_admissible variableId)
          (variable_collection_term_admissible
            (x#sourceId) (set_variable_admissible sourceId))
          (variable_collection_term_admissible standardSource
            (standard_token_sequence_admissible bodyTokens))
          hCollectionEquality)
        hObjectVariableCollection
    exact FirstOrder.Derives.negElim hObjectMember hNonmember

/--
tag 9 的 checker 失败要么否定对象分支，要么保留唯一候选及宿主公式错配。
-/
theorem fs_zfc_support_raw_logical_vacuous_forall_neg_or_candidate
    (raw freeBase : Nat)
    (formula : SetFormula)
    (formulaCode : SetTerm)
    (base : FreeVarId)
    (hBaseLower : 700 ≤ base)
    (hRawBound : raw < freeBase)
    (hTag : (godel_unpair_value raw).1 = 9)
    (hFormulaCode :
      Term.Admissible formulaCode SetSort.set)
    (hFormulaFresh :
      ∀ id,
        id ∈
          [base + 40, base + 52, base + 53, base + 54,
            base + 55, base + 56, base + 57] →
        (SetSort.set, id) ∉ Term.freeSupport formulaCode)
    (hCheck :
      fs_logical_base_axiom_check
        freeBase formula raw = false) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_vacuous_forall_certificate_condition_with_ids
        formulaCode (numₘ(raw))
        (base + 52) (base + 53) (base + 54) (base + 55)
        (base + 56) (base + 57) (base + 40) (base + 41)) ∨
    ∃ expectedTokens expected,
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] expectedTokens =
        some expected ∧
      formula ≠ expected ∧
      Derives fs_zfc_support_raw_theory [] (
        logical_vacuous_forall_certificate_condition_with_ids
            formulaCode (numₘ(raw))
            (base + 52) (base + 53) (base + 54) (base + 55)
            (base + 56) (base + 57) (base + 40) (base + 41) ⟶ₘ
          formulaCode ≐ₘ
            standard_token_sequence expectedTokens) := by
  let payloadCode := (godel_unpair_value raw).2
  let payloadPair := godel_unpair_value payloadCode
  let eigen := payloadPair.1
  let bodyCode := payloadPair.2
  have hRawPayload :
      (godel_unpair_value raw).2 = payloadCode := rfl
  have hPayload :
      godel_unpair_value payloadCode = (eigen, bodyCode) := by
    simp [payloadPair, eigen, bodyCode]
  have hEigenBound : eigen < freeBase := by
    have hEigenPayload : eigen ≤ payloadCode := by
      simpa [hPayload] using
        godel_unpair_value_left_le payloadCode
    have hPayloadRaw : payloadCode ≤ raw := by
      simpa [hRawPayload] using
        godel_unpair_value_right_le raw
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans hEigenPayload hPayloadRaw) hRawBound
  cases hBodyDecode :
      fs_named_formula_token_code_decode freeBase bodyCode with
  | none =>
      exact Or.inl <|
        fs_zfc_support_raw_logical_vacuous_forall_neg_of_structural_failure
          raw freeBase payloadCode eigen bodyCode formulaCode base
          hRawPayload hPayload hEigenBound hFormulaCode
          (hFormulaFresh (base + 40) (by simp))
          (Or.inl hBodyDecode)
  | some sourceFormula =>
      by_cases hFresh :
          (SetSort.set, eigen) ∉
            Formula.freeSupport sourceFormula
      · rcases
          fs_zfc_support_raw_logical_vacuous_forall_candidate
            raw freeBase payloadCode eigen bodyCode sourceFormula
            formulaCode base hBaseLower hRawBound
            hRawPayload hPayload hBodyDecode hFormulaCode
            hFormulaFresh with
          ⟨expectedTokens, hExpectedDecode, hExpected⟩
        let expected :=
          Formula.imp sourceFormula
            (Formula.forallE SetSort.set
              (Formula.closeFreeAt
                SetSort.set eigen 0 sourceFormula))
        have hFormulaCheck :
            fs_formula_code_eq formula expected = false := by
          simpa [fs_logical_base_axiom_check,
            fs_logical_base_axiom_check_with, hTag,
            payloadCode, payloadPair, eigen, bodyCode,
            hBodyDecode, hFresh, expected] using hCheck
        exact Or.inr
          ⟨expectedTokens, expected,
            by simpa [expected] using hExpectedDecode,
            fs_formula_code_eq_ne_of_false hFormulaCheck,
            hExpected⟩
      · exact Or.inl <|
          fs_zfc_support_raw_logical_vacuous_forall_neg_of_structural_failure
            raw freeBase payloadCode eigen bodyCode formulaCode base
            hRawPayload hPayload hEigenBound hFormulaCode
            (hFormulaFresh (base + 40) (by simp))
            (Or.inr
              ⟨sourceFormula, hBodyDecode,
                Classical.byContradiction hFresh⟩)

/-- tag 9 检查失败时，由结构失败或规范候选两种完备情形导出对象层否定。 -/
theorem fs_zfc_support_raw_logical_vacuous_forall_neg_of_check_false
    (raw freeBase : Nat)
    (row : List Nat)
    (decoded : FSDecodedFormula)
    (base : FreeVarId)
    (hBaseLower : 700 ≤ base)
    (hRawBound : raw < freeBase)
    (hTag : (godel_unpair_value raw).1 = 9)
    (hDecode : fs_formula_row_decode freeBase row = some decoded)
    (hCheck :
      fs_logical_base_axiom_check
        freeBase decoded.formula raw = false) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_vacuous_forall_certificate_condition_with_ids
        (standard_token_sequence row) (numₘ(raw))
        (base + 52) (base + 53) (base + 54) (base + 55)
        (base + 56) (base + 57) (base + 40) (base + 41)) := by
  rcases
      fs_zfc_support_raw_logical_vacuous_forall_neg_or_candidate
        raw freeBase decoded.formula
        (standard_token_sequence row) base
        hBaseLower hRawBound hTag
        (standard_token_sequence_admissible row)
        (by
          intro id _
          rw [standard_token_sequence_freeSupport_nil]
          exact List.not_mem_nil)
        hCheck with
    hNeg |
      ⟨expectedTokens, expected, hExpectedDecode,
        hMismatch, hExpected⟩
  · exact hNeg
  · have hNamedDecode :=
      fs_formula_row_decode_named_of_some hDecode
    have hRowNe : row ≠ expectedTokens := by
      intro hRows
      rw [hRows] at hNamedDecode
      apply hMismatch
      exact Option.some.inj <|
        hNamedDecode.symm.trans hExpectedDecode
    exact
      fs_zfc_support_raw_neg_of_candidate_code_ne
        (logical_vacuous_forall_certificate_condition_with_ids
          (standard_token_sequence row) (numₘ(raw))
          (base + 52) (base + 53) (base + 54) (base + 55)
          (base + 56) (base + 57) (base + 40) (base + 41))
        (standard_token_sequence row)
        row expectedTokens hExpected
        (FirstOrder.Derives.eq_refl_m
          (standard_token_sequence row))
        hRowNe

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
