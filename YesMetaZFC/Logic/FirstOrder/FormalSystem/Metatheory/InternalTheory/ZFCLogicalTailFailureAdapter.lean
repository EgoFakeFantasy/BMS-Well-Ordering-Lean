import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalBaseFailureAdapter
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCProjectDecodeObjectClosure

/-!
# 逻辑 transcript 尾失败适配

本模块只在失败适配器内部消费完整逻辑证书的有限 transcript。成功对象条件的
序列恢复、逐点读取与 canonical closure 唯一性仍由既有层提供；这里不引入新的
反演关系，也不把 trace 暴露到 Rosser 终局接口。
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

/-! ## 规范 payload 的有限坐标 -/

/--
非空规范 payload 的定义域若等于某个后继，则末索引恰为最后一个 numeral。

该定理只做有限 numeral 消去；它不恢复或解释 formula trace。
-/
theorem fs_zfc_support_raw_logical_last_index_eq
    {Γ : Context signature}
    (sequence lastIndex : SetTerm)
    (payload : List Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hLastIndex : Term.Admissible lastIndex SetSort.set)
    (hSequenceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence ≐ₘ standard_token_sequence payload)
    (hDomainSuccessor :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ Sₘ(lastIndex)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      lastIndex ≐ₘ numₘ(payload.length - 1) := by
  have hDomainEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ
          domₘ(standard_token_sequence payload) :=
    domain_term_congr_of_equality
      sequence (standard_token_sequence payload)
      hSequence (standard_token_sequence_admissible payload)
      hSequenceEquality
  have hStandardDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(standard_token_sequence payload) ≐ₘ
          numₘ(payload.length) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_standard_sequence
          (standard_token_sequence_domain_eq_length payload)
  have hDomainLength :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ numₘ(payload.length) :=
    Metatheory.Derives.equality_trans
      hDomainEquality hStandardDomain
  have hLastMemberSuccessor :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        lastIndex ∈ₘ Sₘ(lastIndex) :=
    fs_zfc_support_raw_logical_mem_successor_self
      lastIndex hLastIndex
  have hLastMemberDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        lastIndex ∈ₘ domₘ(sequence) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        lastIndex (domₘ(sequence)) (Sₘ(lastIndex))
        hLastIndex
        (domain_term_admissible sequence hSequence)
        (successor_term_admissible lastIndex hLastIndex)
        hDomainSuccessor)
      hLastMemberSuccessor
  have hLastMemberLength :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        lastIndex ∈ₘ numₘ(payload.length) :=
    FirstOrder.Derives.iffElimRight
      (membership_right_iff_of_equality
        lastIndex (domₘ(sequence)) (numₘ(payload.length))
        hLastIndex
        (domain_term_admissible sequence hSequence)
        (finite_numeral_term_admissible payload.length)
        hDomainLength)
      hLastMemberDomain
  apply fs_zfc_support_raw_finite_numeral_member_elim_context
    payload.length lastIndex
    (lastIndex ≐ₘ numₘ(payload.length - 1))
    hLastIndex
    (Formula.Admissible.equal hLastIndex
      (finite_numeral_term_admissible (payload.length - 1)))
    hLastMemberLength
  intro index hIndex
  let Δ : Context signature :=
    (lastIndex ≐ₘ numₘ(index)) :: Γ
  have hIndexEquality :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        lastIndex ≐ₘ numₘ(index) :=
    FirstOrder.Derives.assumption (by simp [Δ])
  by_cases hFinal : index = payload.length - 1
  · simpa [Δ, hFinal] using hIndexEquality
  · have hSuccessorEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          Sₘ(lastIndex) ≐ₘ Sₘ(numₘ(index)) :=
      successor_term_congr_of_equality
        lastIndex (numₘ(index))
        hLastIndex (finite_numeral_term_admissible index)
        hIndexEquality
    have hDomainIndex :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(sequence) ≐ₘ numₘ(index + 1) := by
      simpa [finite_numeral_term, successor_term] using
        Metatheory.Derives.equality_trans
          (FirstOrder.Derives.context_weaken_cons hDomainSuccessor)
          hSuccessorEquality
    have hLengthEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(payload.length) ≐ₘ numₘ(index + 1) :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm
          (FirstOrder.Derives.context_weaken_cons hDomainLength))
        hDomainIndex
    exact FirstOrder.Derives.falsumElim
      (fs_zfc_support_raw_falsum_of_numeral_equality
        (by
          intro hLength
          apply hFinal
          omega)
        hLengthEquality)

/-- 规范 payload 序列在一个宿主已知位置的对象层值。 -/
theorem fs_zfc_support_raw_logical_payload_apply
    {Γ : Context signature}
    (sequence : SetTerm)
    (payload : List Nat)
    (index : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hIndex : index < payload.length)
    (hSequenceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence ≐ₘ standard_token_sequence payload) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (sequence ·ₘ numₘ(index)) ≐ₘ numₘ(payload[index]) := by
  have hSequenceAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (sequence ·ₘ numₘ(index)) ≐ₘ
          (standard_token_sequence payload ·ₘ numₘ(index)) :=
    function_application_term_congr_function_of_equality
      sequence (standard_token_sequence payload) (numₘ(index))
      hSequence (standard_token_sequence_admissible payload)
      (finite_numeral_term_admissible index)
      hSequenceEquality
  have hGet :
      payload[index]? = some payload[index] :=
    List.getElem?_eq_getElem hIndex
  have hStandardAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (standard_token_sequence payload ·ₘ numₘ(index)) ≐ₘ
          numₘ(payload[index]) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_standard_sequence
          (standard_token_sequence_apply_getElem? payload hGet)
  exact Metatheory.Derives.equality_trans
    hSequenceAt hStandardAt

/-! ## transcript 闭包边的 numeral 实例 -/

/-- 固定 checked binder 编号下，把全称 closure 字段实例化到一个宿主 numeral。 -/
theorem fs_zfc_support_raw_logical_closure_step_of_all_at_numeral
    {Γ : Context signature}
    (index : Nat)
    (hAllSteps :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[SetSort.set, ProofT.lc_line_index_id],
          (x#ProofT.lc_line_index_id ∈ₘ
              x#ProofT.lc_last_index_id) ⟶ₘ
            logical_closure_certificate_step_condition
              (x#ProofT.lc_sequence_id)
              (x#ProofT.lc_formula_trace_id)
              (x#ProofT.lc_line_index_id))
    (hIndexMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(index) ∈ₘ x#ProofT.lc_last_index_id) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      logical_closure_certificate_step_condition
        (x#ProofT.lc_sequence_id)
        (x#ProofT.lc_formula_trace_id)
        (numₘ(index)) := by
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := numₘ(index)) hAllSteps
  rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    at hAtRaw
  have hSequenceSubstitution :
      Term.substituteFree SetSort.set
          ProofT.lc_line_index_id (numₘ(index))
          (x#ProofT.lc_sequence_id) =
        x#ProofT.lc_sequence_id := by
    simp [Term.substituteFree, set_variable,
      show ProofT.lc_sequence_id ≠
        ProofT.lc_line_index_id by native_decide]
  have hFormulaTraceSubstitution :
      Term.substituteFree SetSort.set
          ProofT.lc_line_index_id (numₘ(index))
          (x#ProofT.lc_formula_trace_id) =
        x#ProofT.lc_formula_trace_id := by
    simp [Term.substituteFree, set_variable,
      show ProofT.lc_formula_trace_id ≠
        ProofT.lc_line_index_id by native_decide]
  have hLineIndexSubstitution :
      Term.substituteFree SetSort.set
          ProofT.lc_line_index_id (numₘ(index))
          (x#ProofT.lc_line_index_id) =
        numₘ(index) := by
    simp [Term.substituteFree, set_variable]
  have hStepSubstitution :=
    logical_closure_certificate_step_condition_substitute_closed
      (x#ProofT.lc_sequence_id)
      (x#ProofT.lc_formula_trace_id)
      (x#ProofT.lc_line_index_id)
      (numₘ(index))
      (x#ProofT.lc_sequence_id)
      (x#ProofT.lc_formula_trace_id)
      (numₘ(index))
      ProofT.lc_line_index_id
      (by native_decide)
      (finite_numeral_term_admissible index)
      (finite_numeral_term_freeSupport index)
      hSequenceSubstitution
      hFormulaTraceSubstitution
      hLineIndexSubstitution
  have hAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (numₘ(index) ∈ₘ
            x#ProofT.lc_last_index_id) ⟶ₘ
          logical_closure_certificate_step_condition
            (x#ProofT.lc_sequence_id)
            (x#ProofT.lc_formula_trace_id)
            (numₘ(index)) := by
    simpa [Formula.substituteFree, Term.substituteFree, set_variable,
      show ProofT.lc_last_index_id ≠
        ProofT.lc_line_index_id by native_decide,
      hStepSubstitution] using
      hAtRaw
  exact FirstOrder.Derives.impElim hAt hIndexMember

/-! ## payload 数值到闭包变量代码 -/

/--
把 transcript 中第 `index` 个 eigen 数值等式，压缩为规范全称闭包唯一性所需的
单 token 变量代码等式。
-/
theorem fs_zfc_support_raw_logical_payload_variable_code_eq_standard
    {Γ : Context signature}
    (certificateSequence : SetTerm)
    (index eigen : Nat)
    (hCertificateSequence :
      Term.Admissible certificateSequence SetSort.set)
    (hPayloadAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (certificateSequence ·ₘ numₘ(index)) ≐ₘ numₘ(eigen)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      var_codeₘ(numₘ(2) *ₘ
          (certificateSequence ·ₘ numₘ(index))) ≐ₘ
        standard_token_sequence
          [Numbered.variable_token (free_name eigen)] := by
  have hCongruence :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        var_codeₘ(numₘ(2) *ₘ
            (certificateSequence ·ₘ numₘ(index))) ≐ₘ
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
      (certificateSequence ·ₘ numₘ(index))
      (numₘ(eigen))
      (function_application_term_admissible
        certificateSequence (numₘ(index))
        hCertificateSequence
        (finite_numeral_term_admissible index))
      (finite_numeral_term_admissible eigen)
      hPayloadAt
  have hArithmetic :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        var_codeₘ(numₘ(2) *ₘ numₘ(eigen)) ≐ₘ
          var_codeₘ(numₘ(2 * eigen)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        Metatheory.Derives.equality_symm
          (fs_zfc_support_raw_variable_code_term_numeral_mul eigen)
  have hStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        var_codeₘ(numₘ(2 * eigen)) ≐ₘ
          standard_token_sequence
            [Numbered.variable_token (free_name eigen)] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        apply FirstOrder.Derives.theory_weaken
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation hFormula)
        simpa [GodelQuotation.Numbered.named_variable_code,
          free_name] using
          named_variable_code_eq_standard_token_sequence
            (free_name eigen)
  exact Metatheory.Derives.equality_trans hCongruence <|
    Metatheory.Derives.equality_trans hArithmetic hStandard

/-! ## opening 护栏的局部函数性 -/

/-- 深度见证固定后，opening 护栏中的未平移 bound token 唯一。 -/
private theorem fs_zfc_support_raw_forall_open_bound_target_eq
    {Γ : Context signature}
    (depth : Nat)
    (targetValue witness : SetTerm)
    (hWitness :
      Term.Admissible witness SetSort.set)
    (hTargetEncoding :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ
          variable_symbol_number_term
            (canonical_binder_bound_name_term witness))
    (hWitnessEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        witness ≐ₘ numₘ(depth)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ
        numₘ(Numbered.variable_token
          (bound_name depth)) := by
  have hNameEquality :=
    canonical_binder_bound_name_term_congr_of_equality
      witness (numₘ(depth))
      hWitness
      (finite_numeral_term_admissible depth)
      hWitnessEquality
  have hTermEquality :=
    canonical_binder_variable_token_term_congr_of_equality
      (canonical_binder_bound_name_term witness)
      (canonical_binder_bound_name_term (numₘ(depth)))
      (successor_term_admissible _ <|
        natural_multiplication_term_admissible _ _
          (finite_numeral_term_admissible 2) hWitness)
      (successor_term_admissible _ <|
        natural_multiplication_term_admissible _ _
          (finite_numeral_term_admissible 2)
          (finite_numeral_term_admissible depth))
      hNameEquality
  have hValue :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(Numbered.variable_token
            (bound_name depth)) ≐ₘ
          variable_symbol_number_term
            (canonical_binder_bound_name_term
              (numₘ(depth))) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation
          (canonical_binder_bound_token_value depth)
  exact Metatheory.Derives.equality_trans hTargetEncoding <|
    Metatheory.Derives.equality_trans hTermEquality <|
      Metatheory.Derives.equality_symm hValue

/--
逆向护栏的 bound 见证支在已知 source token 时唯一决定 opening 目标。

见证只按已知 source 数值做有限消去；成功反演层在这里仅被调用。
-/
private theorem fs_zfc_support_raw_forall_open_bound_guard_unique
    {Γ : Context signature}
    {variableToken sourceToken targetToken : Nat}
    (relation :
      CanonicalForallOpenToken variableToken
        sourceToken targetToken)
    (sourceValue targetValue : SetTerm)
    (boundDepthId : FreeVarId)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hTargetFresh :
      (SetSort.set, boundDepthId) ∉
        Term.freeSupport targetValue)
    (hContextFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, boundDepthId) ∉
          Formula.freeSupport formula)
    (hCase :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, boundDepthId],
          (((x#boundDepthId ∈ₘ ωₘ) ∧ₘ
              (x#boundDepthId ∈ₘ Sₘ(sourceValue))) ∧ₘ
            ((sourceValue ≐ₘ
                variable_symbol_number_term
                  (canonical_binder_shifted_bound_name_term
                    (x#boundDepthId))) ∧ₘ
              (targetValue ≐ₘ
                variable_symbol_number_term
                  (canonical_binder_bound_name_term
                    (x#boundDepthId)))))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ numₘ(targetToken) := by
  let depth : SetTerm := x#boundDepthId
  let body : SetFormula :=
    (((depth ∈ₘ ωₘ) ∧ₘ
        (depth ∈ₘ Sₘ(sourceValue))) ∧ₘ
      ((sourceValue ≐ₘ
          variable_symbol_number_term
            (canonical_binder_shifted_bound_name_term depth)) ∧ₘ
        (targetValue ≐ₘ
          variable_symbol_number_term
            (canonical_binder_bound_name_term depth))))
  have hDepth :
      Term.Admissible depth SetSort.set :=
    set_variable_admissible boundDepthId
  have hDouble :
      Term.Admissible
        (canonical_binder_free_name_term depth)
        SetSort.set :=
    natural_multiplication_term_admissible _ _
      (finite_numeral_term_admissible 2) hDepth
  have hBody :
      Formula.Admissible body :=
    Formula.Admissible.conj
      (Formula.Admissible.conj
        (membership_formula_admissible
          hDepth omega_term_admissible)
        (membership_formula_admissible hDepth
          (successor_term_admissible
            sourceValue hSourceValue)))
      (Formula.Admissible.conj
        (Formula.Admissible.equal hSourceValue
          (variable_symbol_number_term_admissible _ <|
            successor_term_admissible _ <|
              successor_term_admissible _ <|
                successor_term_admissible _ hDouble))
        (Formula.Admissible.equal hTargetValue
          (variable_symbol_number_term_admissible _ <|
            successor_term_admissible _ hDouble)))
  have hConclusion :
      Formula.Admissible
        (targetValue ≐ₘ numₘ(targetToken)) :=
    Formula.Admissible.equal hTargetValue
      (finite_numeral_term_admissible targetToken)
  have hExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, boundDepthId], body := by
    simpa [body, depth,
      canonical_binder_bound_name_term,
      canonical_binder_shifted_bound_name_term] using hCase
  apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := boundDepthId)
    (body := body)
    (conclusion := targetValue ≐ₘ numₘ(targetToken))
    (hBodyCheck := Formula.check_admissible_complete hBody)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · exact hContextFresh
  · simpa [Formula.freeSupport,
      finite_numeral_term_freeSupport] using hTargetFresh
  · exact hExists
  · let Δ : Context signature := body :: Γ
    change Δ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ numₘ(targetToken)
    have hRaw :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hBoundData :=
      FirstOrder.Derives.conjElimLeft hRaw
    have hDepthBound :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          depth ∈ₘ Sₘ(sourceValue) := by
      simpa [body] using
        FirstOrder.Derives.conjElimRight hBoundData
    have hEncodingData :=
      FirstOrder.Derives.conjElimRight hRaw
    have hSourceEncoding :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          sourceValue ≐ₘ
            variable_symbol_number_term
              (canonical_binder_shifted_bound_name_term depth) := by
      simpa [body] using
        FirstOrder.Derives.conjElimLeft hEncodingData
    have hTargetEncoding :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          targetValue ≐ₘ
            variable_symbol_number_term
              (canonical_binder_bound_name_term depth) := by
      simpa [body] using
        FirstOrder.Derives.conjElimRight hEncodingData
    have hSourceEqualityAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          sourceValue ≐ₘ numₘ(sourceToken) :=
      FirstOrder.Derives.context_weaken_cons hSourceEquality
    have hSuccessorEquality :=
      successor_term_congr_of_equality
        sourceValue (numₘ(sourceToken))
        hSourceValue
        (finite_numeral_term_admissible sourceToken)
        hSourceEqualityAt
    have hFiniteBound :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          depth ∈ₘ numₘ(sourceToken + 1) := by
      simpa [finite_numeral_term] using
        FirstOrder.Derives.iffElimRight
          (membership_right_iff_of_equality
            depth (Sₘ(sourceValue))
            (Sₘ(numₘ(sourceToken)))
            hDepth
            (successor_term_admissible
              sourceValue hSourceValue)
            (successor_term_admissible _
              (finite_numeral_term_admissible sourceToken))
            hSuccessorEquality)
          hDepthBound
    apply fs_zfc_support_raw_finite_numeral_member_elim_context
      (sourceToken + 1) depth
      (targetValue ≐ₘ numₘ(targetToken))
      hDepth hConclusion hFiniteBound
    intro index hIndex
    let Ε : Context signature :=
      (depth ≐ₘ numₘ(index)) :: Δ
    change Ε ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ numₘ(targetToken)
    have hDepthEquality :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          depth ≐ₘ numₘ(index) :=
      FirstOrder.Derives.assumption (by simp [Ε])
    have hSourceEqualityBranch :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          sourceValue ≐ₘ numₘ(sourceToken) :=
      FirstOrder.Derives.context_weaken_cons
        hSourceEqualityAt
    have hSourceEncodingBranch :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          sourceValue ≐ₘ
            variable_symbol_number_term
              (canonical_binder_shifted_bound_name_term depth) :=
      FirstOrder.Derives.context_weaken_cons hSourceEncoding
    have hTargetEncodingBranch :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          targetValue ≐ₘ
            variable_symbol_number_term
              (canonical_binder_bound_name_term depth) :=
      FirstOrder.Derives.context_weaken_cons hTargetEncoding
    have hShifted :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          sourceValue ≐ₘ
            numₘ(Numbered.variable_token
              (bound_name (index + 1))) :=
      fs_zfc_support_raw_bound_target_token_eq
        index sourceValue depth hDepth
        hSourceEncodingBranch hDepthEquality
    have hWrong
        (hNe :
          sourceToken ≠
            Numbered.variable_token
              (bound_name (index + 1))) :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          targetValue ≐ₘ numₘ(targetToken) :=
      FirstOrder.Derives.falsumElim <|
        fs_zfc_support_raw_falsum_of_numeral_equality
          hNe <|
            Metatheory.Derives.equality_trans
              (Metatheory.Derives.equality_symm
                hSourceEqualityBranch)
              hShifted
    cases relation with
    | logical symbol =>
        exact hWrong <|
          logical_token_ne_variable_token symbol _
    | membership =>
        exact hWrong <|
          membership_token_ne_variable_token _
    | free id =>
        exact hWrong <|
          variable_token_ne_variable_token <|
            free_name_ne_bound_name id _
    | outer =>
        exact hWrong <|
          variable_token_ne_variable_token <| by
            intro h
            have hDepth :=
              bound_name_injective h
            omega
    | bound expectedDepth =>
        by_cases hEqual : index = expectedDepth
        · subst index
          exact fs_zfc_support_raw_forall_open_bound_target_eq
            expectedDepth targetValue depth hDepth
            hTargetEncodingBranch hDepthEquality
        · exact hWrong <|
            variable_token_ne_variable_token <| by
              intro h
              apply hEqual
              have hDepth :=
                bound_name_injective h
              omega
    | constant constantIndex =>
        exact hWrong <|
          constant_token_ne_variable_token constantIndex _
    | function arity functionIndex =>
        exact hWrong <|
          function_token_ne_variable_token
            arity functionIndex _
    | predicate arity predicateIndex =>
        exact hWrong <|
          predicate_token_ne_variable_token
            arity predicateIndex _

/--
opening 的对象层单 token 条件在已知 source 与变量零点时函数性成立。

普通 token 由逆向护栏的固定支直接恢复；bound token 的固定支与既有
binder-shift 函数性矛盾，见证支则交给上面的有限消去定理。
-/
private theorem fs_zfc_support_raw_forall_open_token_unique
    {Γ : Context signature}
    {variableToken sourceToken targetToken : Nat}
    (relation :
      CanonicalForallOpenToken variableToken
        sourceToken targetToken)
    (sourceValue variableCode targetValue : SetTerm)
    (freshBase : FreeVarId)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hVariableValue :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (variableCode ·ₘ numₘ(0)) ≐ₘ
          numₘ(variableToken))
    (hSourceFresh :
      ∀ id, freshBase ≤ id → id ≤ freshBase + 6 →
        (SetSort.set, id) ∉ Term.freeSupport sourceValue)
    (hTargetFresh :
      ∀ id, freshBase ≤ id → id ≤ freshBase + 6 →
        (SetSort.set, id) ∉ Term.freeSupport targetValue)
    (hContextFresh :
      ∀ formula, formula ∈ Γ → ∀ id,
        freshBase ≤ id → id ≤ freshBase + 6 →
        (SetSort.set, id) ∉ Formula.freeSupport formula)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_forall_open_token_condition_with_ids
          sourceValue variableCode targetValue
          freshBase (freshBase + 1) (freshBase + 2)
          (freshBase + 3) (freshBase + 4)
          (freshBase + 5) (freshBase + 6)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ numₘ(targetToken) := by
  let outerValue : SetTerm :=
    canonical_outer_binder_variable_code_term ·ₘ numₘ(0)
  let outerCase : SetFormula :=
    (sourceValue ≐ₘ outerValue) ∧ₘ
      (targetValue ≐ₘ variableCode ·ₘ numₘ(0))
  let nonOuterCase : SetFormula :=
    (¬ₘ (sourceValue ≐ₘ outerValue)) ∧ₘ
      (canonical_binder_shift_token_condition_with_ids
          targetValue sourceValue
          freshBase (freshBase + 1) (freshBase + 2)
          (freshBase + 3) (freshBase + 4)
          (freshBase + 5) (freshBase + 6) ∧ₘ
        canonical_forall_open_reverse_guard_with_id
          sourceValue targetValue (freshBase + 1))
  have hOuterValue :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        outerValue ≐ₘ
          numₘ(Numbered.variable_token (bound_name 0)) := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
    exact FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_quotation_occurrence hFormula) <| by
          simpa [outerValue, canonical_outer_binder_variable_code_term,
            Numbered.named_variable_code, bound_name] using
            named_variable_code_apply_zero 1
  have hCases :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        outerCase ∨ₘ nonOuterCase := by
    simpa [outerCase, nonOuterCase, outerValue,
      canonical_forall_open_token_condition_with_ids] using
        hCondition
  have hFixedFresh
      (id : FreeVarId)
      (hLower : freshBase ≤ id)
      (hUpper : id ≤ freshBase + 6) :
      (SetSort.set, id) ∉
        Formula.freeSupport (targetValue ≐ₘ sourceValue) := by
    intro hMember
    simp only [Formula.freeSupport] at hMember
    rcases List.mem_append.mp hMember with hTarget | hSource
    · exact hTargetFresh id hLower hUpper hTarget
    · exact hSourceFresh id hLower hUpper hSource
  have hNonOuterFresh
      (id : FreeVarId)
      (hLower : freshBase ≤ id)
      (hUpper : id ≤ freshBase + 6) :
      (SetSort.set, id) ∉
        Formula.freeSupport nonOuterCase := by
    have hSource := hSourceFresh id hLower hUpper
    have hTarget := hTargetFresh id hLower hUpper
    intro hMember
    simp only [nonOuterCase, Formula.freeSupport] at hMember
    rcases List.mem_append.mp hMember with hLeft | hRight
    · rcases List.mem_append.mp hLeft with
        hSourceMember | hOuterMember
      · exact hSource hSourceMember
      · have hOuterFree :
            Term.freeSupport outerValue = [] := by
          simp [outerValue,


            Term.freeSupport, Term.freeSupportList,
            finite_numeral_term_freeSupport]
        rw [hOuterFree] at hOuterMember
        exact List.not_mem_nil hOuterMember
    · rcases List.mem_append.mp hRight with
        hShiftMember | hGuardMember
      · rcases
          canonical_binder_shift_token_condition_with_ids_freeSupport_subset
            targetValue sourceValue
            freshBase (freshBase + 1) (freshBase + 2)
            (freshBase + 3) (freshBase + 4)
            (freshBase + 5) (freshBase + 6)
            (SetSort.set, id) hShiftMember with
          hTargetMember | hSourceMember
        · exact hTarget hTargetMember
        · exact hSource hSourceMember
      · rcases
          canonical_forall_open_reverse_guard_with_id_freeSupport_subset
            sourceValue targetValue (freshBase + 1)
            (SetSort.set, id) hGuardMember with
          hSourceMember | hTargetMember
        · exact hSource hSourceMember
        · exact hTarget hTargetMember
  apply FirstOrder.Derives.disjElim hCases
  · let Δ : Context signature := outerCase :: Γ
    change Δ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ numₘ(targetToken)
    have hRaw :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] outerCase :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hSourceOuter :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          sourceValue ≐ₘ outerValue := by
      simpa [outerCase] using
        FirstOrder.Derives.conjElimLeft hRaw
    have hTargetVariable :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          targetValue ≐ₘ variableCode ·ₘ numₘ(0) := by
      simpa [outerCase] using
        FirstOrder.Derives.conjElimRight hRaw
    have hSourceEqualityAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          sourceValue ≐ₘ numₘ(sourceToken) :=
      FirstOrder.Derives.context_weaken_cons hSourceEquality
    have hVariableValueAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          (variableCode ·ₘ numₘ(0)) ≐ₘ
            numₘ(variableToken) :=
      FirstOrder.Derives.context_weaken_cons hVariableValue
    have hOuterValueAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          outerValue ≐ₘ
            numₘ(Numbered.variable_token (bound_name 0)) :=
      FirstOrder.Derives.context_weaken_cons hOuterValue
    have hWrong
        (hNe :
          sourceToken ≠
            Numbered.variable_token (bound_name 0)) :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          targetValue ≐ₘ numₘ(targetToken) :=
      FirstOrder.Derives.falsumElim <|
        fs_zfc_support_raw_falsum_of_numeral_equality hNe <|
          Metatheory.Derives.equality_trans
            (Metatheory.Derives.equality_symm hSourceEqualityAt) <|
              Metatheory.Derives.equality_trans
                hSourceOuter hOuterValueAt
    cases relation with
    | logical symbol =>
        exact hWrong <|
          logical_token_ne_variable_token symbol _
    | membership =>
        exact hWrong <|
          membership_token_ne_variable_token _
    | free id =>
        exact hWrong <|
          variable_token_ne_variable_token <|
            free_name_ne_bound_name id _
    | outer =>
        exact Metatheory.Derives.equality_trans
          hTargetVariable hVariableValueAt
    | bound depth =>
        exact hWrong <|
          variable_token_ne_variable_token <| by
            intro h
            have hDepth := bound_name_injective h
            omega
    | constant index =>
        exact hWrong <|
          constant_token_ne_variable_token index _
    | function arity index =>
        exact hWrong <|
          function_token_ne_variable_token arity index _
    | predicate arity index =>
        exact hWrong <|
          predicate_token_ne_variable_token arity index _
  · let Δ : Context signature := nonOuterCase :: Γ
    change Δ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ numₘ(targetToken)
    have hRaw :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] nonOuterCase :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hNotOuter :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          ¬ₘ (sourceValue ≐ₘ outerValue) := by
      simpa [nonOuterCase] using
        FirstOrder.Derives.conjElimLeft hRaw
    have hShiftGuard :=
      FirstOrder.Derives.conjElimRight hRaw
    have hShift :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_binder_shift_token_condition_with_ids
            targetValue sourceValue
            freshBase (freshBase + 1) (freshBase + 2)
            (freshBase + 3) (freshBase + 4)
            (freshBase + 5) (freshBase + 6) := by
      simpa [nonOuterCase] using
        FirstOrder.Derives.conjElimLeft hShiftGuard
    have hGuard :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_forall_open_reverse_guard_with_id
            sourceValue targetValue (freshBase + 1) := by
      simpa [nonOuterCase] using
        FirstOrder.Derives.conjElimRight hShiftGuard
    rw [canonical_forall_open_reverse_guard_with_id] at hGuard
    apply FirstOrder.Derives.disjElim hGuard
    · let Ε : Context signature :=
        (targetValue ≐ₘ sourceValue) :: Δ
      change Ε ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ numₘ(targetToken)
      have hFixed :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            targetValue ≐ₘ sourceValue :=
        FirstOrder.Derives.assumption (by simp [Ε])
      have hSourceEqualityAt :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            sourceValue ≐ₘ numₘ(sourceToken) :=
        FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons hSourceEquality
      have hOuterValueAt :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            outerValue ≐ₘ
              numₘ(Numbered.variable_token (bound_name 0)) :=
        FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons hOuterValue
      have hNotOuterAt :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            ¬ₘ (sourceValue ≐ₘ outerValue) :=
        FirstOrder.Derives.context_weaken_cons hNotOuter
      have hFixedResult :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            targetValue ≐ₘ numₘ(sourceToken) :=
        Metatheory.Derives.equality_trans hFixed hSourceEqualityAt
      cases relation with
      | logical symbol =>
          exact hFixedResult
      | membership =>
          exact hFixedResult
      | free id =>
          exact hFixedResult
      | outer =>
          exact FirstOrder.Derives.falsumElim <|
            FirstOrder.Derives.negElim
              (Metatheory.Derives.equality_trans
                hSourceEqualityAt <|
                  Metatheory.Derives.equality_symm hOuterValueAt)
              hNotOuterAt
      | bound depth =>
          have hShiftAt :
              Ε ⊢ₘ[fs_zfc_support_raw_theory]
                canonical_binder_shift_token_condition_with_ids
                  targetValue sourceValue
                  freshBase (freshBase + 1) (freshBase + 2)
                  (freshBase + 3) (freshBase + 4)
                  (freshBase + 5) (freshBase + 6) :=
            FirstOrder.Derives.context_weaken_cons hShift
          have hShiftedAgain :=
            fs_zfc_support_raw_canonical_binder_shift_token_unique
              (CanonicalBinderShiftToken.bound (depth + 1))
              targetValue sourceValue freshBase
              hTargetValue hSourceValue
              hFixedResult
              (by
                intro id hLower hUpper
                exact hTargetFresh id hLower hUpper)
              (by
                intro id hLower hUpper
                exact hSourceFresh id hLower hUpper)
              (by
                intro formula hFormula id hLower hUpper
                simp only [Ε, Δ, List.mem_cons] at hFormula
                rcases hFormula with rfl | rfl | hFormula
                · exact hFixedFresh id hLower hUpper
                · exact hNonOuterFresh id hLower hUpper
                · exact hContextFresh formula hFormula
                    id hLower hUpper)
              hShiftAt
          exact FirstOrder.Derives.falsumElim <|
            fs_zfc_support_raw_falsum_of_numeral_equality
              (variable_token_ne_variable_token <| by
                intro h
                have hDepth := bound_name_injective h
                omega) <|
              Metatheory.Derives.equality_trans
                (Metatheory.Derives.equality_symm
                  hSourceEqualityAt)
                hShiftedAgain
      | constant index =>
          exact hFixedResult
      | function arity index =>
          exact hFixedResult
      | predicate arity index =>
          exact hFixedResult
    · let Ε : Context signature :=
        (∃ₘ[SetSort.set, freshBase + 1],
          (((x#(freshBase + 1) ∈ₘ ωₘ) ∧ₘ
              (x#(freshBase + 1) ∈ₘ Sₘ(sourceValue))) ∧ₘ
            ((sourceValue ≐ₘ
                variable_symbol_number_term
                  (canonical_binder_shifted_bound_name_term
                    (x#(freshBase + 1)))) ∧ₘ
              (targetValue ≐ₘ
                variable_symbol_number_term
                  (canonical_binder_bound_name_term
                    (x#(freshBase + 1))))))) :: Δ
      change Ε ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ numₘ(targetToken)
      have hBoundCase :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            ∃ₘ[SetSort.set, freshBase + 1],
              (((x#(freshBase + 1) ∈ₘ ωₘ) ∧ₘ
                  (x#(freshBase + 1) ∈ₘ Sₘ(sourceValue))) ∧ₘ
                ((sourceValue ≐ₘ
                    variable_symbol_number_term
                      (canonical_binder_shifted_bound_name_term
                        (x#(freshBase + 1)))) ∧ₘ
                  (targetValue ≐ₘ
                    variable_symbol_number_term
                      (canonical_binder_bound_name_term
                        (x#(freshBase + 1)))))) :=
        FirstOrder.Derives.assumption (by simp [Ε])
      exact fs_zfc_support_raw_forall_open_bound_guard_unique
        relation sourceValue targetValue (freshBase + 1)
        hSourceValue hTargetValue
        (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons hSourceEquality)
        (hTargetFresh (freshBase + 1)
          (Nat.le_succ freshBase)
          (Nat.add_le_add_left (by decide : 1 ≤ 6) freshBase))
        (by
          intro formula hFormula
          simp only [Ε, Δ, List.mem_cons] at hFormula
          rcases hFormula with rfl | rfl | hFormula
          · intro hMember
            have hClosed :=
              (Formula.mem_freeSupport_closeFreeAt_iff
                (σ := signature)
                (freeVariable := (SetSort.set, freshBase + 1))
                (target := SetSort.set)
                (id := freshBase + 1)
                (depth := 0)
                (formula := _)).1 hMember
            exact hClosed.2 rfl
          · exact hNonOuterFresh (freshBase + 1)
              (Nat.le_succ freshBase)
              (Nat.add_le_add_left (by decide : 1 ≤ 6) freshBase)
          · exact hContextFresh formula hFormula
              (freshBase + 1) (Nat.le_succ freshBase)
              (Nat.add_le_add_left (by decide : 1 ≤ 6) freshBase))
        hBoundCase

/-! ## opening 的有限代码函数性 -/

/-- 将 opening 代码条件的逐点全称式实例化到标准下标。 -/
private theorem fs_zfc_support_raw_forall_open_point_at
    {Γ : Context signature}
    (index : Nat)
    (sourceCode variableCode targetCode : SetTerm)
    (indexId : FreeVarId)
    (hSourceFresh :
      (SetSort.set, indexId) ∉ Term.freeSupport sourceCode)
    (hVariableFresh :
      (SetSort.set, indexId) ∉ Term.freeSupport variableCode)
    (hTargetFresh :
      (SetSort.set, indexId) ∉ Term.freeSupport targetCode)
    (hPointwise :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[SetSort.set, indexId],
          (x#indexId ∈ₘ domₘ(sourceCode)) ⟶ₘ
            canonical_forall_open_token_condition_with_ids
              (sourceCode ·ₘ x#indexId)
              variableCode
              (targetCode ·ₘ x#indexId)
              (indexId + 1) (indexId + 2)
              (indexId + 3) (indexId + 4)
              (indexId + 5) (indexId + 6)
              (indexId + 7)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (numₘ(index) ∈ₘ domₘ(sourceCode)) ⟶ₘ
        canonical_forall_open_token_condition_with_ids
          (sourceCode ·ₘ numₘ(index))
          variableCode
          (targetCode ·ₘ numₘ(index))
          (indexId + 1) (indexId + 2)
          (indexId + 3) (indexId + 4)
          (indexId + 5) (indexId + 6)
          (indexId + 7) := by
  have hSourceSubstitute :
      Term.substituteFree SetSort.set indexId
          (numₘ(index)) sourceCode =
        sourceCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set indexId (numₘ(index)) sourceCode
      hSourceFresh
  have hVariableSubstitute :
      Term.substituteFree SetSort.set indexId
          (numₘ(index)) variableCode =
        variableCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set indexId (numₘ(index)) variableCode
      hVariableFresh
  have hTargetSubstitute :
      Term.substituteFree SetSort.set indexId
          (numₘ(index)) targetCode =
        targetCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set indexId (numₘ(index)) targetCode
      hTargetFresh
  have hCloseCommute
      (closedId : FreeVarId)
      (depth : Nat)
      (formula : SetFormula)
      (hDistinct : indexId ≠ closedId) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) := by
    exact (Formula.closeFreeAt_substituteFree_comm
      SetSort.set indexId closedId depth
      (numₘ(index)) formula hDistinct
      (finite_numeral_term_admissible index).2
      (by simp [finite_numeral_term_freeSupport])).symm
  have hClose₁ (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            (indexId + 1) depth formula) =
        Formula.closeFreeAt SetSort.set (indexId + 1) depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) :=
    hCloseCommute (indexId + 1) depth formula (by simp)
  have hClose₂ (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            (indexId + 2) depth formula) =
        Formula.closeFreeAt SetSort.set (indexId + 2) depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) :=
    hCloseCommute (indexId + 2) depth formula (by simp)
  have hClose₃ (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            (indexId + 3) depth formula) =
        Formula.closeFreeAt SetSort.set (indexId + 3) depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) :=
    hCloseCommute (indexId + 3) depth formula (by simp)
  have hClose₄ (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            (indexId + 4) depth formula) =
        Formula.closeFreeAt SetSort.set (indexId + 4) depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) :=
    hCloseCommute (indexId + 4) depth formula (by simp)
  have hClose₅ (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            (indexId + 5) depth formula) =
        Formula.closeFreeAt SetSort.set (indexId + 5) depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) :=
    hCloseCommute (indexId + 5) depth formula (by simp)
  have hClose₆ (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            (indexId + 6) depth formula) =
        Formula.closeFreeAt SetSort.set (indexId + 6) depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) :=
    hCloseCommute (indexId + 6) depth formula (by simp)
  have hClose₇ (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set
            (indexId + 7) depth formula) =
        Formula.closeFreeAt SetSort.set (indexId + 7) depth
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) formula) :=
    hCloseCommute (indexId + 7) depth formula (by simp)
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := numₘ(index)) hPointwise
  simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
    canonical_forall_open_token_condition_with_ids,
    canonical_forall_open_reverse_guard_with_id,
    canonical_binder_shift_token_condition_with_ids,
    canonical_binder_shift_fixed_token_condition_substituteFree,
    Formula.substituteFree, Formula.next_depth,
    Term.substituteFree, set_variable,
    hSourceSubstitute, hVariableSubstitute,
    hTargetSubstitute,
    hClose₁, hClose₂, hClose₃, hClose₄,
    hClose₅, hClose₆, hClose₇,
    GodelQuotation.gq_binder_shift_numeral_substitute] using
      hAtRaw

/-- 标准 source token 串和 opening 图唯一决定目标代码。 -/
private theorem fs_zfc_support_raw_forall_open_code_unique
    {Γ : Context signature}
    {variableToken : Nat}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalForallOpenTokens variableToken
        sourceTokens targetTokens)
    (sourceCode variableCode targetCode : SetTerm)
    (indexId : FreeVarId)
    (hSourceCode :
      Term.CheckCertificate sourceCode SetSort.set)
    (hTargetCode :
      Term.CheckCertificate targetCode SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceCode ≐ₘ standard_token_sequence sourceTokens)
    (hVariableValue :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (variableCode ·ₘ numₘ(0)) ≐ₘ
          numₘ(variableToken))
    (hSourceFresh :
      ∀ id, indexId ≤ id → id ≤ indexId + 7 →
        (SetSort.set, id) ∉ Term.freeSupport sourceCode)
    (hVariableFresh :
      ∀ id, indexId ≤ id → id ≤ indexId + 7 →
        (SetSort.set, id) ∉ Term.freeSupport variableCode)
    (hTargetFresh :
      ∀ id, indexId ≤ id → id ≤ indexId + 7 →
        (SetSort.set, id) ∉ Term.freeSupport targetCode)
    (hContextFresh :
      ∀ formula, formula ∈ Γ → ∀ id,
        indexId ≤ id → id ≤ indexId + 7 →
        (SetSort.set, id) ∉ Formula.freeSupport formula)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_forall_open_code_condition_with_ids
          sourceCode variableCode targetCode
          indexId (indexId + 1) (indexId + 2)
          (indexId + 3) (indexId + 4)
          (indexId + 5) (indexId + 6)
          (indexId + 7)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      targetCode ≐ₘ standard_token_sequence targetTokens := by
  rw [canonical_forall_open_code_condition_with_ids] at hCondition
  have hData := FirstOrder.Derives.conjElimLeft hCondition
  have hPointwise := FirstOrder.Derives.conjElimRight hCondition
  have hFormulaData := FirstOrder.Derives.conjElimLeft hData
  have hTargetFormula :=
    FirstOrder.Derives.conjElimRight hFormulaData
  have hDomainEquality :=
    FirstOrder.Derives.conjElimRight hData
  have hTargetMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        targetCode ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          FirstOrder.Derives.theory_weaken
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_godel_quotation hFormula)
            (GodelQuotation.gq_formula_code_definition_instance
              targetCode hTargetCode.admissible))
      hTargetFormula
  have hTargetFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition targetCode := by
    have hCodeString :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          targetCode ∈ₘ CodeStrₘ :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            fs_zfc_support_raw_derives_of_godel_quotation
              (GodelQuotation.gq_formula_code_member_implies_code_string
                targetCode hTargetCode.admissible))
        hTargetMember
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_standard_sequence
            (GodelQuotation.code_string_member_implies_finite_sequence_at
              targetCode hTargetCode.admissible))
      hCodeString
  have hTargetFunction :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        is_function_formula targetCode := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimLeft hTargetFinite
  have hSourceDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sourceCode) ≐ₘ numₘ(sourceTokens.length) :=
    GodelQuotation.gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      sourceCode sourceTokens hSourceEquality hSourceCode
  have hTargetDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(targetCode) ≐ₘ numₘ(targetTokens.length) := by
    have hTargetSource :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(targetCode) ≐ₘ domₘ(sourceCode) :=
      Metatheory.Derives.equality_symm hDomainEquality
    simpa [relation.length_eq] using
      Metatheory.Derives.equality_trans
        hTargetSource hSourceDomain
  apply
    GodelQuotation.gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_standard_sequence_semantics
          hFormula)
      (fun _ hFormula =>
        fs_zfc_support_raw_theory_sentence hFormula)
      targetCode targetTokens
      hTargetFunction hTargetDomain
      (hSource := hTargetCode)
  intro index targetToken hTargetGet
  rcases relation.getElem?_source_relation hTargetGet with
    ⟨sourceToken, hSourceGet, tokenRelation⟩
  have hReferencePointGq :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        ((numₘ(index) ∈ₘ
            domₘ(standard_token_sequence sourceTokens)) ∧ₘ
          ((standard_token_sequence sourceTokens ·ₘ
              numₘ(index)) ≐ₘ numₘ(sourceToken))) :=
    GodelQuotation.gq_standard_token_sequence_point_inversion
      (standard_token_sequence sourceTokens)
      sourceTokens
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set)
        (standard_token_sequence sourceTokens))
      hSourceGet
  have hReferencePoint :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ((numₘ(index) ∈ₘ
            domₘ(standard_token_sequence sourceTokens)) ∧ₘ
          ((standard_token_sequence sourceTokens ·ₘ
              numₘ(index)) ≐ₘ numₘ(sourceToken))) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation hFormula)
          hReferencePointGq
  have hSourcePoint :=
    GodelQuotation.gq_point_inversion_of_equality_of_theory
      sourceCode (standard_token_sequence sourceTokens)
      (numₘ(index)) (numₘ(sourceToken))
      hSourceEquality hReferencePoint
      (hLeft := hSourceCode)
  have hAt :=
    fs_zfc_support_raw_forall_open_point_at
      index sourceCode variableCode targetCode indexId
      (hSourceFresh indexId (Nat.le_refl indexId)
        (Nat.le_add_right indexId 7))
      (hVariableFresh indexId (Nat.le_refl indexId)
        (Nat.le_add_right indexId 7))
      (hTargetFresh indexId (Nat.le_refl indexId)
        (Nat.le_add_right indexId 7))
      hPointwise
  have hTokenCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_forall_open_token_condition_with_ids
          (sourceCode ·ₘ numₘ(index))
          variableCode
          (targetCode ·ₘ numₘ(index))
          (indexId + 1) (indexId + 2)
          (indexId + 3) (indexId + 4)
          (indexId + 5) (indexId + 6)
          (indexId + 7) :=
    FirstOrder.Derives.impElim hAt
      (FirstOrder.Derives.conjElimLeft hSourcePoint)
  have hSourceAt :
      Term.Admissible
        (sourceCode ·ₘ numₘ(index)) SetSort.set :=
    function_application_term_admissible
      sourceCode (numₘ(index))
      hSourceCode.admissible
      (finite_numeral_term_admissible index)
  have hTargetAt :
      Term.Admissible
        (targetCode ·ₘ numₘ(index)) SetSort.set :=
    function_application_term_admissible
      targetCode (numₘ(index))
      hTargetCode.admissible
      (finite_numeral_term_admissible index)
  have hSourceAtFresh :
      ∀ id, indexId + 1 ≤ id → id ≤ indexId + 7 →
        (SetSort.set, id) ∉
          Term.freeSupport (sourceCode ·ₘ numₘ(index)) := by
    intro id hLower hUpper
    simpa [Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport] using
      hSourceFresh id
        (Nat.le_trans (Nat.le_add_right indexId 1) hLower)
        hUpper
  have hTargetAtFresh :
      ∀ id, indexId + 1 ≤ id → id ≤ indexId + 7 →
        (SetSort.set, id) ∉
          Term.freeSupport (targetCode ·ₘ numₘ(index)) := by
    intro id hLower hUpper
    simpa [Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport] using
      hTargetFresh id
        (Nat.le_trans (Nat.le_add_right indexId 1) hLower)
        hUpper
  exact fs_zfc_support_raw_forall_open_token_unique
    tokenRelation
    (sourceCode ·ₘ numₘ(index))
    variableCode
    (targetCode ·ₘ numₘ(index))
    (indexId + 1)
    hSourceAt hTargetAt
    (FirstOrder.Derives.conjElimRight hSourcePoint)
    hVariableValue
    hSourceAtFresh hTargetAtFresh
    (by
      intro formula hFormula id hLower hUpper
      exact hContextFresh formula hFormula id
        (Nat.le_trans
          (Nat.le_add_right indexId 1) hLower)
        hUpper)
    hTokenCondition

/-! ## 全称候选的 opening 推进 -/

/--
把第 `index` 个规范全称候选沿已验证的二元 opening 关系推进到
第 `index + 1` 个候选。量词体见证在证明内部消去。
-/
theorem fs_zfc_support_raw_logical_open_tokens_step
    {Γ : Context signature}
    (certificateSequence formulaTrace : SetTerm)
    (index eigen : Nat)
    (bodyTokens targetTokens : List Nat)
    (hTokenOpen :
      CanonicalForallOpenTokens
        (Numbered.variable_token (free_name eigen))
        bodyTokens targetTokens)
    (hCertificateSequence :
      Term.Admissible certificateSequence SetSort.set)
    (hFormulaTrace :
      Term.Admissible formulaTrace SetSort.set)
    (hReservedFresh :
      ReservedIdsFresh
        [310, 311, 460, 461, 462, 463, 464, 465,
          466, 467, 468, 469, 470]
        [certificateSequence, formulaTrace])
    (hContextFresh :
      ∀ formula, formula ∈ Γ → ∀ id,
        id ∈ [460, 461, 462, 463, 464, 465,
          466, 467, 468] →
        (SetSort.set, id) ∉ Formula.freeSupport formula)
    (hStep :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_closure_certificate_step_condition
          certificateSequence formulaTrace (numₘ(index)))
    (hPayloadAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (certificateSequence ·ₘ numₘ(index)) ≐ₘ numₘ(eigen))
    (hCurrent :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (formulaTrace ·ₘ numₘ(index)) ≐ₘ
          standard_token_sequence
            (Numbered.universal_tokens 1 bodyTokens)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (formulaTrace ·ₘ numₘ(index + 1)) ≐ₘ
        standard_token_sequence targetTokens := by
  let sourceCode : SetTerm :=
    formulaTrace ·ₘ numₘ(index)
  let variableCode : SetTerm :=
    var_codeₘ(numₘ(2) *ₘ
      (certificateSequence ·ₘ numₘ(index)))
  let targetCode : SetTerm :=
    formulaTrace ·ₘ Sₘ(numₘ(index))
  let bodyCode : SetTerm := x#460
  let openingBody : SetFormula :=
    ((formula_codeₘ(bodyCode) ∧ₘ
        (sourceCode ≐ₘ
          forall_codeₘ(
            canonical_outer_binder_variable_code_term,
            bodyCode))) ∧ₘ
      canonical_forall_open_code_condition_with_ids
        bodyCode variableCode targetCode
        461 462 463 464 465 466 467 468)
  have hSourceCode :
      Term.Admissible sourceCode SetSort.set := by
    exact function_application_term_admissible
      formulaTrace (numₘ(index)) hFormulaTrace
        (finite_numeral_term_admissible index)
  have hVariableCode :
      Term.Admissible variableCode SetSort.set := by
    exact variable_code_term_admissible _ <|
      natural_multiplication_term_admissible
        (numₘ(2))
        (certificateSequence ·ₘ numₘ(index))
        (finite_numeral_term_admissible 2) <|
          function_application_term_admissible
            certificateSequence (numₘ(index))
            hCertificateSequence
            (finite_numeral_term_admissible index)
  have hTargetCode :
      Term.Admissible targetCode SetSort.set := by
    exact function_application_term_admissible
      formulaTrace (Sₘ(numₘ(index))) hFormulaTrace <|
        successor_term_admissible (numₘ(index))
          (finite_numeral_term_admissible index)
  have hBodyCode :
      Term.Admissible bodyCode SetSort.set := by
    exact set_variable_admissible 460
  have hOpeningBody :
      Formula.Admissible openingBody := by
    dsimp only [openingBody]
    exact Formula.Admissible.conj
      (Formula.Admissible.conj
        (is_formula_code_formula_admissible hBodyCode)
        (Formula.Admissible.equal hSourceCode <|
          universal_formula_code_term_admissible
            canonical_outer_binder_variable_code_term bodyCode
            (variable_code_term_admissible _ <|
              finite_numeral_term_admissible 1)
            hBodyCode))
      (canonical_forall_open_code_condition_with_ids_admissible
        bodyCode variableCode targetCode
        461 462 463 464 465 466 467 468
        hBodyCode hVariableCode hTargetCode)
  have hConclusion :
      Formula.Admissible
        (targetCode ≐ₘ standard_token_sequence targetTokens) :=
    Formula.Admissible.equal hTargetCode
      (standard_token_sequence_admissible targetTokens)
  have hOpen :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_forall_open_code_condition
          sourceCode variableCode targetCode := by
    simpa [logical_closure_certificate_step_condition,
      sourceCode, variableCode, targetCode] using
        FirstOrder.Derives.conjElimRight hStep
  have hExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, 460], openingBody := by
    simpa [canonical_forall_open_code_condition,
      openingBody, bodyCode] using hOpen
  have hTermFresh
      (term : SetTerm)
      (hTerm : term ∈ [certificateSequence, formulaTrace])
      (id : FreeVarId)
      (hId :
        id ∈ [310, 311, 460, 461, 462, 463, 464, 465,
          466, 467, 468, 469, 470]) :
      (SetSort.set, id) ∉ Term.freeSupport term :=
    hReservedFresh term hTerm id hId
  have hTraceAtFresh
      (id : FreeVarId)
      (hId :
        id ∈ [310, 311, 460, 461, 462, 463, 464, 465,
          466, 467, 468, 469, 470])
      (argument : SetTerm)
      (hArgument : Term.freeSupport argument = []) :
      (SetSort.set, id) ∉
        Term.freeSupport (formulaTrace ·ₘ argument) := by
    simpa [Term.freeSupport, Term.freeSupportList,
      hArgument] using
        hTermFresh formulaTrace (by simp) id hId
  have hTargetFresh
      (id : FreeVarId)
      (hId :
        id ∈ [310, 311, 460, 461, 462, 463, 464, 465,
          466, 467, 468, 469, 470]) :
      (SetSort.set, id) ∉ Term.freeSupport targetCode := by
    exact hTraceAtFresh id hId (Sₘ(numₘ(index))) <| by
      simp [Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hVariableFresh
      (id : FreeVarId)
      (hId :
        id ∈ [310, 311, 460, 461, 462, 463, 464, 465,
          466, 467, 468, 469, 470]) :
      (SetSort.set, id) ∉ Term.freeSupport variableCode := by
    simpa [variableCode, Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport] using
        hTermFresh certificateSequence (by simp) id hId
  apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 460)
    (body := openingBody)
    (conclusion :=
      targetCode ≐ₘ standard_token_sequence targetTokens)
    (hBodyCheck := Formula.check_admissible_complete hOpeningBody)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    exact hContextFresh formula hFormula 460 (by simp)
  · simpa [Formula.freeSupport,
      standard_token_sequence_freeSupport_nil] using
        hTargetFresh 460 (by simp)
  · exact hExists
  · let Δ : Context signature := openingBody :: Γ
    have hRaw :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] openingBody :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hData := FirstOrder.Derives.conjElimLeft hRaw
    have hBodyFormula := FirstOrder.Derives.conjElimLeft hData
    have hParentEquality := FirstOrder.Derives.conjElimRight hData
    have hCondition := FirstOrder.Derives.conjElimRight hRaw
    have hBodyMember :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          bodyCode ∈ₘ FormulaCodeₘ :=
      FirstOrder.Derives.iffElimRight
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp) <|
            FirstOrder.Derives.theory_weaken
              (fun _ hFormula =>
                fs_zfc_support_raw_contains_godel_quotation hFormula)
              (GodelQuotation.gq_formula_code_definition_instance
                bodyCode hBodyCode))
        hBodyFormula
    have hCurrentAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          sourceCode ≐ₘ
            standard_token_sequence
              (Numbered.universal_tokens 1 bodyTokens) := by
      simpa [sourceCode] using
        FirstOrder.Derives.context_weaken_cons hCurrent
    have hUniversalEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          standard_token_sequence
              (Numbered.universal_tokens 1 bodyTokens) ≐ₘ
            forall_codeₘ(
              Numbered.named_variable_code 1, bodyCode) := by
      simpa [canonical_outer_binder_variable_code_term] using
        Metatheory.Derives.equality_trans
          (Metatheory.Derives.equality_symm hCurrentAt)
          hParentEquality
    have hBodyStandard :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          bodyCode ≐ₘ standard_token_sequence bodyTokens :=
      fs_zfc_support_raw_universal_body_eq_standard
        1 bodyCode bodyTokens
        (Term.check_certificate_of_admissible hBodyCode)
        hBodyMember hUniversalEquality
    have hVariableStandard :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          variableCode ≐ₘ
            standard_token_sequence
              [Numbered.variable_token (free_name eigen)] := by
      simpa [variableCode] using
        FirstOrder.Derives.context_weaken_cons <|
          fs_zfc_support_raw_logical_payload_variable_code_eq_standard
            certificateSequence index eigen
            hCertificateSequence hPayloadAt
    have hVariableApplication :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          (variableCode ·ₘ numₘ(0)) ≐ₘ
            (standard_token_sequence
                [Numbered.variable_token (free_name eigen)] ·ₘ
              numₘ(0)) :=
      function_application_term_congr_function_of_equality
        variableCode
        (standard_token_sequence
          [Numbered.variable_token (free_name eigen)])
        (numₘ(0))
        hVariableCode
        (standard_token_sequence_admissible _)
        (finite_numeral_term_admissible 0)
        hVariableStandard
    have hVariableReference :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          (standard_token_sequence
              [Numbered.variable_token (free_name eigen)] ·ₘ
            numₘ(0)) ≐ₘ
              numₘ(Numbered.variable_token (free_name eigen)) := by
      apply FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp)
      exact fs_zfc_support_raw_derives_of_godel_quotation <| by
        simpa using
          GodelQuotation.gq_weaken_standard_sequence <|
            GodelQuotation.standard_token_sequence_apply_getElem?
              [Numbered.variable_token (free_name eigen)]
              (by simp)
    have hVariableValue :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          (variableCode ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.variable_token (free_name eigen)) :=
      Metatheory.Derives.equality_trans
        hVariableApplication hVariableReference
    have hRange
        (id : Nat)
        (hLower : 461 ≤ id)
        (hUpper : id ≤ 468) :
        id ∈ [310, 311, 460, 461, 462, 463, 464, 465,
          466, 467, 468, 469, 470] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hShortRange
        (id : Nat)
        (hLower : 461 ≤ id)
        (hUpper : id ≤ 468) :
        id ∈ [460, 461, 462, 463, 464, 465,
          466, 467, 468] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hOpeningBodyFresh
        (id : Nat)
        (hLower : 461 ≤ id)
        (hUpper : id ≤ 468) :
        (SetSort.set, id) ∉ Formula.freeSupport openingBody := by
      intro hMember
      have hNe : id ≠ 460 := by omega
      simp only [openingBody, Formula.freeSupport] at hMember
      rcases List.mem_append.mp hMember with hData | hInner
      · rcases List.mem_append.mp hData with hFormulaCode | hParent
        · simp only [Term.freeSupportList] at hFormulaCode
          rcases List.mem_append.mp hFormulaCode with hBody | hEmpty
          · have hEq : id = 460 := by
              have hSingle :
                  (SetSort.set, id) ∈ [(SetSort.set, 460)] := by
                simpa only [bodyCode, Term.freeSupport] using hBody
              exact congrArg Prod.snd (List.mem_singleton.mp hSingle)
            exact hNe hEq
          · exact List.not_mem_nil hEmpty
        · rcases List.mem_append.mp hParent with hSource | hUniversal
          · exact
              (hTraceAtFresh id (hRange id hLower hUpper)
                (numₘ(index))
                (finite_numeral_term_freeSupport index)) hSource
          · have hFalse : False := by
              have hEq : id = 460 := by
                have hSingle :
                    (SetSort.set, id) ∈ [(SetSort.set, 460)] := by
                  simpa only [canonical_outer_binder_variable_code_term,
                    bodyCode, Term.freeSupport, Term.freeSupportList,
                    finite_numeral_term_freeSupport] using hUniversal
                exact congrArg Prod.snd (List.mem_singleton.mp hSingle)
              exact hNe hEq
            exact hFalse
      · rcases
            canonical_forall_open_code_condition_with_ids_freeSupport_subset
              bodyCode variableCode targetCode
              461 462 463 464 465 466 467 468
              (SetSort.set, id) hInner with
          hBody | hVariable | hTarget
        · have hEq : id = 460 := by
            simpa [bodyCode, Term.freeSupport] using hBody
          exact hNe hEq
        · exact
            (hVariableFresh id (hRange id hLower hUpper)) hVariable
        · exact
            (hTargetFresh id (hRange id hLower hUpper)) hTarget
    exact
      fs_zfc_support_raw_forall_open_code_unique
        hTokenOpen
        bodyCode variableCode targetCode 461
        (Term.check_certificate_of_admissible hBodyCode)
        (Term.check_certificate_of_admissible hTargetCode)
        hBodyStandard hVariableValue
        (by
          intro id hLower hUpper
          intro hMember
          have hEquality : id = 460 := by
            have hSingle :
                (SetSort.set, id) ∈ [(SetSort.set, 460)] := by
              simpa only [bodyCode, Term.freeSupport] using hMember
            exact congrArg Prod.snd (List.mem_singleton.mp hSingle)
          subst id
          exact Nat.not_succ_le_self 460 hLower)
        (by
          intro id hLower hUpper
          exact hVariableFresh id (hRange id hLower hUpper))
        (by
          intro id hLower hUpper
          exact hTargetFresh id (hRange id hLower hUpper))
        (by
          intro formula hFormula id hLower hUpper
          rcases List.mem_cons.mp hFormula with rfl | hFormula
          · exact hOpeningBodyFresh id hLower hUpper
          · exact hContextFresh formula hFormula id
              (hShortRange id hLower hUpper))
        hCondition

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
