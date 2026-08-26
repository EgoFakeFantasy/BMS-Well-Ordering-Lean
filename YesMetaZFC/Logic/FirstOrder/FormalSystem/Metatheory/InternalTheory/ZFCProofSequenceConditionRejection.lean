import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CertifiedSequenceCodeSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceConditionRejection

/-!
# 二维证明序列条件的对象层否定回放

本模块反演 `proof_sequence_code_condition_with_ids` 的外层行码递归。
末步消去只枚举对象条件已经给出的有限 trace 与行码范围；匹配分支再把
内层自然数序列条件交给 `ZFCSequenceConditionRejection`，不构造额外的
内部理论或语义解释。
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

set_option autoImplicit false

/-! ## 外层末步的有限消去 -/

/-- 打开 proof-sequence 单步中的行码存在见证后得到的公式体。 -/
private def proof_sequence_rejection_step_body
    (sequence trace code : SetTerm)
    (index : Nat)
    (rowCodeId rowTraceId rowIndexId : FreeVarId) :
    SetFormula :=
  (x#rowCodeId ∈ₘ code) ∧ₘ
    proof_sequence_code_step_condition_with_ids
      sequence trace (numₘ(index)) (x#rowCodeId)
      rowTraceId rowIndexId

private theorem proof_sequence_rejection_step_body_admissible
    (sequence trace code : SetTerm)
    (index : Nat)
    (rowCodeId rowTraceId rowIndexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hTrace : Term.Admissible trace SetSort.set)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (proof_sequence_rejection_step_body
        sequence trace code index
        rowCodeId rowTraceId rowIndexId) := by
  unfold proof_sequence_rejection_step_body
  exact Formula.Admissible.conj
    (membership_formula_admissible
      (set_variable_admissible rowCodeId) hCode)
    (proof_sequence_code_step_condition_with_ids_admissible
      sequence trace (numₘ(index)) (x#rowCodeId)
      rowTraceId rowIndexId
      hSequence hTrace
      (finite_numeral_term_admissible index)
      (set_variable_admissible rowCodeId))

/--
消去 proof-sequence 外层递归的最后一步。

调用方只需处理元层上确实满足
`targetCode = nat_sequence_code_step accumulator item` 的有限分支；
不匹配分支由有限 numeral 不等式在对象层自动关闭。
-/
theorem fs_zfc_support_raw_proof_sequence_step_code_elim
    {Γ : Context signature}
    (sequence trace code : SetTerm)
    (targetCode index bound : Nat)
    (rowCodeId rowTraceId rowIndexId : FreeVarId)
    (conclusion : SetFormula)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hTrace : Term.Admissible trace SetSort.set)
    (hCode : Term.Admissible code SetSort.set)
    (hRowCodeFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, rowCodeId) ∉ Formula.freeSupport formula)
    (hConclusion : Formula.Admissible conclusion)
    (hConclusionFresh :
      (SetSort.set, rowCodeId) ∉ Formula.freeSupport conclusion)
    (hCodeEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code ≐ₘ numₘ(bound))
    (hStep :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, rowCodeId],
          proof_sequence_rejection_step_body
            sequence trace code index
            rowCodeId rowTraceId rowIndexId)
    (hTraceBound :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (trace ·ₘ numₘ(index)) ∈ₘ numₘ(bound + 1))
    (hFinal :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(targetCode) ≐ₘ
          (trace ·ₘ numₘ(index + 1)))
    (hBranch :
      ∀ accumulator, accumulator < bound + 1 →
        ∀ item, item < bound →
          targetCode =
              nat_sequence_code_step accumulator item →
            ((x#rowCodeId) ≐ₘ numₘ(item)) ::
              ((trace ·ₘ numₘ(index)) ≐ₘ
                numₘ(accumulator)) ::
              proof_sequence_rejection_step_body
                sequence trace code index
                rowCodeId rowTraceId rowIndexId :: Γ
                ⊢ₘ[fs_zfc_support_raw_theory] conclusion) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] conclusion := by
  let body : SetFormula :=
    proof_sequence_rejection_step_body
      sequence trace code index
      rowCodeId rowTraceId rowIndexId
  have hBody :
      Formula.Admissible body := by
    simpa [body] using
      proof_sequence_rejection_step_body_admissible
        sequence trace code index
        rowCodeId rowTraceId rowIndexId
        hSequence hTrace hCode
  nd_apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := rowCodeId)
    (body := body)
    (conclusion := conclusion)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · exact hRowCodeFreshContext
  · exact hConclusionFresh
  · simpa [body] using hStep
  · let Δ : Context signature := body :: Γ
    have hBodyAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hRowCodeMember :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          (x#rowCodeId) ∈ₘ code := by
      simpa [body, proof_sequence_rejection_step_body] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hProofStep :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          proof_sequence_code_step_condition_with_ids
            sequence trace (numₘ(index)) (x#rowCodeId)
            rowTraceId rowIndexId := by
      simpa [body, proof_sequence_rejection_step_body] using
        FirstOrder.Derives.conjElimRight hBodyAt
    have hRowCodeNumeral :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          (x#rowCodeId) ∈ₘ numₘ(bound) := by
      exact FirstOrder.Derives.iffElimRight
        (membership_right_iff_of_equality
          (x#rowCodeId) code (numₘ(bound))
          (set_variable_admissible rowCodeId)
          hCode
          (finite_numeral_term_admissible bound)
          (FirstOrder.Derives.context_weaken_cons hCodeEquality))
        hRowCodeMember
    have hTraceBoundAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          (trace ·ₘ numₘ(index)) ∈ₘ
            numₘ(bound + 1) :=
      FirstOrder.Derives.context_weaken_cons hTraceBound
    apply
      fs_zfc_support_raw_finite_numeral_member_elim_context
        (bound + 1)
        (trace ·ₘ numₘ(index))
        conclusion
        (function_application_term_admissible
          trace (numₘ(index)) hTrace
          (finite_numeral_term_admissible index))
        hConclusion
        hTraceBoundAt
    intro accumulator hAccumulator
    let Ε : Context signature :=
      ((trace ·ₘ numₘ(index)) ≐ₘ numₘ(accumulator)) :: Δ
    have hRowCodeNumeralAt :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          (x#rowCodeId) ∈ₘ numₘ(bound) :=
      FirstOrder.Derives.context_weaken_cons hRowCodeNumeral
    apply
      fs_zfc_support_raw_finite_numeral_member_elim_context
        bound
        (x#rowCodeId)
        conclusion
        (set_variable_admissible rowCodeId)
        hConclusion
        hRowCodeNumeralAt
    intro item hItem
    let Ζ : Context signature :=
      ((x#rowCodeId) ≐ₘ numₘ(item)) :: Ε
    have hTraceEquality :
        Ζ ⊢ₘ[fs_zfc_support_raw_theory]
          (trace ·ₘ numₘ(index)) ≐ₘ
            numₘ(accumulator) :=
      FirstOrder.Derives.assumption
        (by simp [Ζ, Ε, Δ])
    have hRowCodeEquality :
        Ζ ⊢ₘ[fs_zfc_support_raw_theory]
          (x#rowCodeId) ≐ₘ numₘ(item) :=
      FirstOrder.Derives.assumption
        (by simp [Ζ])
    have hOuter :
        Ζ ⊢ₘ[fs_zfc_support_raw_theory]
          (trace ·ₘ Sₘ(numₘ(index))) ≐ₘ
            Sₘ(godel_pairₘ(
              ⟨trace ·ₘ numₘ(index),
                x#rowCodeId⟩ₘ)) := by
      simpa [proof_sequence_code_step_condition_with_ids] using
        FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.context_weaken_cons
            (FirstOrder.Derives.context_weaken_cons hProofStep))
    have hTracePoint :
        Term.Admissible
          (trace ·ₘ numₘ(index)) SetSort.set :=
      function_application_term_admissible
        trace (numₘ(index)) hTrace
        (finite_numeral_term_admissible index)
    have hPairEquality :
        Ζ ⊢ₘ[fs_zfc_support_raw_theory]
          godel_pairₘ(
            ⟨trace ·ₘ numₘ(index), x#rowCodeId⟩ₘ) ≐ₘ
          godel_pairₘ(
            ⟨numₘ(accumulator), numₘ(item)⟩ₘ) :=
      godel_pairing_term_congr_of_equalities
        (trace ·ₘ numₘ(index))
        (numₘ(accumulator))
        (x#rowCodeId)
        (numₘ(item))
        hTracePoint
        (finite_numeral_term_admissible accumulator)
        (set_variable_admissible rowCodeId)
        (finite_numeral_term_admissible item)
        hTraceEquality hRowCodeEquality
    have hSuccessorEquality :
        Ζ ⊢ₘ[fs_zfc_support_raw_theory]
          Sₘ(godel_pairₘ(
            ⟨trace ·ₘ numₘ(index), x#rowCodeId⟩ₘ)) ≐ₘ
          Sₘ(godel_pairₘ(
            ⟨numₘ(accumulator), numₘ(item)⟩ₘ)) :=
      successor_term_congr_of_equality
        (godel_pairₘ(
          ⟨trace ·ₘ numₘ(index), x#rowCodeId⟩ₘ))
        (godel_pairₘ(
          ⟨numₘ(accumulator), numₘ(item)⟩ₘ))
        (godel_pairing_term_admissible
          ⟨trace ·ₘ numₘ(index), x#rowCodeId⟩ₘ
          (ordered_pair_term_admissible
            (trace ·ₘ numₘ(index)) (x#rowCodeId)
            hTracePoint
            (set_variable_admissible rowCodeId)))
        (godel_pairing_term_admissible
          ⟨numₘ(accumulator), numₘ(item)⟩ₘ
          (ordered_pair_term_admissible
            (numₘ(accumulator)) (numₘ(item))
            (finite_numeral_term_admissible accumulator)
            (finite_numeral_term_admissible item)))
        hPairEquality
    have hStepGround :
        Ζ ⊢ₘ[fs_zfc_support_raw_theory]
          (trace ·ₘ numₘ(index + 1)) ≐ₘ
            Sₘ(godel_pairₘ(
              ⟨numₘ(accumulator), numₘ(item)⟩ₘ)) := by
      have hRaw :=
        Metatheory.Derives.equality_trans
          hOuter hSuccessorEquality
      simpa [finite_numeral_term, successor_term] using hRaw
    have hGround :
        Derives fs_zfc_support_raw_theory [] (
          Sₘ(godel_pairₘ(
            ⟨numₘ(accumulator), numₘ(item)⟩ₘ)) ≐ₘ
              numₘ(nat_sequence_code_step
                accumulator item)) :=
      fs_zfc_support_raw_nat_sequence_code_step_numeral_eq
        accumulator item
    have hFinalAt :
        Ζ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(targetCode) ≐ₘ
            (trace ·ₘ numₘ(index + 1)) :=
      FirstOrder.Derives.context_weaken_cons
        (FirstOrder.Derives.context_weaken_cons
          (FirstOrder.Derives.context_weaken_cons hFinal))
    have hTargetPair :
        Ζ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(targetCode) ≐ₘ
            Sₘ(godel_pairₘ(
              ⟨numₘ(accumulator), numₘ(item)⟩ₘ)) :=
      Metatheory.Derives.equality_trans
        hFinalAt hStepGround
    have hTargetGround :
        Ζ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(targetCode) ≐ₘ
            numₘ(nat_sequence_code_step
              accumulator item) :=
      Metatheory.Derives.equality_trans
        hTargetPair
        (FirstOrder.Derives.context_weaken
          (Γ := [])
          (Δ := Ζ)
          (by simp [Ζ, Ε, Δ])
          hGround)
    by_cases hMatch :
        targetCode =
          nat_sequence_code_step accumulator item
    · simpa [Ζ, Ε, Δ, body] using
        hBranch accumulator hAccumulator item hItem hMatch
    · exact FirstOrder.Derives.falsumElim
        (fs_zfc_support_raw_falsum_of_numeral_equality
          hMatch hTargetGround)

/-! ## 完整二维条件的结构投影 -/

/-- 二维编码条件中由最外层存在量词关闭的轨迹体。 -/
private def proof_sequence_rejection_trace_body
    (sequence code : SetTerm)
    (traceId indexId rowCodeId rowTraceId rowIndexId : FreeVarId) :
    SetFormula :=
  (x#traceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
    (((domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
        sequence_trace_code_bound_with_id
          (x#traceId) code indexId) ∧ₘ
      ((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
      ((∀ₘ[SetSort.set, indexId],
          (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
            (∃ₘ[SetSort.set, rowCodeId],
              ((x#rowCodeId ∈ₘ code) ∧ₘ
                proof_sequence_code_step_condition_with_ids
                  sequence (x#traceId) (x#indexId) (x#rowCodeId)
                  rowTraceId rowIndexId))) ∧ₘ
        (code ≐ₘ (x#traceId ·ₘ domₘ(sequence)))))

private theorem proof_sequence_rejection_trace_body_admissible
    (sequence code : SetTerm)
    (traceId indexId rowCodeId rowTraceId rowIndexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (proof_sequence_rejection_trace_body
        sequence code traceId indexId
        rowCodeId rowTraceId rowIndexId) := by
  unfold proof_sequence_rejection_trace_body
  prove_admissible

/--
将二维证明序列编码条件投影为外层空间、自然数码、定义域界与轨迹存在式。
-/
theorem fs_zfc_support_raw_proof_sequence_code_condition_parts
    {Γ : Context signature}
    (sequence code : SetTerm)
    (traceId indexId rowCodeId rowTraceId rowIndexId : FreeVarId)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        proof_sequence_code_condition_with_ids
          sequence code traceId indexId
          rowCodeId rowTraceId rowIndexId) :
    (Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence ∈ₘ seq_spaceₘ(FormulaCodeₘ)) ∧
      (Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code ∈ₘ ωₘ) ∧
      (Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence_domain_code_bound sequence code) ∧
      (Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, traceId],
          proof_sequence_rejection_trace_body
            sequence code traceId indexId
            rowCodeId rowTraceId rowIndexId) := by
  have hLeft :=
    FirstOrder.Derives.conjElimLeft hCondition
  have hTrace :=
    FirstOrder.Derives.conjElimRight hCondition
  have hSpaceCode :=
    FirstOrder.Derives.conjElimLeft hLeft
  have hDomain :=
    FirstOrder.Derives.conjElimRight hLeft
  have hSpace :=
    FirstOrder.Derives.conjElimLeft hSpaceCode
  have hCode :=
    FirstOrder.Derives.conjElimRight hSpaceCode
  exact ⟨hSpace, hCode, hDomain, by
    simpa [proof_sequence_rejection_trace_body] using hTrace⟩

/-! ## 外层全称递推的 numeral 实例 -/

/-- 将二维编码的外层全称递推实例化到一个有效 numeral。 -/
theorem fs_zfc_support_raw_proof_sequence_step_at
    {Γ : Context signature}
    (sequence trace code : SetTerm)
    (indexId rowCodeId rowTraceId rowIndexId : FreeVarId)
    (length index : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hIndexNeRowCode : indexId ≠ rowCodeId)
    (hIndexNeRowTrace : indexId ≠ rowTraceId)
    (hIndexNeRowIndex : indexId ≠ rowIndexId)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉ Term.freeSupport sequence)
    (hIndexFreshTrace :
      (SetSort.set, indexId) ∉ Term.freeSupport trace)
    (hIndexFreshCode :
      (SetSort.set, indexId) ∉ Term.freeSupport code)
    (hDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ numₘ(length))
    (hSteps :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[SetSort.set, indexId],
          (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
            (∃ₘ[SetSort.set, rowCodeId],
              ((x#rowCodeId ∈ₘ code) ∧ₘ
                proof_sequence_code_step_condition_with_ids
                  sequence trace (x#indexId) (x#rowCodeId)
                  rowTraceId rowIndexId)))
    (hIndex : index < length) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      ∃ₘ[SetSort.set, rowCodeId],
        proof_sequence_rejection_step_body
          sequence trace code index
          rowCodeId rowTraceId rowIndexId := by
  have hNumeral :
      Term.Admissible (numₘ(index)) SetSort.set :=
    finite_numeral_term_admissible index
  have hNumeralFresh (id : FreeVarId) :
      (SetSort.set, id) ∉
        Term.freeSupport (numₘ(index)) := by
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hSequenceSubstitution :
      Term.substituteFree SetSort.set indexId
          (numₘ(index)) sequence =
        sequence :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set indexId (numₘ(index))
      sequence hIndexFreshSequence
  have hTraceSubstitution :
      Term.substituteFree SetSort.set indexId
          (numₘ(index)) trace =
        trace :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set indexId (numₘ(index))
      trace hIndexFreshTrace
  have hCodeSubstitution :
      Term.substituteFree SetSort.set indexId
          (numₘ(index)) code =
        code :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set indexId (numₘ(index))
      code hIndexFreshCode
  have hIndexSubstitution :
      Term.substituteFree SetSort.set indexId
          (numₘ(index)) (x#indexId) =
        numₘ(index) := by
    simp [Term.substituteFree, set_variable]
  have hRowCodeSubstitution :
      Term.substituteFree SetSort.set indexId
          (numₘ(index)) (x#rowCodeId) =
        x#rowCodeId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hIndexNeRowCode]
  have hStepSubstitution :=
    proof_sequence_code_step_condition_with_ids_substitute_closed
      sequence trace (x#indexId) (x#rowCodeId)
      (numₘ(index))
      sequence trace (numₘ(index)) (x#rowCodeId)
      indexId rowTraceId rowIndexId
      hIndexNeRowTrace hIndexNeRowIndex
      hNumeral.2
      (hNumeralFresh rowTraceId)
      (hNumeralFresh rowIndexId)
      hSequenceSubstitution hTraceSubstitution
      hIndexSubstitution hRowCodeSubstitution
  have hRowCodeCommute (body : SetFormula) :
      Formula.substituteFree SetSort.set indexId
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set rowCodeId 0 body) =
        Formula.closeFreeAt SetSort.set rowCodeId 0
          (Formula.substituteFree SetSort.set indexId
            (numₘ(index)) body) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set indexId rowCodeId 0
      (numₘ(index)) body
      hIndexNeRowCode hNumeral.2
      (hNumeralFresh rowCodeId)).symm
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := numₘ(index)) hSteps
  rw [Formula.openAt_closeFreeAt_eq_substituteFree] at hAtRaw
  have hAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (numₘ(index) ∈ₘ domₘ(sequence)) ⟶ₘ
          (∃ₘ[SetSort.set, rowCodeId],
            proof_sequence_rejection_step_body
              sequence trace code index
              rowCodeId rowTraceId rowIndexId) := by
    simpa [proof_sequence_rejection_step_body,
      Formula.substituteFree, Term.substituteFree,
      set_variable, hSequenceSubstitution,
      hTraceSubstitution, hCodeSubstitution,
      hIndexSubstitution, hRowCodeSubstitution,
      hStepSubstitution, hRowCodeCommute] using hAtRaw
  exact FirstOrder.Derives.impElim hAt
    (fs_zfc_support_raw_numeral_mem_domain_of_domain_eq
      sequence length index hSequence hDomain hIndex)

/-! ## 二维编码递归的规范唯一性 -/

private theorem nat_sequence_code_condition_trace_fresh
    (sequence code : SetTerm)
    (traceId indexId : FreeVarId)
    (hTraceFreshSequence :
      (SetSort.set, traceId) ∉ Term.freeSupport sequence)
    (hTraceFreshCode :
      (SetSort.set, traceId) ∉ Term.freeSupport code) :
    (SetSort.set, traceId) ∉
      Formula.freeSupport
        (nat_sequence_code_condition_with_ids
          sequence code traceId indexId) := by
  have hSequenceSpace :
      (SetSort.set, traceId) ∉
        Formula.freeSupport
          (sequence ∈ₘ seq_spaceₘ(ωₘ)) := by
    simp [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, hTraceFreshSequence]
  have hNatural :
      (SetSort.set, traceId) ∉
        Formula.freeSupport (code ∈ₘ ωₘ) := by
    simp [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, hTraceFreshCode]
  have hDomain :
      (SetSort.set, traceId) ∉
        Formula.freeSupport
          (sequence_domain_code_bound sequence code) := by
    simp only [sequence_domain_code_bound,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.append_nil]
    exact List.not_mem_append
      hTraceFreshSequence hTraceFreshCode
  have hValue :
      (SetSort.set, traceId) ∉
        Formula.freeSupport
          (nat_sequence_value_code_bound_with_id
            sequence code indexId) := by
    unfold nat_sequence_value_code_bound_with_id
    simp only [Formula.freeSupport]
    by_cases hIds : traceId = indexId
    · subst indexId
      exact Formula.not_mem_freeSupport_closeFreeAt
        (σ := signature)
        SetSort.set traceId 0 _
    · apply
        Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      intro hMember
      simp only [Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList, List.append_nil] at hMember
      rcases List.mem_cons.mp hMember with hIndex | hMember
      · exact hIds (congrArg Prod.snd hIndex)
      · rcases List.mem_append.mp hMember with
          hSequenceLeft | hMember
        · exact hTraceFreshSequence hSequenceLeft
        · rcases List.mem_append.mp hMember with
            hSequenceRight | hMember
          · rcases List.mem_append.mp hSequenceRight with
              hSequence | hIndex'
            · exact hTraceFreshSequence hSequence
            · exact hIds
                (congrArg Prod.snd
                  (List.mem_singleton.mp hIndex'))
          · exact hTraceFreshCode hMember
  have hTraceExists :
      (SetSort.set, traceId) ∉
        Formula.freeSupport
          (∃ₘ[SetSort.set, traceId],
            (x#traceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
              (((domₘ(x#traceId) ≐ₘ
                    Sₘ(domₘ(sequence))) ∧ₘ
                  sequence_trace_code_bound_with_id
                    (x#traceId) code indexId) ∧ₘ
                ((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
                ((∀ₘ[SetSort.set, indexId],
                    (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
                      nat_sequence_code_step_condition
                        sequence (x#traceId) (x#indexId)) ∧ₘ
                  (code ≐ₘ
                    (x#traceId ·ₘ domₘ(sequence)))))) := by
    simpa only [Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        (σ := signature)
        SetSort.set traceId 0
        ((x#traceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
          (((domₘ(x#traceId) ≐ₘ
                Sₘ(domₘ(sequence))) ∧ₘ
              sequence_trace_code_bound_with_id
                (x#traceId) code indexId) ∧ₘ
            ((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
            ((∀ₘ[SetSort.set, indexId],
                (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
                  nat_sequence_code_step_condition
                    sequence (x#traceId) (x#indexId)) ∧ₘ
              (code ≐ₘ
                (x#traceId ·ₘ domₘ(sequence))))))
  unfold nat_sequence_code_condition_with_ids
  exact List.not_mem_append
    (List.not_mem_append
      (List.not_mem_append
        (List.not_mem_append
          hSequenceSpace hNatural)
        hDomain)
      hValue)
    hTraceExists

private theorem proof_sequence_rejection_step_body_row_trace_fresh
    (sequence trace code : SetTerm)
    (index : Nat)
    (rowCodeId rowTraceId rowIndexId : FreeVarId)
    (hRowCodeNeRowTrace : rowCodeId ≠ rowTraceId)
    (hRowTraceFreshSequence :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport sequence)
    (hRowTraceFreshTrace :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport trace)
    (hRowTraceFreshCode :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport code) :
    (SetSort.set, rowTraceId) ∉
      Formula.freeSupport
        (proof_sequence_rejection_step_body
          sequence trace code index
          rowCodeId rowTraceId rowIndexId) := by
  have hRowCodeFresh :
      (SetSort.set, rowTraceId) ∉
        Term.freeSupport (x#rowCodeId) := by
    intro hMember
    change (SetSort.set, rowTraceId) ∈
      [(SetSort.set, rowCodeId)] at hMember
    have hPair :
        (SetSort.set, rowTraceId) =
          (SetSort.set, rowCodeId) :=
      List.mem_singleton.mp hMember
    exact hRowCodeNeRowTrace
      (congrArg Prod.snd hPair).symm
  have hSequenceAtFresh :
      (SetSort.set, rowTraceId) ∉
        Term.freeSupport
          (sequence ·ₘ numₘ(index)) := by
    simpa [Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport] using
      hRowTraceFreshSequence
  have hInnerFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport
          (nat_sequence_code_condition_with_ids
            (sequence ·ₘ numₘ(index))
            (x#rowCodeId)
            rowTraceId rowIndexId) :=
    nat_sequence_code_condition_trace_fresh
      (sequence ·ₘ numₘ(index))
      (x#rowCodeId)
      rowTraceId rowIndexId
      hSequenceAtFresh hRowCodeFresh
  have hMembershipFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport
          ((x#rowCodeId) ∈ₘ code) := by
    simp only [Formula.freeSupport,
      Term.freeSupportList, List.append_nil]
    exact List.not_mem_append
      hRowCodeFresh hRowTraceFreshCode
  have hTraceNextFresh :
      (SetSort.set, rowTraceId) ∉
        Term.freeSupport
          (trace ·ₘ Sₘ(numₘ(index))) := by
    simpa [Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport] using
      hRowTraceFreshTrace
  have hPairNextFresh :
      (SetSort.set, rowTraceId) ∉
        Term.freeSupport
          (Sₘ(godel_pairₘ(
            ⟨trace ·ₘ numₘ(index),
              x#rowCodeId⟩ₘ))) := by
    simp only [Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport,
      List.append_nil]
    exact List.not_mem_append
      hRowTraceFreshTrace hRowCodeFresh
  have hOuterFresh :
      (SetSort.set, rowTraceId) ∉
        Formula.freeSupport
          ((trace ·ₘ Sₘ(numₘ(index))) ≐ₘ
            Sₘ(godel_pairₘ(
              ⟨trace ·ₘ numₘ(index),
                x#rowCodeId⟩ₘ))) := by
    simp only [Formula.freeSupport]
    exact List.not_mem_append
      hTraceNextFresh hPairNextFresh
  unfold proof_sequence_rejection_step_body
  unfold proof_sequence_code_step_condition_with_ids
  exact List.not_mem_append
    hMembershipFresh
    (List.not_mem_append hInnerFresh hOuterFresh)

/--
外层二维编码 trace 的前缀唯一性。

每次只反演最后一个对象层行码见证；终码的配对单射给出规范前缀码，
内层行条件则立即交给一维自然数序列唯一性。因此递归始终回到原上下文，
不会累积或重复捕获行码 eigenvariable。
-/
theorem fs_zfc_support_raw_proof_sequence_code_prefix_unique
    {Γ : Context signature}
    (sequence trace code : SetTerm)
    (rows : List (List Nat))
    (length bound : Nat)
    (rowCodeId rowTraceId rowIndexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hTrace : Term.Admissible trace SetSort.set)
    (hCode : Term.Admissible code SetSort.set)
    (hRowCodeNeRowTrace : rowCodeId ≠ rowTraceId)
    (hRowCodeNeRowIndex : rowCodeId ≠ rowIndexId)
    (hRowTraceNeRowIndex : rowTraceId ≠ rowIndexId)
    (hRowCodeFreshSequence :
      (SetSort.set, rowCodeId) ∉ Term.freeSupport sequence)
    (hRowCodeFreshTrace :
      (SetSort.set, rowCodeId) ∉ Term.freeSupport trace)
    (hRowCodeFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, rowCodeId) ∉ Formula.freeSupport formula)
    (hRowTraceFreshSequence :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport sequence)
    (hRowTraceFreshTrace :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport trace)
    (hRowTraceFreshCode :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport code)
    (hRowTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, rowTraceId) ∉ Formula.freeSupport formula)
    (hRowIndexFreshSequence :
      (SetSort.set, rowIndexId) ∉ Term.freeSupport sequence)
    (hZero :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (trace ·ₘ numₘ(0)) ≐ₘ numₘ(0))
    (hStep :
      ∀ index, index < length →
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          ∃ₘ[SetSort.set, rowCodeId],
            proof_sequence_rejection_step_body
              sequence trace code index
              rowCodeId rowTraceId rowIndexId)
    (hTraceBound :
      ∀ index, index ≤ length →
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          (trace ·ₘ numₘ(index)) ∈ₘ numₘ(bound + 1))
    (hCodeEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code ≐ₘ numₘ(bound))
    (hFinal :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(proof_sequence_code_value rows) ≐ₘ
          (trace ·ₘ numₘ(length))) :
    (Γ ⊢ₘ[fs_zfc_support_raw_theory]
      numₘ(length) ≐ₘ numₘ(rows.length)) ∧
      (∀ index (hIndex : index < rows.length),
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          (sequence ·ₘ numₘ(index)) ≐ₘ
            standard_token_sequence (rows[index]'hIndex)) := by
  induction rows using list_snoc_induction generalizing Γ length with
  | hNil =>
      by_cases hLength : length = 0
      · subst length
        constructor
        · exact FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set) (numₘ(0))
        · intro index hIndex
          simp at hIndex
      · obtain ⟨prefixLength, rfl⟩ :=
          Nat.exists_eq_succ_of_ne_zero hLength
        have hFalse :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              Formula.falsum := by
          apply
            fs_zfc_support_raw_proof_sequence_step_code_elim
              sequence trace code
              0 prefixLength bound
              rowCodeId rowTraceId rowIndexId
              Formula.falsum
              hSequence hTrace hCode
              hRowCodeFreshContext
              Formula.Admissible.falsum
              List.not_mem_nil
              hCodeEquality
              (hStep prefixLength (Nat.lt_succ_self _))
              (hTraceBound prefixLength (Nat.le_succ _))
          · simpa [proof_sequence_code_value,
              proof_sequence_code_from,
              nat_sequence_code_value] using hFinal
          · intro accumulator hAccumulator item hItem hMatch
            exfalso
            simp [nat_sequence_code_step] at hMatch
        constructor
        · exact FirstOrder.Derives.falsumElim
            hFalse
        · intro index hIndex
          simp at hIndex
    | hSnoc xs row ih =>
        by_cases hLength : length = 0
        · subst length
          have hFinalZero :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                numₘ(proof_sequence_code_value
                  (xs ++ [row])) ≐ₘ numₘ(0) :=
            Metatheory.Derives.equality_trans
              hFinal hZero
          have hPositive :
              0 <
                proof_sequence_code_value (xs ++ [row]) := by
            rw [proof_sequence_code_value_append_singleton]
            exact Nat.succ_pos _
          have hFalse :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                Formula.falsum :=
            fs_zfc_support_raw_falsum_of_numeral_equality
              (Nat.ne_of_gt hPositive) hFinalZero
          constructor
          · exact FirstOrder.Derives.falsumElim
              hFalse
          · intro index hIndex
            exact FirstOrder.Derives.falsumElim
              hFalse
        · obtain ⟨prefixLength, rfl⟩ :=
            Nat.exists_eq_succ_of_ne_zero hLength
          let lastConclusion : SetFormula :=
            (numₘ(proof_sequence_code_value xs) ≐ₘ
                (trace ·ₘ numₘ(prefixLength))) ∧ₘ
              ((sequence ·ₘ numₘ(prefixLength)) ≐ₘ
                standard_token_sequence row)
          have hLastConclusion :
              Formula.Admissible lastConclusion := by
            simpa [lastConclusion] using
              Formula.Admissible.conj
                (Formula.Admissible.equal
                  (finite_numeral_term_admissible
                    (proof_sequence_code_value xs))
                  (function_application_term_admissible
                    trace (numₘ(prefixLength)) hTrace
                    (finite_numeral_term_admissible
                      prefixLength)))
                (Formula.Admissible.equal
                  (function_application_term_admissible
                    sequence (numₘ(prefixLength)) hSequence
                    (finite_numeral_term_admissible
                      prefixLength))
                  (standard_token_sequence_admissible row))
          have hLastConclusionFresh :
              (SetSort.set, rowCodeId) ∉
                Formula.freeSupport lastConclusion := by
            simp only [lastConclusion, Formula.freeSupport,
              Term.freeSupport, Term.freeSupportList,
              finite_numeral_term_freeSupport,
              standard_token_sequence_freeSupport_nil,
              List.append_nil, List.nil_append]
            exact List.not_mem_append
              hRowCodeFreshTrace hRowCodeFreshSequence
          have hLast :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                lastConclusion := by
            apply
              fs_zfc_support_raw_proof_sequence_step_code_elim
                sequence trace code
                (proof_sequence_code_value (xs ++ [row]))
                prefixLength bound
                rowCodeId rowTraceId rowIndexId
                lastConclusion
                hSequence hTrace hCode
                hRowCodeFreshContext
                hLastConclusion
                hLastConclusionFresh
                hCodeEquality
                (hStep prefixLength (Nat.lt_succ_self _))
                (hTraceBound prefixLength (Nat.le_succ _))
                hFinal
            intro accumulator hAccumulator item hItem hMatch
            have hStepMatch :
                nat_sequence_code_step
                    (proof_sequence_code_value xs)
                    (nat_sequence_code_value row) =
                  nat_sequence_code_step accumulator item := by
              simpa using hMatch
            have hPairMatch :
                godel_pair_value
                    (proof_sequence_code_value xs)
                    (nat_sequence_code_value row) =
                  godel_pair_value accumulator item := by
              apply Nat.succ.inj
              simpa [nat_sequence_code_step] using hStepMatch
            rcases godel_pair_value_eq_iff.mp hPairMatch with
              ⟨hAccumulator, hItemCode⟩
            subst accumulator
            subst item
            let body : SetFormula :=
              proof_sequence_rejection_step_body
                sequence trace code prefixLength
                rowCodeId rowTraceId rowIndexId
            let Δ : Context signature :=
              ((x#rowCodeId) ≐ₘ
                  numₘ(nat_sequence_code_value row)) ::
                ((trace ·ₘ numₘ(prefixLength)) ≐ₘ
                  numₘ(proof_sequence_code_value xs)) ::
                body :: Γ
            have hBody :
                Formula.Admissible body := by
              simpa [body] using
                proof_sequence_rejection_step_body_admissible
                  sequence trace code prefixLength
                  rowCodeId rowTraceId rowIndexId
                  hSequence hTrace hCode
            have hBodyAt :
                Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
              FirstOrder.Derives.assumption
                (by simp [Δ])
            have hProofStep :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  proof_sequence_code_step_condition_with_ids
                    sequence trace (numₘ(prefixLength))
                    (x#rowCodeId)
                    rowTraceId rowIndexId := by
              simpa [body,
                proof_sequence_rejection_step_body] using
                FirstOrder.Derives.conjElimRight hBodyAt
            have hInner :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  nat_sequence_code_condition_with_ids
                    (sequence ·ₘ numₘ(prefixLength))
                    (x#rowCodeId)
                    rowTraceId rowIndexId := by
              simpa [proof_sequence_code_step_condition_with_ids] using
                FirstOrder.Derives.conjElimLeft hProofStep
            have hTraceEquality :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  (trace ·ₘ numₘ(prefixLength)) ≐ₘ
                    numₘ(proof_sequence_code_value xs) :=
              FirstOrder.Derives.assumption
                (by simp [Δ])
            have hPrefix :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  numₘ(proof_sequence_code_value xs) ≐ₘ
                    (trace ·ₘ numₘ(prefixLength)) :=
              Metatheory.Derives.equality_symm
                hTraceEquality
            have hRowCodeEquality :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  (x#rowCodeId) ≐ₘ
                    numₘ(nat_sequence_code_value row) :=
              FirstOrder.Derives.assumption
                (by simp [Δ])
            have hRowTraceFreshSequenceAt :
                (SetSort.set, rowTraceId) ∉
                  Term.freeSupport
                    (sequence ·ₘ numₘ(prefixLength)) := by
              simpa [Term.freeSupport, Term.freeSupportList,
                finite_numeral_term_freeSupport] using
                hRowTraceFreshSequence
            have hRowIndexFreshSequenceAt :
                (SetSort.set, rowIndexId) ∉
                  Term.freeSupport
                    (sequence ·ₘ numₘ(prefixLength)) := by
              simpa [Term.freeSupport, Term.freeSupportList,
                finite_numeral_term_freeSupport] using
                hRowIndexFreshSequence
            have hRowIndexFreshCode :
                (SetSort.set, rowIndexId) ∉
                  Term.freeSupport (x#rowCodeId) := by
              intro hMember
              change (SetSort.set, rowIndexId) ∈
                [(SetSort.set, rowCodeId)] at hMember
              have hEquality :
                  (SetSort.set, rowIndexId) =
                    (SetSort.set, rowCodeId) :=
                List.mem_singleton.mp hMember
              exact hRowCodeNeRowIndex
                (congrArg Prod.snd hEquality).symm
            have hRowTraceFreshDelta :
                ∀ formula, formula ∈ Δ →
                  (SetSort.set, rowTraceId) ∉
                    Formula.freeSupport formula := by
              intro formula hFormula
              simp only [Δ, List.mem_cons] at hFormula
              rcases hFormula with rfl | hFormula
              · have hVariableFresh :
                    (SetSort.set, rowTraceId) ∉
                      Term.freeSupport (x#rowCodeId) := by
                  intro hMember
                  change (SetSort.set, rowTraceId) ∈
                    [(SetSort.set, rowCodeId)] at hMember
                  have hPair :
                      (SetSort.set, rowTraceId) =
                        (SetSort.set, rowCodeId) :=
                    List.mem_singleton.mp hMember
                  exact hRowCodeNeRowTrace
                    (congrArg Prod.snd hPair).symm
                simpa [Formula.freeSupport,
                  finite_numeral_term_freeSupport] using
                  hVariableFresh
              · rcases hFormula with rfl | hFormula
                · simpa [Formula.freeSupport,
                    Term.freeSupport, Term.freeSupportList,
                    finite_numeral_term_freeSupport] using
                    hRowTraceFreshTrace
                · rcases hFormula with rfl | hFormula
                  · simpa [body] using
                      proof_sequence_rejection_step_body_row_trace_fresh
                        sequence trace code prefixLength
                        rowCodeId rowTraceId rowIndexId
                        hRowCodeNeRowTrace
                        hRowTraceFreshSequence
                        hRowTraceFreshTrace
                        hRowTraceFreshCode
                  · exact hRowTraceFreshContext formula hFormula
            have hRow :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  (sequence ·ₘ numₘ(prefixLength)) ≐ₘ
                    standard_token_sequence row :=
              fs_zfc_support_raw_nat_sequence_code_condition_unique_of_code_equality
                (sequence ·ₘ numₘ(prefixLength))
                (x#rowCodeId)
                row rowTraceId rowIndexId
                (function_application_term_admissible
                  sequence (numₘ(prefixLength)) hSequence
                  (finite_numeral_term_admissible
                    prefixLength))
                (set_variable_admissible rowCodeId)
                hRowTraceNeRowIndex
                hRowTraceFreshSequenceAt
                hRowIndexFreshSequenceAt
                hRowIndexFreshCode
                hRowTraceFreshDelta
                hInner
                hRowCodeEquality
            simpa [Δ, body, lastConclusion] using
              FirstOrder.Derives.conjIntro hPrefix hRow
          have hPrefixFinal :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                numₘ(proof_sequence_code_value xs) ≐ₘ
                  (trace ·ₘ numₘ(prefixLength)) := by
            simpa [lastConclusion] using
              FirstOrder.Derives.conjElimLeft hLast
          have hLastRow :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                (sequence ·ₘ numₘ(prefixLength)) ≐ₘ
                  standard_token_sequence row := by
            simpa [lastConclusion] using
              FirstOrder.Derives.conjElimRight hLast
          have hIH :=
            ih (Γ := Γ) prefixLength
              hRowCodeFreshContext
              hRowTraceFreshContext
              hZero
              (fun index hIndex =>
                hStep index (by omega))
              (fun index hIndex =>
                hTraceBound index (by omega))
              hCodeEquality
              hPrefixFinal
          constructor
          · have hSuccessorLength :=
              successor_term_congr_of_equality
                (numₘ(prefixLength))
                (numₘ(xs.length))
                (finite_numeral_term_admissible
                  prefixLength)
                (finite_numeral_term_admissible xs.length)
                hIH.1
            simpa [List.length_append,
              finite_numeral_term, successor_term] using
              hSuccessorLength
          · intro index hIndex
            by_cases hPrefixIndex : index < xs.length
            · simpa [List.getElem_append, hPrefixIndex] using
                hIH.2 index hPrefixIndex
            · have hIndexEq : index = xs.length := by
                have hIndex' : index < xs.length + 1 := by
                  simpa [List.length_append] using hIndex
                omega
              subst index
              have hApplication :
                  Γ ⊢ₘ[fs_zfc_support_raw_theory]
                    (sequence ·ₘ numₘ(prefixLength)) ≐ₘ
                      (sequence ·ₘ numₘ(xs.length)) :=
                function_application_term_congr_argument_of_equality
                  sequence
                  (numₘ(prefixLength))
                  (numₘ(xs.length))
                  hSequence
                  (finite_numeral_term_admissible
                    prefixLength)
                  (finite_numeral_term_admissible xs.length)
                  hIH.1
              have hApplicationSymm :=
                Metatheory.Derives.equality_symm
                  hApplication
              have hLastAt :
                  Γ ⊢ₘ[fs_zfc_support_raw_theory]
                    (sequence ·ₘ numₘ(xs.length)) ≐ₘ
                      standard_token_sequence row :=
                Metatheory.Derives.equality_trans
                  hApplicationSymm hLastRow
              simpa [List.getElem_append] using hLastAt

/-! ## 回放数据到规范二维序列 -/

/-- 将已经打开的二维编码数据收束为规范行序列。 -/
theorem fs_zfc_support_raw_proof_sequence_code_replay_of_data
    {Γ : Context signature}
    (sequence trace code : SetTerm)
    (rows : List (List Nat))
    (length bound : Nat)
    (rowCodeId rowTraceId rowIndexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hTrace : Term.Admissible trace SetSort.set)
    (hCode : Term.Admissible code SetSort.set)
    (hRowCodeNeRowTrace : rowCodeId ≠ rowTraceId)
    (hRowCodeNeRowIndex : rowCodeId ≠ rowIndexId)
    (hRowTraceNeRowIndex : rowTraceId ≠ rowIndexId)
    (hRowCodeFreshSequence :
      (SetSort.set, rowCodeId) ∉ Term.freeSupport sequence)
    (hRowCodeFreshTrace :
      (SetSort.set, rowCodeId) ∉ Term.freeSupport trace)
    (hRowCodeFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, rowCodeId) ∉ Formula.freeSupport formula)
    (hRowTraceFreshSequence :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport sequence)
    (hRowTraceFreshTrace :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport trace)
    (hRowTraceFreshCode :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport code)
    (hRowTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, rowTraceId) ∉ Formula.freeSupport formula)
    (hRowIndexFreshSequence :
      (SetSort.set, rowIndexId) ∉ Term.freeSupport sequence)
    (hFunction :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        is_function_formula sequence)
    (hDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ numₘ(length))
    (hZero :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (trace ·ₘ numₘ(0)) ≐ₘ numₘ(0))
    (hStep :
      ∀ index, index < length →
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          ∃ₘ[SetSort.set, rowCodeId],
            proof_sequence_rejection_step_body
              sequence trace code index
              rowCodeId rowTraceId rowIndexId)
    (hTraceBound :
      ∀ index, index ≤ length →
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          (trace ·ₘ numₘ(index)) ∈ₘ numₘ(bound + 1))
    (hCodeEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code ≐ₘ numₘ(bound))
    (hFinal :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(proof_sequence_code_value rows) ≐ₘ
          (trace ·ₘ numₘ(length))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      sequence ≐ₘ
        standard_sequence
          (rows.map standard_token_sequence) := by
  let elements : List SetTerm :=
    rows.map standard_token_sequence
  have hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨row, _, rfl⟩
    exact standard_token_sequence_admissible row
  have hElementsClosed :
      ∀ element, element ∈ elements →
        Term.freeSupport element = [] := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨row, _, rfl⟩
    exact standard_token_sequence_freeSupport_nil row
  have hUnique :=
    fs_zfc_support_raw_proof_sequence_code_prefix_unique
      sequence trace code rows length bound
      rowCodeId rowTraceId rowIndexId
      hSequence hTrace hCode
      hRowCodeNeRowTrace hRowCodeNeRowIndex
      hRowTraceNeRowIndex
      hRowCodeFreshSequence hRowCodeFreshTrace
      hRowCodeFreshContext
      hRowTraceFreshSequence hRowTraceFreshTrace
      hRowTraceFreshCode hRowTraceFreshContext
      hRowIndexFreshSequence
      hZero hStep hTraceBound hCodeEquality hFinal
  have hDomainRows :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ numₘ(elements.length) := by
    have hDomainLength :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(sequence) ≐ₘ numₘ(rows.length) :=
      Metatheory.Derives.equality_trans
        hDomain hUnique.1
    simpa [elements] using hDomainLength
  apply standard_sequence_eq_of_function_domain_pointwise
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (fun _ hFormula =>
      fs_zfc_support_raw_contains_standard_sequence_semantics
        hFormula)
    (fun _ hFormula =>
      fs_zfc_support_raw_theory_sentence hFormula)
    sequence elements hSequence
    hElements hElementsClosed hFunction hDomainRows
  intro index element hGet
  rcases List.getElem?_eq_some_iff.mp hGet with
    ⟨hIndex, rfl⟩
  have hRowsIndex : index < rows.length := by
    simpa [elements] using hIndex
  simpa [elements] using
    hUnique.2 index hRowsIndex

/-! ## 完整二维条件的规范唯一性 -/

/--
完整二维证明序列条件在最终码为规范 numeral 时唯一决定行序列。

这里的 `rows` 只是外部有限列表；对象层只回放其数码递推与行内
自然数序列条件，不引入任何语义假设。
-/
theorem fs_zfc_support_raw_proof_sequence_code_condition_unique_of_code_equality
    {Γ : Context signature}
    (sequence code : SetTerm)
    (rows : List (List Nat))
    (traceId indexId rowCodeId rowTraceId rowIndexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCode : Term.Admissible code SetSort.set)
    (hTraceNeIndex : traceId ≠ indexId)
    (hTraceNeRowCode : traceId ≠ rowCodeId)
    (hTraceNeRowTrace : traceId ≠ rowTraceId)
    (hIndexNeRowCode : indexId ≠ rowCodeId)
    (hIndexNeRowTrace : indexId ≠ rowTraceId)
    (hIndexNeRowIndex : indexId ≠ rowIndexId)
    (hRowCodeNeRowTrace : rowCodeId ≠ rowTraceId)
    (hRowCodeNeRowIndex : rowCodeId ≠ rowIndexId)
    (hRowTraceNeRowIndex : rowTraceId ≠ rowIndexId)
    (hTraceFreshSequence :
      (SetSort.set, traceId) ∉ Term.freeSupport sequence)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉ Term.freeSupport sequence)
    (hIndexFreshCode :
      (SetSort.set, indexId) ∉ Term.freeSupport code)
    (hRowCodeFreshSequence :
      (SetSort.set, rowCodeId) ∉ Term.freeSupport sequence)
    (hRowCodeFreshCode :
      (SetSort.set, rowCodeId) ∉ Term.freeSupport code)
    (hRowTraceFreshSequence :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport sequence)
    (hRowTraceFreshCode :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport code)
    (hRowIndexFreshSequence :
      (SetSort.set, rowIndexId) ∉ Term.freeSupport sequence)
    (hTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport formula)
    (hRowCodeFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, rowCodeId) ∉ Formula.freeSupport formula)
    (hRowTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, rowTraceId) ∉ Formula.freeSupport formula)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        proof_sequence_code_condition_with_ids
          sequence code traceId indexId
          rowCodeId rowTraceId rowIndexId)
    (hCodeEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code ≐ₘ numₘ(proof_sequence_code_value rows)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      sequence ≐ₘ
        standard_sequence
          (rows.map standard_token_sequence) := by
  let bound : Nat := proof_sequence_code_value rows
  let elements : List SetTerm :=
    rows.map standard_token_sequence
  have hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨row, _, rfl⟩
    exact standard_token_sequence_admissible row
  have hElementsClosed :
      ∀ element, element ∈ elements →
        Term.freeSupport element = [] := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨row, _, rfl⟩
    exact standard_token_sequence_freeSupport_nil row
  have hStandard :
      Term.Admissible (standard_sequence elements) SetSort.set := by
    exact seq_admissible_m 0 hElements
  have hStandardFreshTrace :
      (SetSort.set, traceId) ∉
        Term.freeSupport (standard_sequence elements) := by
    rw [show Term.freeSupport (standard_sequence elements) = [] by
      exact seq_support_nil_m 0 hElementsClosed]
    exact List.not_mem_nil
  have hParts :=
    fs_zfc_support_raw_proof_sequence_code_condition_parts
      sequence code traceId indexId
      rowCodeId rowTraceId rowIndexId hCondition
  rcases hParts with
    ⟨hSpace, _, hDomainBound, hTraceExists⟩
  have hFormulaCodeNonempty :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        FormulaCodeₘ ≠ₘ ∅ₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := [])
      (Δ := Γ)
      (by
        intro formula hFormula
        simp at hFormula)
      (fs_zfc_support_raw_derives_of_godel_quotation
        GodelQuotation.formula_code_set_nonempty_derives)
  have hFunction :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        is_function_formula sequence :=
    fs_zfc_support_raw_sequence_space_function_of_target
      FormulaCodeₘ sequence
      formula_code_set_term_admissible hSequence
      hFormulaCodeNonempty hSpace
  have hDomainMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ∈ₘ numₘ(bound + 1) := by
    have hSuccessorCodeEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          Sₘ(code) ≐ₘ Sₘ(numₘ(bound)) :=
      successor_term_congr_of_equality
        code (numₘ(bound))
        hCode
        (finite_numeral_term_admissible bound)
        (by simpa [bound] using hCodeEquality)
    have hTransport :=
      membership_right_iff_of_equality
        (domₘ(sequence)) (Sₘ(code))
        (Sₘ(numₘ(bound)))
        (domain_term_admissible sequence hSequence)
        (successor_term_admissible code hCode)
        (successor_term_admissible
          (numₘ(bound))
          (finite_numeral_term_admissible bound))
        hSuccessorCodeEquality
    have hAtSuccessor :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(sequence) ∈ₘ Sₘ(numₘ(bound)) :=
      FirstOrder.Derives.iffElimRight
        hTransport
        (by simpa [sequence_domain_code_bound] using hDomainBound)
    simpa [finite_numeral_term, successor_term] using
      hAtSuccessor
  apply
    fs_zfc_support_raw_finite_numeral_member_elim_context
      (bound + 1)
      (domₘ(sequence))
      (sequence ≐ₘ standard_sequence elements)
      (domain_term_admissible sequence hSequence)
      (Formula.Admissible.equal hSequence hStandard)
      hDomainMember
  intro length _
  let domainEquation : SetFormula :=
    domₘ(sequence) ≐ₘ numₘ(length)
  let Δ : Context signature :=
    domainEquation :: Γ
  change Δ ⊢ₘ[fs_zfc_support_raw_theory]
    sequence ≐ₘ standard_sequence elements
  have hDomainEquationAdmissible :
      Formula.Admissible domainEquation := by
    simpa [domainEquation] using
      Formula.Admissible.equal
        (domain_term_admissible sequence hSequence)
        (finite_numeral_term_admissible length)
  have hDomain :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ numₘ(length) := by
    simpa [Δ, domainEquation] using
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := Δ)
        (φ := domainEquation)
        (by simp [Δ]))
  let traceBody : SetFormula :=
    proof_sequence_rejection_trace_body
      sequence code traceId indexId
      rowCodeId rowTraceId rowIndexId
  have hTraceBodyAdmissible :
      Formula.Admissible traceBody := by
    simpa [traceBody] using
      proof_sequence_rejection_trace_body_admissible
        sequence code traceId indexId
        rowCodeId rowTraceId rowIndexId
        hSequence hCode
  have hTraceExistsAt :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, traceId], traceBody := by
    simpa [traceBody] using
      FirstOrder.Derives.context_weaken_cons hTraceExists
  nd_apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Δ)
    (sort := SetSort.set)
    (eigen := traceId)
    (body := traceBody)
    (conclusion := sequence ≐ₘ standard_sequence elements)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    simp only [Δ, List.mem_cons] at hFormula
    rcases hFormula with rfl | hFormula
    · simpa [domainEquation, Formula.freeSupport,
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport] using
        hTraceFreshSequence
    · exact hTraceFreshContext formula hFormula
  · simp only [Formula.freeSupport]
    exact List.not_mem_append
      hTraceFreshSequence hStandardFreshTrace
  · exact hTraceExistsAt
  · let Ε : Context signature :=
      traceBody :: Δ
    change Ε ⊢ₘ[fs_zfc_support_raw_theory]
      sequence ≐ₘ standard_sequence elements
    have hTraceBodyAt :
        Ε ⊢ₘ[fs_zfc_support_raw_theory] traceBody :=
      FirstOrder.Derives.assumption
        (by simp [Ε])
    have hTraceTail :=
      FirstOrder.Derives.conjElimRight hTraceBodyAt
    have hTraceDomainBound :=
      FirstOrder.Derives.conjElimLeft hTraceTail
    have hTraceRight :=
      FirstOrder.Derives.conjElimRight hTraceTail
    have hTraceSpace :=
      FirstOrder.Derives.conjElimLeft hTraceBodyAt
    have hTraceBound :=
      FirstOrder.Derives.conjElimRight hTraceDomainBound
    have hTraceDomainRaw :=
      FirstOrder.Derives.conjElimLeft hTraceDomainBound
    have hZero :=
      FirstOrder.Derives.conjElimLeft hTraceRight
    have hStepsFinal :=
      FirstOrder.Derives.conjElimRight hTraceRight
    have hSteps :=
      FirstOrder.Derives.conjElimLeft hStepsFinal
    have hFinalRaw :=
      FirstOrder.Derives.conjElimRight hStepsFinal
    have hTrace :
        Term.Admissible (x#traceId) SetSort.set :=
      set_variable_admissible traceId
    have hDomainAt :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(sequence) ≐ₘ numₘ(length) :=
      FirstOrder.Derives.context_weaken_cons hDomain
    have hFunctionAt :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          is_function_formula sequence :=
      FirstOrder.Derives.context_weaken_cons
        (FirstOrder.Derives.context_weaken_cons hFunction)
    have hCodeEqualityAt :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          code ≐ₘ numₘ(bound) :=
      FirstOrder.Derives.context_weaken_cons
        (FirstOrder.Derives.context_weaken_cons
          (by simpa [bound] using hCodeEquality))
    have hIndexFreshTrace :
        (SetSort.set, indexId) ∉
          Term.freeSupport (x#traceId) := by
      intro hMember
      change (SetSort.set, indexId) ∈
        [(SetSort.set, traceId)] at hMember
      have hEquality :
          (SetSort.set, indexId) =
            (SetSort.set, traceId) :=
        List.mem_singleton.mp hMember
      exact hTraceNeIndex
        (congrArg Prod.snd hEquality).symm
    have hRowCodeFreshTrace :
        (SetSort.set, rowCodeId) ∉
          Term.freeSupport (x#traceId) := by
      intro hMember
      change (SetSort.set, rowCodeId) ∈
        [(SetSort.set, traceId)] at hMember
      have hEquality :
          (SetSort.set, rowCodeId) =
            (SetSort.set, traceId) :=
        List.mem_singleton.mp hMember
      exact hTraceNeRowCode
        (congrArg Prod.snd hEquality).symm
    have hRowTraceFreshTrace :
        (SetSort.set, rowTraceId) ∉
          Term.freeSupport (x#traceId) := by
      intro hMember
      change (SetSort.set, rowTraceId) ∈
        [(SetSort.set, traceId)] at hMember
      have hEquality :
          (SetSort.set, rowTraceId) =
            (SetSort.set, traceId) :=
        List.mem_singleton.mp hMember
      exact hTraceNeRowTrace
        (congrArg Prod.snd hEquality).symm
    have hRowCodeFreshTraceBody :
        (SetSort.set, rowCodeId) ∉
          Formula.freeSupport traceBody := by
      simpa [traceBody, proof_sequence_rejection_trace_body,
        proof_sequence_code_trace_body_with_ids] using
        proof_sequence_code_trace_body_with_ids_row_code_fresh
          sequence code traceId indexId
          rowCodeId rowTraceId rowIndexId
          hRowCodeFreshSequence hRowCodeFreshCode
          hRowCodeFreshTrace hIndexNeRowCode
    have hRowTraceFreshTraceBody :
        (SetSort.set, rowTraceId) ∉
          Formula.freeSupport traceBody := by
      simpa [traceBody, proof_sequence_rejection_trace_body,
        proof_sequence_code_trace_body_with_ids] using
        proof_sequence_code_trace_body_with_ids_row_trace_fresh
          sequence code traceId indexId
          rowCodeId rowTraceId rowIndexId
          hRowTraceFreshSequence hRowTraceFreshCode
          hRowTraceFreshTrace hIndexNeRowTrace
          hRowCodeNeRowTrace
    have hRowCodeFreshContextAt :
        ∀ formula, formula ∈ Ε →
          (SetSort.set, rowCodeId) ∉
            Formula.freeSupport formula := by
      intro formula hFormula
      simp only [Ε, Δ, List.mem_cons] at hFormula
      rcases hFormula with rfl | rfl | hFormula
      · exact hRowCodeFreshTraceBody
      · simpa [domainEquation, Formula.freeSupport,
          Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport] using
          hRowCodeFreshSequence
      · exact hRowCodeFreshContext formula hFormula
    have hRowTraceFreshContextAt :
        ∀ formula, formula ∈ Ε →
          (SetSort.set, rowTraceId) ∉
            Formula.freeSupport formula := by
      intro formula hFormula
      simp only [Ε, Δ, List.mem_cons] at hFormula
      rcases hFormula with rfl | rfl | hFormula
      · exact hRowTraceFreshTraceBody
      · simpa [domainEquation, Formula.freeSupport,
          Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport] using
          hRowTraceFreshSequence
      · exact hRowTraceFreshContext formula hFormula
    have hSuccessorCodeEquality :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          Sₘ(code) ≐ₘ Sₘ(numₘ(bound)) :=
      successor_term_congr_of_equality
        code (numₘ(bound)) hCode
        (finite_numeral_term_admissible bound)
        hCodeEqualityAt
    have hTraceDomainSucc :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(x#traceId) ≐ₘ Sₘ(numₘ(length)) :=
      Metatheory.Derives.equality_trans
        hTraceDomainRaw
        (successor_term_congr_of_equality
          (domₘ(sequence)) (numₘ(length))
          (domain_term_admissible sequence hSequence)
          (finite_numeral_term_admissible length)
          hDomainAt)
    have hTraceDomain :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(x#traceId) ≐ₘ numₘ(length + 1) := by
      simpa [finite_numeral_term, successor_term] using
        hTraceDomainSucc
    have hStepAt :
        ∀ index, index < length →
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            ∃ₘ[SetSort.set, rowCodeId],
              proof_sequence_rejection_step_body
                sequence (x#traceId) code index
                rowCodeId rowTraceId rowIndexId := by
      intro index hIndex
      exact fs_zfc_support_raw_proof_sequence_step_at
        sequence (x#traceId) code
        indexId rowCodeId rowTraceId rowIndexId
        length index hSequence
        hIndexNeRowCode hIndexNeRowTrace hIndexNeRowIndex
        hIndexFreshSequence hIndexFreshTrace
        hIndexFreshCode hDomainAt hSteps hIndex
    have hTraceAt :
        ∀ index, index ≤ length →
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            (x#traceId ·ₘ numₘ(index)) ∈ₘ
              numₘ(bound + 1) := by
      intro index hIndex
      have hAtCode :=
        fs_zfc_support_raw_sequence_trace_bound_at
          (x#traceId) code indexId
          (length + 1) index hTrace hCode
          hIndexFreshTrace hIndexFreshCode hTraceDomain
          hTraceBound
          (by omega)
      have hAtSuccessor :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            (x#traceId ·ₘ numₘ(index)) ∈ₘ
              Sₘ(numₘ(bound)) :=
        FirstOrder.Derives.iffElimRight
          (membership_right_iff_of_equality
            (x#traceId ·ₘ numₘ(index))
            (Sₘ(code)) (Sₘ(numₘ(bound)))
            (function_application_term_admissible
              (x#traceId) (numₘ(index)) hTrace
              (finite_numeral_term_admissible index))
            (successor_term_admissible code hCode)
            (successor_term_admissible
              (numₘ(bound))
              (finite_numeral_term_admissible bound))
            hSuccessorCodeEquality)
          hAtCode
      simpa [finite_numeral_term, successor_term] using
        hAtSuccessor
    have hTraceDomainApplication :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          (x#traceId ·ₘ domₘ(sequence)) ≐ₘ
            (x#traceId ·ₘ numₘ(length)) :=
      function_application_term_congr_argument_of_equality
        (x#traceId) (domₘ(sequence)) (numₘ(length))
        hTrace (domain_term_admissible sequence hSequence)
        (finite_numeral_term_admissible length) hDomainAt
    have hFinal :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(bound) ≐ₘ
            (x#traceId ·ₘ numₘ(length)) := by
      have hNumeralCode :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            numₘ(bound) ≐ₘ code :=
        Metatheory.Derives.equality_symm
          hCodeEqualityAt
      have hNumeralToDomain :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            numₘ(bound) ≐ₘ
              (x#traceId ·ₘ domₘ(sequence)) :=
        Metatheory.Derives.equality_trans
          hNumeralCode hFinalRaw
      simpa using
        Metatheory.Derives.equality_trans
          hNumeralToDomain hTraceDomainApplication
    exact
      fs_zfc_support_raw_proof_sequence_code_replay_of_data
        sequence (x#traceId) code rows length bound
        rowCodeId rowTraceId rowIndexId
        hSequence hTrace hCode
        hRowCodeNeRowTrace hRowCodeNeRowIndex
        hRowTraceNeRowIndex
        hRowCodeFreshSequence hRowCodeFreshTrace
        hRowCodeFreshContextAt
        hRowTraceFreshSequence hRowTraceFreshTrace
        hRowTraceFreshCode hRowTraceFreshContextAt
        hRowIndexFreshSequence
        hFunctionAt hDomainAt hZero hStepAt hTraceAt
        (by simpa [bound] using hCodeEqualityAt)
        hFinal

/-- 规范二维 numeral 代码下的唯一性薄包装。 -/
theorem fs_zfc_support_raw_proof_sequence_code_condition_unique
    {Γ : Context signature}
    (sequence : SetTerm)
    (rows : List (List Nat))
    (traceId indexId rowCodeId rowTraceId rowIndexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hTraceNeIndex : traceId ≠ indexId)
    (hTraceNeRowCode : traceId ≠ rowCodeId)
    (hTraceNeRowTrace : traceId ≠ rowTraceId)
    (hIndexNeRowCode : indexId ≠ rowCodeId)
    (hIndexNeRowTrace : indexId ≠ rowTraceId)
    (hIndexNeRowIndex : indexId ≠ rowIndexId)
    (hRowCodeNeRowTrace : rowCodeId ≠ rowTraceId)
    (hRowCodeNeRowIndex : rowCodeId ≠ rowIndexId)
    (hRowTraceNeRowIndex : rowTraceId ≠ rowIndexId)
    (hTraceFreshSequence :
      (SetSort.set, traceId) ∉ Term.freeSupport sequence)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉ Term.freeSupport sequence)
    (hRowCodeFreshSequence :
      (SetSort.set, rowCodeId) ∉ Term.freeSupport sequence)
    (hRowTraceFreshSequence :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport sequence)
    (hRowIndexFreshSequence :
      (SetSort.set, rowIndexId) ∉ Term.freeSupport sequence)
    (hTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport formula)
    (hRowCodeFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, rowCodeId) ∉ Formula.freeSupport formula)
    (hRowTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, rowTraceId) ∉ Formula.freeSupport formula)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        proof_sequence_code_condition_with_ids
          sequence
          (numₘ(proof_sequence_code_value rows))
          traceId indexId rowCodeId rowTraceId rowIndexId) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      sequence ≐ₘ
        standard_sequence
          (rows.map standard_token_sequence) := by
  apply
    fs_zfc_support_raw_proof_sequence_code_condition_unique_of_code_equality
      sequence (numₘ(proof_sequence_code_value rows)) rows
      traceId indexId rowCodeId rowTraceId rowIndexId
      hSequence
      (finite_numeral_term_admissible
        (proof_sequence_code_value rows))
      hTraceNeIndex hTraceNeRowCode hTraceNeRowTrace
      hIndexNeRowCode hIndexNeRowTrace hIndexNeRowIndex
      hRowCodeNeRowTrace hRowCodeNeRowIndex hRowTraceNeRowIndex
  · exact hTraceFreshSequence
  · exact hIndexFreshSequence
  · rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  · exact hRowCodeFreshSequence
  · rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  · exact hRowTraceFreshSequence
  · rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  · exact hRowIndexFreshSequence
  · exact hTraceFreshContext
  · exact hRowCodeFreshContext
  · exact hRowTraceFreshContext
  · exact hCondition
  · exact FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set)
      (numₘ(proof_sequence_code_value rows))

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
