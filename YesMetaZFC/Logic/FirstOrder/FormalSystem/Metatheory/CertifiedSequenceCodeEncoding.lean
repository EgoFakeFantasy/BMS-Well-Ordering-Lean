import YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofCode
import YesMetaZFC.Logic.FirstOrder.Hilbert.Substitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncoding

/-!
# 证书化证明码使用的有限序列编码

本模块只提供自然数有限序列、公式代码有限序列以及末行条件的对象层语法。
它不读取理论成员关系，也不携带任何关于理论的强度假设；证明码 verifier
由上层模块单独组合。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

private def certified_sequence_fresh_base (terms : List SetTerm) :
    FreeVarId :=
  FreshVariable.fresh_id SetSort.set
    (terms.map fun term => term ≐ₘ term)

/-! ## 自然数有限序列编码 -/

/-- 数值序列编码轨迹的一步递归方程。 -/
def nat_sequence_code_step_condition
    (sequence trace index : SetTerm) : SetFormula :=
  (trace ·ₘ Sₘ(index)) ≐ₘ
    Sₘ(godel_pairₘ(
      ⟨trace ·ₘ index, sequence ·ₘ index⟩ₘ))

/--
有限序列的长度不超过其自然数编码。

对具体编码 `c`，该条件把未知定义域压入有限序数 `S(c)`，供负向
checked replay 做纯有限消去。
-/
def sequence_domain_code_bound
    (sequence code : SetTerm) : SetFormula :=
  domₘ(sequence) ∈ₘ Sₘ(code)

/-- 自然数序列的每个值严格小于其最终编码。 -/
def nat_sequence_value_code_bound_with_id
    (sequence code : SetTerm) (indexId : FreeVarId) : SetFormula :=
  ∀ₘ[SetSort.set, indexId],
    (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
      ((sequence ·ₘ x#indexId) ∈ₘ code)

/-- 编码轨迹的每个中间值不超过最终编码。 -/
def sequence_trace_code_bound_with_id
    (trace code : SetTerm) (indexId : FreeVarId) : SetFormula :=
  ∀ₘ[SetSort.set, indexId],
    (x#indexId ∈ₘ domₘ(trace)) ⟶ₘ
      ((trace ·ₘ x#indexId) ∈ₘ Sₘ(code))

/-- 显式编号的自然数有限序列编码关系。 -/
def nat_sequence_code_condition_with_ids
    (sequence code : SetTerm) (traceId indexId : FreeVarId) :
    SetFormula :=
  ((((sequence ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
        (code ∈ₘ ωₘ)) ∧ₘ
      sequence_domain_code_bound sequence code) ∧ₘ
    nat_sequence_value_code_bound_with_id
      sequence code indexId) ∧ₘ
    (∃ₘ[SetSort.set, traceId],
      (x#traceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
        (((domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
            sequence_trace_code_bound_with_id
              (x#traceId) code indexId) ∧ₘ
          ((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
          ((∀ₘ[SetSort.set, indexId],
              (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
                nat_sequence_code_step_condition
                  sequence (x#traceId) (x#indexId)) ∧ₘ
            (code ≐ₘ (x#traceId ·ₘ domₘ(sequence))))))

/-- 自然数有限序列编码关系的 canonical 包装。 -/
def nat_sequence_code_condition
    (sequence code : SetTerm) : SetFormula :=
  let traceId := certified_sequence_fresh_base [sequence, code]
  let indexId := traceId + 1
  nat_sequence_code_condition_with_ids
    sequence code traceId indexId

/-! ## 公式代码有限序列编码 -/

/-- 显式编号的公式代码有限序列编码单步关系。 -/
def proof_sequence_code_step_condition_with_ids
    (sequence trace index rowCode : SetTerm)
    (rowTraceId rowIndexId : FreeVarId) : SetFormula :=
  nat_sequence_code_condition_with_ids
      (sequence ·ₘ index) rowCode rowTraceId rowIndexId ∧ₘ
    ((trace ·ₘ Sₘ(index)) ≐ₘ
      Sₘ(godel_pairₘ(
        ⟨trace ·ₘ index, rowCode⟩ₘ)))

/-- 显式编号的公式代码有限序列编码关系。 -/
def proof_sequence_code_condition_with_ids
    (sequence code : SetTerm)
    (traceId indexId rowCodeId rowTraceId rowIndexId : FreeVarId) :
    SetFormula :=
  (((sequence ∈ₘ seq_spaceₘ(FormulaCodeₘ)) ∧ₘ
      (code ∈ₘ ωₘ)) ∧ₘ
    sequence_domain_code_bound sequence code) ∧ₘ
    (∃ₘ[SetSort.set, traceId],
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
            (code ≐ₘ (x#traceId ·ₘ domₘ(sequence))))))

/-! ## 证明序列末行 -/

/-- 证明序列以 `conclusion` 为末行。 -/
def proof_sequence_terminal_condition
    (sequence conclusion : SetTerm) : SetFormula :=
  ∃ₘ[SetSort.set],
    (bₛ#0 ∈ₘ domₘ(sequence)) ∧ₘ
      ((domₘ(sequence) ≐ₘ Sₘ(bₛ#0)) ∧ₘ
        (conclusion ≐ₘ (sequence ·ₘ bₛ#0)))

/-! ## admissibility -/

theorem proof_sequence_terminal_condition_admissible
    (sequence conclusion : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hConclusion : Term.Admissible conclusion SetSort.set) :
    Formula.Admissible
      (proof_sequence_terminal_condition sequence conclusion) := by
  prove_admissible

theorem nat_sequence_code_step_condition_admissible
    (sequence trace index : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hTrace : Term.Admissible trace SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible
      (nat_sequence_code_step_condition sequence trace index) := by
  have hSuccessorIndex :=
    successor_term_admissible index hIndex
  have hTraceNext :=
    function_application_term_admissible
      trace (Sₘ(index)) hTrace hSuccessorIndex
  have hTraceAt :=
    function_application_term_admissible
      trace index hTrace hIndex
  have hSequenceAt :=
    function_application_term_admissible
      sequence index hSequence hIndex
  have hPair :=
    ordered_pair_term_admissible
      (trace ·ₘ index) (sequence ·ₘ index)
      hTraceAt hSequenceAt
  have hPairCode :=
    godel_pairing_term_admissible
      ⟨trace ·ₘ index, sequence ·ₘ index⟩ₘ hPair
  have hSuccessorCode :=
    successor_term_admissible
      (godel_pairₘ(⟨trace ·ₘ index, sequence ·ₘ index⟩ₘ))
      hPairCode
  simpa [nat_sequence_code_step_condition] using
    Formula.Admissible.equal hTraceNext hSuccessorCode

theorem sequence_domain_code_bound_admissible
    (sequence code : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (sequence_domain_code_bound sequence code) := by
  exact membership_formula_admissible
    (domain_term_admissible sequence hSequence)
    (successor_term_admissible code hCode)

theorem nat_sequence_value_code_bound_with_id_admissible
    (sequence code : SetTerm) (indexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (nat_sequence_value_code_bound_with_id
        sequence code indexId) := by
  have hIndex :
      Term.Admissible (x#indexId) SetSort.set :=
    set_variable_admissible indexId
  have hDomain :=
    membership_formula_admissible hIndex
      (domain_term_admissible sequence hSequence)
  have hValue :=
    membership_formula_admissible
      (function_application_term_admissible
        sequence (x#indexId) hSequence hIndex)
      hCode
  simpa [nat_sequence_value_code_bound_with_id] using
    Formula.Admissible.forall_closeFreeAt
      SetSort.set indexId
      (Formula.Admissible.imp hDomain hValue)

theorem sequence_trace_code_bound_with_id_admissible
    (trace code : SetTerm) (indexId : FreeVarId)
    (hTrace : Term.Admissible trace SetSort.set)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (sequence_trace_code_bound_with_id
        trace code indexId) := by
  have hIndex :
      Term.Admissible (x#indexId) SetSort.set :=
    set_variable_admissible indexId
  have hDomain :=
    membership_formula_admissible hIndex
      (domain_term_admissible trace hTrace)
  have hValue :=
    membership_formula_admissible
      (function_application_term_admissible
        trace (x#indexId) hTrace hIndex)
      (successor_term_admissible code hCode)
  simpa [sequence_trace_code_bound_with_id] using
    Formula.Admissible.forall_closeFreeAt
      SetSort.set indexId
      (Formula.Admissible.imp hDomain hValue)

theorem nat_sequence_code_condition_with_ids_admissible
    (sequence code : SetTerm) (traceId indexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (nat_sequence_code_condition_with_ids
        sequence code traceId indexId) := by
  have hNaturalSequenceSpace :=
    finite_sequence_space_term_admissible
      ωₘ omega_term_admissible
  have hSequenceSpace :=
    membership_formula_admissible hSequence hNaturalSequenceSpace
  have hCodeNatural :=
    membership_formula_admissible hCode omega_term_admissible
  have hSequenceDomainBound :=
    sequence_domain_code_bound_admissible
      sequence code hSequence hCode
  have hSequenceValueBound :=
    nat_sequence_value_code_bound_with_id_admissible
      sequence code indexId hSequence hCode
  have hTrace :
      Term.Admissible (x#traceId) SetSort.set :=
    set_variable_admissible traceId
  have hTraceSpace :=
    membership_formula_admissible hTrace hNaturalSequenceSpace
  have hTraceDomain :=
    domain_term_admissible (x#traceId) hTrace
  have hSequenceDomain :=
    domain_term_admissible sequence hSequence
  have hSuccessorSequenceDomain :=
    successor_term_admissible
      (domₘ(sequence)) hSequenceDomain
  have hDomainEquation :=
    Formula.Admissible.equal
      hTraceDomain hSuccessorSequenceDomain
  have hTraceValueBound :=
    sequence_trace_code_bound_with_id_admissible
      (x#traceId) code indexId hTrace hCode
  have hZero := finite_numeral_term_admissible 0
  have hTraceZero :=
    function_application_term_admissible
      (x#traceId) (numₘ(0)) hTrace hZero
  have hInitialEquation :=
    Formula.Admissible.equal hTraceZero hZero
  have hIndex :
      Term.Admissible (x#indexId) SetSort.set :=
    set_variable_admissible indexId
  have hIndexDomain :=
    membership_formula_admissible hIndex hSequenceDomain
  have hStep :=
    nat_sequence_code_step_condition_admissible
      sequence (x#traceId) (x#indexId)
      hSequence hTrace hIndex
  have hAllSteps :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set indexId
      (Formula.Admissible.imp hIndexDomain hStep)
  have hTraceFinal :=
    function_application_term_admissible
      (x#traceId) (domₘ(sequence))
      hTrace hSequenceDomain
  have hFinalEquation :=
    Formula.Admissible.equal hCode hTraceFinal
  have hTraceBody :=
    Formula.Admissible.conj
      hTraceSpace
      (Formula.Admissible.conj
        (Formula.Admissible.conj
          hDomainEquation hTraceValueBound)
        (Formula.Admissible.conj
          hInitialEquation
          (Formula.Admissible.conj
            hAllSteps hFinalEquation)))
  have hTraceExists :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set traceId hTraceBody
  simpa [nat_sequence_code_condition_with_ids] using
    Formula.Admissible.conj
      (Formula.Admissible.conj
        (Formula.Admissible.conj
          (Formula.Admissible.conj
            hSequenceSpace hCodeNatural)
          hSequenceDomainBound)
        hSequenceValueBound)
      hTraceExists

theorem proof_sequence_code_step_condition_with_ids_admissible
    (sequence trace index rowCode : SetTerm)
    (rowTraceId rowIndexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hTrace : Term.Admissible trace SetSort.set)
    (hIndex : Term.Admissible index SetSort.set)
    (hRowCode : Term.Admissible rowCode SetSort.set) :
    Formula.Admissible
      (proof_sequence_code_step_condition_with_ids
        sequence trace index rowCode rowTraceId rowIndexId) := by
  have hSequenceAt :=
    function_application_term_admissible
      sequence index hSequence hIndex
  have hRowEncoding :=
    nat_sequence_code_condition_with_ids_admissible
      (sequence ·ₘ index) rowCode rowTraceId rowIndexId
      hSequenceAt hRowCode
  have hSuccessorIndex :=
    successor_term_admissible index hIndex
  have hTraceNext :=
    function_application_term_admissible
      trace (Sₘ(index)) hTrace hSuccessorIndex
  have hTraceAt :=
    function_application_term_admissible
      trace index hTrace hIndex
  have hPair :=
    ordered_pair_term_admissible
      (trace ·ₘ index) rowCode hTraceAt hRowCode
  have hPairCode :=
    godel_pairing_term_admissible
      ⟨trace ·ₘ index, rowCode⟩ₘ hPair
  have hSuccessorCode :=
    successor_term_admissible
      (godel_pairₘ(⟨trace ·ₘ index, rowCode⟩ₘ))
      hPairCode
  have hStepEquation :=
    Formula.Admissible.equal hTraceNext hSuccessorCode
  simpa [proof_sequence_code_step_condition_with_ids] using
    Formula.Admissible.conj hRowEncoding hStepEquation

theorem proof_sequence_code_condition_with_ids_admissible
    (sequence code : SetTerm)
    (traceId indexId rowCodeId rowTraceId rowIndexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (proof_sequence_code_condition_with_ids
        sequence code traceId indexId rowCodeId rowTraceId rowIndexId) := by
  have hFormulaSequenceSpace :=
    finite_sequence_space_term_admissible
      FormulaCodeₘ formula_code_set_term_admissible
  have hSequenceSpace :=
    membership_formula_admissible hSequence hFormulaSequenceSpace
  have hCodeNatural :=
    membership_formula_admissible hCode omega_term_admissible
  have hSequenceDomainBound :=
    sequence_domain_code_bound_admissible
      sequence code hSequence hCode
  have hNaturalSequenceSpace :=
    finite_sequence_space_term_admissible
      ωₘ omega_term_admissible
  have hTrace :
      Term.Admissible (x#traceId) SetSort.set :=
    set_variable_admissible traceId
  have hTraceSpace :=
    membership_formula_admissible hTrace hNaturalSequenceSpace
  have hTraceDomain :=
    domain_term_admissible (x#traceId) hTrace
  have hSequenceDomain :=
    domain_term_admissible sequence hSequence
  have hSuccessorSequenceDomain :=
    successor_term_admissible
      (domₘ(sequence)) hSequenceDomain
  have hDomainEquation :=
    Formula.Admissible.equal
      hTraceDomain hSuccessorSequenceDomain
  have hTraceValueBound :=
    sequence_trace_code_bound_with_id_admissible
      (x#traceId) code indexId hTrace hCode
  have hZero := finite_numeral_term_admissible 0
  have hTraceZero :=
    function_application_term_admissible
      (x#traceId) (numₘ(0)) hTrace hZero
  have hInitialEquation :=
    Formula.Admissible.equal hTraceZero hZero
  have hIndex :
      Term.Admissible (x#indexId) SetSort.set :=
    set_variable_admissible indexId
  have hIndexDomain :=
    membership_formula_admissible hIndex hSequenceDomain
  have hRowCode :
      Term.Admissible (x#rowCodeId) SetSort.set :=
    set_variable_admissible rowCodeId
  have hStep :=
    proof_sequence_code_step_condition_with_ids_admissible
      sequence (x#traceId) (x#indexId) (x#rowCodeId)
      rowTraceId rowIndexId
      hSequence hTrace hIndex hRowCode
  have hRowCodeBound :=
    membership_formula_admissible hRowCode hCode
  have hRowCodeExists :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set rowCodeId
      (Formula.Admissible.conj hRowCodeBound hStep)
  have hAllSteps :=
    Formula.Admissible.forall_closeFreeAt
      SetSort.set indexId
      (Formula.Admissible.imp hIndexDomain hRowCodeExists)
  have hTraceFinal :=
    function_application_term_admissible
      (x#traceId) (domₘ(sequence))
      hTrace hSequenceDomain
  have hFinalEquation :=
    Formula.Admissible.equal hCode hTraceFinal
  have hTraceBody :=
    Formula.Admissible.conj
      hTraceSpace
      (Formula.Admissible.conj
        (Formula.Admissible.conj
          hDomainEquation hTraceValueBound)
        (Formula.Admissible.conj
          hInitialEquation
          (Formula.Admissible.conj
            hAllSteps hFinalEquation)))
  have hTraceExists :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set traceId hTraceBody
  simpa [proof_sequence_code_condition_with_ids] using
      Formula.Admissible.conj
      (Formula.Admissible.conj
        (Formula.Admissible.conj
          hSequenceSpace hCodeNatural)
        hSequenceDomainBound)
      hTraceExists

/-! ## 自由变量支持 -/

/-- 自然数序列编码自身的 trace 绑定号不会泄漏到自由支持。 -/
theorem nat_sequence_code_condition_with_ids_trace_fresh
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
  have hValueFresh :
      (SetSort.set, traceId) ∉
        Formula.freeSupport
          (nat_sequence_value_code_bound_with_id
            sequence code indexId) := by
    unfold nat_sequence_value_code_bound_with_id
    by_cases hIds : traceId = indexId
    · subst indexId
      exact Formula.not_mem_freeSupport_closeFreeAt
        (σ := signature) SetSort.set traceId 0 _
    · apply Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      intro hMember
      simp only [Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList, List.append_nil] at hMember
      rcases List.mem_cons.mp hMember with hIndex | hMember
      · exact hIds (congrArg Prod.snd hIndex)
      · rcases List.mem_append.mp hMember with
          hSequenceLeft | hMember
        · exact hTraceFreshSequence hSequenceLeft
        · rcases List.mem_append.mp hMember with
            hSequenceRight | hCodeMember
          · rcases List.mem_append.mp hSequenceRight with
              hSequence | hIndex'
            · exact hTraceFreshSequence hSequence
            · exact hIds
                (congrArg Prod.snd
                  (List.mem_singleton.mp hIndex'))
          · exact hTraceFreshCode hCodeMember
  have hSpaceCodeFresh :
      (SetSort.set, traceId) ∉
        Formula.freeSupport
          ((sequence ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
            (code ∈ₘ ωₘ)) := by
    simp only [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.append_nil]
    exact List.not_mem_append hTraceFreshSequence
      hTraceFreshCode
  have hDomainFresh :
      (SetSort.set, traceId) ∉
        Formula.freeSupport
          (sequence_domain_code_bound sequence code) := by
    simp only [sequence_domain_code_bound,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, List.append_nil]
    exact List.not_mem_append
      hTraceFreshSequence hTraceFreshCode
  have hSpaceDomainFresh :
      (SetSort.set, traceId) ∉
        Formula.freeSupport
          (((sequence ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
              (code ∈ₘ ωₘ)) ∧ₘ
            sequence_domain_code_bound sequence code) := by
    simp only [Formula.freeSupport]
    exact List.not_mem_append
      hSpaceCodeFresh hDomainFresh
  have hPrefixFresh :
      (SetSort.set, traceId) ∉
        Formula.freeSupport
          ((((sequence ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
              (code ∈ₘ ωₘ)) ∧ₘ
            sequence_domain_code_bound sequence code) ∧ₘ
            nat_sequence_value_code_bound_with_id
              sequence code indexId) := by
    simp only [Formula.freeSupport]
    exact List.not_mem_append
      hSpaceDomainFresh hValueFresh
  have hTraceExistsFresh :
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
    exact Formula.not_mem_freeSupport_closeFreeAt
      (σ := signature) SetSort.set traceId 0
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
  simp only [Formula.freeSupport]
  exact List.not_mem_append hPrefixFresh hTraceExistsFresh

/-- 轨迹值界只保留轨迹、编码与索引绑定号的支持。 -/
theorem sequence_trace_code_bound_with_id_fresh_of_not_mem
    (trace code : SetTerm)
    (targetId indexId : FreeVarId)
    (hTargetFreshTrace :
      (SetSort.set, targetId) ∉ Term.freeSupport trace)
    (hTargetFreshCode :
      (SetSort.set, targetId) ∉ Term.freeSupport code)
    (hTargetNeIndex : targetId ≠ indexId) :
    (SetSort.set, targetId) ∉
      Formula.freeSupport
        (sequence_trace_code_bound_with_id
          trace code indexId) := by
  unfold sequence_trace_code_bound_with_id
  apply Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
  have hTargetVarNeIndex :
      (SetSort.set, targetId) ≠
        (SetSort.set, indexId) := by
    intro hEquality
    exact hTargetNeIndex
      (congrArg Prod.snd hEquality)
  simp only [Formula.freeSupport, Term.freeSupport,
    Term.freeSupportList, List.append_nil]
  have hIndexFresh :
      (SetSort.set, targetId) ∉
        [(SetSort.set, indexId)] := by
    intro hMember
    exact hTargetVarNeIndex
      (List.mem_singleton.mp hMember)
  have hIndexTraceFresh :=
    List.not_mem_append hIndexFresh hTargetFreshTrace
  have hTraceIndexCodeFresh :=
    List.not_mem_append
      (List.not_mem_append hTargetFreshTrace hIndexFresh)
      hTargetFreshCode
  exact List.not_mem_append hIndexTraceFresh
    hTraceIndexCodeFresh

/-! ## 闭项替换 -/

/--
自然数序列编码关系逐参数保持捕获规避的闭项替换。

这里只要求替换项对该关系实际关闭的两个编号新鲜；不附加 quotation
或对象理论假设。
-/
theorem nat_sequence_code_condition_with_ids_substitute_closed
    (sequence code replacement sequenceResult codeResult : SetTerm)
    (sourceId traceId indexId : FreeVarId)
    (hSourceNeTrace : sourceId ≠ traceId)
    (hSourceNeIndex : sourceId ≠ indexId)
    (hReplacementClosed : Term.BoundClosed replacement)
    (hReplacementFreshTrace :
      (SetSort.set, traceId) ∉ Term.freeSupport replacement)
    (hReplacementFreshIndex :
      (SetSort.set, indexId) ∉ Term.freeSupport replacement)
    (hSequenceSubstitution :
      Term.substituteFree SetSort.set sourceId replacement sequence =
        sequenceResult)
    (hCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement code =
        codeResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (nat_sequence_code_condition_with_ids
          sequence code traceId indexId) =
      nat_sequence_code_condition_with_ids
        sequenceResult codeResult traceId indexId := by
  have hTraceCommute (body : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement
          (Formula.closeFreeAt SetSort.set traceId 0 body) =
        Formula.closeFreeAt SetSort.set traceId 0
          (Formula.substituteFree SetSort.set sourceId replacement body) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId traceId 0 replacement body
      hSourceNeTrace hReplacementClosed
      hReplacementFreshTrace).symm
  have hIndexCommute (body : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement
          (Formula.closeFreeAt SetSort.set indexId 0 body) =
        Formula.closeFreeAt SetSort.set indexId 0
          (Formula.substituteFree SetSort.set sourceId replacement body) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId indexId 0 replacement body
      hSourceNeIndex hReplacementClosed
      hReplacementFreshIndex).symm
  have hZeroFixed :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(0)) =
        numₘ(0) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  simp [nat_sequence_code_condition_with_ids,
    sequence_domain_code_bound,
    nat_sequence_value_code_bound_with_id,
    sequence_trace_code_bound_with_id,
    nat_sequence_code_step_condition,
    Formula.substituteFree, Term.substituteFree, set_variable,
    hSequenceSubstitution, hCodeSubstitution, hZeroFixed,
    Ne.symm hSourceNeTrace, Ne.symm hSourceNeIndex,
    hTraceCommute, hIndexCommute]

/--
证明序列单步关系逐参数保持捕获规避的闭项替换。

单步关系只在内层自然数序列条件中关闭 `rowTraceId` 与 `rowIndexId`，
因此这里只暴露这两个必要的新鲜性条件。
-/
theorem proof_sequence_code_step_condition_with_ids_substitute_closed
    (sequence trace index rowCode replacement
      sequenceResult traceResult indexResult rowCodeResult : SetTerm)
    (sourceId rowTraceId rowIndexId : FreeVarId)
    (hSourceNeRowTrace : sourceId ≠ rowTraceId)
    (hSourceNeRowIndex : sourceId ≠ rowIndexId)
    (hReplacementClosed : Term.BoundClosed replacement)
    (hReplacementFreshRowTrace :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport replacement)
    (hReplacementFreshRowIndex :
      (SetSort.set, rowIndexId) ∉ Term.freeSupport replacement)
    (hSequenceSubstitution :
      Term.substituteFree SetSort.set sourceId replacement sequence =
        sequenceResult)
    (hTraceSubstitution :
      Term.substituteFree SetSort.set sourceId replacement trace =
        traceResult)
    (hIndexSubstitution :
      Term.substituteFree SetSort.set sourceId replacement index =
        indexResult)
    (hRowCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement rowCode =
        rowCodeResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (proof_sequence_code_step_condition_with_ids
          sequence trace index rowCode rowTraceId rowIndexId) =
      proof_sequence_code_step_condition_with_ids
        sequenceResult traceResult indexResult rowCodeResult
        rowTraceId rowIndexId := by
  have hSequenceAtSubstitution :
      Term.substituteFree SetSort.set sourceId replacement
          (sequence ·ₘ index) =
        sequenceResult ·ₘ indexResult := by
    simp [Term.substituteFree,
      hSequenceSubstitution, hIndexSubstitution]
  have hInnerSubstitution :=
    nat_sequence_code_condition_with_ids_substitute_closed
      (sequence ·ₘ index) rowCode replacement
      (sequenceResult ·ₘ indexResult) rowCodeResult
      sourceId rowTraceId rowIndexId
      hSourceNeRowTrace hSourceNeRowIndex
      hReplacementClosed
      hReplacementFreshRowTrace
      hReplacementFreshRowIndex
      hSequenceAtSubstitution hRowCodeSubstitution
  simp [proof_sequence_code_step_condition_with_ids,
    Formula.substituteFree, Term.substituteFree,
    hTraceSubstitution,
    hIndexSubstitution, hRowCodeSubstitution,
    hInnerSubstitution]

/-- 证明序列末行条件逐参数保持自由变量替换。 -/
theorem proof_sequence_terminal_condition_substitute
    (sequence conclusion replacement
      sequenceResult conclusionResult : SetTerm)
    (sourceId : FreeVarId)
    (hSequenceSubstitution :
      Term.substituteFree SetSort.set sourceId replacement sequence =
        sequenceResult)
    (hConclusionSubstitution :
      Term.substituteFree SetSort.set sourceId replacement conclusion =
        conclusionResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (proof_sequence_terminal_condition sequence conclusion) =
      proof_sequence_terminal_condition
        sequenceResult conclusionResult := by
  simp [proof_sequence_terminal_condition,
    Formula.substituteFree, Term.substituteFree,
    hSequenceSubstitution, hConclusionSubstitution]

/--
公式序列编码关系逐参数保持捕获规避的闭项替换。

五个 freshness 条件恰好对应该关系关闭的五个局部编号。
-/
theorem proof_sequence_code_condition_with_ids_substitute_closed
    (sequence code replacement sequenceResult codeResult : SetTerm)
    (sourceId traceId indexId rowCodeId rowTraceId rowIndexId :
      FreeVarId)
    (hSourceNeTrace : sourceId ≠ traceId)
    (hSourceNeIndex : sourceId ≠ indexId)
    (hSourceNeRowCode : sourceId ≠ rowCodeId)
    (hSourceNeRowTrace : sourceId ≠ rowTraceId)
    (hSourceNeRowIndex : sourceId ≠ rowIndexId)
    (hReplacementClosed : Term.BoundClosed replacement)
    (hReplacementFreshTrace :
      (SetSort.set, traceId) ∉ Term.freeSupport replacement)
    (hReplacementFreshIndex :
      (SetSort.set, indexId) ∉ Term.freeSupport replacement)
    (hReplacementFreshRowCode :
      (SetSort.set, rowCodeId) ∉ Term.freeSupport replacement)
    (hReplacementFreshRowTrace :
      (SetSort.set, rowTraceId) ∉ Term.freeSupport replacement)
    (hReplacementFreshRowIndex :
      (SetSort.set, rowIndexId) ∉ Term.freeSupport replacement)
    (hSequenceSubstitution :
      Term.substituteFree SetSort.set sourceId replacement sequence =
        sequenceResult)
    (hCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement code =
        codeResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (proof_sequence_code_condition_with_ids
          sequence code traceId indexId rowCodeId rowTraceId rowIndexId) =
      proof_sequence_code_condition_with_ids
        sequenceResult codeResult
        traceId indexId rowCodeId rowTraceId rowIndexId := by
  have hCommute
      (closedId : FreeVarId)
      (hDistinct : sourceId ≠ closedId)
      (hFresh :
        (SetSort.set, closedId) ∉ Term.freeSupport replacement)
      (body : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement
          (Formula.closeFreeAt SetSort.set closedId 0 body) =
        Formula.closeFreeAt SetSort.set closedId 0
          (Formula.substituteFree SetSort.set sourceId replacement body) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId closedId 0 replacement body
      hDistinct hReplacementClosed hFresh).symm
  have hTraceCommute :=
    hCommute traceId hSourceNeTrace hReplacementFreshTrace
  have hIndexCommute :=
    hCommute indexId hSourceNeIndex hReplacementFreshIndex
  have hRowCodeCommute :=
    hCommute rowCodeId hSourceNeRowCode hReplacementFreshRowCode
  have hRowTraceCommute :=
    hCommute rowTraceId hSourceNeRowTrace hReplacementFreshRowTrace
  have hRowIndexCommute :=
    hCommute rowIndexId hSourceNeRowIndex hReplacementFreshRowIndex
  have hZeroFixed :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(0)) =
        numₘ(0) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  simp [proof_sequence_code_condition_with_ids,
    sequence_domain_code_bound,
    nat_sequence_value_code_bound_with_id,
    sequence_trace_code_bound_with_id,
    proof_sequence_code_step_condition_with_ids,
    nat_sequence_code_condition_with_ids,
    nat_sequence_code_step_condition,
    Formula.substituteFree, Term.substituteFree, set_variable,
    hSequenceSubstitution, hCodeSubstitution, hZeroFixed,
    Ne.symm hSourceNeTrace, Ne.symm hSourceNeIndex,
    Ne.symm hSourceNeRowCode, Ne.symm hSourceNeRowTrace,
    Ne.symm hSourceNeRowIndex,
    hTraceCommute, hIndexCommute, hRowCodeCommute,
    hRowTraceCommute, hRowIndexCommute]

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
