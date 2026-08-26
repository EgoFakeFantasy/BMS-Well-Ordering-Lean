import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateConditionRejection

/-!
# 单例逻辑证书 transcript 的终端反演

本模块只反演长度为一的逻辑证书 payload。由规范序列等式与
`dom certificateSequence = S(lastIndex)` 可知末索引只能为 `0`，进而终端证书
值只能是 payload 的唯一数值字段。整个接口只使用序列、定义域和二元等式关系，
不反演公式 trace，也不展开十二类基础 Hilbert 公理。
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
规范单例序列的定义域若是某个对象后继，则该对象只能等于 `0`。
-/
theorem fs_zfc_support_raw_logical_singleton_last_index_eq_zero
    {Γ : Context signature}
    (sequence lastIndex : SetTerm)
    (value : Nat)
    (hSequence :
      Term.Admissible sequence SetSort.set)
    (hLastIndex :
      Term.Admissible lastIndex SetSort.set)
    (hSequenceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence ≐ₘ standard_token_sequence [value])
    (hDomainSuccessor :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ Sₘ(lastIndex)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      lastIndex ≐ₘ numₘ(0) := by
  have hDomainEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ
          domₘ(standard_token_sequence [value]) :=
    domain_term_congr_of_equality
      sequence (standard_token_sequence [value])
      hSequence
      (standard_token_sequence_admissible [value])
      hSequenceEquality
  have hStandardDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(standard_token_sequence [value]) ≐ₘ
          numₘ(1) := by
    simpa using
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (fs_zfc_support_raw_derives_of_standard_sequence
          (standard_token_sequence_domain_eq_length [value]))
  have hDomainOne :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ numₘ(1) :=
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
        lastIndex
        (domₘ(sequence)) (Sₘ(lastIndex))
        hLastIndex
        (domain_term_admissible sequence hSequence)
        (successor_term_admissible lastIndex hLastIndex)
        hDomainSuccessor)
      hLastMemberSuccessor
  have hLastMemberOne :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        lastIndex ∈ₘ numₘ(1) :=
    FirstOrder.Derives.iffElimRight
      (membership_right_iff_of_equality
        lastIndex
        (domₘ(sequence)) (numₘ(1))
        hLastIndex
        (domain_term_admissible sequence hSequence)
        (finite_numeral_term_admissible 1)
        hDomainOne)
      hLastMemberDomain
  apply
    fs_zfc_support_raw_finite_numeral_member_elim_context
      1 lastIndex (lastIndex ≐ₘ numₘ(0))
      hLastIndex
      (Formula.Admissible.equal
        hLastIndex (finite_numeral_term_admissible 0))
      hLastMemberOne
  intro index hIndex
  have hIndexZero : index = 0 := by omega
  subst index
  exact FirstOrder.Derives.assumption (by simp)

/--
单例规范序列在其对象末索引处的值等于唯一 payload 数值。
-/
theorem fs_zfc_support_raw_logical_singleton_terminal_value
    {Γ : Context signature}
    (sequence lastIndex : SetTerm)
    (value : Nat)
    (hSequence :
      Term.Admissible sequence SetSort.set)
    (hLastIndex :
      Term.Admissible lastIndex SetSort.set)
    (hSequenceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence ≐ₘ standard_token_sequence [value])
    (hLastIndexZero :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        lastIndex ≐ₘ numₘ(0)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (sequence ·ₘ lastIndex) ≐ₘ numₘ(value) := by
  have hTerminalToStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (sequence ·ₘ lastIndex) ≐ₘ
          (standard_token_sequence [value] ·ₘ numₘ(0)) :=
    function_application_term_congr_of_equalities
      sequence (standard_token_sequence [value])
      lastIndex (numₘ(0))
      hSequence
      (standard_token_sequence_admissible [value])
      hLastIndex
      (finite_numeral_term_admissible 0)
      hSequenceEquality hLastIndexZero
  have hStandardValue :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (standard_token_sequence [value] ·ₘ numₘ(0)) ≐ₘ
          numₘ(value) := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
    exact fs_zfc_support_raw_derives_of_standard_sequence
      (standard_token_sequence_apply_getElem?
        [value] (by simp))
  exact Metatheory.Derives.equality_trans
    hTerminalToStandard hStandardValue

/--
对象自然数序列条件直接给出单例 transcript 的末索引和值。

序列唯一性先在空上下文中封装为蕴含，因此调用方上下文无需满足内部 trace
变量的新鲜性。
-/
theorem fs_zfc_support_raw_logical_singleton_terminal_inversion
    {Γ : Context signature}
    (sequence lastIndex : SetTerm)
    (value : Nat)
    (traceId indexId : FreeVarId)
    (hSequence :
      Term.Admissible sequence SetSort.set)
    (hLastIndex :
      Term.Admissible lastIndex SetSort.set)
    (hTraceNeIndex : traceId ≠ indexId)
    (hTraceFreshSequence :
      (SetSort.set, traceId) ∉ Term.freeSupport sequence)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉ Term.freeSupport sequence)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        nat_sequence_code_condition_with_ids
          sequence
          (numₘ(nat_sequence_code_value [value]))
          traceId indexId)
    (hDomainSuccessor :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ Sₘ(lastIndex)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
        lastIndex ≐ₘ numₘ(0) ∧ₘ
      (sequence ·ₘ lastIndex) ≐ₘ numₘ(value) := by
  have hSequenceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence ≐ₘ standard_token_sequence [value] :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (fs_zfc_support_raw_nat_sequence_condition_unique_imp
          sequence [value] traceId indexId
          hSequence hTraceNeIndex
          hTraceFreshSequence hIndexFreshSequence))
      hCondition
  have hLastIndexZero :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        lastIndex ≐ₘ numₘ(0) :=
    fs_zfc_support_raw_logical_singleton_last_index_eq_zero
      sequence lastIndex value
      hSequence hLastIndex
      hSequenceEquality hDomainSuccessor
  have hTerminalValue :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (sequence ·ₘ lastIndex) ≐ₘ numₘ(value) :=
    fs_zfc_support_raw_logical_singleton_terminal_value
      sequence lastIndex value
      hSequence hLastIndex
      hSequenceEquality hLastIndexZero
  exact FirstOrder.Derives.conjIntro
    hLastIndexZero hTerminalValue

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
