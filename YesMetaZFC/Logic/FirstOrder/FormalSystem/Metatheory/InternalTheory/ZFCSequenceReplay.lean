import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedReplay

/-!
# ZFC 有界自然数序列 checked replay

本模块把外部的规范自然数序列编码轨迹提升为对象层的
`nat_sequence_code_condition_with_ids` 证书。这里只处理有限、闭合的具体列表；
开放变量的 schema 装配仍由上层 verifier 组合。
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

/-! ## 有限 numeral 边界的等式运输 -/

/--
若两个对象项分别等于有限 numeral，且左数值不超过右数值，则左项属于右项的
后继。该接口把地面自然数边界运输回对象项，供所有有限 checked replay 共用。
-/
theorem fs_zfc_support_raw_member_successor_of_numeral_equalities
    (point bound : SetTerm)
    (pointValue boundValue : Nat)
    (hPoint : Term.Admissible point SetSort.set)
    (hBound : Term.Admissible bound SetSort.set)
    (hPointEquality :
      Derives fs_zfc_support_raw_theory [] (
        point ≐ₘ numₘ(pointValue)))
    (hBoundEquality :
      Derives fs_zfc_support_raw_theory [] (
        bound ≐ₘ numₘ(boundValue)))
    (hLe : pointValue ≤ boundValue) :
    Derives fs_zfc_support_raw_theory [] (
      point ∈ₘ Sₘ(bound)) := by
  have hPointNumeral :
      Term.Admissible (numₘ(pointValue)) SetSort.set :=
    finite_numeral_term_admissible pointValue
  have hBoundNumeral :
      Term.Admissible (numₘ(boundValue)) SetSort.set :=
    finite_numeral_term_admissible boundValue
  have hBoundSuccessor :
      Term.Admissible (Sₘ(bound)) SetSort.set :=
    successor_term_admissible bound hBound
  have hBoundNumeralSuccessor :
      Term.Admissible (Sₘ(numₘ(boundValue))) SetSort.set :=
    successor_term_admissible
      (numₘ(boundValue)) hBoundNumeral
  have hSuccessorEquality :
      Derives fs_zfc_support_raw_theory [] (
        Sₘ(bound) ≐ₘ Sₘ(numₘ(boundValue))) :=
    successor_term_congr_of_equality
      bound (numₘ(boundValue))
      hBound hBoundNumeral hBoundEquality
  have hGround :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(pointValue) ∈ₘ Sₘ(numₘ(boundValue))) := by
    simpa [finite_numeral_term, successor_term] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_sequence_finite_numeral_mem_of_lt
          pointValue (boundValue + 1)
          (Nat.lt_succ_of_le hLe))
  have hNumeralAtBound :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(pointValue) ∈ₘ Sₘ(bound)) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(pointValue))
        (Sₘ(bound))
        (Sₘ(numₘ(boundValue)))
        hPointNumeral hBoundSuccessor
        hBoundNumeralSuccessor hSuccessorEquality)
      hGround
  exact FirstOrder.Derives.iffElimLeft
    (membership_left_iff_of_equality
      point (numₘ(pointValue)) (Sₘ(bound))
      hPoint hPointNumeral hBoundSuccessor
      hPointEquality)
    hNumeralAtBound

/-! ## 规范轨迹的单步回放 -/

private theorem fs_zfc_support_raw_nat_sequence_step_at_numeral
    (tokens : List Nat)
    (index item : Nat)
    (hIndex : index < tokens.length)
    (hItem : tokens[index]? = some item) :
    Derives fs_zfc_support_raw_theory [] (
      let trace := standard_token_sequence (nat_sequence_code_trace tokens)
      let sequence := standard_token_sequence tokens
      (trace ·ₘ Sₘ(numₘ(index))) ≐ₘ
        Sₘ(godel_pairₘ(
          ⟨trace ·ₘ numₘ(index), sequence ·ₘ numₘ(index)⟩ₘ))) := by
  let trace : SetTerm :=
    standard_token_sequence (nat_sequence_code_trace tokens)
  let sequence : SetTerm :=
    standard_token_sequence tokens
  let prefixCode : Nat :=
    nat_sequence_code_from 0 (tokens.take index)
  have hTraceAdmissible :
      Term.Admissible trace SetSort.set := by
    simpa [trace] using
      standard_token_sequence_admissible
        (nat_sequence_code_trace tokens)
  have hSequenceAdmissible :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence] using
      standard_token_sequence_admissible tokens
  have hPrefixAdmissible :
      Term.Admissible (numₘ(prefixCode)) SetSort.set :=
    finite_numeral_term_admissible prefixCode
  have hItemAdmissible :
      Term.Admissible (numₘ(item)) SetSort.set :=
    finite_numeral_term_admissible item
  have hIndexAdmissible :
      Term.Admissible (numₘ(index)) SetSort.set :=
    finite_numeral_term_admissible index
  have hCurrentStd :
      Derives standard_sequence_semantics_theory [] (
        trace ·ₘ numₘ(index) ≐ₘ numₘ(prefixCode)) := by
    have hTraceGet :
        (nat_sequence_code_trace tokens)[index]? =
          some prefixCode := by
      simpa [prefixCode] using
        nat_sequence_code_trace_from_getElem?
          0 tokens index (Nat.le_of_lt hIndex)
    simpa [trace] using
      standard_token_sequence_apply_getElem?
        (nat_sequence_code_trace tokens) hTraceGet
  have hNextStd :
      Derives standard_sequence_semantics_theory [] (
        trace ·ₘ numₘ(index + 1) ≐ₘ
          numₘ(nat_sequence_code_step prefixCode item)) := by
    have hTraceGet :
        (nat_sequence_code_trace tokens)[index + 1]? =
          some (nat_sequence_code_step prefixCode item) := by
      simpa [prefixCode] using
        nat_sequence_code_trace_step tokens index item hItem
    simpa [trace] using
      standard_token_sequence_apply_getElem?
        (nat_sequence_code_trace tokens) hTraceGet
  have hSourceStd :
      Derives standard_sequence_semantics_theory [] (
        sequence ·ₘ numₘ(index) ≐ₘ numₘ(item)) := by
    simpa [sequence] using
      standard_token_sequence_apply_getElem? tokens hItem
  have hCurrent :
      Derives fs_zfc_support_raw_theory [] (
        trace ·ₘ numₘ(index) ≐ₘ numₘ(prefixCode)) :=
    fs_zfc_support_raw_derives_of_standard_sequence hCurrentStd
  have hNext :
      Derives fs_zfc_support_raw_theory [] (
        trace ·ₘ numₘ(index + 1) ≐ₘ
          numₘ(nat_sequence_code_step prefixCode item)) :=
    fs_zfc_support_raw_derives_of_standard_sequence hNextStd
  have hSource :
      Derives fs_zfc_support_raw_theory [] (
        sequence ·ₘ numₘ(index) ≐ₘ numₘ(item)) :=
    fs_zfc_support_raw_derives_of_standard_sequence hSourceStd
  have hTraceCurrent :
      Term.Admissible (trace ·ₘ numₘ(index)) SetSort.set :=
    function_application_term_admissible
      trace (numₘ(index)) hTraceAdmissible hIndexAdmissible
  have hSequenceCurrent :
      Term.Admissible (sequence ·ₘ numₘ(index)) SetSort.set :=
    function_application_term_admissible
      sequence (numₘ(index)) hSequenceAdmissible hIndexAdmissible
  have hPairLeft :
      Term.Admissible
        (⟨trace ·ₘ numₘ(index), sequence ·ₘ numₘ(index)⟩ₘ)
        SetSort.set :=
    ordered_pair_term_admissible
      (trace ·ₘ numₘ(index)) (sequence ·ₘ numₘ(index))
      hTraceCurrent hSequenceCurrent
  have hPairRight :
      Term.Admissible
        (⟨numₘ(prefixCode), numₘ(item)⟩ₘ)
        SetSort.set :=
    ordered_pair_term_admissible
      (numₘ(prefixCode)) (numₘ(item))
      hPrefixAdmissible hItemAdmissible
  have hPairEquality :
      Derives fs_zfc_support_raw_theory [] (
        ⟨trace ·ₘ numₘ(index), sequence ·ₘ numₘ(index)⟩ₘ ≐ₘ
          ⟨numₘ(prefixCode), numₘ(item)⟩ₘ) :=
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      (fun left right => ⟨left, right⟩ₘ)
      (fun left right hLeft hRight =>
        ordered_pair_term_admissible left right hLeft hRight)
      (by intros; simp [Term.substituteFree])
      (trace ·ₘ numₘ(index)) (numₘ(prefixCode))
      (sequence ·ₘ numₘ(index)) (numₘ(item))
      hTraceCurrent hPrefixAdmissible
      hSequenceCurrent hItemAdmissible
      hCurrent hSource
  have hGodelPairEquality :
      Derives fs_zfc_support_raw_theory [] (
        godel_pairₘ(
          ⟨trace ·ₘ numₘ(index), sequence ·ₘ numₘ(index)⟩ₘ) ≐ₘ
          godel_pairₘ(⟨numₘ(prefixCode), numₘ(item)⟩ₘ)) :=
    Metatheory.Derives.unary_term_constructor_congr_of_equality
      (fun pair => godel_pairₘ(pair))
      (fun pair hPair => godel_pairing_term_admissible pair hPair)
      (by intros; simp [Term.substituteFree])
      (⟨trace ·ₘ numₘ(index), sequence ·ₘ numₘ(index)⟩ₘ)
      (⟨numₘ(prefixCode), numₘ(item)⟩ₘ)
      hPairLeft hPairRight hPairEquality
  have hGodelPairValue :
      Derives fs_zfc_support_raw_theory [] (
        godel_pairₘ(⟨numₘ(prefixCode), numₘ(item)⟩ₘ) ≐ₘ
          numₘ(godel_pair_value prefixCode item)) :=
    fs_zfc_support_raw_godel_pair_value_eq prefixCode item
  have hPairValue :
      Derives fs_zfc_support_raw_theory [] (
        godel_pairₘ(
          ⟨trace ·ₘ numₘ(index), sequence ·ₘ numₘ(index)⟩ₘ) ≐ₘ
          numₘ(godel_pair_value prefixCode item)) :=
    Metatheory.Derives.equality_trans
      hGodelPairEquality
      hGodelPairValue
  have hSuccessorPairValue :
      Derives fs_zfc_support_raw_theory [] (
        Sₘ(godel_pairₘ(
          ⟨trace ·ₘ numₘ(index), sequence ·ₘ numₘ(index)⟩ₘ)) ≐ₘ
          Sₘ(numₘ(godel_pair_value prefixCode item))) :=
    successor_term_congr_of_equality
      (godel_pairₘ(
        ⟨trace ·ₘ numₘ(index), sequence ·ₘ numₘ(index)⟩ₘ))
      (numₘ(godel_pair_value prefixCode item))
      (godel_pairing_term_admissible
        (⟨trace ·ₘ numₘ(index), sequence ·ₘ numₘ(index)⟩ₘ)
        hPairLeft)
      (finite_numeral_term_admissible
        (godel_pair_value prefixCode item))
      hPairValue
  have hNextValue :
      Derives fs_zfc_support_raw_theory [] (
        trace ·ₘ numₘ(index + 1) ≐ₘ
          Sₘ(numₘ(godel_pair_value prefixCode item))) := by
    simpa [nat_sequence_code_step, finite_numeral_term,
      successor_term] using hNext
  have hSuccessorPairValueBack :
      Derives fs_zfc_support_raw_theory [] (
        Sₘ(numₘ(godel_pair_value prefixCode item)) ≐ₘ
          Sₘ(godel_pairₘ(
            ⟨trace ·ₘ numₘ(index), sequence ·ₘ numₘ(index)⟩ₘ))) :=
    Metatheory.Derives.equality_symm
      hSuccessorPairValue
  have hResult :=
    Metatheory.Derives.equality_trans
      hNextValue hSuccessorPairValueBack
  simpa [trace, sequence, finite_numeral_term,
    successor_term] using hResult

private theorem fs_zfc_support_raw_nat_sequence_step_of_index_equality
    (tokens : List Nat)
    (index : Nat)
    (point : SetTerm)
    (hPoint : Term.Admissible point SetSort.set)
    (hIndex : index < tokens.length) :
    Derives fs_zfc_support_raw_theory [] (
      (point ≐ₘ numₘ(index)) ⟶ₘ
        nat_sequence_code_step_condition
          (standard_token_sequence tokens)
          (standard_token_sequence (nat_sequence_code_trace tokens))
          point) := by
  let trace : SetTerm :=
    standard_token_sequence (nat_sequence_code_trace tokens)
  let sequence : SetTerm :=
    standard_token_sequence tokens
  let parameter : FreeVarId := 390
  let body : SetFormula :=
    nat_sequence_code_step_condition
      sequence trace (x#parameter)
  let equality : SetFormula :=
    point ≐ₘ numₘ(index)
  let Γ : Context signature :=
    [equality]
  have hTrace :
      Term.Admissible trace SetSort.set := by
    simpa [trace] using
      standard_token_sequence_admissible
        (nat_sequence_code_trace tokens)
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence] using
      standard_token_sequence_admissible tokens
  have hBodyAdmissible :
      Formula.Admissible body := by
    simpa [body] using
      nat_sequence_code_step_condition_admissible
        sequence trace (x#parameter)
        hSequence hTrace
        (set_variable_admissible parameter)
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] equality := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ)
        (φ := equality)
        (by simp [Γ]))
  have hTraceFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement trace =
        trace := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport trace = [] by
      simp [trace]]
    simp
  have hSequenceFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement sequence =
        sequence := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport sequence = [] by
      simp [sequence]]
    simp
  have hIff :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (sort := SetSort.set)
      (eigen := parameter)
      (left := point)
      (right := numₘ(index))
      (body := body)
      hEquality
  have hTransport :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (nat_sequence_code_step_condition
          sequence trace point) ↔ₘ
          nat_sequence_code_step_condition
            sequence trace (numₘ(index)) := by
    simpa [body, equality, nat_sequence_code_step_condition,
      Formula.substituteFree,
      Term.substituteFree, set_variable,
      hTraceFixed, hSequenceFixed] using hIff
  have hConcrete :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        nat_sequence_code_step_condition
          sequence trace (numₘ(index)) := by
    exact FirstOrder.Derives.context_weaken
      (Γ := [])
      (Δ := Γ)
      (by simp [Γ])
      (by
        simpa [trace, sequence] using
          fs_zfc_support_raw_nat_sequence_step_at_numeral
            tokens index (tokens[index])
            hIndex
            (List.getElem?_eq_some_iff.mpr
              ⟨hIndex, rfl⟩))
  simpa [Γ, equality, trace, sequence,
    nat_sequence_code_step_condition] using
    FirstOrder.Derives.iffElimLeft hTransport hConcrete

/-! ## 有限定义域上的逐点全称装配 -/

/-- 把有限定义域上的具体等式分支提升为对象层全称条件。 -/
theorem fs_zfc_support_raw_finite_domain_forall_imp
    (sequence : SetTerm)
    (bound : Nat)
    (indexId : FreeVarId)
    (conclusion : SetFormula)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hConclusion : Formula.Admissible conclusion)
    (hDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(sequence) ≐ₘ numₘ(bound)))
    (hBranch :
      ∀ index, index < bound →
        Derives fs_zfc_support_raw_theory [] (
          ((x#indexId ≐ₘ numₘ(index)) ⟶ₘ conclusion))) :
    Derives fs_zfc_support_raw_theory [] (
      ∀ₘ[SetSort.set, indexId],
        ((x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ conclusion) ) := by
  let point : SetTerm := x#indexId
  have hPoint :
      Term.Admissible point SetSort.set := by
    simpa [point] using set_variable_admissible indexId
  have hDomainIff :
      Derives fs_zfc_support_raw_theory [] (
        (point ∈ₘ domₘ(sequence)) ↔ₘ
          (point ∈ₘ numₘ(bound))) :=
    membership_right_iff_of_equality
      point (domₘ(sequence)) (numₘ(bound))
      hPoint
      (domain_term_admissible sequence hSequence)
      (finite_numeral_term_admissible bound)
      hDomain
  have hNumeralCondition :
      Derives fs_zfc_support_raw_theory [] (
        (stdseq_numeral_member_condition bound point) ⟶ₘ
          conclusion) :=
    stdseq_numeral_member_condition_elim_of_theory
      bound point conclusion
      (fun index hIndex => by
        simpa [point] using hBranch index hIndex)
  have hDomainToNumeral :
      Derives fs_zfc_support_raw_theory [] (
        (point ∈ₘ domₘ(sequence)) ⟶ₘ
          (point ∈ₘ numₘ(bound))) := by
    nd_apply FirstOrder.Derives.impIntro
    have hMember :
        [point ∈ₘ domₘ(sequence)] ⊢ₘ[fs_zfc_support_raw_theory]
          point ∈ₘ domₘ(sequence) :=
      .assumption (by simp)
    exact FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken_cons hDomainIff)
      hMember
  have hNumeralToCondition :
      Derives fs_zfc_support_raw_theory [] (
        (point ∈ₘ numₘ(bound)) ⟶ₘ
          (stdseq_numeral_member_condition bound point)) := by
    have hNumeralIff :
        Derives fs_zfc_support_raw_theory [] (
          (point ∈ₘ numₘ(bound)) ↔ₘ
            stdseq_numeral_member_condition bound point) :=
      fs_zfc_support_raw_derives_of_standard_sequence
        (stdseq_numeral_member_iff bound point hPoint)
    nd_apply FirstOrder.Derives.impIntro
    have hMember :
        [point ∈ₘ numₘ(bound)] ⊢ₘ[fs_zfc_support_raw_theory]
          point ∈ₘ numₘ(bound) :=
      .assumption (by simp)
    exact FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken_cons hNumeralIff)
      hMember
  have hDomainCondition :
      Derives fs_zfc_support_raw_theory [] (
        (point ∈ₘ domₘ(sequence)) ⟶ₘ conclusion) :=
    Metatheory.Derives.imp_trans
      hDomainToNumeral
      (Metatheory.Derives.imp_trans
        hNumeralToCondition hNumeralCondition)
  have hTheoryFresh :
      ∀ formula, fs_zfc_support_raw_theory formula →
        (SetSort.set, indexId) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  have hGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := fs_zfc_support_raw_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := indexId)
      hTheoryFresh
      (by simp)
      hDomainCondition
  simpa [point] using hGeneralized

/-! ## 规范序列编码的有限界 -/

/-- 已知具体定义域时，把长度上界提升为对象层编码域界。 -/
theorem fs_zfc_support_raw_sequence_domain_code_bound_of_domain_eq
    (sequence : SetTerm)
    (length code : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(sequence) ≐ₘ numₘ(length)))
    (hLength : length ≤ code) :
    Derives fs_zfc_support_raw_theory [] (
      sequence_domain_code_bound sequence (numₘ(code))) := by
  have hNumeral :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(length) ∈ₘ numₘ(code + 1)) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_sequence_finite_numeral_mem_of_lt
        length (code + 1) (by omega))
  have hTransport :=
    membership_left_iff_of_equality
      (domₘ(sequence)) (numₘ(length)) (numₘ(code + 1))
      (domain_term_admissible sequence hSequence)
      (finite_numeral_term_admissible length)
      (finite_numeral_term_admissible (code + 1))
      hDomain
  simpa [sequence_domain_code_bound, finite_numeral_term,
    successor_term] using
    FirstOrder.Derives.iffElimLeft hTransport hNumeral

/-- 规范自然数序列的外部逐项上界可在对象层逐点回放。 -/
theorem fs_zfc_support_raw_standard_token_sequence_value_code_bound_with_id
    (tokens : List Nat)
    (code : Nat)
    (indexId : FreeVarId)
    (hValues :
      ∀ token, token ∈ tokens → token < code) :
    Derives fs_zfc_support_raw_theory [] (
      nat_sequence_value_code_bound_with_id
        (standard_token_sequence tokens) (numₘ(code)) indexId) := by
  let sequence : SetTerm := standard_token_sequence tokens
  let point : SetTerm := x#indexId
  let conclusion : SetFormula :=
    (sequence ·ₘ point) ∈ₘ numₘ(code)
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence] using standard_token_sequence_admissible tokens
  have hPoint :
      Term.Admissible point SetSort.set := by
    simpa [point] using set_variable_admissible indexId
  have hConclusion :
      Formula.Admissible conclusion := by
    simpa [conclusion] using
      membership_formula_admissible
        (function_application_term_admissible
          sequence point hSequence hPoint)
        (finite_numeral_term_admissible code)
  have hDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(sequence) ≐ₘ numₘ(tokens.length)) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (by simpa [sequence] using
        standard_token_sequence_domain_eq_length tokens)
  have hAll :=
    fs_zfc_support_raw_finite_domain_forall_imp
      sequence tokens.length indexId conclusion
      hSequence hConclusion hDomain
      (fun index hIndex => by
        let token : Nat := tokens[index]
        let equality : SetFormula := point ≐ₘ numₘ(index)
        let Γ : Context signature := [equality]
        nd_apply FirstOrder.Derives.impIntro
        have hEquality :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              point ≐ₘ numₘ(index) := by
          simpa [Γ, equality] using
            (FirstOrder.Derives.assumption
              (T := fs_zfc_support_raw_theory)
              (Γ := Γ)
              (φ := equality)
              (by simp [Γ]))
        have hArgument :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              (sequence ·ₘ point) ≐ₘ
                (sequence ·ₘ numₘ(index)) :=
          function_application_term_congr_argument_of_equality
            sequence point (numₘ(index))
            hSequence hPoint
            (finite_numeral_term_admissible index)
            hEquality
        have hAtNumeral :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              (sequence ·ₘ numₘ(index)) ≐ₘ numₘ(token) :=
          FirstOrder.Derives.context_weaken
            (Γ := [])
            (Δ := Γ)
            (by simp [Γ])
            (by
              simpa [sequence, token] using
                fs_zfc_support_raw_derives_of_standard_sequence
                  (standard_token_sequence_apply_getElem?
                    tokens
                    (List.getElem?_eq_some_iff.mpr
                      ⟨hIndex, rfl⟩)))
        have hValueEquality :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              (sequence ·ₘ point) ≐ₘ numₘ(token) :=
          Metatheory.Derives.equality_trans
            hArgument hAtNumeral
        have hTokenMember :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              numₘ(token) ∈ₘ numₘ(code) :=
          FirstOrder.Derives.context_weaken
            (Γ := [])
            (Δ := Γ)
            (by simp [Γ])
            (fs_zfc_support_raw_derives_of_standard_sequence
              (standard_sequence_finite_numeral_mem_of_lt
                token code
                (hValues token (by
                  simp [token]))))
        exact FirstOrder.Derives.iffElimLeft
          (membership_left_iff_of_equality
            (sequence ·ₘ point) (numₘ(token)) (numₘ(code))
            (function_application_term_admissible
              sequence point hSequence hPoint)
            (finite_numeral_term_admissible token)
            (finite_numeral_term_admissible code)
            hValueEquality)
          hTokenMember)
  simpa [nat_sequence_value_code_bound_with_id,
    conclusion, sequence, point] using hAll

/-- 规范编码轨迹的外部非严格上界可在对象层逐点回放。 -/
theorem fs_zfc_support_raw_standard_token_sequence_trace_code_bound_with_id
    (tokens : List Nat)
    (code : Nat)
    (indexId : FreeVarId)
    (hValues :
      ∀ token, token ∈ tokens → token ≤ code) :
    Derives fs_zfc_support_raw_theory [] (
      sequence_trace_code_bound_with_id
        (standard_token_sequence tokens) (numₘ(code)) indexId) := by
  have hBound :=
    fs_zfc_support_raw_standard_token_sequence_value_code_bound_with_id
      tokens (code + 1) indexId
      (fun token hToken => by
        have := hValues token hToken
        omega)
  simpa [sequence_trace_code_bound_with_id,
    nat_sequence_value_code_bound_with_id,
    finite_numeral_term, successor_term] using hBound

/-! ## 完整有限序列条件 -/

theorem fs_zfc_support_raw_nat_sequence_code_condition_with_ids
    (tokens : List Nat)
    (traceId indexId : FreeVarId)
    (hIds : traceId ≠ indexId) :
    Derives fs_zfc_support_raw_theory [] (
      nat_sequence_code_condition_with_ids
        (standard_token_sequence tokens)
        (numₘ(nat_sequence_code_value tokens))
        traceId indexId) := by
  let sequence : SetTerm :=
    standard_token_sequence tokens
  let code : SetTerm :=
    numₘ(nat_sequence_code_value tokens)
  let trace : SetTerm :=
    standard_token_sequence (nat_sequence_code_trace tokens)
  let index : SetTerm :=
    x#indexId
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence] using
      standard_token_sequence_admissible tokens
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      finite_numeral_term_admissible
        (nat_sequence_code_value tokens)
  have hTrace :
      Term.Admissible trace SetSort.set := by
    simpa [trace] using
      standard_token_sequence_admissible
        (nat_sequence_code_trace tokens)
  have hSequenceSpace :
      Derives fs_zfc_support_raw_theory [] (
        sequence ∈ₘ seq_spaceₘ(ωₘ)) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (by simpa [sequence] using
        standard_token_sequence_mem_sequence_space tokens)
  have hCodeOmega :
      Derives fs_zfc_support_raw_theory [] (code ∈ₘ ωₘ) :=
    let hCodeOmegaStd :
        Derives standard_sequence_semantics_theory [] (
          numₘ(nat_sequence_code_value tokens) ∈ₘ ωₘ) :=
      standard_sequence_finite_numeral_mem_omega
        (nat_sequence_code_value tokens)
    fs_zfc_support_raw_derives_of_standard_sequence
      (by simpa [code] using hCodeOmegaStd)
  have hSequenceDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(sequence) ≐ₘ numₘ(tokens.length)) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (by simpa [sequence] using
        standard_token_sequence_domain_eq_length tokens)
  have hSequenceDomainBound :
      Derives fs_zfc_support_raw_theory [] (
        sequence_domain_code_bound sequence code) := by
    simpa [code] using
      fs_zfc_support_raw_sequence_domain_code_bound_of_domain_eq
        sequence tokens.length (nat_sequence_code_value tokens)
        hSequence hSequenceDomain
        (nat_sequence_length_le_code tokens)
  have hSequenceValueBound :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_value_code_bound_with_id
          sequence code indexId) := by
    simpa [sequence, code] using
      fs_zfc_support_raw_standard_token_sequence_value_code_bound_with_id
        tokens (nat_sequence_code_value tokens) indexId
        (fun token hToken =>
          mem_lt_nat_sequence_code_value hToken)
  have hTraceDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(trace) ≐ₘ
          numₘ((nat_sequence_code_trace tokens).length)) :=
    let hTraceDomainStd :
        Derives standard_sequence_semantics_theory [] (
          domₘ(standard_token_sequence
            (nat_sequence_code_trace tokens)) ≐ₘ
            numₘ((nat_sequence_code_trace tokens).length)) :=
      standard_token_sequence_domain_eq_length
        (nat_sequence_code_trace tokens)
    fs_zfc_support_raw_derives_of_standard_sequence
      (by simpa [trace] using hTraceDomainStd)
  have hTraceDomainNumeral :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(trace) ≐ₘ Sₘ(numₘ(tokens.length))) := by
    simpa [nat_sequence_code_trace_length,
      finite_numeral_term, successor_term] using hTraceDomain
  have hSequenceDomainSymm :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(tokens.length) ≐ₘ domₘ(sequence)) :=
    Metatheory.Derives.equality_symm
      hSequenceDomain
  have hSuccessorDomain :
      Derives fs_zfc_support_raw_theory [] (
        Sₘ(numₘ(tokens.length)) ≐ₘ Sₘ(domₘ(sequence))) :=
    successor_term_congr_of_equality
      (numₘ(tokens.length)) (domₘ(sequence))
      (finite_numeral_term_admissible tokens.length)
      (domain_term_admissible sequence hSequence)
      hSequenceDomainSymm
  have hTraceDomainFinal :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(trace) ≐ₘ Sₘ(domₘ(sequence))) :=
    Metatheory.Derives.equality_trans
      hTraceDomainNumeral hSuccessorDomain
  have hInitial :
      Derives fs_zfc_support_raw_theory [] (
        trace ·ₘ numₘ(0) ≐ₘ numₘ(0)) := by
    have hTraceZero :
        (nat_sequence_code_trace tokens)[0]? = some 0 := by
      cases tokens <;>
        simp [nat_sequence_code_trace, nat_sequence_code_trace_from]
    have hInitialStd :
        Derives standard_sequence_semantics_theory [] (
          standard_token_sequence (nat_sequence_code_trace tokens) ·ₘ
              numₘ(0) ≐ₘ numₘ(0)) :=
      standard_token_sequence_apply_getElem?
        (nat_sequence_code_trace tokens) hTraceZero
    exact fs_zfc_support_raw_derives_of_standard_sequence
      (by simpa [trace] using hInitialStd)
  have hPoint :
      Term.Admissible index SetSort.set :=
    set_variable_admissible indexId
  have hDomainIff :
      Derives fs_zfc_support_raw_theory [] (
        (index ∈ₘ domₘ(sequence)) ↔ₘ
          (index ∈ₘ numₘ(tokens.length))) :=
    membership_right_iff_of_equality
      index (domₘ(sequence)) (numₘ(tokens.length))
      hPoint
      (domain_term_admissible sequence hSequence)
      (finite_numeral_term_admissible tokens.length)
      hSequenceDomain
  let stepConclusion : SetFormula :=
    nat_sequence_code_step_condition sequence trace index
  have hStepConclusion :
      Formula.Admissible stepConclusion := by
    simpa [stepConclusion] using
      nat_sequence_code_step_condition_admissible
        sequence trace index hSequence hTrace hPoint
  have hNumeralStep :
      Derives fs_zfc_support_raw_theory [] (
        (stdseq_numeral_member_condition tokens.length index) ⟶ₘ
          stepConclusion) := by
    simpa [stepConclusion] using
      stdseq_numeral_member_condition_elim_of_theory
        tokens.length index stepConclusion
        (fun branch hBranch => by
          simpa [stepConclusion] using
            fs_zfc_support_raw_nat_sequence_step_of_index_equality
              tokens branch index hPoint hBranch)
  have hDomainStep :
      Derives fs_zfc_support_raw_theory [] (
        (index ∈ₘ domₘ(sequence)) ⟶ₘ stepConclusion) :=
    by
      have hDomainToNumeral :
          Derives fs_zfc_support_raw_theory [] (
            (index ∈ₘ domₘ(sequence)) ⟶ₘ
              (index ∈ₘ numₘ(tokens.length))) := by
        nd_apply FirstOrder.Derives.impIntro
        have hMember :
            [index ∈ₘ domₘ(sequence)] ⊢ₘ[fs_zfc_support_raw_theory]
              index ∈ₘ domₘ(sequence) :=
          .assumption (by simp)
        exact FirstOrder.Derives.iffElimRight
          (FirstOrder.Derives.context_weaken_cons hDomainIff)
          hMember
      have hNumeralToCondition :
          Derives fs_zfc_support_raw_theory [] (
            (index ∈ₘ numₘ(tokens.length)) ⟶ₘ
              (stdseq_numeral_member_condition tokens.length index)) := by
        have hNumeralIff :
            Derives fs_zfc_support_raw_theory [] (
              (index ∈ₘ numₘ(tokens.length)) ↔ₘ
                stdseq_numeral_member_condition tokens.length index) :=
          fs_zfc_support_raw_derives_of_standard_sequence
            (stdseq_numeral_member_iff tokens.length index hPoint)
        nd_apply FirstOrder.Derives.impIntro
        have hMember :
            [index ∈ₘ numₘ(tokens.length)]
              ⊢ₘ[fs_zfc_support_raw_theory]
                index ∈ₘ numₘ(tokens.length) :=
          .assumption (by simp)
        exact FirstOrder.Derives.iffElimRight
          (FirstOrder.Derives.context_weaken_cons hNumeralIff)
          hMember
      exact Metatheory.Derives.imp_trans
        hDomainToNumeral
        (Metatheory.Derives.imp_trans hNumeralToCondition hNumeralStep)
  have hAllSteps :
      Derives fs_zfc_support_raw_theory [] (
        ∀ₘ[SetSort.set],
            (bₛ#0 ∈ₘ domₘ(sequence)) ⟶ₘ
            nat_sequence_code_step_condition
              sequence trace (bₛ#0)) := by
    have hTheoryFresh :
        ∀ formula, fs_zfc_support_raw_theory formula →
          (SetSort.set, indexId) ∉ Formula.freeSupport formula := by
      intro formula hFormula
      rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
      exact List.not_mem_nil
    have hSequenceFreeSupport :
        Term.freeSupport sequence = [] := by
      simp [sequence]
    have hTraceFreeSupport :
        Term.freeSupport trace = [] := by
      simp [trace]
    have hSequenceFresh :
        (SetSort.set, indexId) ∉ Term.freeSupport sequence := by
      rw [hSequenceFreeSupport]
      exact List.not_mem_nil
    have hTraceFresh :
        (SetSort.set, indexId) ∉ Term.freeSupport trace := by
      rw [hTraceFreeSupport]
      exact List.not_mem_nil
    have hSequenceClose :
        Term.closeFreeAt SetSort.set indexId 0 sequence = sequence :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set indexId 0 sequence hSequence.2 hSequenceFresh
    have hTraceClose :
        Term.closeFreeAt SetSort.set indexId 0 trace = trace :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set indexId 0 trace hTrace.2 hTraceFresh
    have hGeneralized :=
      FirstOrder.Derives.forall_intro
        (T := fs_zfc_support_raw_theory)
        (Γ := [])
        (sort := SetSort.set)
        (eigen := indexId)
        hTheoryFresh
        (by simp)
        hDomainStep
    simpa [index, stepConclusion, nat_sequence_code_step_condition,
      Formula.closeFreeAt,
      Formula.next_depth, Term.closeFreeAt, set_variable,
      hSequenceClose, hTraceClose] using hGeneralized
  have hTraceFinal :
      Derives fs_zfc_support_raw_theory [] (
        trace ·ₘ numₘ(tokens.length) ≐ₘ code) := by
    have hTraceLast :
        (nat_sequence_code_trace tokens)[tokens.length]? =
          some (nat_sequence_code_value tokens) :=
      nat_sequence_code_trace_last tokens
    simpa [trace, code] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_token_sequence_apply_getElem?
          (nat_sequence_code_trace tokens) hTraceLast)
  have hTraceAtDomain :
      Derives fs_zfc_support_raw_theory [] (
        trace ·ₘ numₘ(tokens.length) ≐ₘ
          trace ·ₘ domₘ(sequence)) :=
    function_application_term_congr_argument_of_equality
      trace (numₘ(tokens.length)) (domₘ(sequence))
      hTrace
      (finite_numeral_term_admissible tokens.length)
      (domain_term_admissible sequence hSequence)
      hSequenceDomainSymm
  have hFinal :
      Derives fs_zfc_support_raw_theory [] (
        code ≐ₘ trace ·ₘ domₘ(sequence)) := by
    have hTraceFinalSymm :
        Derives fs_zfc_support_raw_theory [] (
          code ≐ₘ trace ·ₘ numₘ(tokens.length)) :=
      Metatheory.Derives.equality_symm
        hTraceFinal
    exact Metatheory.Derives.equality_trans
      hTraceFinalSymm hTraceAtDomain
  have hTraceSpace :
      Derives fs_zfc_support_raw_theory [] (
        trace ∈ₘ seq_spaceₘ(ωₘ)) :=
    let hTraceSpaceStd :
        Derives standard_sequence_semantics_theory [] (
          standard_token_sequence (nat_sequence_code_trace tokens) ∈ₘ
            seq_spaceₘ(ωₘ)) :=
      standard_token_sequence_mem_sequence_space
        (nat_sequence_code_trace tokens)
    fs_zfc_support_raw_derives_of_standard_sequence
      (by simpa [trace] using hTraceSpaceStd)
  have hTraceValueBound :
      Derives fs_zfc_support_raw_theory [] (
        sequence_trace_code_bound_with_id
          trace code indexId) := by
    simpa [trace, code] using
      fs_zfc_support_raw_standard_token_sequence_trace_code_bound_with_id
        (nat_sequence_code_trace tokens)
        (nat_sequence_code_value tokens)
        indexId
        (fun value hValue =>
          trace_mem_le_nat_sequence_code_value hValue)
  let stepBody : SetFormula :=
    (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
      nat_sequence_code_step_condition
        sequence (x#traceId) (x#indexId)
  let body : SetFormula :=
    (((x#traceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
        (domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence)))) ∧ₘ
      sequence_trace_code_bound_with_id
        (x#traceId) code indexId) ∧ₘ
      (((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
        ((∀ₘ[SetSort.set, indexId],
            stepBody) ∧ₘ
          (code ≐ₘ (x#traceId ·ₘ domₘ(sequence)))))
  have hTraceFreeSupport :
      Term.freeSupport trace = [] := by
    simp [trace]
  have hTraceFresh :
      (SetSort.set, indexId) ∉ Term.freeSupport trace := by
    rw [hTraceFreeSupport]
    exact List.not_mem_nil
  have hSequenceFreeSupport :
      Term.freeSupport sequence = [] := by
    simp [sequence]
  have hSequenceFresh :
      (SetSort.set, indexId) ∉ Term.freeSupport sequence := by
    rw [hSequenceFreeSupport]
    exact List.not_mem_nil
  have hSequenceClose :
      Term.closeFreeAt SetSort.set indexId 0 sequence = sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 sequence hSequence.2 hSequenceFresh
  have hSequenceSubstitute :
      Term.substituteFree SetSort.set traceId trace sequence = sequence :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set traceId trace sequence (by
        rw [hSequenceFreeSupport]
        exact List.not_mem_nil)
  have hTraceClose :
      Term.closeFreeAt SetSort.set indexId 0 trace = trace :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 trace hTrace.2 hTraceFresh
  have hZeroSubstitute :
      Term.substituteFree SetSort.set traceId trace numₘ(0) = numₘ(0) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set traceId trace (numₘ(0)) (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hCodeFresh :
      (SetSort.set, indexId) ∉ Term.freeSupport code := by
    rw [show Term.freeSupport code = [] by
      simpa [code] using
        finite_numeral_term_freeSupport
          (nat_sequence_code_value tokens)]
    exact List.not_mem_nil
  have hCodeClose :
      Term.closeFreeAt SetSort.set indexId 0 code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 code hCode.2 hCodeFresh
  have hCodeSubstitute :
      Term.substituteFree SetSort.set traceId trace code = code :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set traceId trace code (by
        rw [show Term.freeSupport code = [] by
          simpa [code] using
            finite_numeral_term_freeSupport
              (nat_sequence_code_value tokens)]
        exact List.not_mem_nil)
  have hInnerComm :
      Formula.closeFreeAt SetSort.set indexId 0
          (Formula.substituteFree SetSort.set traceId trace stepBody) =
        Formula.substituteFree SetSort.set traceId trace
          (Formula.closeFreeAt SetSort.set indexId 0 stepBody) :=
    Formula.closeFreeAt_substituteFree_comm
      SetSort.set traceId indexId 0 trace stepBody
      hIds hTrace.2 hTraceFresh
  have hAllStepsSubstituted :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set traceId trace
          (Formula.forallE SetSort.set
            (Formula.closeFreeAt SetSort.set indexId 0 stepBody))) := by
    simp only [Formula.substituteFree]
    rw [← hInnerComm]
    simpa [stepBody, Formula.substituteFree, Formula.closeFreeAt,
      Formula.next_depth, nat_sequence_code_step_condition,
      Term.closeFreeAt, Term.substituteFree, set_variable,
      trace, sequence, hIds, Ne.symm hIds,
      hSequenceClose, hSequenceSubstitute, hTraceClose] using hAllSteps
  unfold nat_sequence_code_condition_with_ids
  apply FirstOrder.Derives.conjIntro
    (FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjIntro
          hSequenceSpace hCodeOmega)
        hSequenceDomainBound)
      hSequenceValueBound)
  nd_apply FirstOrder.Derives.exists_intro_substituted
    traceId (witness := trace)
  simpa [body, stepBody, Formula.substituteFree, Formula.closeFreeAt,
    sequence_trace_code_bound_with_id,
    Formula.next_depth, nat_sequence_code_step_condition,
    Term.closeFreeAt, Term.substituteFree, set_variable,
    trace, sequence, code, hIds, Ne.symm hIds,
    hSequenceClose, hSequenceSubstitute, hTraceClose,
    hZeroSubstitute, hCodeClose, hCodeSubstitute] using
    (FirstOrder.Derives.conjIntro
      hTraceSpace
      (FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjIntro
          hTraceDomainFinal hTraceValueBound)
        (FirstOrder.Derives.conjIntro
          hInitial
          (FirstOrder.Derives.conjIntro
            hAllStepsSubstituted hFinal))))

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
