import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceRejection

/-!
# 自然数序列条件的对象层否定回放

本模块把任意满足对象层自然数编码条件的序列见证反演为规范序列。
它只消费有限数码成员消去和 `ZFCSequenceRejection` 的递归唯一性；
不引入模型、标准模型或额外的内部理论层。
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

/-! ## 序列空间的函数部分 -/

/--
任意非空目标集上的有限序列空间成员都是函数。

该投影只展开有限序列空间与映射谓词的对象层定义合同；目标集非空是
`seq_space` 定义合同本身所需的最弱前提。
-/
theorem fs_zfc_support_raw_sequence_space_function_of_target
    {Γ : Context signature}
    (target sequence : SetTerm)
    (hTarget : Term.Admissible target SetSort.set)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hTargetNonempty :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        target ≠ₘ ∅ₘ)
    (hSpace :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence ∈ₘ seq_spaceₘ(target)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      is_function_formula sequence := by
  let sequenceSpace : SetTerm := seq_spaceₘ(target)
  let conclusion : SetFormula := is_function_formula sequence
  let freshnessBasis : List SetFormula :=
    [conclusion, target ≐ₘ target, sequence ≐ₘ sequence]
  let witnessId : FreeVarId :=
    FreshVariable.fresh_id SetSort.set freshnessBasis
  let witness : SetTerm := x#witnessId
  let witnessCondition : SetFormula :=
    (witness ∈ₘ ωₘ) ∧ₘ
      is_mapping_formula sequence witness target
  have hSequenceSpace :
      Term.Admissible sequenceSpace SetSort.set := by
    simpa [sequenceSpace] using
      finite_sequence_space_term_admissible
        target hTarget
  have hConclusion :
      Formula.Admissible conclusion := by
    simpa [conclusion] using
      is_function_formula_admissible hSequence
  have hWitness :
      Term.Admissible witness SetSort.set := by
    simpa [witness] using
      set_variable_admissible witnessId
  have hWitnessCondition :
      Formula.Admissible witnessCondition := by
    simpa [witnessCondition] using
      Formula.Admissible.conj
        (membership_formula_admissible
          hWitness omega_term_admissible)
        (is_mapping_formula_admissible
          hSequence hWitness hTarget)
  have hWitnessFreshTarget :
      (SetSort.set, witnessId) ∉
        Term.freeSupport target := by
    dsimp [witnessId, freshnessBasis]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m
        (sort := SetSort.set)
        (formulas := [
          conclusion, target ≐ₘ target,
          sequence ≐ₘ sequence])
        (formula := target ≐ₘ target)
        (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hWitnessFreshSequence :
      (SetSort.set, witnessId) ∉
        Term.freeSupport sequence := by
    dsimp [witnessId, freshnessBasis]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m
        (sort := SetSort.set)
        (formulas := [
          conclusion, target ≐ₘ target,
          sequence ≐ₘ sequence])
        (formula := sequence ≐ₘ sequence)
        (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hWitnessFreshConclusion :
      (SetSort.set, witnessId) ∉
        Formula.freeSupport conclusion := by
    dsimp [witnessId, freshnessBasis]
    exact
      FreshVariable.fresh_id_not_mem_m
        (sort := SetSort.set)
        (formulas := [
          conclusion, target ≐ₘ target,
          sequence ≐ₘ sequence])
        (formula := conclusion)
        (by simp)
  have hWitnessCloseTarget :
      Term.closeFreeAt SetSort.set witnessId 0 target =
        target :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set witnessId 0 target
      hTarget.2 hWitnessFreshTarget
  have hWitnessCloseSequence :
      Term.closeFreeAt SetSort.set witnessId 0 sequence =
        sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set witnessId 0 sequence
      hSequence.2 hWitnessFreshSequence
  have hPoint :
      Derives fs_zfc_support_raw_theory [] (
        witnessCondition ⟶ₘ conclusion) := by
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature := [witnessCondition]
    have hWitnessConditionAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          witnessCondition :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hMapping :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          is_mapping_formula sequence witness target := by
      simpa [witnessCondition] using
        FirstOrder.Derives.conjElimRight
          hWitnessConditionAt
    have hMappingDefinition :
        Derives fs_zfc_support_raw_theory [] (
          is_mapping_formula sequence witness target ⟶ₘ
            is_mapping_condition sequence witness target) :=
      FirstOrder.Derives.theory_weaken
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_mapping_predicate
            hFormula)
        (is_mapping_implies_condition
          sequence witness target
          hSequence hWitness hTarget)
    have hMappingCondition :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          is_mapping_condition sequence witness target :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := [])
          (Δ := Δ)
          (by simp [Δ])
          hMappingDefinition)
        hMapping
    simpa [conclusion] using
      FirstOrder.Derives.conjElimLeft
        hMappingCondition
  have hTheoryFresh :
      ∀ formula, fs_zfc_support_raw_theory formula →
        (SetSort.set, witnessId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  have hLiftRaw :=
    Metatheory.Derives.exists_imp_of_imp
      (T := fs_zfc_support_raw_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := witnessId)
      hTheoryFresh
      (by
        intro formula hFormula
        cases hFormula)
      hWitnessFreshConclusion
      hPoint
  have hFiniteToFunction :
      Derives fs_zfc_support_raw_theory [] (
        finite_sequence_member_condition target sequence ⟶ₘ
          conclusion) := by
    simpa [finite_sequence_member_condition,
      witnessCondition, witness, conclusion,
      Formula.closeFreeAt, Term.closeFreeAt,
      set_variable, set_bound_variable,
      hWitnessCloseTarget, hWitnessCloseSequence] using
      hLiftRaw
  have hContract :
      Derives fs_zfc_support_raw_theory [] (
        finite_sequence_space_definition_instance
          target sequenceSpace) :=
    FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_finite_sequence_space
          hFormula)
      (finite_sequence_space_definition_instance_derives
        target sequenceSpace hTarget hSequenceSpace)
  have hSpaceIff :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (sequenceSpace ≐ₘ seq_spaceₘ(target)) ↔ₘ
          finite_sequence_space_spec
            target sequenceSpace :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := [])
        (Δ := Γ)
        (by
          intro formula hFormula
          simp at hFormula)
        (by simpa [sequenceSpace] using hContract))
      hTargetNonempty
  have hSpaceSpec :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_space_spec
          target sequenceSpace :=
    FirstOrder.Derives.iffElimRight hSpaceIff
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) sequenceSpace)
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := sequence) hSpaceSpec
  have hTargetOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term target =
        target :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term target hTarget.2
  have hSequenceSpaceOpen
      (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term sequenceSpace =
        sequenceSpace :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term sequenceSpace
      hSequenceSpace.2
  have hAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (sequence ∈ₘ sequenceSpace) ↔ₘ
          finite_sequence_member_condition
            target sequence := by
    simpa [finite_sequence_space_spec,
      finite_sequence_member_condition,
      Formula.openAt, Formula.next_depth,
      Term.openAt, hTargetOpen,
      hSequenceSpaceOpen] using hAtRaw
  have hFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_member_condition
          target sequence :=
    FirstOrder.Derives.iffElimRight
      hAt
      (by simpa [sequenceSpace] using hSpace)
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := [])
      (Δ := Γ)
      (by
        intro formula hFormula
        simp at hFormula)
      hFiniteToFunction)
    hFinite

theorem fs_zfc_support_raw_sequence_space_function
    {Γ : Context signature}
    (sequence : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hSpace :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence ∈ₘ seq_spaceₘ(ωₘ)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      is_function_formula sequence := by
  have hTargetNonempty :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ωₘ ≠ₘ ∅ₘ :=
      (FirstOrder.Derives.context_weaken
        (Γ := [])
        (Δ := Γ)
        (by
          intro ψ hψ
          simp at hψ)
        (fs_zfc_support_raw_derives_of_standard_sequence
          GodelQuotation.standard_sequence_omega_ne_empty))
  exact fs_zfc_support_raw_sequence_space_function_of_target
    ωₘ sequence omega_term_admissible hSequence
    hTargetNonempty hSpace

/-! ## 编码轨迹体 -/

/-- 自然数序列编码条件中由最外层存在量词关闭的轨迹体。 -/
private def nat_sequence_rejection_trace_body
    (sequence code : SetTerm)
    (traceId indexId : FreeVarId) : SetFormula :=
  (x#traceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
    (((domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
        sequence_trace_code_bound_with_id
          (x#traceId) code indexId) ∧ₘ
      ((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
      ((∀ₘ[SetSort.set, indexId],
          (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
            nat_sequence_code_step_condition
              sequence (x#traceId) (x#indexId)) ∧ₘ
        (code ≐ₘ (x#traceId ·ₘ domₘ(sequence)))))

private theorem nat_sequence_rejection_trace_body_admissible
    (sequence code : SetTerm)
    (traceId indexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible
      (nat_sequence_rejection_trace_body
        sequence code traceId indexId) := by
  unfold nat_sequence_rejection_trace_body
  prove_admissible

/-! ## 自然数序列条件的结构投影 -/

/-- 将自然数序列条件一次性投影为其五个可消费部分。 -/
theorem fs_zfc_support_raw_nat_sequence_code_condition_parts
    {Γ : Context signature}
    (sequence code : SetTerm)
    (traceId indexId : FreeVarId)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        nat_sequence_code_condition_with_ids
          sequence code traceId indexId) :
    (Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence ∈ₘ seq_spaceₘ(ωₘ)) ∧
      (Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code ∈ₘ ωₘ) ∧
      (Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence_domain_code_bound sequence code) ∧
      (Γ ⊢ₘ[fs_zfc_support_raw_theory]
        nat_sequence_value_code_bound_with_id
          sequence code indexId) ∧
      (Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, traceId],
          (x#traceId ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
            (((domₘ(x#traceId) ≐ₘ Sₘ(domₘ(sequence))) ∧ₘ
                sequence_trace_code_bound_with_id
                  (x#traceId) code indexId) ∧ₘ
              ((x#traceId ·ₘ numₘ(0)) ≐ₘ numₘ(0)) ∧ₘ
              ((∀ₘ[SetSort.set, indexId],
                  (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
                    nat_sequence_code_step_condition
                      sequence (x#traceId) (x#indexId)) ∧ₘ
                (code ≐ₘ (x#traceId ·ₘ domₘ(sequence)))))) := by
  have hLeft :=
    FirstOrder.Derives.conjElimLeft hCondition
  have hTrace :=
    FirstOrder.Derives.conjElimRight hCondition
  have hLeft₁ :=
    FirstOrder.Derives.conjElimLeft hLeft
  have hValue :=
    FirstOrder.Derives.conjElimRight hLeft
  have hLeft₂ :=
    FirstOrder.Derives.conjElimLeft hLeft₁
  have hDomain :=
    FirstOrder.Derives.conjElimRight hLeft₁
  have hSequenceCode :=
    FirstOrder.Derives.conjElimLeft hLeft₂
  have hCode :=
    FirstOrder.Derives.conjElimRight hLeft₂
  exact ⟨
    hSequenceCode,
    ⟨hCode,
      ⟨hDomain,
        ⟨hValue, hTrace⟩⟩⟩⟩

/-! ## 回放数据到规范序列 -/

/-- 将已经打开的对象层回放数据收束为规范 token 序列。 -/
theorem fs_zfc_support_raw_nat_sequence_code_replay_of_data
    {Γ : Context signature}
    (sequence trace : SetTerm)
    (tokens : List Nat)
    (length bound : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hTrace : Term.Admissible trace SetSort.set)
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
          nat_sequence_code_step_condition
            sequence trace (numₘ(index)))
    (hValueBound :
      ∀ index, index < length →
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          (sequence ·ₘ numₘ(index)) ∈ₘ numₘ(bound))
    (hTraceBound :
      ∀ index, index ≤ length →
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          (trace ·ₘ numₘ(index)) ∈ₘ numₘ(bound + 1))
    (hFinal :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(nat_sequence_code_value tokens) ≐ₘ
          (trace ·ₘ numₘ(length))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      sequence ≐ₘ standard_token_sequence tokens := by
  have hUnique :=
    fs_zfc_support_raw_nat_sequence_code_prefix_unique
      sequence trace tokens length bound
      hSequence hTrace hZero hStep hValueBound hTraceBound hFinal
  have hDomainTokens :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ numₘ(tokens.length) :=
    Metatheory.Derives.equality_trans
      hDomain hUnique.1
  apply stdtok_source_eq_of_function_domain_pointwise
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (fun _ hFormula =>
      fs_zfc_support_raw_contains_standard_sequence_semantics
        hFormula)
    (fun _ hFormula =>
      fs_zfc_support_raw_theory_sentence hFormula)
    sequence tokens hSequence hFunction hDomainTokens
  intro index token hGet
  rcases List.getElem?_eq_some_iff.mp hGet with
    ⟨hIndex, rfl⟩
  simpa using hUnique.2 index hIndex

/-! ## 有限定义域上的全称式实例化 -/

/-- 由标准长度定义域等式得到任意有效 numeral 的定义域成员关系。 -/
theorem fs_zfc_support_raw_numeral_mem_domain_of_domain_eq
    {Γ : Context signature}
    (sequence : SetTerm)
    (length index : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ numₘ(length))
    (hIndex : index < length) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      numₘ(index) ∈ₘ domₘ(sequence) := by
  have hNumeral :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(index) ∈ₘ numₘ(length) :=
    FirstOrder.Derives.context_weaken
      (Γ := [])
      (Δ := Γ)
      (by
        intro ψ hψ
        simp at hψ)
      (fs_zfc_support_raw_derives_of_standard_sequence
        (standard_sequence_finite_numeral_mem_of_lt
          index length hIndex))
  exact FirstOrder.Derives.iffElimLeft
    (membership_right_iff_of_equality
      (numₘ(index)) (domₘ(sequence)) (numₘ(length))
      (finite_numeral_term_admissible index)
      (domain_term_admissible sequence hSequence)
      (finite_numeral_term_admissible length)
      hDomain)
    hNumeral

/-- 把对象层序列值界全称式实例化到一个有效 numeral。 -/
theorem fs_zfc_support_raw_nat_sequence_value_bound_at
    {Γ : Context signature}
    (sequence code : SetTerm)
    (indexId : FreeVarId)
    (length index : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCode : Term.Admissible code SetSort.set)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉ Term.freeSupport sequence)
    (hIndexFreshCode :
      (SetSort.set, indexId) ∉ Term.freeSupport code)
    (hDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ numₘ(length))
    (hBound :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        nat_sequence_value_code_bound_with_id
          sequence code indexId)
    (hIndex : index < length) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (sequence ·ₘ numₘ(index)) ∈ₘ code := by
  have hSequenceClose :
      Term.closeFreeAt SetSort.set indexId 0 sequence =
        sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 sequence
      hSequence.2 hIndexFreshSequence
  have hCodeClose :
      Term.closeFreeAt SetSort.set indexId 0 code =
        code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 code
      hCode.2 hIndexFreshCode
  have hSequenceOpen :
      Term.openAt SetSort.set 0 (numₘ(index)) sequence =
        sequence :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (numₘ(index)) sequence hSequence.2
  have hCodeOpen :
      Term.openAt SetSort.set 0 (numₘ(index)) code =
        code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (numₘ(index)) code hCode.2
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := numₘ(index)) hBound
  have hAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (numₘ(index) ∈ₘ domₘ(sequence)) ⟶ₘ
          ((sequence ·ₘ numₘ(index)) ∈ₘ code) := by
    simpa [nat_sequence_value_code_bound_with_id,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Term.openAt, Term.closeFreeAt,
      set_variable, hSequenceClose, hCodeClose,
      hSequenceOpen, hCodeOpen] using hAtRaw
  exact FirstOrder.Derives.impElim hAt
    (fs_zfc_support_raw_numeral_mem_domain_of_domain_eq
      sequence length index hSequence hDomain hIndex)

/-- 把对象层编码递归全称式实例化到一个有效 numeral。 -/
theorem fs_zfc_support_raw_nat_sequence_step_at
    {Γ : Context signature}
    (sequence trace : SetTerm)
    (indexId : FreeVarId)
    (length index : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hTrace : Term.Admissible trace SetSort.set)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉ Term.freeSupport sequence)
    (hIndexFreshTrace :
      (SetSort.set, indexId) ∉ Term.freeSupport trace)
    (hDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ numₘ(length))
    (hSteps :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[SetSort.set, indexId],
          (x#indexId ∈ₘ domₘ(sequence)) ⟶ₘ
            nat_sequence_code_step_condition
              sequence trace (x#indexId))
    (hIndex : index < length) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      nat_sequence_code_step_condition
        sequence trace (numₘ(index)) := by
  have hSequenceClose :
      Term.closeFreeAt SetSort.set indexId 0 sequence =
        sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 sequence
      hSequence.2 hIndexFreshSequence
  have hTraceClose :
      Term.closeFreeAt SetSort.set indexId 0 trace =
        trace :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 trace
      hTrace.2 hIndexFreshTrace
  have hSequenceOpen :
      Term.openAt SetSort.set 0 (numₘ(index)) sequence =
        sequence :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (numₘ(index)) sequence hSequence.2
  have hTraceOpen :
      Term.openAt SetSort.set 0 (numₘ(index)) trace =
        trace :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (numₘ(index)) trace hTrace.2
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := numₘ(index)) hSteps
  have hAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (numₘ(index) ∈ₘ domₘ(sequence)) ⟶ₘ
          nat_sequence_code_step_condition
            sequence trace (numₘ(index)) := by
    simpa [nat_sequence_code_step_condition,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Term.openAt, Term.closeFreeAt,
      set_variable, hSequenceClose, hTraceClose,
      hSequenceOpen, hTraceOpen] using hAtRaw
  exact FirstOrder.Derives.impElim hAt
    (fs_zfc_support_raw_numeral_mem_domain_of_domain_eq
      sequence length index hSequence hDomain hIndex)

/-- 把编码轨迹值界实例化到其标准长度定义域中的一个 numeral。 -/
theorem fs_zfc_support_raw_sequence_trace_bound_at
    {Γ : Context signature}
    (trace code : SetTerm)
    (indexId : FreeVarId)
    (length index : Nat)
    (hTrace : Term.Admissible trace SetSort.set)
    (hCode : Term.Admissible code SetSort.set)
    (hIndexFreshTrace :
      (SetSort.set, indexId) ∉ Term.freeSupport trace)
    (hIndexFreshCode :
      (SetSort.set, indexId) ∉ Term.freeSupport code)
    (hDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(trace) ≐ₘ numₘ(length))
    (hBound :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence_trace_code_bound_with_id
          trace code indexId)
    (hIndex : index < length) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (trace ·ₘ numₘ(index)) ∈ₘ Sₘ(code) := by
  have hSuccessorCode :
      Term.Admissible (Sₘ(code)) SetSort.set :=
    successor_term_admissible code hCode
  have hIndexFreshSuccessor :
      (SetSort.set, indexId) ∉
        Term.freeSupport (Sₘ(code)) := by
    simpa [successor_term, Term.freeSupport,
      Term.freeSupportList] using hIndexFreshCode
  have hValueBound :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        nat_sequence_value_code_bound_with_id
          trace (Sₘ(code)) indexId := by
    simpa [sequence_trace_code_bound_with_id,
      nat_sequence_value_code_bound_with_id] using hBound
  exact fs_zfc_support_raw_nat_sequence_value_bound_at
    trace (Sₘ(code)) indexId length index
    hTrace hSuccessorCode
    hIndexFreshTrace hIndexFreshSuccessor
    hDomain hValueBound hIndex

/-! ## 自然数序列条件的规范唯一性 -/

/--
已知最终码等于规范 numeral 时，对象层自然数序列编码条件唯一决定序列。

新鲜性假设只表达两个对象量词编号确实不捕获调用方项或局部上下文；
它们不携带任何证明论强度。
-/
theorem fs_zfc_support_raw_nat_sequence_code_condition_unique_of_code_equality
    {Γ : Context signature}
    (sequence code : SetTerm)
    (tokens : List Nat)
    (traceId indexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCode : Term.Admissible code SetSort.set)
    (hTraceNeIndex : traceId ≠ indexId)
    (hTraceFreshSequence :
      (SetSort.set, traceId) ∉ Term.freeSupport sequence)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉ Term.freeSupport sequence)
    (hIndexFreshCode :
      (SetSort.set, indexId) ∉ Term.freeSupport code)
    (hTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport formula)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        nat_sequence_code_condition_with_ids
          sequence code traceId indexId)
    (hCodeEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code ≐ₘ numₘ(nat_sequence_code_value tokens)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      sequence ≐ₘ standard_token_sequence tokens := by
  let bound : Nat := nat_sequence_code_value tokens
  have hParts :=
    fs_zfc_support_raw_nat_sequence_code_condition_parts
      sequence code traceId indexId hCondition
  rcases hParts with
    ⟨hSpace, _, hDomainBound,
      hValueBound, hTraceExists⟩
  have hFunction :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        is_function_formula sequence :=
    fs_zfc_support_raw_sequence_space_function
      sequence hSequence hSpace
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
        (domₘ(sequence)) (Sₘ(code)) (Sₘ(numₘ(bound)))
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
      (sequence ≐ₘ standard_token_sequence tokens)
      (domain_term_admissible sequence hSequence)
      (Formula.Admissible.equal
        hSequence
        (standard_token_sequence_admissible tokens))
      hDomainMember
  intro length hLength
  let domainEquation : SetFormula :=
    domₘ(sequence) ≐ₘ numₘ(length)
  let Δ : Context signature :=
    domainEquation :: Γ
  change Δ ⊢ₘ[fs_zfc_support_raw_theory]
    sequence ≐ₘ standard_token_sequence tokens
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
    nat_sequence_rejection_trace_body
      sequence code traceId indexId
  have hTraceBodyAdmissible :
      Formula.Admissible traceBody := by
    simpa [traceBody] using
      nat_sequence_rejection_trace_body_admissible
        sequence code traceId indexId
        hSequence hCode
  have hTraceExistsAt :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[SetSort.set, traceId], traceBody := by
    simpa [traceBody, nat_sequence_rejection_trace_body] using
      FirstOrder.Derives.context_weaken_cons hTraceExists
  nd_apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Δ)
    (sort := SetSort.set)
    (eigen := traceId)
    (body := traceBody)
    (conclusion :=
      sequence ≐ₘ standard_token_sequence tokens)
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
  · simpa [Formula.freeSupport,
      standard_token_sequence_freeSupport_nil] using
      hTraceFreshSequence
  · exact hTraceExistsAt
  · let Ε : Context signature :=
      traceBody :: Δ
    change Ε ⊢ₘ[fs_zfc_support_raw_theory]
      sequence ≐ₘ standard_token_sequence tokens
    have hTraceBody :
        Ε ⊢ₘ[fs_zfc_support_raw_theory] traceBody :=
      FirstOrder.Derives.assumption
        (by simp [Ε])
    have hTraceTail :=
      FirstOrder.Derives.conjElimRight hTraceBody
    have hTraceDomainBound :=
      FirstOrder.Derives.conjElimLeft hTraceTail
    have hTraceRight :=
      FirstOrder.Derives.conjElimRight hTraceTail
    have hTraceSpace :=
      FirstOrder.Derives.conjElimLeft hTraceBody
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
    have hValueBoundAt :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          nat_sequence_value_code_bound_with_id
            sequence code indexId :=
      FirstOrder.Derives.context_weaken_cons
        (FirstOrder.Derives.context_weaken_cons hValueBound)
    have hCodeEqualityAt :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          code ≐ₘ numₘ(bound) :=
      FirstOrder.Derives.context_weaken_cons
        (FirstOrder.Derives.context_weaken_cons
          (by simpa [bound] using hCodeEquality))
    have hSuccessorCodeEqualityAt :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          Sₘ(code) ≐ₘ Sₘ(numₘ(bound)) :=
      successor_term_congr_of_equality
        code (numₘ(bound))
        hCode
        (finite_numeral_term_admissible bound)
        hCodeEqualityAt
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
    have hSuccessorDomain :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          Sₘ(domₘ(sequence)) ≐ₘ
            Sₘ(numₘ(length)) :=
      successor_term_congr_of_equality
        (domₘ(sequence)) (numₘ(length))
        (domain_term_admissible sequence hSequence)
        (finite_numeral_term_admissible length)
        hDomainAt
    have hTraceDomainSucc :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(x#traceId) ≐ₘ
            Sₘ(numₘ(length)) :=
      Metatheory.Derives.equality_trans
        hTraceDomainRaw hSuccessorDomain
    have hTraceDomain :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(x#traceId) ≐ₘ numₘ(length + 1) := by
      simpa [finite_numeral_term, successor_term] using
        hTraceDomainSucc
    have hStepAt :
        ∀ index, index < length →
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            nat_sequence_code_step_condition
              sequence (x#traceId) (numₘ(index)) := by
      intro index hIndex
      exact fs_zfc_support_raw_nat_sequence_step_at
        sequence (x#traceId) indexId length index
        hSequence hTrace
        hIndexFreshSequence hIndexFreshTrace
        hDomainAt hSteps hIndex
    have hValueAt :
        ∀ index, index < length →
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            (sequence ·ₘ numₘ(index)) ∈ₘ
              numₘ(bound) := by
      intro index hIndex
      have hAtCode :=
        fs_zfc_support_raw_nat_sequence_value_bound_at
          sequence code indexId length index
          hSequence hCode
          hIndexFreshSequence hIndexFreshCode
          hDomainAt hValueBoundAt hIndex
      exact FirstOrder.Derives.iffElimRight
        (membership_right_iff_of_equality
          (sequence ·ₘ numₘ(index))
          code (numₘ(bound))
          (function_application_term_admissible
            sequence (numₘ(index))
            hSequence
            (finite_numeral_term_admissible index))
          hCode
          (finite_numeral_term_admissible bound)
          hCodeEqualityAt)
        hAtCode
    have hTraceAt :
        ∀ index, index ≤ length →
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            (x#traceId ·ₘ numₘ(index)) ∈ₘ
              numₘ(bound + 1) := by
      intro index hIndex
      have hAtCode :=
        fs_zfc_support_raw_sequence_trace_bound_at
          (x#traceId) code indexId
          (length + 1) index
          hTrace hCode
          hIndexFreshTrace hIndexFreshCode
          hTraceDomain hTraceBound
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
              (x#traceId) (numₘ(index))
              hTrace
              (finite_numeral_term_admissible index))
            (successor_term_admissible code hCode)
            (successor_term_admissible
              (numₘ(bound))
              (finite_numeral_term_admissible bound))
            hSuccessorCodeEqualityAt)
          hAtCode
      simpa [finite_numeral_term, successor_term] using
        hAtSuccessor
    have hTraceDomainApplication :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          (x#traceId ·ₘ domₘ(sequence)) ≐ₘ
            (x#traceId ·ₘ numₘ(length)) :=
      function_application_term_congr_argument_of_equality
        (x#traceId) (domₘ(sequence)) (numₘ(length))
        hTrace
        (domain_term_admissible sequence hSequence)
        (finite_numeral_term_admissible length)
        hDomainAt
    have hFinal :
        Ε ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(nat_sequence_code_value tokens) ≐ₘ
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
      have hFinalBound :
          Ε ⊢ₘ[fs_zfc_support_raw_theory]
            numₘ(bound) ≐ₘ
              (x#traceId ·ₘ numₘ(length)) :=
        Metatheory.Derives.equality_trans
          hNumeralToDomain hTraceDomainApplication
      simpa [bound] using hFinalBound
    exact
      fs_zfc_support_raw_nat_sequence_code_replay_of_data
        sequence (x#traceId) tokens length bound
        hSequence hTrace
        hFunctionAt hDomainAt hZero
        hStepAt hValueAt hTraceAt hFinal

/-- 规范 numeral 代码下的自然数序列条件唯一性。 -/
theorem fs_zfc_support_raw_nat_sequence_code_condition_unique
    {Γ : Context signature}
    (sequence : SetTerm)
    (tokens : List Nat)
    (traceId indexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hTraceNeIndex : traceId ≠ indexId)
    (hTraceFreshSequence :
      (SetSort.set, traceId) ∉ Term.freeSupport sequence)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉ Term.freeSupport sequence)
    (hTraceFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, traceId) ∉ Formula.freeSupport formula)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        nat_sequence_code_condition_with_ids
          sequence
          (numₘ(nat_sequence_code_value tokens))
          traceId indexId) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      sequence ≐ₘ standard_token_sequence tokens := by
  apply
    fs_zfc_support_raw_nat_sequence_code_condition_unique_of_code_equality
      sequence
      (numₘ(nat_sequence_code_value tokens))
      tokens traceId indexId
      hSequence
      (finite_numeral_term_admissible
        (nat_sequence_code_value tokens))
      hTraceNeIndex
      hTraceFreshSequence
      hIndexFreshSequence
  · rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  · exact hTraceFreshContext
  · exact hCondition
  · exact FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set)
      (numₘ(nat_sequence_code_value tokens))

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
