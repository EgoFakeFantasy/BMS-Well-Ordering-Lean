import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceReplay

/-
# ZFC 自然数序列的有限反演

本模块只处理自然数序列编码的否定方向。核心接口把对象层的有限定义域、
逐点自然数界和递归轨迹，反演成一个给定规范列表的逐点等式。它不枚举
对象层序列对象本身，也不引入任何语义假设。
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

/-! ## 有限 numeral 成员的对象层消去 -/

/-- 在任意局部上下文中消去一个有限 numeral 的成员见证。 -/
theorem fs_zfc_support_raw_finite_numeral_member_elim_context
    {Γ : Context signature}
    (bound : Nat)
    (point : SetTerm)
    (conclusion : SetFormula)
    (hPoint : Term.Admissible point SetSort.set)
    (hConclusion : Formula.Admissible conclusion)
    (hMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        point ∈ₘ numₘ(bound))
    (hBranch :
      ∀ index, index < bound →
        (point ≐ₘ numₘ(index)) :: Γ
          ⊢ₘ[fs_zfc_support_raw_theory] conclusion) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] conclusion := by
  have hIffRaw :=
    stdseq_numeral_member_iff bound point hPoint
  have hIff :=
    FirstOrder.Derives.context_weaken
      (Γ := [])
      (Δ := Γ)
      (by simp)
      (fs_zfc_support_raw_derives_of_standard_sequence hIffRaw)
  have hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        stdseq_numeral_member_condition bound point :=
    FirstOrder.Derives.iffElimRight hIff hMember
  have hCases :
      stdseq_numeral_member_condition bound point :: Γ
        ⊢ₘ[fs_zfc_support_raw_theory] conclusion :=
    stdseq_numeral_member_condition_elim_context
      bound point conclusion hBranch
      (hPointCheck := Term.check_admissible_complete hPoint)
      (hConclusionCheck :=
        Formula.check_admissible_complete hConclusion)
  exact FirstOrder.Derives.cut hCondition hCases

/-- 对象层中不同的有限 numeral 等式直接给出矛盾。 -/
theorem fs_zfc_support_raw_falsum_of_numeral_equality
    {Γ : Context signature}
    {left right : Nat}
    (hNe : left ≠ right)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(left) ≐ₘ numₘ(right)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  have hNotEquality :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (numₘ(left) ≐ₘ numₘ(right))) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_sequence_finite_numeral_ne hNe)
  exact FirstOrder.Derives.negElim
    hEquality
    (FirstOrder.Derives.context_weaken
      (Γ := [])
      (Δ := Γ)
      (by simp)
      hNotEquality)

/-- 自然数序列编码递归一步在两个有限 numeral 输入上的地面计算。 -/
theorem fs_zfc_support_raw_nat_sequence_code_step_numeral_eq
    (accumulator item : Nat) :
    Derives fs_zfc_support_raw_theory [] (
      Sₘ(godel_pairₘ(⟨numₘ(accumulator), numₘ(item)⟩ₘ)) ≐ₘ
        numₘ(nat_sequence_code_step accumulator item)) := by
  let pair : SetTerm :=
    ⟨numₘ(accumulator), numₘ(item)⟩ₘ
  have hAccumulator :
      Term.Admissible (numₘ(accumulator)) SetSort.set :=
    finite_numeral_term_admissible accumulator
  have hItem :
      Term.Admissible (numₘ(item)) SetSort.set :=
    finite_numeral_term_admissible item
  have hPair :
      Term.Admissible pair SetSort.set := by
    simpa [pair] using
      ordered_pair_term_admissible
        (numₘ(accumulator)) (numₘ(item))
        hAccumulator hItem
  have hPairCode :
      Term.Admissible (godel_pairₘ(pair)) SetSort.set :=
    godel_pairing_term_admissible pair hPair
  have hValue :
      Derives fs_zfc_support_raw_theory [] (
        godel_pairₘ(pair) ≐ₘ
          numₘ(godel_pair_value accumulator item)) :=
    by
      simpa [pair] using
        fs_zfc_support_raw_godel_pair_value_eq
          accumulator item
  have hSuccessor :=
    successor_term_congr_of_equality
      (godel_pairₘ(pair))
      (numₘ(godel_pair_value accumulator item))
      hPairCode
      (finite_numeral_term_admissible
        (godel_pair_value accumulator item))
      hValue
  simpa [pair, nat_sequence_code_step,
    finite_numeral_term, successor_term] using hSuccessor

/-! ## 列表尾递归辅助 -/

theorem list_snoc_induction
    {α : Type}
    (motive : List α → Prop)
    (hNil : motive [])
    (hSnoc :
      ∀ list item, motive list →
        motive (list ++ [item])) :
    ∀ list, motive list := by
  intro list
  have hReverse :
      ∀ (reverseList : List α), motive reverseList.reverse := by
    intro reverseList
    induction reverseList with
    | nil =>
        simpa using hNil
    | cons item reverseList ih =>
        simpa [List.reverse_cons] using
          hSnoc reverseList.reverse item ih
  simpa using hReverse list.reverse

/-! ## 规范自然数序列的逐点反演 -/

/-
`length` 是对象序列的外部定义域长度，`bound` 是对象层给出的统一自然数
上界。递归按规范列表的尾部进行；每一步只在有限 numeral 成员条件上作
对象层分支，匹配分支再调用列表前缀的归纳假设。
-/

theorem fs_zfc_support_raw_nat_sequence_code_prefix_unique
    {Γ : Context signature}
    (sequence trace : SetTerm)
    (tokens : List Nat)
    (length bound : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hTrace : Term.Admissible trace SetSort.set)
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
    (Γ ⊢ₘ[fs_zfc_support_raw_theory]
      numₘ(length) ≐ₘ numₘ(tokens.length)) ∧
      (∀ index (hIndex : index < tokens.length),
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          (sequence ·ₘ numₘ(index)) ≐ₘ
            numₘ(tokens[index]'hIndex)) := by
  induction tokens using list_snoc_induction generalizing Γ length with
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
        have hStepLast := hStep prefixLength (Nat.lt_succ_self _)
        have hValueLast := hValueBound prefixLength
          (Nat.lt_succ_self _)
        have hTraceLast := hTraceBound prefixLength
          (Nat.le_succ _)
        have hValuePoint :
            Term.Admissible
              (sequence ·ₘ numₘ(prefixLength)) SetSort.set :=
          function_application_term_admissible
            sequence (numₘ(prefixLength))
            hSequence
            (finite_numeral_term_admissible prefixLength)
        have hTracePoint :
            Term.Admissible
              (trace ·ₘ numₘ(prefixLength)) SetSort.set :=
          function_application_term_admissible
            trace (numₘ(prefixLength))
            hTrace
            (finite_numeral_term_admissible prefixLength)
        have hFalse :
            Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
          apply
            fs_zfc_support_raw_finite_numeral_member_elim_context
              (bound + 1)
              (trace ·ₘ numₘ(prefixLength))
              Formula.falsum
              hTracePoint
              Formula.Admissible.falsum
              hTraceLast
          intro accumulator hAccumulator
          have hValueMember :
              (trace ·ₘ numₘ(prefixLength)) ≐ₘ
                  numₘ(accumulator) :: Γ
                ⊢ₘ[fs_zfc_support_raw_theory]
                  (sequence ·ₘ numₘ(prefixLength)) ∈ₘ
                    numₘ(bound) :=
            FirstOrder.Derives.context_weaken_cons hValueLast
          apply
            fs_zfc_support_raw_finite_numeral_member_elim_context
              bound
              (sequence ·ₘ numₘ(prefixLength))
              Formula.falsum
              hValuePoint
              Formula.Admissible.falsum
              hValueMember
          intro item hItem
          let Δ : Context signature :=
            (sequence ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(item) ::
              (trace ·ₘ numₘ(prefixLength)) ≐ₘ
                numₘ(accumulator) :: Γ
          have hTraceEquality :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                trace ·ₘ numₘ(prefixLength) ≐ₘ
                  numₘ(accumulator) :=
            FirstOrder.Derives.assumption (by simp [Δ])
          have hValueEquality :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                sequence ·ₘ numₘ(prefixLength) ≐ₘ
                  numₘ(item) :=
            FirstOrder.Derives.assumption (by simp [Δ])
          have hStep' :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                nat_sequence_code_step_condition
                  sequence trace (numₘ(prefixLength)) := by
            exact FirstOrder.Derives.context_weaken_cons
              (FirstOrder.Derives.context_weaken_cons hStepLast)
          have hFinal' :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                numₘ(0) ≐ₘ
                  trace ·ₘ numₘ(prefixLength + 1) := by
            simpa [nat_sequence_code_value, finite_numeral_term,
              successor_term] using
              FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons hFinal)
          have hStepEquality :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                trace ·ₘ numₘ(prefixLength + 1) ≐ₘ
                  Sₘ(godel_pairₘ(
                    ⟨numₘ(accumulator), numₘ(item)⟩ₘ)) := by
            have hStepRaw :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  trace ·ₘ Sₘ(numₘ(prefixLength)) ≐ₘ
                    Sₘ(godel_pairₘ(
                      ⟨trace ·ₘ numₘ(prefixLength),
                        sequence ·ₘ numₘ(prefixLength)⟩ₘ)) := by
              simpa [nat_sequence_code_step_condition] using
                hStep'
            have hPairEquality :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  godel_pairₘ(
                    ⟨trace ·ₘ numₘ(prefixLength),
                      sequence ·ₘ numₘ(prefixLength)⟩ₘ) ≐ₘ
                    godel_pairₘ(
                      ⟨numₘ(accumulator), numₘ(item)⟩ₘ) :=
              godel_pairing_term_congr_of_equalities
                (trace ·ₘ numₘ(prefixLength))
                (numₘ(accumulator))
                (sequence ·ₘ numₘ(prefixLength))
                (numₘ(item))
                hTracePoint
                (finite_numeral_term_admissible accumulator)
                hValuePoint
                (finite_numeral_term_admissible item)
                hTraceEquality
                hValueEquality
            have hSuccessorEquality :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  Sₘ(godel_pairₘ(
                    ⟨trace ·ₘ numₘ(prefixLength),
                      sequence ·ₘ numₘ(prefixLength)⟩ₘ)) ≐ₘ
                    Sₘ(godel_pairₘ(
                      ⟨numₘ(accumulator), numₘ(item)⟩ₘ)) :=
              successor_term_congr_of_equality
                (godel_pairₘ(
                  ⟨trace ·ₘ numₘ(prefixLength),
                    sequence ·ₘ numₘ(prefixLength)⟩ₘ))
                (godel_pairₘ(
                  ⟨numₘ(accumulator), numₘ(item)⟩ₘ))
                (godel_pairing_term_admissible
                  ⟨trace ·ₘ numₘ(prefixLength),
                    sequence ·ₘ numₘ(prefixLength)⟩ₘ
                  (ordered_pair_term_admissible
                    (trace ·ₘ numₘ(prefixLength))
                    (sequence ·ₘ numₘ(prefixLength))
                    hTracePoint hValuePoint))
                (godel_pairing_term_admissible
                  ⟨numₘ(accumulator), numₘ(item)⟩ₘ
                  (ordered_pair_term_admissible
                    (numₘ(accumulator)) (numₘ(item))
                    (finite_numeral_term_admissible accumulator)
                    (finite_numeral_term_admissible item)))
                hPairEquality
            have hStepToGround :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  trace ·ₘ Sₘ(numₘ(prefixLength)) ≐ₘ
                    Sₘ(godel_pairₘ(
                      ⟨numₘ(accumulator), numₘ(item)⟩ₘ)) :=
              Metatheory.Derives.equality_trans
                hStepRaw hSuccessorEquality
            simpa [finite_numeral_term, successor_term] using hStepToGround
          have hGround :
              Derives fs_zfc_support_raw_theory [] (
                Sₘ(godel_pairₘ(
                  ⟨numₘ(accumulator), numₘ(item)⟩ₘ)) ≐ₘ
                    numₘ(nat_sequence_code_step
                      accumulator item)) :=
            fs_zfc_support_raw_nat_sequence_code_step_numeral_eq
              accumulator item
          have hFinalToStep :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                numₘ(0) ≐ₘ
                  Sₘ(godel_pairₘ(
                    ⟨numₘ(accumulator), numₘ(item)⟩ₘ)) :=
            Metatheory.Derives.equality_trans
              hFinal'
              hStepEquality
          have hGroundDelta :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                Sₘ(godel_pairₘ(
                  ⟨numₘ(accumulator), numₘ(item)⟩ₘ)) ≐ₘ
                    numₘ(nat_sequence_code_step
                      accumulator item) :=
            FirstOrder.Derives.context_weaken
              (Γ := [])
              (Δ := Δ)
              (by
                intro ψ hψ
                simp at hψ)
              hGround
          have hZeroEquality :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                numₘ(0) ≐ₘ
                  numₘ(nat_sequence_code_step
                    accumulator item) := by
            exact Metatheory.Derives.equality_trans
              hFinalToStep
              hGroundDelta
          exact
            fs_zfc_support_raw_falsum_of_numeral_equality
              (by simp [nat_sequence_code_step])
              hZeroEquality
        constructor
        · exact FirstOrder.Derives.falsumElim
            hFalse
        · intro index hIndex
          simp at hIndex
    | hSnoc xs item ih =>
        by_cases hLength : length = 0
        · subst length
          have hFinalZero :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                numₘ(nat_sequence_code_value (xs ++ [item])) ≐ₘ
                  numₘ(0) :=
            Metatheory.Derives.equality_trans
              hFinal
              hZero
          have hFalse :
              Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum :=
            fs_zfc_support_raw_falsum_of_numeral_equality
              (by
                apply Nat.ne_of_gt
                exact nat_sequence_code_value_pos_of_ne_nil
                  (by simp))
              hFinalZero
          constructor
          · exact FirstOrder.Derives.falsumElim
              hFalse
          · intro index hIndex
            exact FirstOrder.Derives.falsumElim
              hFalse
        · obtain ⟨prefixLength, rfl⟩ :=
            Nat.exists_eq_succ_of_ne_zero hLength
          have hStepLast :=
            hStep prefixLength (Nat.lt_succ_self _)
          have hValueLast :=
            hValueBound prefixLength (Nat.lt_succ_self _)
          have hTraceLast :=
            hTraceBound prefixLength (Nat.le_succ _)
          have hValuePoint :
              Term.Admissible
                (sequence ·ₘ numₘ(prefixLength)) SetSort.set :=
            function_application_term_admissible
              sequence (numₘ(prefixLength))
              hSequence
              (finite_numeral_term_admissible prefixLength)
          have hTracePoint :
              Term.Admissible
                (trace ·ₘ numₘ(prefixLength)) SetSort.set :=
            function_application_term_admissible
              trace (numₘ(prefixLength))
              hTrace
              (finite_numeral_term_admissible prefixLength)
          have hCodeEquality
              (accumulator itemAt : Nat) :
              ((sequence ·ₘ numₘ(prefixLength)) ≐ₘ
                  numₘ(itemAt)) ::
                ((trace ·ₘ numₘ(prefixLength)) ≐ₘ
                  numₘ(accumulator)) :: Γ
                ⊢ₘ[fs_zfc_support_raw_theory]
                  numₘ(nat_sequence_code_step
                    (nat_sequence_code_value xs) item) ≐ₘ
                    numₘ(nat_sequence_code_step
                      accumulator itemAt) := by
            let Δ : Context signature :=
              (sequence ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(itemAt) ::
                (trace ·ₘ numₘ(prefixLength)) ≐ₘ
                  numₘ(accumulator) :: Γ
            have hTraceEquality :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  trace ·ₘ numₘ(prefixLength) ≐ₘ
                    numₘ(accumulator) :=
              FirstOrder.Derives.assumption (by simp [Δ])
            have hValueEquality :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  sequence ·ₘ numₘ(prefixLength) ≐ₘ
                    numₘ(itemAt) :=
              FirstOrder.Derives.assumption (by simp [Δ])
            have hStep' :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  nat_sequence_code_step_condition
                    sequence trace (numₘ(prefixLength)) := by
              exact FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons hStepLast)
            have hFinal' :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  numₘ(nat_sequence_code_step
                    (nat_sequence_code_value xs) item) ≐ₘ
                    trace ·ₘ numₘ(prefixLength + 1) := by
              simpa [nat_sequence_code_value_append_singleton,
                finite_numeral_term, successor_term] using
                FirstOrder.Derives.context_weaken_cons
                  (FirstOrder.Derives.context_weaken_cons hFinal)
            have hStepRaw :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  trace ·ₘ Sₘ(numₘ(prefixLength)) ≐ₘ
                    Sₘ(godel_pairₘ(
                      ⟨trace ·ₘ numₘ(prefixLength),
                        sequence ·ₘ numₘ(prefixLength)⟩ₘ)) := by
              simpa [nat_sequence_code_step_condition] using hStep'
            have hPairEquality :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  godel_pairₘ(
                    ⟨trace ·ₘ numₘ(prefixLength),
                      sequence ·ₘ numₘ(prefixLength)⟩ₘ) ≐ₘ
                    godel_pairₘ(
                      ⟨numₘ(accumulator), numₘ(itemAt)⟩ₘ) :=
              godel_pairing_term_congr_of_equalities
                (trace ·ₘ numₘ(prefixLength))
                (numₘ(accumulator))
                (sequence ·ₘ numₘ(prefixLength))
                (numₘ(itemAt))
                hTracePoint
                (finite_numeral_term_admissible accumulator)
                hValuePoint
                (finite_numeral_term_admissible itemAt)
                hTraceEquality
                hValueEquality
            have hSuccessorEquality :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  Sₘ(godel_pairₘ(
                    ⟨trace ·ₘ numₘ(prefixLength),
                      sequence ·ₘ numₘ(prefixLength)⟩ₘ)) ≐ₘ
                    Sₘ(godel_pairₘ(
                      ⟨numₘ(accumulator), numₘ(itemAt)⟩ₘ)) :=
              successor_term_congr_of_equality
                (godel_pairₘ(
                  ⟨trace ·ₘ numₘ(prefixLength),
                    sequence ·ₘ numₘ(prefixLength)⟩ₘ))
                (godel_pairₘ(
                  ⟨numₘ(accumulator), numₘ(itemAt)⟩ₘ))
                (godel_pairing_term_admissible
                  ⟨trace ·ₘ numₘ(prefixLength),
                    sequence ·ₘ numₘ(prefixLength)⟩ₘ
                  (ordered_pair_term_admissible
                    (trace ·ₘ numₘ(prefixLength))
                    (sequence ·ₘ numₘ(prefixLength))
                    hTracePoint hValuePoint))
                (godel_pairing_term_admissible
                  ⟨numₘ(accumulator), numₘ(itemAt)⟩ₘ
                  (ordered_pair_term_admissible
                    (numₘ(accumulator)) (numₘ(itemAt))
                    (finite_numeral_term_admissible accumulator)
                    (finite_numeral_term_admissible itemAt)))
                hPairEquality
            have hStepToGround :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  trace ·ₘ Sₘ(numₘ(prefixLength)) ≐ₘ
                    Sₘ(godel_pairₘ(
                      ⟨numₘ(accumulator), numₘ(itemAt)⟩ₘ)) :=
              Metatheory.Derives.equality_trans
                hStepRaw hSuccessorEquality
            have hStepEquality :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  trace ·ₘ numₘ(prefixLength + 1) ≐ₘ
                    Sₘ(godel_pairₘ(
                      ⟨numₘ(accumulator), numₘ(itemAt)⟩ₘ)) := by
              simpa [finite_numeral_term, successor_term] using
                hStepToGround
            have hGround :
                Derives fs_zfc_support_raw_theory [] (
                  Sₘ(godel_pairₘ(
                    ⟨numₘ(accumulator), numₘ(itemAt)⟩ₘ)) ≐ₘ
                      numₘ(nat_sequence_code_step
                        accumulator itemAt)) :=
              fs_zfc_support_raw_nat_sequence_code_step_numeral_eq
                accumulator itemAt
            have hFinalToStep :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  numₘ(nat_sequence_code_step
                    (nat_sequence_code_value xs) item) ≐ₘ
                    Sₘ(godel_pairₘ(
                      ⟨numₘ(accumulator), numₘ(itemAt)⟩ₘ)) :=
              Metatheory.Derives.equality_trans
                hFinal'
                hStepEquality
            have hGroundDelta :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  Sₘ(godel_pairₘ(
                    ⟨numₘ(accumulator), numₘ(itemAt)⟩ₘ)) ≐ₘ
                      numₘ(nat_sequence_code_step
                        accumulator itemAt) :=
              FirstOrder.Derives.context_weaken
                (Γ := [])
                (Δ := Δ)
                (by
                  intro ψ hψ
                  simp at hψ)
                hGround
            have hCode := Metatheory.Derives.equality_trans
              hFinalToStep hGroundDelta
            simpa [Δ] using hCode
          have hFiniteCases
              (conclusion : SetFormula)
              (hConclusion : Formula.Admissible conclusion)
              (hBranch :
                ∀ accumulator, accumulator < bound + 1 →
                  ∀ itemAt, itemAt < bound →
                    ((sequence ·ₘ numₘ(prefixLength)) ≐ₘ
                        numₘ(itemAt)) ::
                      ((trace ·ₘ numₘ(prefixLength)) ≐ₘ
                        numₘ(accumulator)) :: Γ
                        ⊢ₘ[fs_zfc_support_raw_theory]
                          conclusion) :
              Γ ⊢ₘ[fs_zfc_support_raw_theory] conclusion := by
            apply
              fs_zfc_support_raw_finite_numeral_member_elim_context
                (bound + 1)
                (trace ·ₘ numₘ(prefixLength))
                conclusion
                hTracePoint
                hConclusion
                hTraceLast
            intro accumulator hAccumulator
            have hValueMember :
                (trace ·ₘ numₘ(prefixLength)) ≐ₘ
                    numₘ(accumulator) :: Γ
                  ⊢ₘ[fs_zfc_support_raw_theory]
                    (sequence ·ₘ numₘ(prefixLength)) ∈ₘ
                      numₘ(bound) :=
              FirstOrder.Derives.context_weaken_cons hValueLast
            apply
              fs_zfc_support_raw_finite_numeral_member_elim_context
                bound
                (sequence ·ₘ numₘ(prefixLength))
                conclusion
                hValuePoint
                hConclusion
                hValueMember
            intro itemAt hItemAt
            exact hBranch accumulator hAccumulator itemAt hItemAt
          have hLengthDerivation :
              Γ ⊢ₘ[fs_zfc_support_raw_theory]
                numₘ(prefixLength.succ) ≐ₘ
                  numₘ((xs ++ [item]).length) := by
            apply hFiniteCases
            · exact Formula.Admissible.equal
                (finite_numeral_term_admissible prefixLength.succ)
                (finite_numeral_term_admissible
                  (xs ++ [item]).length)
            · intro accumulator hAccumulator itemAt hItemAt
              let Δ : Context signature :=
                (sequence ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(itemAt) ::
                  (trace ·ₘ numₘ(prefixLength)) ≐ₘ
                    numₘ(accumulator) :: Γ
              have hCode :
                  Δ ⊢ₘ[fs_zfc_support_raw_theory]
                    numₘ(nat_sequence_code_step
                      (nat_sequence_code_value xs) item) ≐ₘ
                      numₘ(nat_sequence_code_step
                        accumulator itemAt) := by
                simpa [Δ] using
                  hCodeEquality accumulator itemAt
              by_cases hMatch :
                  nat_sequence_code_step
                    (nat_sequence_code_value xs) item =
                    nat_sequence_code_step accumulator itemAt
              · have hPairCode :
                    godel_pair_value
                      (nat_sequence_code_value xs) item =
                      godel_pair_value accumulator itemAt := by
                  apply Nat.succ.inj
                  simpa [nat_sequence_code_step] using hMatch
                rcases godel_pair_value_eq_iff.mp hPairCode with
                  ⟨hAccumulatorCode, hItemCode⟩
                subst accumulator
                subst itemAt
                have hTraceEquality :
                    Δ ⊢ₘ[fs_zfc_support_raw_theory]
                      trace ·ₘ numₘ(prefixLength) ≐ₘ
                        numₘ(nat_sequence_code_value xs) :=
                  FirstOrder.Derives.assumption (by simp [Δ])
                have hZeroDelta :
                    Δ ⊢ₘ[fs_zfc_support_raw_theory]
                      trace ·ₘ numₘ(0) ≐ₘ numₘ(0) :=
                  FirstOrder.Derives.context_weaken_cons
                    (FirstOrder.Derives.context_weaken_cons hZero)
                have hStepPrefix :
                    ∀ index, index < prefixLength →
                      Δ ⊢ₘ[fs_zfc_support_raw_theory]
                        nat_sequence_code_step_condition
                          sequence trace (numₘ(index)) := by
                  intro index hIndex
                  exact FirstOrder.Derives.context_weaken_cons
                    (FirstOrder.Derives.context_weaken_cons
                      (hStep index (by omega)))
                have hValuePrefix :
                    ∀ index, index < prefixLength →
                      Δ ⊢ₘ[fs_zfc_support_raw_theory]
                        (sequence ·ₘ numₘ(index)) ∈ₘ numₘ(bound) := by
                  intro index hIndex
                  exact FirstOrder.Derives.context_weaken_cons
                    (FirstOrder.Derives.context_weaken_cons
                      (hValueBound index (by omega)))
                have hTracePrefix :
                    ∀ index, index ≤ prefixLength →
                      Δ ⊢ₘ[fs_zfc_support_raw_theory]
                        (trace ·ₘ numₘ(index)) ∈ₘ
                          numₘ(bound + 1) := by
                  intro index hIndex
                  exact FirstOrder.Derives.context_weaken_cons
                    (FirstOrder.Derives.context_weaken_cons
                      (hTraceBound index (by omega)))
                have hFinalPrefix :
                    Δ ⊢ₘ[fs_zfc_support_raw_theory]
                      numₘ(nat_sequence_code_value xs) ≐ₘ
                        trace ·ₘ numₘ(prefixLength) :=
                  Metatheory.Derives.equality_symm
                    hTraceEquality
                have hIH :=
                  ih (Γ := Δ)
                    prefixLength
                    hZeroDelta
                    hStepPrefix
                    hValuePrefix
                    hTracePrefix
                    hFinalPrefix
                have hSuccessorLength :=
                  successor_term_congr_of_equality
                    (numₘ(prefixLength))
                    (numₘ(xs.length))
                    (finite_numeral_term_admissible prefixLength)
                    (finite_numeral_term_admissible xs.length)
                    hIH.1
                simpa [Δ, List.length_append,
                  finite_numeral_term, successor_term] using
                  hSuccessorLength
              · have hFalse :
                    Δ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum :=
                  fs_zfc_support_raw_falsum_of_numeral_equality
                    hMatch hCode
                exact FirstOrder.Derives.falsumElim
                  hFalse
          have hPrefixReplay
              (accumulator itemAt : Nat)
              (hMatch :
                nat_sequence_code_step
                    (nat_sequence_code_value xs) item =
                  nat_sequence_code_step accumulator itemAt) :
              (((sequence ·ₘ numₘ(prefixLength)) ≐ₘ
                    numₘ(itemAt) ::
                  (trace ·ₘ numₘ(prefixLength)) ≐ₘ
                    numₘ(accumulator) :: Γ)
                ⊢ₘ[fs_zfc_support_raw_theory]
                  numₘ(prefixLength) ≐ₘ numₘ(xs.length)) ∧
                (∀ index (hIndex : index < xs.length),
                  (((sequence ·ₘ numₘ(prefixLength)) ≐ₘ
                        numₘ(itemAt) ::
                      (trace ·ₘ numₘ(prefixLength)) ≐ₘ
                        numₘ(accumulator) :: Γ)
                    ⊢ₘ[fs_zfc_support_raw_theory]
                      (sequence ·ₘ numₘ(index)) ≐ₘ
                        numₘ(xs[index]'hIndex))) := by
            let Δ : Context signature :=
              (sequence ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(itemAt) ::
                (trace ·ₘ numₘ(prefixLength)) ≐ₘ
                  numₘ(accumulator) :: Γ
            have hPairCode :
                  godel_pair_value
                    (nat_sequence_code_value xs) item =
                    godel_pair_value accumulator itemAt := by
              apply Nat.succ.inj
              simpa [nat_sequence_code_step] using hMatch
            rcases godel_pair_value_eq_iff.mp hPairCode with
              ⟨hAccumulatorCode, hItemCode⟩
            subst accumulator
            subst itemAt
            have hTraceEquality :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  trace ·ₘ numₘ(prefixLength) ≐ₘ
                    numₘ(nat_sequence_code_value xs) :=
              FirstOrder.Derives.assumption (by simp [Δ])
            have hZeroDelta :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  trace ·ₘ numₘ(0) ≐ₘ numₘ(0) :=
              FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons hZero)
            have hStepPrefix :
                ∀ index, index < prefixLength →
                  Δ ⊢ₘ[fs_zfc_support_raw_theory]
                    nat_sequence_code_step_condition
                      sequence trace (numₘ(index)) := by
              intro index hIndex
              exact FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons
                  (hStep index (by omega)))
            have hValuePrefix :
                ∀ index, index < prefixLength →
                  Δ ⊢ₘ[fs_zfc_support_raw_theory]
                    (sequence ·ₘ numₘ(index)) ∈ₘ numₘ(bound) := by
              intro index hIndex
              exact FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons
                  (hValueBound index (by omega)))
            have hTracePrefix :
                ∀ index, index ≤ prefixLength →
                  Δ ⊢ₘ[fs_zfc_support_raw_theory]
                    (trace ·ₘ numₘ(index)) ∈ₘ
                      numₘ(bound + 1) := by
              intro index hIndex
              exact FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons
                  (hTraceBound index (by omega)))
            have hFinalPrefix :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  numₘ(nat_sequence_code_value xs) ≐ₘ
                    trace ·ₘ numₘ(prefixLength) :=
              Metatheory.Derives.equality_symm
                hTraceEquality
            have hIH :=
              ih (Γ := Δ)
                prefixLength
                hZeroDelta
                hStepPrefix
                hValuePrefix
                hTracePrefix
                hFinalPrefix
            simpa [Δ] using hIH
          constructor
          · exact hLengthDerivation
          · intro index hIndex
            apply hFiniteCases
            · exact Formula.Admissible.equal
                (function_application_term_admissible
                  sequence (numₘ(index)) hSequence
                  (finite_numeral_term_admissible index))
                (finite_numeral_term_admissible
                  ((xs ++ [item])[index]'hIndex))
            · intro accumulator hAccumulator itemAt hItemAt
              let Δ : Context signature :=
                (sequence ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(itemAt) ::
                  (trace ·ₘ numₘ(prefixLength)) ≐ₘ
                    numₘ(accumulator) :: Γ
              have hCode :
                  Δ ⊢ₘ[fs_zfc_support_raw_theory]
                    numₘ(nat_sequence_code_step
                      (nat_sequence_code_value xs) item) ≐ₘ
                      numₘ(nat_sequence_code_step
                        accumulator itemAt) := by
                simpa [Δ] using
                  hCodeEquality accumulator itemAt
              by_cases hMatch :
                  nat_sequence_code_step
                    (nat_sequence_code_value xs) item =
                    nat_sequence_code_step accumulator itemAt
              · have hPairCode :
                    godel_pair_value
                      (nat_sequence_code_value xs) item =
                      godel_pair_value accumulator itemAt := by
                  apply Nat.succ.inj
                  simpa [nat_sequence_code_step] using hMatch
                rcases godel_pair_value_eq_iff.mp hPairCode with
                  ⟨hAccumulatorCode, hItemCode⟩
                subst accumulator
                subst itemAt
                have hPrefix :=
                  hPrefixReplay
                    (nat_sequence_code_value xs) item (by rfl)
                have hApplicationEquality :
                    Δ ⊢ₘ[fs_zfc_support_raw_theory]
                      (sequence ·ₘ numₘ(prefixLength)) ≐ₘ
                        (sequence ·ₘ numₘ(xs.length)) := by
                  simpa [Δ] using
                    function_application_term_congr_argument_of_equality
                      sequence
                      (numₘ(prefixLength))
                      (numₘ(xs.length))
                      hSequence
                      (finite_numeral_term_admissible prefixLength)
                      (finite_numeral_term_admissible xs.length)
                      hPrefix.1
                by_cases hPrefixIndex : index < xs.length
                · have hPoint := hPrefix.2 index hPrefixIndex
                  simpa [Δ, List.getElem_append, hPrefixIndex] using
                    hPoint
                · have hIndexEq : index = xs.length := by
                    have hIndex' : index < xs.length + 1 := by
                      simpa [List.length_append] using hIndex
                    omega
                  subst index
                  have hValueEquality :
                      Δ ⊢ₘ[fs_zfc_support_raw_theory]
                        sequence ·ₘ numₘ(prefixLength) ≐ₘ
                          numₘ(item) :=
                    FirstOrder.Derives.assumption (by simp [Δ])
                  have hApplicationSymm :=
                    Metatheory.Derives.equality_symm
                      hApplicationEquality
                  have hLast :=
                    Metatheory.Derives.equality_trans
                      hApplicationSymm
                      hValueEquality
                  simpa [Δ, List.getElem_append] using hLast
              · have hFalse :
                    Δ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum :=
                  fs_zfc_support_raw_falsum_of_numeral_equality
                    hMatch hCode
                exact FirstOrder.Derives.falsumElim
                  hFalse

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
