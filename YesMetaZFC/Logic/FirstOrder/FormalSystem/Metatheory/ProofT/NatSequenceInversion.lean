import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceConditionInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceSpaceSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.PairingInversionDirect
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceInversion

/-!
# 内在自然数序列反演

本模块迁移自然数序列反演的有限归纳核心。对象项、轨迹项和递归步均使用内在
上下文；有限 numeral 的成员消去由 `CertificateCore` 提供，不再携带旧式
`Admissible`、自由支撑或变量编号参数。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open IntrinsicPairing

set_option autoImplicit false

/-! ## 外部列表辅助 -/

theorem list_snoc_induction
    {α : Type}
    (motive : List α → Prop)
    (hNil : motive [])
    (hSnoc : ∀ list item, motive list → motive (list ++ [item])) :
    ∀ list, motive list := by
  intro list
  have hReverse : ∀ (reverseList : List α), motive reverseList.reverse := by
    intro reverseList
    induction reverseList with
    | nil =>
        simpa using hNil
    | cons item reverseList ih =>
        simpa [List.reverse_cons] using
          hSnoc reverseList.reverse item ih
  simpa using hReverse list.reverse

/-! ## 地面递归步 -/

/-- 规范自然数递归步在对象层直接计算为一个 numeral。 -/
theorem nat_sequence_code_step_numeral_eq
    {T : SetTheory}
    (C : CertificateCore T)
    (accumulator item : Nat) :
    ([] : Context signature []) ⊢ₘ[T]
      Sₘ(godel_pairₘ(numₘ(accumulator), numₘ(item))) ≐ₘ
        numₘ(nat_sequence_code_step accumulator item) := by
  have hPair := C.pair_value accumulator item
  have hStep := successor_term_congr_of_equality
    (godel_pairₘ(numₘ(accumulator), numₘ(item)))
    (numₘ(godel_pair_value accumulator item)) hPair
  simpa [nat_sequence_code_step, finite_numeral_term, successor_term] using hStep

private theorem lift_closed
    {T : SetTheory} {free : SetContext}
    {formula : SetSentence}
    (hFormula :
      ([] : Context signature []) ⊢ₘ[T] formula) :
    ([] : Context signature free) ⊢ₘ[T]
      Formula.renameFree
        (VariableRenaming.empty : VariableRenaming [] free)
        formula := by
  simpa using
    FirstOrder.Derives.free_renaming
      (T := T)
      (ρ := (VariableRenaming.empty : VariableRenaming [] free))
      hFormula

theorem nat_sequence_code_step_numeral_at
    {T : SetTheory}
    (C : CertificateCore T)
    {free : SetContext}
    {Γ : Context signature free}
    (accumulator item : Nat) :
    Γ ⊢ₘ[T]
      Sₘ(godel_pairₘ(numₘ(accumulator), numₘ(item))) ≐ₘ
        numₘ(nat_sequence_code_step accumulator item) := by
  have hGround := nat_sequence_code_step_numeral_eq C accumulator item
  have hFree := lift_closed (free := free) hGround
  have hContext := FirstOrder.Derives.context_weaken
    (Γ := ([] : Context signature free))
    (Δ := Γ) (by simp) hFree
  simpa [Formula.renameFree, Formula.rename, Renaming.free,
    Formula.renameMapped, Term.renameMapped, Arguments.renameMapped,
    finite_numeral_term_renameMapped] using hContext

theorem numeral_ne_context
    {T : SetTheory}
    (C : CertificateCore T)
    {free : SetContext}
    {Γ : Context signature free}
    {left right : Nat}
    (hNe : left ≠ right) :
    Γ ⊢ₘ[T] ¬ₘ(numₘ(left) ≐ₘ numₘ(right)) := by
  have hClosed := C.numeral_ne hNe
  have hFree := FirstOrder.Derives.free_renaming
    (T := T)
    (ρ := (VariableRenaming.empty : VariableRenaming [] free))
    hClosed
  have hContext := FirstOrder.Derives.context_weaken
    (Γ := ([] : Context signature free))
    (Δ := Γ) (by simp) hFree
  simpa [Formula.renameFree, Formula.rename, Renaming.free,
    Formula.renameMapped, Term.renameMapped, Arguments.renameMapped,
    finite_numeral_term_renameMapped] using hContext

theorem falsum_of_numeral_equality
    {T : SetTheory}
    (C : CertificateCore T)
    {free : SetContext}
    {Γ : Context signature free}
    {left right : Nat}
    (hNe : left ≠ right)
    (hEquality : Γ ⊢ₘ[T] numₘ(left) ≐ₘ numₘ(right)) :
    Γ ⊢ₘ[T] Formula.falsum :=
  FirstOrder.Derives.neg_elim hEquality
    (numeral_ne_context C hNe)

/-! ## 有限前缀反演 -/

/-- 递归轨迹和末码共同决定自然数序列的有限前缀。 -/
theorem nat_sequence_code_prefix_unique
    {T : SetTheory}
    (C : CertificateCore T)
    {free : SetContext}
    {Γ : Context signature free}
    (sequence trace : SetOpenTerm free)
    (tokens : List Nat)
    (length bound : Nat)
    (hZero :
      Γ ⊢ₘ[T] (trace ·ₘ numₘ(0)) ≐ₘ numₘ(0))
    (hStep :
      ∀ index, index < length →
        Γ ⊢ₘ[T]
          nat_sequence_code_step_condition
            sequence trace (numₘ(index)))
    (hValueBound :
      ∀ index, index < length →
        Γ ⊢ₘ[T] (sequence ·ₘ numₘ(index)) ∈ₘ numₘ(bound))
    (hTraceBound :
      ∀ index, index ≤ length →
        Γ ⊢ₘ[T] (trace ·ₘ numₘ(index)) ∈ₘ numₘ(bound + 1))
    (hFinal :
      Γ ⊢ₘ[T]
        numₘ(nat_sequence_code_value tokens) ≐ₘ
          (trace ·ₘ numₘ(length))) :
    (Γ ⊢ₘ[T] numₘ(length) ≐ₘ numₘ(tokens.length)) ∧
      (∀ index (hIndex : index < tokens.length),
        Γ ⊢ₘ[T]
          (sequence ·ₘ numₘ(index)) ≐ₘ
            numₘ(tokens[index]'hIndex)) := by
  induction tokens using list_snoc_induction generalizing Γ length with
  | hNil =>
      by_cases hLength : length = 0
      · subst length
        constructor
        · exact Metatheory.Derives.equality_refl
            (T := T) (Γ := Γ) (numₘ(0))
        · intro index hIndex
          simp at hIndex
      · obtain ⟨prefixLength, rfl⟩ :=
          Nat.exists_eq_succ_of_ne_zero hLength
        have hStepLast := hStep prefixLength (Nat.lt_succ_self _)
        have hValueLast := hValueBound prefixLength
          (Nat.lt_succ_self _)
        have hTraceLast := hTraceBound prefixLength
          (Nat.le_succ _)
        have hFalse : Γ ⊢ₘ[T] Formula.falsum := by
          apply C.member_elim
            (bound + 1) (trace ·ₘ numₘ(prefixLength)) Formula.falsum
            hTraceLast
          intro accumulator hAccumulator
          have hValueMember :
              (trace ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(accumulator) :: Γ
                ⊢ₘ[T] (sequence ·ₘ numₘ(prefixLength)) ∈ₘ numₘ(bound) :=
            FirstOrder.Derives.context_weaken_cons hValueLast
          apply C.member_elim
            bound (sequence ·ₘ numₘ(prefixLength)) Formula.falsum
            hValueMember
          intro item hItem
          let Δ : Context signature free :=
            (sequence ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(item) ::
              (trace ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(accumulator) :: Γ
          have hTraceEquality :
              Δ ⊢ₘ[T] trace ·ₘ numₘ(prefixLength) ≐ₘ numₘ(accumulator) :=
            FirstOrder.Derives.assumption (by simp [Δ])
          have hValueEquality :
              Δ ⊢ₘ[T] sequence ·ₘ numₘ(prefixLength) ≐ₘ numₘ(item) :=
            FirstOrder.Derives.assumption (by simp [Δ])
          have hStep' : Δ ⊢ₘ[T]
              nat_sequence_code_step_condition
                sequence trace (numₘ(prefixLength)) := by
            exact FirstOrder.Derives.context_weaken_cons
              (FirstOrder.Derives.context_weaken_cons hStepLast)
          have hFinal' : Δ ⊢ₘ[T]
              numₘ(0) ≐ₘ trace ·ₘ numₘ(prefixLength + 1) := by
            simpa [nat_sequence_code_value, finite_numeral_term,
              successor_term] using!
              FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons hFinal)
          have hStepRaw : Δ ⊢ₘ[T]
              trace ·ₘ Sₘ(numₘ(prefixLength)) ≐ₘ
                Sₘ(godel_pairₘ(
                  trace ·ₘ numₘ(prefixLength),
                  sequence ·ₘ numₘ(prefixLength))) := by
            simpa [nat_sequence_code_step_condition] using hStep'
          have hPairEquality : Δ ⊢ₘ[T]
              godel_pairₘ(
                  trace ·ₘ numₘ(prefixLength),
                  sequence ·ₘ numₘ(prefixLength)) ≐ₘ
                godel_pairₘ(numₘ(accumulator), numₘ(item)) :=
            pair_congr_of_equalities
              (trace ·ₘ numₘ(prefixLength)) (numₘ(accumulator))
              (sequence ·ₘ numₘ(prefixLength)) (numₘ(item))
              hTraceEquality hValueEquality
          have hSuccessorEquality : Δ ⊢ₘ[T]
              Sₘ(godel_pairₘ(
                trace ·ₘ numₘ(prefixLength),
                sequence ·ₘ numₘ(prefixLength))) ≐ₘ
              Sₘ(godel_pairₘ(numₘ(accumulator), numₘ(item))) :=
            successor_term_congr_of_equality
              (godel_pairₘ(
                trace ·ₘ numₘ(prefixLength),
                sequence ·ₘ numₘ(prefixLength)))
              (godel_pairₘ(numₘ(accumulator), numₘ(item)))
              hPairEquality
          have hStepEquality : Δ ⊢ₘ[T]
              trace ·ₘ numₘ(prefixLength + 1) ≐ₘ
                Sₘ(godel_pairₘ(numₘ(accumulator), numₘ(item))) := by
            have hStepToGround :=
              Metatheory.Derives.equality_trans hStepRaw hSuccessorEquality
            simpa [finite_numeral_term, successor_term] using hStepToGround
          have hGroundDelta :=
            nat_sequence_code_step_numeral_at C accumulator item (Γ := Δ)
          have hZeroEquality : Δ ⊢ₘ[T]
              numₘ(0) ≐ₘ numₘ(nat_sequence_code_step accumulator item) :=
            Metatheory.Derives.equality_trans hFinal'
              (Metatheory.Derives.equality_trans hStepEquality hGroundDelta)
          exact falsum_of_numeral_equality C
            (by simp [nat_sequence_code_step]) hZeroEquality
        constructor
        · exact FirstOrder.Derives.falsum_elim hFalse
        · intro index hIndex
          exact FirstOrder.Derives.falsum_elim hFalse
  | hSnoc xs item ih =>
      by_cases hLength : length = 0
      · subst length
        have hFinalZero : Γ ⊢ₘ[T]
            numₘ(nat_sequence_code_value (xs ++ [item])) ≐ₘ numₘ(0) :=
          Metatheory.Derives.equality_trans hFinal hZero
        have hFalse := falsum_of_numeral_equality C
          (by
            apply Nat.ne_of_gt
            exact nat_sequence_code_value_pos_of_ne_nil (by simp))
          hFinalZero
        constructor
        · exact FirstOrder.Derives.falsum_elim hFalse
        · intro index hIndex
          exact FirstOrder.Derives.falsum_elim hFalse
      · obtain ⟨prefixLength, rfl⟩ :=
          Nat.exists_eq_succ_of_ne_zero hLength
        have hStepLast := hStep prefixLength (Nat.lt_succ_self _)
        have hValueLast := hValueBound prefixLength
          (Nat.lt_succ_self _)
        have hTraceLast := hTraceBound prefixLength
          (Nat.le_succ _)
        have hCodeEquality (accumulator itemAt : Nat) :
            (sequence ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(itemAt) ::
              (trace ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(accumulator) :: Γ
                ⊢ₘ[T]
              numₘ(nat_sequence_code_step
                (nat_sequence_code_value xs) item) ≐ₘ
                numₘ(nat_sequence_code_step accumulator itemAt) := by
          let Δ : Context signature free :=
            (sequence ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(itemAt) ::
              (trace ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(accumulator) :: Γ
          have hTraceEquality :
              Δ ⊢ₘ[T] trace ·ₘ numₘ(prefixLength) ≐ₘ numₘ(accumulator) :=
            FirstOrder.Derives.assumption (by simp [Δ])
          have hValueEquality :
              Δ ⊢ₘ[T] sequence ·ₘ numₘ(prefixLength) ≐ₘ numₘ(itemAt) :=
            FirstOrder.Derives.assumption (by simp [Δ])
          have hStep' : Δ ⊢ₘ[T]
              nat_sequence_code_step_condition
                sequence trace (numₘ(prefixLength)) := by
            exact FirstOrder.Derives.context_weaken_cons
              (FirstOrder.Derives.context_weaken_cons hStepLast)
          have hFinal' : Δ ⊢ₘ[T]
              numₘ(nat_sequence_code_step
                (nat_sequence_code_value xs) item) ≐ₘ
                trace ·ₘ numₘ(prefixLength + 1) := by
            simpa [nat_sequence_code_value_append_singleton,
              finite_numeral_term, successor_term] using
              FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons hFinal)
          have hStepRaw : Δ ⊢ₘ[T]
              trace ·ₘ Sₘ(numₘ(prefixLength)) ≐ₘ
                Sₘ(godel_pairₘ(
                  trace ·ₘ numₘ(prefixLength),
                  sequence ·ₘ numₘ(prefixLength))) := by
            simpa [nat_sequence_code_step_condition] using hStep'
          have hPairEquality : Δ ⊢ₘ[T]
              godel_pairₘ(
                  trace ·ₘ numₘ(prefixLength),
                  sequence ·ₘ numₘ(prefixLength)) ≐ₘ
                godel_pairₘ(numₘ(accumulator), numₘ(itemAt)) :=
            pair_congr_of_equalities
              (trace ·ₘ numₘ(prefixLength)) (numₘ(accumulator))
              (sequence ·ₘ numₘ(prefixLength)) (numₘ(itemAt))
              hTraceEquality hValueEquality
          have hSuccessorEquality : Δ ⊢ₘ[T]
              Sₘ(godel_pairₘ(
                trace ·ₘ numₘ(prefixLength),
                sequence ·ₘ numₘ(prefixLength))) ≐ₘ
              Sₘ(godel_pairₘ(numₘ(accumulator), numₘ(itemAt))) :=
            successor_term_congr_of_equality
              (godel_pairₘ(
                trace ·ₘ numₘ(prefixLength),
                sequence ·ₘ numₘ(prefixLength)))
              (godel_pairₘ(numₘ(accumulator), numₘ(itemAt)))
              hPairEquality
          have hStepEquality : Δ ⊢ₘ[T]
              trace ·ₘ numₘ(prefixLength + 1) ≐ₘ
                Sₘ(godel_pairₘ(numₘ(accumulator), numₘ(itemAt))) := by
            have hStepToGround :=
              Metatheory.Derives.equality_trans hStepRaw hSuccessorEquality
            simpa [finite_numeral_term, successor_term] using hStepToGround
          have hGroundDelta :=
            nat_sequence_code_step_numeral_at C accumulator itemAt (Γ := Δ)
          exact Metatheory.Derives.equality_trans hFinal'
            (Metatheory.Derives.equality_trans hStepEquality hGroundDelta)
        have hFiniteCases
            (conclusion : SetOpenFormula free)
            (hBranch :
              ∀ accumulator, accumulator < bound + 1 →
                ∀ itemAt, itemAt < bound →
                  (sequence ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(itemAt) ::
                    (trace ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(accumulator) :: Γ
                      ⊢ₘ[T] conclusion) :
            Γ ⊢ₘ[T] conclusion := by
          apply C.member_elim
            (bound + 1) (trace ·ₘ numₘ(prefixLength)) conclusion hTraceLast
          intro accumulator hAccumulator
          have hValueMember :
              (trace ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(accumulator) :: Γ
                ⊢ₘ[T] (sequence ·ₘ numₘ(prefixLength)) ∈ₘ numₘ(bound) :=
            FirstOrder.Derives.context_weaken_cons hValueLast
          apply C.member_elim
            bound (sequence ·ₘ numₘ(prefixLength)) conclusion hValueMember
          intro itemAt hItemAt
          exact hBranch accumulator hAccumulator itemAt hItemAt
        have hLengthDerivation : Γ ⊢ₘ[T]
            numₘ(prefixLength.succ) ≐ₘ
              numₘ((xs ++ [item]).length) := by
          apply hFiniteCases
          intro accumulator hAccumulator itemAt hItemAt
          let Δ : Context signature free :=
            (sequence ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(itemAt) ::
              (trace ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(accumulator) :: Γ
          have hCode := hCodeEquality accumulator itemAt
          by_cases hMatch :
              nat_sequence_code_step
                (nat_sequence_code_value xs) item =
              nat_sequence_code_step accumulator itemAt
          · have hPairCode :
                godel_pair_value (nat_sequence_code_value xs) item =
                  godel_pair_value accumulator itemAt := by
              apply Nat.succ.inj
              simpa [nat_sequence_code_step] using hMatch
            rcases godel_pair_value_eq_iff.mp hPairCode with
              ⟨hAccumulatorCode, hItemCode⟩
            subst accumulator
            subst itemAt
            have hTraceEquality :
                Δ ⊢ₘ[T] trace ·ₘ numₘ(prefixLength) ≐ₘ
                  numₘ(nat_sequence_code_value xs) :=
              FirstOrder.Derives.assumption (by simp [Δ])
            have hZeroDelta : Δ ⊢ₘ[T]
                trace ·ₘ numₘ(0) ≐ₘ numₘ(0) :=
              FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons hZero)
            have hStepPrefix :
                ∀ index, index < prefixLength →
                  Δ ⊢ₘ[T]
                    nat_sequence_code_step_condition
                      sequence trace (numₘ(index)) := by
              intro index hIndex
              exact FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons
                  (hStep index (by omega)))
            have hValuePrefix :
                ∀ index, index < prefixLength →
                  Δ ⊢ₘ[T] (sequence ·ₘ numₘ(index)) ∈ₘ numₘ(bound) := by
              intro index hIndex
              exact FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons
                  (hValueBound index (by omega)))
            have hTracePrefix :
                ∀ index, index ≤ prefixLength →
                  Δ ⊢ₘ[T] (trace ·ₘ numₘ(index)) ∈ₘ numₘ(bound + 1) := by
              intro index hIndex
              exact FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons
                  (hTraceBound index (by omega)))
            have hFinalPrefix : Δ ⊢ₘ[T]
                numₘ(nat_sequence_code_value xs) ≐ₘ
                  trace ·ₘ numₘ(prefixLength) :=
              Metatheory.Derives.equality_symm hTraceEquality
            have hIH := ih (Γ := Δ) prefixLength hZeroDelta
              hStepPrefix hValuePrefix hTracePrefix hFinalPrefix
            have hSuccessorLength :=
              successor_term_congr_of_equality
                (numₘ(prefixLength)) (numₘ(xs.length)) hIH.1
            simpa [Δ, List.length_append,
              finite_numeral_term, successor_term] using hSuccessorLength
          · exact FirstOrder.Derives.falsum_elim <|
              falsum_of_numeral_equality C hMatch hCode
        constructor
        · exact hLengthDerivation
        · intro index hIndex
          apply hFiniteCases
          intro accumulator hAccumulator itemAt hItemAt
          let Δ : Context signature free :=
            (sequence ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(itemAt) ::
              (trace ·ₘ numₘ(prefixLength)) ≐ₘ numₘ(accumulator) :: Γ
          have hCode := hCodeEquality accumulator itemAt
          by_cases hMatch :
              nat_sequence_code_step
                (nat_sequence_code_value xs) item =
              nat_sequence_code_step accumulator itemAt
          · have hPairCode :
                godel_pair_value (nat_sequence_code_value xs) item =
                  godel_pair_value accumulator itemAt := by
              apply Nat.succ.inj
              simpa [nat_sequence_code_step] using hMatch
            rcases godel_pair_value_eq_iff.mp hPairCode with
              ⟨hAccumulatorCode, hItemCode⟩
            subst accumulator
            subst itemAt
            have hTraceEquality :
                Δ ⊢ₘ[T] trace ·ₘ numₘ(prefixLength) ≐ₘ
                  numₘ(nat_sequence_code_value xs) :=
              FirstOrder.Derives.assumption (by simp [Δ])
            have hZeroDelta : Δ ⊢ₘ[T]
                trace ·ₘ numₘ(0) ≐ₘ numₘ(0) :=
              FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons hZero)
            have hStepPrefix :
                ∀ index, index < prefixLength →
                  Δ ⊢ₘ[T]
                    nat_sequence_code_step_condition
                      sequence trace (numₘ(index)) := by
              intro prefixIndex hPrefixIndex
              exact FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons
                  (hStep prefixIndex (by omega)))
            have hValuePrefix :
                ∀ prefixIndex, prefixIndex < prefixLength →
                  Δ ⊢ₘ[T]
                    (sequence ·ₘ numₘ(prefixIndex)) ∈ₘ numₘ(bound) := by
              intro prefixIndex hPrefixIndex
              exact FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons
                  (hValueBound prefixIndex (by omega)))
            have hTracePrefix :
                ∀ prefixIndex, prefixIndex ≤ prefixLength →
                  Δ ⊢ₘ[T]
                    (trace ·ₘ numₘ(prefixIndex)) ∈ₘ numₘ(bound + 1) := by
              intro prefixIndex hPrefixIndex
              exact FirstOrder.Derives.context_weaken_cons
                (FirstOrder.Derives.context_weaken_cons
                  (hTraceBound prefixIndex (by omega)))
            have hFinalPrefix : Δ ⊢ₘ[T]
                numₘ(nat_sequence_code_value xs) ≐ₘ
                  trace ·ₘ numₘ(prefixLength) :=
              Metatheory.Derives.equality_symm hTraceEquality
            have hPrefix := ih (Γ := Δ) prefixLength hZeroDelta
              hStepPrefix hValuePrefix hTracePrefix hFinalPrefix
            have hApplicationEquality : Δ ⊢ₘ[T]
                sequence ·ₘ numₘ(prefixLength) ≐ₘ
                  sequence ·ₘ numₘ(xs.length) :=
              function_application_term_congr_argument_of_equality
                sequence (numₘ(prefixLength)) (numₘ(xs.length)) hPrefix.1
            by_cases hPrefixIndex : index < xs.length
            · have hPoint := hPrefix.2 index hPrefixIndex
              simpa [Δ, List.getElem_append, hPrefixIndex] using hPoint
            · have hIndexEq : index = xs.length := by
                have hIndex' : index < xs.length + 1 := by
                  simpa [List.length_append] using hIndex
                omega
              subst index
              have hValueEquality : Δ ⊢ₘ[T]
                  sequence ·ₘ numₘ(prefixLength) ≐ₘ numₘ(item) :=
                FirstOrder.Derives.assumption (by simp [Δ])
              have hLast := Metatheory.Derives.equality_trans
                (Metatheory.Derives.equality_symm hApplicationEquality)
                hValueEquality
              simpa [Δ, List.getElem_append] using hLast
          · exact FirstOrder.Derives.falsum_elim <|
              falsum_of_numeral_equality C hMatch hCode

/-! ## 函数图外延 -/

private theorem term_substituteMapped_weakenFree_cons
      {bound free : SetContext}
      (replacement : SetTerm bound (SetSort.set :: free))
      (term : SetTerm bound free) :
      (term.weakenFree SetSort.set).substituteMapped
          VariableSubstitution.boundId
          (VariableSubstitution.cons replacement
            (VariableSubstitution.of_renaming
            (VariableRenaming.weaken SetSort.set))) =
        term.weakenFree SetSort.set := by
  exact Term.rec
    (motive_1 := fun _ term =>
      (term.weakenFree SetSort.set).substituteMapped
          VariableSubstitution.boundId
          (VariableSubstitution.cons replacement
            (VariableSubstitution.of_renaming
              (VariableRenaming.weaken SetSort.set))) =
        term.weakenFree SetSort.set)
    (motive_2 := fun _ arguments =>
      (arguments.weakenFree SetSort.set).substituteMapped
          VariableSubstitution.boundId
          (VariableSubstitution.cons replacement
            (VariableSubstitution.of_renaming
              (VariableRenaming.weaken SetSort.set))) =
        arguments.weakenFree SetSort.set)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun function arguments ih => by
      change Term.app function
          ((arguments.weakenFree SetSort.set).substituteMapped
            VariableSubstitution.boundId
            (VariableSubstitution.cons replacement
              (VariableSubstitution.of_renaming
                (VariableRenaming.weaken SetSort.set)))) =
        Term.app function (arguments.weakenFree SetSort.set)
      rw [ih])
    rfl
    (fun head tail ihHead ihTail => by
      change Arguments.cons
          ((head.weakenFree SetSort.set).substituteMapped
            VariableSubstitution.boundId
            (VariableSubstitution.cons replacement
              (VariableSubstitution.of_renaming
                (VariableRenaming.weaken SetSort.set))))
          ((tail.weakenFree SetSort.set).substituteMapped
            VariableSubstitution.boundId
            (VariableSubstitution.cons replacement
              (VariableSubstitution.of_renaming
                (VariableRenaming.weaken SetSort.set)))) =
        Arguments.cons (head.weakenFree SetSort.set)
          (tail.weakenFree SetSort.set)
      rw [ihHead, ihTail])
    term

private theorem arguments_substituteMapped_weakenFree_cons
      {bound free : SetContext} {sorts : List signature.SortSymbol}
      (replacement : SetTerm bound (SetSort.set :: free))
      (arguments : Arguments signature bound free sorts) :
      (arguments.weakenFree SetSort.set).substituteMapped
          VariableSubstitution.boundId
          (VariableSubstitution.cons replacement
            (VariableSubstitution.of_renaming
              (VariableRenaming.weaken SetSort.set))) =
        arguments.weakenFree SetSort.set := by
  exact Arguments.rec
    (motive_1 := fun _ term =>
      (term.weakenFree SetSort.set).substituteMapped
          VariableSubstitution.boundId
          (VariableSubstitution.cons replacement
            (VariableSubstitution.of_renaming
              (VariableRenaming.weaken SetSort.set))) =
        term.weakenFree SetSort.set)
    (motive_2 := fun _ arguments =>
      (arguments.weakenFree SetSort.set).substituteMapped
          VariableSubstitution.boundId
          (VariableSubstitution.cons replacement
            (VariableSubstitution.of_renaming
              (VariableRenaming.weaken SetSort.set))) =
        arguments.weakenFree SetSort.set)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun function arguments ih => by
      change Term.app function
          ((arguments.weakenFree SetSort.set).substituteMapped
            VariableSubstitution.boundId
            (VariableSubstitution.cons replacement
              (VariableSubstitution.of_renaming
                (VariableRenaming.weaken SetSort.set)))) =
        Term.app function (arguments.weakenFree SetSort.set)
      rw [ih])
    rfl
    (fun head tail ihHead ihTail => by
      change Arguments.cons
          ((head.weakenFree SetSort.set).substituteMapped
            VariableSubstitution.boundId
            (VariableSubstitution.cons replacement
              (VariableSubstitution.of_renaming
                (VariableRenaming.weaken SetSort.set))))
          ((tail.weakenFree SetSort.set).substituteMapped
            VariableSubstitution.boundId
            (VariableSubstitution.cons replacement
              (VariableSubstitution.of_renaming
                (VariableRenaming.weaken SetSort.set)))) =
        Arguments.cons (head.weakenFree SetSort.set)
          (tail.weakenFree SetSort.set)
      rw [ihHead, ihTail])
    arguments

theorem function_equality_of_extensional_agreement
    {T : SetTheory}
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (left right : SetOpenTerm free)
    (hLeftFunction : Γ ⊢ₘ[T] is_function_formula left)
    (hRightFunction : Γ ⊢ₘ[T] is_function_formula right)
    (hAgreement : Γ ⊢ₘ[T]
      function_extensional_agreement left right) :
    Γ ⊢ₘ[T] left ≐ₘ right := by
  let Δ : Context signature (SetSort.set :: free) :=
    FreshVariable.extendContext SetSort.set Γ
  let member : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest (σ := signature) (free := free) SetSort.set
  have hLeftFunction' : Δ ⊢ₘ[T]
      is_function_formula (left.weakenFree SetSort.set) := by
    have hRenamed := FirstOrder.Derives.free_renaming
      (T := T) (VariableRenaming.weaken SetSort.set) hLeftFunction
    simpa only [Δ, FreshVariable.extendContext, Formula.weakenFree,
      Formula.renameFree, Renaming.weakenFree] using! hRenamed
  have hRightFunction' : Δ ⊢ₘ[T]
      is_function_formula (right.weakenFree SetSort.set) := by
    have hRenamed := FirstOrder.Derives.free_renaming
      (T := T) (VariableRenaming.weaken SetSort.set) hRightFunction
    simpa only [Δ, FreshVariable.extendContext, Formula.weakenFree,
      Formula.renameFree, Renaming.weakenFree] using! hRenamed
  have hDomainAgreement : Δ ⊢ₘ[T]
      domₘ(left.weakenFree SetSort.set) ≐ₘ
        domₘ(right.weakenFree SetSort.set) := by
    have hRenamed := FirstOrder.Derives.free_renaming
      (T := T) (VariableRenaming.weaken SetSort.set)
        (FirstOrder.Derives.conj_elim_left hAgreement)
    simpa only [Δ, FreshVariable.extendContext, Formula.weakenFree,
      Formula.renameFree, Renaming.weakenFree] using! hRenamed
  have hPointwiseAt (input : SetOpenTerm (SetSort.set :: free)) :
      Δ ⊢ₘ[T]
        (input ∈ₘ domₘ(left.weakenFree SetSort.set)) ⟶ₘ
          ((left.weakenFree SetSort.set ·ₘ input) ≐ₘ
            (right.weakenFree SetSort.set ·ₘ input)) := by
    let ρ : VariableSubstitution signature free []
        (SetSort.set :: free) :=
      VariableSubstitution.of_renaming
        (bound := []) (VariableRenaming.weaken SetSort.set)
    let body : SetOpenFormula (SetSort.set :: free) :=
      (FreshVariable.newest
          (σ := signature) (free := free) SetSort.set ∈ₘ
        domₘ(left.weakenFree SetSort.set)) ⟶ₘ
          ((left.weakenFree SetSort.set ·ₘ
              FreshVariable.newest
                (σ := signature) (free := free) SetSort.set) ≐ₘ
            (right.weakenFree SetSort.set ·ₘ
              FreshVariable.newest
                (σ := signature) (free := free) SetSort.set))
    let τ : VariableSubstitution signature (SetSort.set :: free) []
        (SetSort.set :: free) :=
      VariableSubstitution.cons input ρ
    have hUniversal := FirstOrder.Derives.free_substitution
      (T := T) ρ
        (FirstOrder.Derives.conj_elim_right hAgreement)
    rw [Formula.substituteFree_forallFreeTop] at hUniversal
    have hAt := FirstOrder.Derives.forall_elim input hUniversal
    rw [Formula.instantiateTop_abstractFreeTop] at hAt
    have hAt' : Context.substituteFree ρ Γ ⊢ₘ[T]
        Formula.instantiateFreeTop input
          (Formula.substituteFree
            (VariableSubstitution.liftFree SetSort.set ρ) body) := by
      simpa [body, function_extensional_agreement,
        FreshVariable.newest] using! hAt
    have hFormula :
        Formula.instantiateFreeTop input
            (Formula.substituteFree
              (VariableSubstitution.liftFree SetSort.set ρ) body) =
          Formula.substituteFree τ body := by
      change
        Formula.substituteMapped VariableSubstitution.boundId
            (VariableSubstitution.instantiateFreeTop input)
            (Formula.substituteMapped VariableSubstitution.boundId
              (VariableSubstitution.liftFree SetSort.set ρ) body) =
          Formula.substituteMapped VariableSubstitution.boundId τ body
      rw [Formula.substituteMapped_comp]
      congr
      funext resultSort entry
      cases entry with
      | here =>
          rfl
      | there previous =>
          simp [τ, ρ, VariableSubstitution.cons,
            VariableSubstitution.liftFree]
    rw [hFormula] at hAt'
    have hAtContext := FirstOrder.Derives.context_weaken
      (Δ := Δ)
      (by
        intro candidate hMember
        obtain ⟨candidateFormula, hCandidate, hCandidateEq⟩ :=
          List.mem_map.mp hMember
        apply List.mem_map.mpr
        refine ⟨candidateFormula, hCandidate, ?_⟩
        rw [← hCandidateEq]
        simp [ρ, Formula.substituteFree, Substitution.free_map,
          Formula.substitute,
          Formula.weakenFree,
          Renaming.weakenFree, Renaming.free,
          Formula.rename])
      hAt'
    simpa [τ, ρ, body, Context.substituteFree,
      Formula.substituteFree, Substitution.free_map,
      Formula.substitute, Formula.substituteMapped,
      Term.substituteFree, Term.substitute, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.cons,
      VariableSubstitution.empty, VariableSubstitution.freeId,
      VariableSubstitution.boundId, VariableSubstitution.weakenBound,
      VariableSubstitution.liftFree, FreshVariable.extendContext,
      FreshVariable.newest,
      term_substituteMapped_weakenFree_cons,
      arguments_substituteMapped_weakenFree_cons] using!
      hAtContext
  have hLeftCoordinateIff : Δ ⊢ₘ[T]
      (member ∈ₘ left.weakenFree SetSort.set) ↔ₘ
        function_graph_member_condition
          (left.weakenFree SetSort.set) member := by
    have hIff := FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_function_application hSentence)
      (is_function_member_iff_coordinates
        (Γ := Δ) (left.weakenFree SetSort.set) member)
    exact FirstOrder.Derives.imp_elim hIff hLeftFunction'
  have hRightCoordinateIff : Δ ⊢ₘ[T]
      (member ∈ₘ right.weakenFree SetSort.set) ↔ₘ
        function_graph_member_condition
          (right.weakenFree SetSort.set) member := by
    have hIff := FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_function_application hSentence)
      (is_function_member_iff_coordinates
        (Γ := Δ) (right.weakenFree SetSort.set) member)
    exact FirstOrder.Derives.imp_elim hIff hRightFunction'
  have hMembershipAgreement : Γ ⊢ₘ[T]
      membership_agreement left right := by
    unfold membership_agreement
    apply FirstOrder.Derives.forall_intro
    apply FirstOrder.Derives.iff_intro
    · apply FirstOrder.Derives.imp_intro
      let Ε : Context signature (SetSort.set :: free) :=
        (member ∈ₘ left.weakenFree SetSort.set) :: Δ
      have hMember : Ε ⊢ₘ[T]
          member ∈ₘ left.weakenFree SetSort.set :=
        FirstOrder.Derives.assumption (by simp [Ε])
      have hCoordinates : Ε ⊢ₘ[T]
          function_graph_member_condition
            (left.weakenFree SetSort.set) member := by
        exact FirstOrder.Derives.iff_elim_left
          (FirstOrder.Derives.context_weaken_cons hLeftCoordinateIff)
          hMember
      have hOrdered : Ε ⊢ₘ[T]
          is_ordered_pair_formula member := by
        simpa [function_graph_member_condition] using
          FirstOrder.Derives.conj_elim_left hCoordinates
      have hDomainLeft : Ε ⊢ₘ[T]
          (member)₀ₘ ∈ₘ domₘ(left.weakenFree SetSort.set) := by
        simpa [function_graph_member_condition] using
          FirstOrder.Derives.conj_elim_left
            (FirstOrder.Derives.conj_elim_right hCoordinates)
      have hValueLeft : Ε ⊢ₘ[T]
          (member)₁ₘ ≐ₘ
            (left.weakenFree SetSort.set ·ₘ (member)₀ₘ) := by
        simpa [function_graph_member_condition] using
          FirstOrder.Derives.conj_elim_right
            (FirstOrder.Derives.conj_elim_right hCoordinates)
      have hDomainRight : Ε ⊢ₘ[T]
          (member)₀ₘ ∈ₘ domₘ(right.weakenFree SetSort.set) :=
        FirstOrder.Derives.iff_elim_left
          (FirstOrder.Derives.context_weaken_cons
            (membership_right_iff_of_equality
              (member)₀ₘ
              (domₘ(left.weakenFree SetSort.set))
              (domₘ(right.weakenFree SetSort.set))
              hDomainAgreement))
          hDomainLeft
      have hPointwiseAt : Ε ⊢ₘ[T]
          (left.weakenFree SetSort.set ·ₘ (member)₀ₘ) ≐ₘ
            (right.weakenFree SetSort.set ·ₘ (member)₀ₘ) :=
        FirstOrder.Derives.imp_elim
          (FirstOrder.Derives.context_weaken_cons
            (hPointwiseAt (member)₀ₘ))
          hDomainLeft
      have hValueRight : Ε ⊢ₘ[T]
          (member)₁ₘ ≐ₘ
            (right.weakenFree SetSort.set ·ₘ (member)₀ₘ) :=
        Metatheory.Derives.equality_trans hValueLeft hPointwiseAt
      have hRightCoordinates : Ε ⊢ₘ[T]
          function_graph_member_condition
            (right.weakenFree SetSort.set) member := by
        simpa [function_graph_member_condition] using
          FirstOrder.Derives.conj_intro hOrdered
            (FirstOrder.Derives.conj_intro hDomainRight hValueRight)
      exact FirstOrder.Derives.iff_elim_right
        (FirstOrder.Derives.context_weaken_cons hRightCoordinateIff)
        hRightCoordinates
    · apply FirstOrder.Derives.imp_intro
      let Ε : Context signature (SetSort.set :: free) :=
        (member ∈ₘ right.weakenFree SetSort.set) :: Δ
      have hMember : Ε ⊢ₘ[T]
          member ∈ₘ right.weakenFree SetSort.set :=
        FirstOrder.Derives.assumption (by simp [Ε])
      have hCoordinates : Ε ⊢ₘ[T]
          function_graph_member_condition
            (right.weakenFree SetSort.set) member := by
        exact FirstOrder.Derives.iff_elim_left
          (FirstOrder.Derives.context_weaken_cons hRightCoordinateIff)
          hMember
      have hOrdered : Ε ⊢ₘ[T]
          is_ordered_pair_formula member := by
        simpa [function_graph_member_condition] using
          FirstOrder.Derives.conj_elim_left hCoordinates
      have hDomainRight : Ε ⊢ₘ[T]
          (member)₀ₘ ∈ₘ domₘ(right.weakenFree SetSort.set) := by
        simpa [function_graph_member_condition] using
          FirstOrder.Derives.conj_elim_left
            (FirstOrder.Derives.conj_elim_right hCoordinates)
      have hValueRight : Ε ⊢ₘ[T]
          (member)₁ₘ ≐ₘ
            (right.weakenFree SetSort.set ·ₘ (member)₀ₘ) := by
        simpa [function_graph_member_condition] using
          FirstOrder.Derives.conj_elim_right
            (FirstOrder.Derives.conj_elim_right hCoordinates)
      have hDomainLeft : Ε ⊢ₘ[T]
          (member)₀ₘ ∈ₘ domₘ(left.weakenFree SetSort.set) :=
        FirstOrder.Derives.iff_elim_right
          (FirstOrder.Derives.context_weaken_cons
            (membership_right_iff_of_equality
              (member)₀ₘ
              (domₘ(left.weakenFree SetSort.set))
              (domₘ(right.weakenFree SetSort.set))
              hDomainAgreement))
          hDomainRight
      have hPointwiseAt : Ε ⊢ₘ[T]
          (left.weakenFree SetSort.set ·ₘ (member)₀ₘ) ≐ₘ
            (right.weakenFree SetSort.set ·ₘ (member)₀ₘ) :=
        FirstOrder.Derives.imp_elim
          (FirstOrder.Derives.context_weaken_cons
            (hPointwiseAt (member)₀ₘ))
          hDomainLeft
      have hValueLeft : Ε ⊢ₘ[T]
          (member)₁ₘ ≐ₘ
            (left.weakenFree SetSort.set ·ₘ (member)₀ₘ) :=
        Metatheory.Derives.equality_trans hValueRight
          (Metatheory.Derives.equality_symm hPointwiseAt)
      have hLeftCoordinates : Ε ⊢ₘ[T]
          function_graph_member_condition
            (left.weakenFree SetSort.set) member := by
        simpa [function_graph_member_condition] using
          FirstOrder.Derives.conj_intro hOrdered
            (FirstOrder.Derives.conj_intro hDomainLeft hValueLeft)
      exact FirstOrder.Derives.iff_elim_right
        (FirstOrder.Derives.context_weaken_cons hLeftCoordinateIff)
        hLeftCoordinates
  have hExtensionality : Γ ⊢ₘ[T]
      extensionality_instance left right := by
    exact FirstOrder.Derives.theory_weaken
      (fun hSentence => S.contains_function_application
        (extensionality_theory_subset_function_application_theory hSentence))
      (extensionality_instance_derives (Γ := Γ) left right)
  simpa [extensionality_instance, agreement_to_equality] using
    FirstOrder.Derives.imp_elim hExtensionality hMembershipAgreement

/-! ## 完整自然数序列回放 -/

/-- 将递归轨迹数据直接回放为规范自然数有限图。 -/
theorem nat_sequence_code_replay_of_data
    {T : SetTheory}
    (C : CertificateCore T)
    (S : FiniteSequenceEvaluationSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (sequence trace : SetOpenTerm free)
    (tokens : List Nat)
    (length bound : Nat)
    (hFunction : Γ ⊢ₘ[T] is_function_formula sequence)
    (hDomain : Γ ⊢ₘ[T]
      domₘ(sequence) ≐ₘ numₘ(length))
    (hZero : Γ ⊢ₘ[T]
      (trace ·ₘ numₘ(0)) ≐ₘ numₘ(0))
    (hStep : ∀ index, index < length →
      Γ ⊢ₘ[T]
        nat_sequence_code_step_condition
          sequence trace (numₘ(index)))
    (hValueBound : ∀ index, index < length →
      Γ ⊢ₘ[T]
        (sequence ·ₘ numₘ(index)) ∈ₘ numₘ(bound))
    (hTraceBound : ∀ index, index ≤ length →
      Γ ⊢ₘ[T]
        (trace ·ₘ numₘ(index)) ∈ₘ numₘ(bound + 1))
    (hFinal : Γ ⊢ₘ[T]
      numₘ(nat_sequence_code_value tokens) ≐ₘ
        (trace ·ₘ numₘ(length))) :
    Γ ⊢ₘ[T] sequence ≐ₘ nat_sequence_graph_term tokens := by
  have hUnique := nat_sequence_code_prefix_unique C sequence trace tokens
    length bound hZero hStep hValueBound hTraceBound hFinal
  let standard : SetOpenTerm free := nat_sequence_graph_term tokens
  have hStandardFunction : Γ ⊢ₘ[T] is_function_formula standard := by
    simpa [standard, nat_sequence_graph_term] using
      (standard_sequence_from_is_function
        (Γ := Γ) S.toFiniteSequenceGraphSupport 0
          (tokens.map fun token => numₘ(token)))
  have hDomainTokens : Γ ⊢ₘ[T]
      domₘ(sequence) ≐ₘ numₘ(tokens.length) :=
    Metatheory.Derives.equality_trans hDomain hUnique.1
  have hStandardDomain : Γ ⊢ₘ[T]
      domₘ(standard) ≐ₘ numₘ(tokens.length) := by
    simpa [standard] using
      (nat_sequence_graph_domain_eq
        (Γ := Γ) S.toFiniteSequenceGraphSupport tokens)
  have hDomainAgreement : Γ ⊢ₘ[T]
      domₘ(sequence) ≐ₘ domₘ(standard) :=
    Metatheory.Derives.equality_trans hDomainTokens
      (Metatheory.Derives.equality_symm hStandardDomain)
  have hPointwise : Γ ⊢ₘ[T]
      Formula.forallFreeTop SetSort.set
        (((.fvar .here : SetOpenTerm (SetSort.set :: free)) ∈ₘ
            domₘ(sequence.weakenFree SetSort.set)) ⟶ₘ
          ((sequence.weakenFree SetSort.set ·ₘ
              (.fvar .here : SetOpenTerm (SetSort.set :: free))) ≐ₘ
            (standard.weakenFree SetSort.set ·ₘ
              (.fvar .here : SetOpenTerm (SetSort.set :: free))))) := by
    apply FirstOrder.Derives.forall_intro
    let Δ : Context signature (SetSort.set :: free) :=
      FreshVariable.extendContext SetSort.set Γ
    let input : SetOpenTerm (SetSort.set :: free) :=
      FreshVariable.newest (σ := signature) (free := free) SetSort.set
    change Δ ⊢ₘ[T]
      (input ∈ₘ domₘ(sequence.weakenFree SetSort.set)) ⟶ₘ
        ((sequence.weakenFree SetSort.set ·ₘ input) ≐ₘ
          (standard.weakenFree SetSort.set ·ₘ input))
    apply FirstOrder.Derives.imp_intro
    let Ε : Context signature (SetSort.set :: free) :=
      (input ∈ₘ domₘ(sequence.weakenFree SetSort.set)) :: Δ
    have hInput : Ε ⊢ₘ[T]
        input ∈ₘ domₘ(sequence.weakenFree SetSort.set) :=
      FirstOrder.Derives.assumption (by simp [Ε])
    have hDomainAt : Δ ⊢ₘ[T]
        domₘ(sequence.weakenFree SetSort.set) ≐ₘ
          numₘ(tokens.length) := by
      have hRenamed := FirstOrder.Derives.free_renaming
        (T := T) (VariableRenaming.weaken SetSort.set) hDomainTokens
      have hHead :
          Formula.renameFree (VariableRenaming.weaken SetSort.set)
              (domₘ(sequence) ≐ₘ numₘ(tokens.length)) =
            domₘ(sequence.weakenFree SetSort.set) ≐ₘ
              numₘ(tokens.length) := by
        have hDomainTerm :
            (domₘ(sequence)).renameMapped
                (VariableRenaming.id)
                (VariableRenaming.weaken SetSort.set) =
              domₘ(sequence.weakenFree SetSort.set) := by
          rw [domain_term_renameMapped]
          rfl
        change
          ((domₘ(sequence)).renameMapped
              (VariableRenaming.id)
              (VariableRenaming.weaken SetSort.set) ≐ₘ
            (numₘ(tokens.length)).renameMapped
              (VariableRenaming.id)
              (VariableRenaming.weaken SetSort.set)) =
          (domₘ(sequence.weakenFree SetSort.set) ≐ₘ
            numₘ(tokens.length))
        rw [hDomainTerm, finite_numeral_term_renameMapped]
      have hTail :
          List.map (Formula.renameFree (VariableRenaming.weaken SetSort.set)) Γ =
            FreshVariable.extendContext SetSort.set Γ := by
        rfl
      rw [hHead, hTail] at hRenamed
      exact hRenamed
    have hInputNumeral : Ε ⊢ₘ[T]
        input ∈ₘ numₘ(tokens.length) :=
      FirstOrder.Derives.iff_elim_left
        (FirstOrder.Derives.context_weaken_cons
          (membership_right_iff_of_equality
            input (domₘ(sequence.weakenFree SetSort.set))
            (numₘ(tokens.length)) hDomainAt))
        hInput
    apply C.member_elim tokens.length input
      ((sequence.weakenFree SetSort.set ·ₘ input) ≐ₘ
        (standard.weakenFree SetSort.set ·ₘ input)) hInputNumeral
    intro index hIndex
    let Ζ : Context signature (SetSort.set :: free) :=
      (input ≐ₘ numₘ(index)) :: Ε
    have hInputEquality : Ζ ⊢ₘ[T]
        input ≐ₘ numₘ(index) :=
      FirstOrder.Derives.assumption (by simp [Ζ])
    have hPrefix : Ζ ⊢ₘ[T]
        sequence.weakenFree SetSort.set ·ₘ numₘ(index) ≐ₘ
          numₘ(tokens[index]'hIndex) := by
      have hRenamed := FirstOrder.Derives.free_renaming
        (T := T) (VariableRenaming.weaken SetSort.set)
          (hUnique.2 index hIndex)
      have hAt : Δ ⊢ₘ[T]
          sequence.weakenFree SetSort.set ·ₘ numₘ(index) ≐ₘ
            numₘ(tokens[index]'hIndex) := by
        simpa [Δ, FreshVariable.extendContext, Formula.weakenFree,
          Formula.renameFree, Formula.rename, Renaming.weakenFree,
          Renaming.free, Formula.renameMapped, Term.renameMapped,
          Arguments.renameMapped, function_application_term_renameMapped,
          finite_numeral_term_renameMapped] using! hRenamed
      exact FirstOrder.Derives.context_weaken_cons
        (FirstOrder.Derives.context_weaken_cons hAt)
    have hSequenceAt : Ζ ⊢ₘ[T]
        sequence.weakenFree SetSort.set ·ₘ input ≐ₘ
          numₘ(tokens[index]'hIndex) := by
      have hApplication :=
        function_application_term_congr_argument_of_equality
          (sequence.weakenFree SetSort.set) input (numₘ(index))
          hInputEquality
      exact Metatheory.Derives.equality_trans hApplication hPrefix
    have hCanonicalAtNumeral : Ζ ⊢ₘ[T]
        numₘ(tokens[index]'hIndex) ≐ₘ
          (standard.weakenFree SetSort.set ·ₘ numₘ(index)) := by
      let elements : List (SetOpenTerm (SetSort.set :: free)) :=
        tokens.map
          (fun token =>
            (numₘ(token) : SetOpenTerm (SetSort.set :: free)))
      have hGet : elements[index]? =
          some (numₘ(tokens[index]'hIndex)) := by
        have hIndexElements : index < elements.length := by
          simpa [elements] using hIndex
        simpa [elements] using
          (List.getElem?_eq_getElem
            (l := elements) (i := index) hIndexElements)
      have hApply := standard_sequence_from_getElem?_apply_eq
        (Γ := Ζ) S 0 (elements := elements) hGet
      simpa [standard, nat_sequence_graph_term,
        standard_sequence_from_weakenFree,
        finite_numeral_term_weakenFree, Function.comp_def] using hApply
    have hCanonicalApplication : Ζ ⊢ₘ[T]
        (standard.weakenFree SetSort.set ·ₘ numₘ(index)) ≐ₘ
          (standard.weakenFree SetSort.set ·ₘ input) := by
      have hApplication :=
        function_application_term_congr_argument_of_equality
          (standard.weakenFree SetSort.set) (numₘ(index)) input
          (Metatheory.Derives.equality_symm hInputEquality)
      exact hApplication
    exact Metatheory.Derives.equality_trans hSequenceAt
      (Metatheory.Derives.equality_trans hCanonicalAtNumeral
        hCanonicalApplication)
  have hAgreement : Γ ⊢ₘ[T]
      function_extensional_agreement sequence standard := by
    simpa [function_extensional_agreement] using
      FirstOrder.Derives.conj_intro hDomainAgreement hPointwise
  simpa [standard] using
    function_equality_of_extensional_agreement S sequence standard
      hFunction hStandardFunction hAgreement

/-! ## 自然数序列条件的直接唯一性 -/

/-- 内在自然数序列条件与规范 numeral 码直接决定规范有限图。 -/
theorem nat_sequence_code_condition_unique_of_code_equality
    {T : SetTheory}
    (C : CertificateCore T)
    (S : FiniteSequenceSpaceSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (sequence code : SetOpenTerm free)
    (tokens : List Nat)
    (hCondition : Γ ⊢ₘ[T]
      nat_sequence_code_condition sequence code)
    (hCodeEquality : Γ ⊢ₘ[T]
      code ≐ₘ numₘ(nat_sequence_code_value tokens)) :
    Γ ⊢ₘ[T] sequence ≐ₘ nat_sequence_graph_term tokens := by
  let bound : Nat := nat_sequence_code_value tokens
  have hParts := nat_sequence_code_condition_parts sequence code hCondition
  have hOmegaNonempty : Γ ⊢ₘ[T] ωₘ ≠ₘ ∅ₘ := by
    apply FirstOrder.Derives.neg_intro
    let Δ : Context signature free := (ωₘ ≐ₘ ∅ₘ) :: Γ
    have hEquality : Δ ⊢ₘ[T] ωₘ ≐ₘ ∅ₘ :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hCodeMember : Δ ⊢ₘ[T] code ∈ₘ ωₘ :=
      FirstOrder.Derives.context_weaken_cons hParts.code_omega
    have hEmptyMember : Δ ⊢ₘ[T] code ∈ₘ ∅ₘ :=
      FirstOrder.Derives.iff_elim_left
        (membership_right_iff_of_equality code ωₘ ∅ₘ hEquality)
        hCodeMember
    have hNoMembers : Δ ⊢ₘ[T] ¬ₘ (code ∈ₘ ∅ₘ) :=
      FirstOrder.Derives.theory_weaken
        (fun hSentence => S.toArithmeticSupport.contains_empty_set hSentence)
        (empty_set_term_has_no_members (Γ := Δ) code)
    exact FirstOrder.Derives.neg_elim hEmptyMember hNoMembers
  have hMemberCondition :=
    sequence_space_member_implies_member_condition
      S ωₘ sequence hOmegaNonempty hParts.sequence_space
  have hFiniteCondition :=
    finite_sequence_member_condition_implies_finite_sequence
      S ωₘ sequence hMemberCondition
  have hFunction : Γ ⊢ₘ[T] is_function_formula sequence := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conj_elim_left hFiniteCondition
  have hCodeEqualityBound : Γ ⊢ₘ[T] code ≐ₘ numₘ(bound) := by
    simpa [bound] using hCodeEquality
  have hSuccessorCodeEquality : Γ ⊢ₘ[T]
      Sₘ(code) ≐ₘ Sₘ(numₘ(bound)) :=
    successor_term_congr_of_equality code (numₘ(bound))
      hCodeEqualityBound
  have hDomainSuccessor : Γ ⊢ₘ[T]
      domₘ(sequence) ∈ₘ Sₘ(numₘ(bound)) :=
    FirstOrder.Derives.iff_elim_left
      (membership_right_iff_of_equality
        (domₘ(sequence)) (Sₘ(code)) (Sₘ(numₘ(bound)))
        hSuccessorCodeEquality)
      hParts.domain_code_bound
  have hDomainMember : Γ ⊢ₘ[T]
      domₘ(sequence) ∈ₘ numₘ(bound + 1) := by
    simpa [finite_numeral_term, successor_term] using hDomainSuccessor
  apply C.member_elim (bound + 1) (domₘ(sequence))
    (sequence ≐ₘ nat_sequence_graph_term tokens) hDomainMember
  intro length hLength
  let domainEquation : SetOpenFormula free :=
    domₘ(sequence) ≐ₘ numₘ(length)
  let Δ : Context signature free := domainEquation :: Γ
  change Δ ⊢ₘ[T] sequence ≐ₘ nat_sequence_graph_term tokens
  have hDomain : Δ ⊢ₘ[T] domₘ(sequence) ≐ₘ numₘ(length) := by
    simpa [Δ, domainEquation] using
      (FirstOrder.Derives.assumption
        (T := T) (Γ := Δ) (formula := domainEquation) (by simp [Δ]))
  have hTraceExists : Δ ⊢ₘ[T]
      (nat_sequence_code_trace_condition
        (sequence.weakenBound SetSort.set)
        (code.weakenBound SetSort.set)
        (.bvar .here)).existsE SetSort.set :=
    FirstOrder.Derives.context_weaken_cons hParts.trace_exists
  exact nat_sequence_code_trace_elim sequence code hTraceExists
    (conclusion := sequence ≐ₘ nat_sequence_graph_term tokens) (by
      intro P
      let base : Context signature (SetSort.set :: free) :=
        FreshVariable.extendContext SetSort.set Δ
      let Ξ : Context signature (SetSort.set :: free) :=
        nat_sequence_trace_context Δ sequence code
      change Ξ ⊢ₘ[T]
        (sequence ≐ₘ nat_sequence_graph_term tokens).weakenFree SetSort.set
      have hFunctionDelta : Δ ⊢ₘ[T] is_function_formula sequence :=
        FirstOrder.Derives.context_weaken_cons hFunction
      have hFunctionBase : base ⊢ₘ[T]
          is_function_formula (sequence.weakenFree SetSort.set) := by
        have hRenamed := FirstOrder.Derives.free_renaming
          (T := T) (VariableRenaming.weaken SetSort.set) hFunctionDelta
        simpa only [base, FreshVariable.extendContext, Formula.weakenFree,
          Formula.renameFree, Renaming.weakenFree] using! hRenamed
      have hFunctionXi : Ξ ⊢ₘ[T]
          is_function_formula (sequence.weakenFree SetSort.set) :=
        FirstOrder.Derives.context_weaken_cons hFunctionBase
      have hDomainBase : base ⊢ₘ[T]
          domₘ(sequence.weakenFree SetSort.set) ≐ₘ numₘ(length) := by
        have hRenamed := FirstOrder.Derives.free_renaming
          (T := T) (VariableRenaming.weaken SetSort.set) hDomain
        have hHead :
            Formula.renameFree (VariableRenaming.weaken SetSort.set)
                (domₘ(sequence) ≐ₘ numₘ(length)) =
              domₘ(sequence.weakenFree SetSort.set) ≐ₘ numₘ(length) := by
          have hDomainTerm :
              (domₘ(sequence)).renameMapped
                  (VariableRenaming.id)
                  (VariableRenaming.weaken SetSort.set) =
                domₘ(sequence.weakenFree SetSort.set) := by
            rw [domain_term_renameMapped]
            rfl
          change
            ((domₘ(sequence)).renameMapped
                (VariableRenaming.id)
                (VariableRenaming.weaken SetSort.set) ≐ₘ
              (numₘ(length)).renameMapped
                (VariableRenaming.id)
                (VariableRenaming.weaken SetSort.set)) =
            (domₘ(sequence.weakenFree SetSort.set) ≐ₘ numₘ(length))
          rw [hDomainTerm, finite_numeral_term_renameMapped]
        have hTail :
            List.map (Formula.renameFree (VariableRenaming.weaken SetSort.set)) Δ =
              FreshVariable.extendContext SetSort.set Δ := rfl
        rw [hHead, hTail] at hRenamed
        exact hRenamed
      have hDomainXi : Ξ ⊢ₘ[T]
          domₘ(sequence.weakenFree SetSort.set) ≐ₘ numₘ(length) :=
        FirstOrder.Derives.context_weaken_cons hDomainBase
      have hCodeEqualityDelta : Δ ⊢ₘ[T] code ≐ₘ numₘ(bound) :=
        FirstOrder.Derives.context_weaken_cons hCodeEqualityBound
      have hCodeEqualityBase : base ⊢ₘ[T]
          code.weakenFree SetSort.set ≐ₘ numₘ(bound) := by
        have hRenamed := FirstOrder.Derives.free_renaming
          (T := T) (VariableRenaming.weaken SetSort.set)
            hCodeEqualityDelta
        simpa [base, FreshVariable.extendContext, Formula.weakenFree,
          Formula.renameFree, Formula.rename, Renaming.weakenFree,
          Renaming.free, Formula.renameMapped, Term.renameMapped,
          Arguments.renameMapped, finite_numeral_term_renameMapped] using!
          hRenamed
      have hCodeEqualityXi : Ξ ⊢ₘ[T]
          code.weakenFree SetSort.set ≐ₘ numₘ(bound) :=
        FirstOrder.Derives.context_weaken_cons hCodeEqualityBase
      have hValueBoundDelta : Δ ⊢ₘ[T]
          nat_sequence_value_code_bound sequence code :=
        FirstOrder.Derives.context_weaken_cons hParts.value_code_bound
      have hValueBoundBase : base ⊢ₘ[T]
          nat_sequence_value_code_bound
            (sequence.weakenFree SetSort.set)
            (code.weakenFree SetSort.set) := by
        have hRenamed := FirstOrder.Derives.free_renaming
          (T := T) (VariableRenaming.weaken SetSort.set)
            hValueBoundDelta
        simpa [base, FreshVariable.extendContext,
          nat_sequence_value_code_bound, Formula.weakenFree,
          Formula.renameFree, Formula.rename, Renaming.weakenFree,
          Renaming.free, Formula.renameMapped, Term.renameMapped,
          Arguments.renameMapped, Formula.LevyBound.boundedForall,
          Formula.LevyBound.membership, Formula.substituteMapped,
          Term.substituteMapped, Arguments.substituteMapped,
          VariableRenaming.weaken, finite_numeral_term_renameMapped,
          Term.weakenFree_weakenBound, Arguments.weakenFree_weakenBound] using!
          hRenamed
      have hValueBoundXi : Ξ ⊢ₘ[T]
          nat_sequence_value_code_bound
            (sequence.weakenFree SetSort.set)
            (code.weakenFree SetSort.set) :=
        FirstOrder.Derives.context_weaken_cons hValueBoundBase
      have hStepReplay : ∀ index, index < length →
          Ξ ⊢ₘ[T] nat_sequence_code_step_condition
            (sequence.weakenFree SetSort.set)
            nat_sequence_trace_term (numₘ(index)) := by
        intro index hIndex
        have hIndexNumeral : Ξ ⊢ₘ[T]
            numₘ(index) ∈ₘ numₘ(length) :=
          FirstOrder.Derives.context_weaken
            (Γ := ([] : Context signature (SetSort.set :: free)))
            (Δ := Ξ) (by simp [Ξ])
            (numeral_mem_of_lt
              S.toArithmeticSupport.contains_successor hIndex)
        have hIndexDomain : Ξ ⊢ₘ[T]
            numₘ(index) ∈ₘ domₘ(sequence.weakenFree SetSort.set) :=
          FirstOrder.Derives.iff_elim_right
            (membership_right_iff_of_equality
              (numₘ(index))
              (domₘ(sequence.weakenFree SetSort.set))
              (numₘ(length)) hDomainXi)
            hIndexNumeral
        exact nat_sequence_code_step_condition_at
          (sequence.weakenFree SetSort.set)
          nat_sequence_trace_term (numₘ(index)) P.step hIndexDomain
      have hValueReplay : ∀ index, index < length →
          Ξ ⊢ₘ[T]
            ((sequence.weakenFree SetSort.set) ·ₘ numₘ(index)) ∈ₘ numₘ(bound) := by
        intro index hIndex
        have hIndexNumeral : Ξ ⊢ₘ[T]
            numₘ(index) ∈ₘ numₘ(length) :=
          FirstOrder.Derives.context_weaken
            (Γ := ([] : Context signature (SetSort.set :: free)))
            (Δ := Ξ) (by simp [Ξ])
            (numeral_mem_of_lt
              S.toArithmeticSupport.contains_successor hIndex)
        have hIndexDomain : Ξ ⊢ₘ[T]
            numₘ(index) ∈ₘ domₘ(sequence.weakenFree SetSort.set) :=
          FirstOrder.Derives.iff_elim_right
            (membership_right_iff_of_equality
              (numₘ(index))
              (domₘ(sequence.weakenFree SetSort.set))
              (numₘ(length)) hDomainXi)
            hIndexNumeral
        have hValueCode := nat_sequence_value_code_bound_at
          (sequence.weakenFree SetSort.set)
          (code.weakenFree SetSort.set) (numₘ(index))
          hValueBoundXi hIndexDomain
        exact FirstOrder.Derives.iff_elim_left
          (membership_right_iff_of_equality
            ((sequence.weakenFree SetSort.set) ·ₘ numₘ(index))
            (code.weakenFree SetSort.set) (numₘ(bound))
            hCodeEqualityXi)
          hValueCode
      have hTraceDomain : Ξ ⊢ₘ[T]
          domₘ(nat_sequence_trace_term) ≐ₘ numₘ(length + 1) := by
        have hSuccessorDomain : Ξ ⊢ₘ[T]
            Sₘ(domₘ(sequence.weakenFree SetSort.set)) ≐ₘ
              Sₘ(numₘ(length)) :=
          successor_term_congr_of_equality
            (domₘ(sequence.weakenFree SetSort.set)) (numₘ(length)) hDomainXi
        have hTraceDomainSucc := Metatheory.Derives.equality_trans
          P.domain_eq hSuccessorDomain
        simpa [finite_numeral_term, successor_term] using hTraceDomainSucc
      have hTraceReplay : ∀ index, index ≤ length →
          Ξ ⊢ₘ[T]
            (nat_sequence_trace_term ·ₘ numₘ(index)) ∈ₘ numₘ(bound + 1) := by
        intro index hIndex
        have hIndexNumeral : Ξ ⊢ₘ[T]
            numₘ(index) ∈ₘ numₘ(length + 1) :=
          FirstOrder.Derives.context_weaken
            (Γ := ([] : Context signature (SetSort.set :: free)))
            (Δ := Ξ) (by simp [Ξ])
            (numeral_mem_of_lt
              S.toArithmeticSupport.contains_successor (by omega))
        have hIndexDomain : Ξ ⊢ₘ[T]
            numₘ(index) ∈ₘ domₘ(nat_sequence_trace_term) :=
          FirstOrder.Derives.iff_elim_right
            (membership_right_iff_of_equality
              (numₘ(index)) (domₘ(nat_sequence_trace_term))
              (numₘ(length + 1)) hTraceDomain)
            hIndexNumeral
        have hTraceCode := sequence_trace_code_bound_at
          nat_sequence_trace_term (code.weakenFree SetSort.set)
          (numₘ(index)) P.code_bound hIndexDomain
        have hSuccessorCodeEquality : Ξ ⊢ₘ[T]
            Sₘ(code.weakenFree SetSort.set) ≐ₘ Sₘ(numₘ(bound)) :=
          successor_term_congr_of_equality
            (code.weakenFree SetSort.set) (numₘ(bound)) hCodeEqualityXi
        have hTraceSuccessor := FirstOrder.Derives.iff_elim_left
          (membership_right_iff_of_equality
            ((nat_sequence_trace_term) ·ₘ numₘ(index))
            (Sₘ(code.weakenFree SetSort.set)) (Sₘ(numₘ(bound)))
            hSuccessorCodeEquality)
          hTraceCode
        simpa [finite_numeral_term, successor_term] using hTraceSuccessor
      have hFinal : Ξ ⊢ₘ[T]
          numₘ(nat_sequence_code_value tokens) ≐ₘ
            (nat_sequence_trace_term ·ₘ numₘ(length)) := by
        have hNumeralCode : Ξ ⊢ₘ[T]
            numₘ(bound) ≐ₘ code.weakenFree SetSort.set :=
          Metatheory.Derives.equality_symm hCodeEqualityXi
        have hNumeralToDomain : Ξ ⊢ₘ[T]
            numₘ(bound) ≐ₘ
              (nat_sequence_trace_term ·ₘ
                domₘ(sequence.weakenFree SetSort.set)) :=
          Metatheory.Derives.equality_trans hNumeralCode P.final_code
        have hTraceDomainApplication : Ξ ⊢ₘ[T]
            (nat_sequence_trace_term ·ₘ
                domₘ(sequence.weakenFree SetSort.set)) ≐ₘ
              (nat_sequence_trace_term ·ₘ numₘ(length)) :=
          function_application_term_congr_argument_of_equality
            nat_sequence_trace_term
            (domₘ(sequence.weakenFree SetSort.set)) (numₘ(length)) hDomainXi
        have hFinalBound := Metatheory.Derives.equality_trans
          hNumeralToDomain hTraceDomainApplication
        simpa [bound] using hFinalBound
      have hReplay := nat_sequence_code_replay_of_data C
        S.toFiniteSequenceEvaluationSupport
          (sequence.weakenFree SetSort.set) nat_sequence_trace_term
        tokens length bound hFunctionXi hDomainXi P.zero_value
        hStepReplay hValueReplay hTraceReplay hFinal
      rw [Formula.weakenFree_eq_renameMapped]
      change Ξ ⊢ₘ[T]
        sequence.renameMapped VariableRenaming.id
            (VariableRenaming.weaken SetSort.set) ≐ₘ
          (nat_sequence_graph_term tokens).renameMapped
            VariableRenaming.id (VariableRenaming.weaken SetSort.set)
      rw [Term.renameMapped_id_weaken sequence]
      rw [Term.renameMapped_id_weaken (nat_sequence_graph_term tokens)]
      simpa [nat_sequence_graph_term, standard_sequence_from_weakenFree,
        finite_numeral_term_weakenFree, Function.comp_def] using hReplay)

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
