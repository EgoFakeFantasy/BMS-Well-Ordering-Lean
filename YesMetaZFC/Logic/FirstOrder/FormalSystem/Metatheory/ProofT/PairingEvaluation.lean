import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ExponentiationTrace

/-!
# 内在 Gödel 配数求值

本模块直接在两个有限 numeral 上验证配数定义。配数的两个分支分别复用幂与加法
轨迹；不再经过旧层的有序对投影、项良构性或兼容桥接。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open ProofCode
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

private theorem finite_exponentiation_addition_value
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    (base exponent addend : Nat) :
    ([] : Context signature []) ⊢ₘ[T]
      ((numₘ(base) ^ₘ numₘ(exponent)) +ₘ numₘ(addend)) ≐ₘ
        numₘ((base ^ exponent) + addend) := by
  have hPower :=
    Metatheory.Derives.equality_symm
      (standard_sequence_finite_numeral_exponentiation S base exponent)
  have hPowerCongr : ([] : Context signature []) ⊢ₘ[T]
      ((numₘ(base) ^ₘ numₘ(exponent)) +ₘ numₘ(addend)) ≐ₘ
        (numₘ(base ^ exponent) +ₘ numₘ(addend)) := by
    let context : SetTerm [SetSort.set] [] :=
      (.bvar .here : SetTerm [SetSort.set] []) +ₘ
        (numₘ(addend) : SetOpenTerm []).weakenBound SetSort.set
    simpa only [context,
      Term.instantiateTop_app,
      Arguments.instantiateTop_cons,
      Arguments.instantiateTop_nil,
      Term.instantiateTop_weakenBound,
      Term.instantiateTop_bvar_here] using!
      Metatheory.Derives.term_context_congr_of_equality
        (T := T) (Γ := ([] : Context signature [])) context hPower
  have hAddition :=
    Metatheory.Derives.equality_symm
      (standard_sequence_finite_numeral_addition
        S (base ^ exponent) addend)
  exact Metatheory.Derives.equality_trans hPowerCongr hAddition

private theorem finite_nested_square_add_value
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    (left right : Nat) :
    ([] : Context signature []) ⊢ₘ[T]
      (((numₘ(left) ^ₘ numₘ(2)) +ₘ numₘ(left)) +ₘ numₘ(right)) ≐ₘ
        numₘ((left ^ 2 + left) + right) := by
  have hInner := finite_exponentiation_addition_value S left 2 left
  have hOuterCongr : ([] : Context signature []) ⊢ₘ[T]
      (((numₘ(left) ^ₘ numₘ(2)) +ₘ numₘ(left)) +ₘ numₘ(right)) ≐ₘ
        (numₘ(left ^ 2 + left) +ₘ numₘ(right)) := by
    let context : SetTerm [SetSort.set] [] :=
      (.bvar .here : SetTerm [SetSort.set] []) +ₘ
        (numₘ(right) : SetOpenTerm []).weakenBound SetSort.set
    simpa only [context,
      Term.instantiateTop_app,
      Arguments.instantiateTop_cons,
      Arguments.instantiateTop_nil,
      Term.instantiateTop_weakenBound,
      Term.instantiateTop_bvar_here] using!
      Metatheory.Derives.term_context_congr_of_equality
        (T := T) (Γ := ([] : Context signature [])) context hInner
  have hOuter :=
    Metatheory.Derives.equality_symm
      (standard_sequence_finite_numeral_addition
        S (left ^ 2 + left) right)
  exact Metatheory.Derives.equality_trans hOuterCongr hOuter

private theorem finite_numeral_not_mem_of_not_lt
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    (left right : Nat) (hNotLt : ¬ left < right) :
    ([] : Context signature []) ⊢ₘ[T]
      ¬ₘ ((numₘ(left) : SetOpenTerm []) ∈ₘ numₘ(right)) := by
  let member : SetOpenFormula [] :=
    (numₘ(left) : SetOpenTerm []) ∈ₘ numₘ(right)
  apply FirstOrder.Derives.neg_intro
  have hMember : [member] ⊢ₘ[T] member :=
    FirstOrder.Derives.assumption List.mem_cons_self
  apply (ArithmeticSupport.finite_core
    S.toFiniteSequenceEvaluationSupport.toArithmeticSupport).member_elim
    right (numₘ(left) : SetOpenTerm []) Formula.falsum hMember
  intro index hIndex
  have hNe : left ≠ index := by omega
  have hNotEquality :=
    (ArithmeticSupport.finite_core
      S.toFiniteSequenceEvaluationSupport.toArithmeticSupport).numeral_ne hNe
  let equality : SetOpenFormula [] :=
    (numₘ(left) : SetOpenTerm []) ≐ₘ numₘ(index)
  let Δ : Context signature [] := equality :: [member]
  have hEquality : Δ ⊢ₘ[T] equality :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hNotEqualityAt : Δ ⊢ₘ[T]
      ¬ₘ ((numₘ(left) : SetOpenTerm []) ≐ₘ numₘ(index)) :=
    FirstOrder.Derives.context_weaken
      (Γ := ([] : Context signature [])) (Δ := Δ)
      (by simp [Δ]) hNotEquality
  exact FirstOrder.Derives.neg_elim hEquality hNotEqualityAt

private theorem finite_natural_leq_not_of_gt
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    (right left : Nat) (hLt : left < right) :
    ([] : Context signature []) ⊢ₘ[T]
      ¬ₘ (natural_leq_condition
        (numₘ(right) : SetOpenTerm []) (numₘ(left) : SetOpenTerm [])) := by
  let condition : SetOpenFormula [] :=
    natural_leq_condition
      (numₘ(right) : SetOpenTerm []) (numₘ(left) : SetOpenTerm [])
  apply FirstOrder.Derives.neg_intro
  have hCondition : [condition] ⊢ₘ[T] condition :=
    FirstOrder.Derives.assumption List.mem_cons_self
  change [condition] ⊢ₘ[T] Formula.falsum
  have hCases : [condition] ⊢ₘ[T]
      ((numₘ(right) : SetOpenTerm []) ≐ₘ numₘ(left)) ∨ₘ
        ((numₘ(right) : SetOpenTerm []) ∈ₘ numₘ(left)) := by
    simpa [condition, natural_leq_condition] using hCondition
  apply FirstOrder.Derives.disj_elim hCases
  · let equality : SetOpenFormula [] :=
      (numₘ(right) : SetOpenTerm []) ≐ₘ numₘ(left)
    have hEquality : equality :: [condition] ⊢ₘ[T] equality :=
      FirstOrder.Derives.assumption (by simp)
    have hNotEquality :=
      (ArithmeticSupport.finite_core
        S.toFiniteSequenceEvaluationSupport.toArithmeticSupport).numeral_ne
        (by omega : right ≠ left)
    exact FirstOrder.Derives.neg_elim hEquality <|
      FirstOrder.Derives.context_weaken
        (Γ := ([] : Context signature []))
        (Δ := equality :: [condition]) (by simp)
        hNotEquality
  · let member : SetOpenFormula [] :=
      (numₘ(right) : SetOpenTerm []) ∈ₘ numₘ(left)
    have hMember : member :: [condition] ⊢ₘ[T] member :=
      FirstOrder.Derives.assumption (by simp)
    have hNotMember := finite_numeral_not_mem_of_not_lt S right left (by omega)
    exact FirstOrder.Derives.neg_elim hMember <|
      FirstOrder.Derives.context_weaken
        (Γ := ([] : Context signature []))
        (Δ := member :: [condition]) (by simp)
        hNotMember

/-- 两个标准 numeral 的 Gödel 配数值在对象层可直接计算。 -/
theorem finite_numeral_godel_pair_value
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    (left right : Nat) :
    ([] : Context signature []) ⊢ₘ[T]
      godel_pairₘ(numₘ(left), numₘ(right)) ≐ₘ
        numₘ(ProofCode.godel_pair_value left right) := by
  let candidate : SetOpenTerm [] :=
    numₘ(ProofCode.godel_pair_value left right)
  have hLeftOmega : ([] : Context signature []) ⊢ₘ[T]
      (numₘ(left) : SetOpenTerm []) ∈ₘ ωₘ :=
    S.finite_numeral_mem_omega left
  have hRightOmega : ([] : Context signature []) ⊢ₘ[T]
      (numₘ(right) : SetOpenTerm []) ∈ₘ ωₘ :=
    S.finite_numeral_mem_omega right
  have hCandidateOmega : ([] : Context signature []) ⊢ₘ[T]
      candidate ∈ₘ ωₘ := by
    simpa [candidate] using
      S.finite_numeral_mem_omega (ProofCode.godel_pair_value left right)
  have hDefinition : ([] : Context signature []) ⊢ₘ[T]
      godel_pairing_definition_instance
        (numₘ(left) : SetOpenTerm [])
        (numₘ(right) : SetOpenTerm []) candidate :=
    S.pairing_definition_instance_derives
      (Γ := ([] : Context signature []))
      (numₘ(left) : SetOpenTerm []) (numₘ(right) : SetOpenTerm []) candidate
  have hContract : ([] : Context signature []) ⊢ₘ[T]
      (candidate ≐ₘ
          godel_pairₘ(numₘ(left), numₘ(right))) ↔ₘ
        godel_pairing_condition
          (numₘ(left) : SetOpenTerm [])
          (numₘ(right) : SetOpenTerm []) candidate := by
    simpa [godel_pairing_definition_instance] using
      FirstOrder.Derives.imp_elim hDefinition <|
        FirstOrder.Derives.conj_intro hLeftOmega hRightOmega
  by_cases hOrder : left < right
  · have hFirstValue : ([] : Context signature []) ⊢ₘ[T]
        candidate ≐ₘ
          ((numₘ(right) ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ numₘ(left)) := by
      have hNumeric :=
        finite_exponentiation_addition_value S right 2 left
      simpa [candidate, ProofCode.godel_pair_value, hOrder,
        finite_numeral_term, successor_term] using
        Metatheory.Derives.equality_symm hNumeric
    have hFirstImp : ([] : Context signature []) ⊢ₘ[T]
        ((numₘ(left) : SetOpenTerm []) ∈ₘ numₘ(right)) ⟶ₘ
          (candidate ≐ₘ
            ((numₘ(right) ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ numₘ(left))) :=
      FirstOrder.Derives.context_weaken_cons hFirstValue
    have hNotSecond : ([] : Context signature []) ⊢ₘ[T]
        ¬ₘ (natural_leq_condition
          (numₘ(right) : SetOpenTerm []) (numₘ(left) : SetOpenTerm [])) :=
      finite_natural_leq_not_of_gt S right left hOrder
    have hSecondImp : ([] : Context signature []) ⊢ₘ[T]
        (natural_leq_condition
          (numₘ(right) : SetOpenTerm []) (numₘ(left) : SetOpenTerm [])) ⟶ₘ
          (candidate ≐ₘ
            (((numₘ(left) ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ numₘ(left)) +ₘ numₘ(right))) := by
      apply FirstOrder.Derives.imp_intro
      exact FirstOrder.Derives.falsum_elim <|
        FirstOrder.Derives.neg_elim
          (FirstOrder.Derives.assumption List.mem_cons_self)
          (FirstOrder.Derives.context_weaken_cons hNotSecond)
    have hCondition := FirstOrder.Derives.conj_intro hCandidateOmega <|
      FirstOrder.Derives.conj_intro hFirstImp hSecondImp
    have hCandidatePair :=
      FirstOrder.Derives.iff_elim_right hContract hCondition
    exact Metatheory.Derives.equality_symm hCandidatePair
  · have hNotFirst : ([] : Context signature []) ⊢ₘ[T]
        ¬ₘ ((numₘ(left) : SetOpenTerm []) ∈ₘ numₘ(right)) :=
      finite_numeral_not_mem_of_not_lt S left right hOrder
    have hFirstImp : ([] : Context signature []) ⊢ₘ[T]
        ((numₘ(left) : SetOpenTerm []) ∈ₘ numₘ(right)) ⟶ₘ
          (candidate ≐ₘ
            ((numₘ(right) ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ numₘ(left))) := by
      apply FirstOrder.Derives.imp_intro
      exact FirstOrder.Derives.falsum_elim <|
        FirstOrder.Derives.neg_elim
          (FirstOrder.Derives.assumption List.mem_cons_self)
          (FirstOrder.Derives.context_weaken_cons hNotFirst)
    have hSecondValue : ([] : Context signature []) ⊢ₘ[T]
        candidate ≐ₘ
          (((numₘ(left) ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ numₘ(left)) +ₘ numₘ(right)) := by
      have hNumeric := finite_nested_square_add_value S left right
      simpa [candidate, ProofCode.godel_pair_value, hOrder,
        finite_numeral_term, successor_term] using
        Metatheory.Derives.equality_symm hNumeric
    have hSecondImp : ([] : Context signature []) ⊢ₘ[T]
        (natural_leq_condition
          (numₘ(right) : SetOpenTerm []) (numₘ(left) : SetOpenTerm [])) ⟶ₘ
          (candidate ≐ₘ
            (((numₘ(left) ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ numₘ(left)) +ₘ numₘ(right))) :=
      FirstOrder.Derives.context_weaken_cons hSecondValue
    have hCondition := FirstOrder.Derives.conj_intro hCandidateOmega <|
      FirstOrder.Derives.conj_intro hFirstImp hSecondImp
    have hCandidatePair :=
      FirstOrder.Derives.iff_elim_right hContract hCondition
    exact Metatheory.Derives.equality_symm hCandidatePair

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
