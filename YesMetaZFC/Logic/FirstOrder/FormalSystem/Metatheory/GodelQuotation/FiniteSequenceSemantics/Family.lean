import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.Elimination
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.StandardTokenSequence

/-!
# 代码字符串序列族的对象层消去

本模块把 `seq_spaceₘ(CodeStrₘ)` 成员精确消去为有限序列族条件。值域中的每个
代码字符串本身都是有限序列，因此该接口同时供项应用、谓词应用和后续有限子串
反演使用。
-/

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/--
以代码字符串为值域的有限序列，其每个值仍是有限序列，因而满足可折叠序列族条件。
-/
theorem code_string_sequence_member_implies_family_condition_of_theory
    {T : SetTheory}
    (hTheory :
      ∀ formula,
        standard_sequence_semantics_theory formula →
          T formula)
    (hTheorySentence :
      ∀ formula, T formula →
        Formula.Sentence formula)
    {Γ : Context signature}
    (sequence : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hMember :
      Γ ⊢ₘ[T]
        sequence ∈ₘ seq_spaceₘ(CodeStrₘ)) :
    Γ ⊢ₘ[T]
      finite_sequence_family_condition sequence := by
  have hCodeStringsNonempty :
      Γ ⊢ₘ[T]
        CodeStrₘ ≠ₘ ∅ₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory
          standard_token_sequence_code_string_ne_empty
  have hFamilyFinite :
      Γ ⊢ₘ[T]
        finite_sequence_condition sequence := by
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            FirstOrder.Derives.theory_weaken hTheory <|
              sequence_space_member_implies_finite_sequence
                CodeStrₘ sequence
                code_string_space_term_admissible hSequence)
        hCodeStringsNonempty)
      hMember
  let freshnessBasis : List SetFormula :=
    (sequence ≐ₘ sequence) :: Γ
  let indexId : FreeVarId :=
    FreshVariable.fresh_id SetSort.set freshnessBasis
  let index : SetTerm := x#indexId
  let domainMembership : SetFormula :=
    index ∈ₘ domₘ(sequence)
  let finiteCondition : SetFormula :=
    domainMembership ⟶ₘ
      finite_sequence_condition (sequence ·ₘ index)
  have hIndex :
      Term.Admissible index SetSort.set := by
    simpa [index] using
      set_variable_admissible indexId
  have hIndexFreshSequence :
      (SetSort.set, indexId) ∉
        Term.freeSupport sequence := by
    dsimp [indexId, freshnessBasis]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m
        (sort := SetSort.set)
        (formulas := (sequence ≐ₘ sequence) :: Γ)
        (formula := sequence ≐ₘ sequence)
        (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hIndexFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, indexId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    dsimp [indexId, freshnessBasis]
    exact
      FreshVariable.fresh_id_not_mem_m
        (sort := SetSort.set)
        (formulas := (sequence ≐ₘ sequence) :: Γ)
        (formula := formula)
        (by simp [hFormula])
  have hTheoryFresh :
      ∀ formula, T formula →
        (SetSort.set, indexId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    rw [(hTheorySentence formula hFormula).2]
    exact List.not_mem_nil
  have hPoint :
      Γ ⊢ₘ[T]
        finiteCondition := by
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature :=
      domainMembership :: Γ
    have hDomain :
        Δ ⊢ₘ[T]
          domainMembership :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hValueMember :
        Δ ⊢ₘ[T]
          (sequence ·ₘ index) ∈ₘ CodeStrₘ := by
      exact FirstOrder.Derives.impElim
        (FirstOrder.Derives.impElim
          (FirstOrder.Derives.impElim
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Δ) (by simp [Δ]) <|
                FirstOrder.Derives.theory_weaken hTheory <|
                  sequence_space_member_application_mem
                    CodeStrₘ sequence index
                    code_string_space_term_admissible
                    hSequence hIndex)
            (FirstOrder.Derives.context_weaken_cons
              hCodeStringsNonempty))
          (FirstOrder.Derives.context_weaken_cons
            hMember))
        hDomain
    have hValueFinite :
        Δ ⊢ₘ[T]
          finite_sequence_condition
            (sequence ·ₘ index) :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            FirstOrder.Derives.theory_weaken hTheory <|
              code_string_member_implies_finite_sequence_at
                (sequence ·ₘ index)
                (function_application_term_admissible
                  sequence index hSequence hIndex))
        hValueMember
    simpa [finiteCondition, domainMembership] using
      hValueFinite
  have hSequenceCloseIndex :
      Term.closeFreeAt SetSort.set indexId 0 sequence =
        sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 sequence
      hSequence.2 hIndexFreshSequence
  have hAllFiniteAtIndex :
      Γ ⊢ₘ[T]
        ∀ₘ[SetSort.set, indexId], finiteCondition :=
    FirstOrder.Derives.forall_intro
      (T := T)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := indexId)
      hTheoryFresh hIndexFreshContext hPoint
  have hAllFinite :
      Γ ⊢ₘ[T]
        ∀ₘ[SetSort.set],
          (bₛ#0 ∈ₘ domₘ(sequence)) ⟶ₘ
            finite_sequence_condition
              (sequence ·ₘ bₛ#0) := by
    simpa [finiteCondition, domainMembership, index,
      finite_sequence_condition,
      Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, set_variable,
      domain_term, function_application_term,
      is_function_formula,
      hSequenceCloseIndex] using hAllFiniteAtIndex
  exact FirstOrder.Derives.conjIntro
    hFamilyFinite <| by
      simpa [finite_sequence_family_condition] using
        hAllFinite

/--
标准序列语义理论中的专用入口。
-/
theorem stdseq_code_string_sequence_member_implies_family_condition
    {Γ : Context signature}
    (sequence : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hMember :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        sequence ∈ₘ seq_spaceₘ(CodeStrₘ)) :
    Γ ⊢ₘ[standard_sequence_semantics_theory]
      finite_sequence_family_condition sequence :=
  code_string_sequence_member_implies_family_condition_of_theory
    (fun _ hFormula => hFormula)
    (fun _ hFormula =>
      standard_sequence_semantics_theory_sentence hFormula)
    sequence hSequence hMember

end YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation
