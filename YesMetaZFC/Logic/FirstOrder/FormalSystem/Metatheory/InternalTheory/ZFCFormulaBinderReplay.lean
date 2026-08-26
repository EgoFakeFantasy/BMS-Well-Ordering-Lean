import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaBinderReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCFormulaSignatureReplay

/-!
# ZFC 中的公式 binder 有界回放

宿主布尔检查只提供每个全称 token 的直接变量后继。本模块在标准 token 序列的
有限定义域上逐点回放该事实，并与现有有限签名条件合成为 verifier 公式条件。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation

set_option autoImplicit false

/-- 显式位置 binder 下，标准 token 序列满足全称后继条件。 -/
theorem
    fs_zfc_support_raw_standard_token_sequence_binder_with_id
    (tokens : List Nat)
    (hTokens : FSFormulaBinderTokens tokens)
    (tokenIndexId : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_formula_binder_condition_with_id
        (standard_token_sequence tokens)
        tokenIndexId) := by
  let sequence : SetTerm :=
    standard_token_sequence tokens
  let point : SetTerm := x#tokenIndexId
  let nextValue : SetTerm :=
    sequence ·ₘ Sₘ(point)
  let conclusion : SetFormula :=
    fs_formula_binder_condition_lifted
      sequence point nextValue
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence] using
      standard_token_sequence_admissible tokens
  have hPoint :
      Term.Admissible point SetSort.set := by
    simpa [point] using
      set_variable_admissible tokenIndexId
  have hDomainTerm :
      Term.Admissible (domₘ(sequence)) SetSort.set :=
    domain_term_admissible sequence hSequence
  have hValue :
      Term.Admissible
        (sequence ·ₘ point) SetSort.set :=
    function_application_term_admissible
      sequence point hSequence hPoint
  have hNext :
      Term.Admissible (Sₘ(point)) SetSort.set :=
    successor_term_admissible point hPoint
  have hNextValue :
      Term.Admissible nextValue SetSort.set := by
    simpa [nextValue] using
      function_application_term_admissible
        sequence (Sₘ(point)) hSequence hNext
  have hConclusion :
      Formula.Admissible conclusion := by
    dsimp [conclusion]
    exact Formula.Admissible.imp
      (Formula.Admissible.equal
        hValue
        (finite_numeral_term_admissible
          (Numbered.logical_token .universal)))
      (Formula.Admissible.conj
        (membership_formula_admissible
          hNext hDomainTerm)
        (fs_variable_token_condition_admissible
          nextValue hNextValue))
  have hDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(sequence) ≐ₘ
          numₘ(tokens.length)) := by
    simpa [sequence] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_token_sequence_domain_eq_length
          tokens)
  have hForall :=
    fs_zfc_support_raw_finite_domain_forall_imp
      sequence tokens.length tokenIndexId conclusion
      hSequence hConclusion hDomain
      (fun index hIndex => by
        let equality : SetFormula :=
          point ≐ₘ numₘ(index)
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
        have hTransport :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              (fs_formula_binder_condition_lifted
                  sequence point
                    (sequence ·ₘ Sₘ(point))) ↔ₘ
                fs_formula_binder_condition_lifted
                  sequence (numₘ(index))
                    (sequence ·ₘ Sₘ(numₘ(index))) :=
          fs_formula_binder_condition_lifted_iff_of_index_equality
            sequence point (numₘ(index))
            hSequence hPoint
            (finite_numeral_term_admissible index)
            hEquality
        let token : Nat := tokens[index]
        have hGet :
            tokens[index]? = some token :=
          List.getElem?_eq_some_iff.mpr
            ⟨hIndex, rfl⟩
        have hConcrete :
            Γ ⊢ₘ[fs_zfc_support_raw_theory]
              fs_formula_binder_condition_lifted
                sequence (numₘ(index))
                  (sequence ·ₘ Sₘ(numₘ(index))) := by
          by_cases hUniversal :
              token =
                Numbered.logical_token .universal
          · have hUniversalGet :
                tokens[index]? =
                  some
                    (Numbered.logical_token
                      .universal) := by
              simpa [token, hUniversal] using hGet
            rcases
                fs_formula_binder_tokens_getElem?
                  tokens hTokens index hUniversalGet with
              ⟨nextToken, name, hNextGet, hDecode⟩
            have hNextIndex :
                index + 1 < tokens.length :=
              (List.getElem?_eq_some_iff.mp
                hNextGet).1
            let antecedent : SetFormula :=
              ((sequence ·ₘ numₘ(index)) ≐ₘ
                numₘ(Numbered.logical_token
                  .universal))
            let Δ : Context signature :=
              antecedent :: Γ
            nd_apply FirstOrder.Derives.impIntro
            have hNextNumeralMember :
                Derives fs_zfc_support_raw_theory [] (
                  numₘ(index + 1) ∈ₘ
                    numₘ(tokens.length)) :=
              fs_zfc_support_raw_derives_of_standard_sequence
                (standard_sequence_finite_numeral_mem_of_lt
                  (index + 1) tokens.length
                  hNextIndex)
            have hNextNumeralDomain :
                Derives fs_zfc_support_raw_theory [] (
                  numₘ(index + 1) ∈ₘ
                    domₘ(sequence)) :=
              FirstOrder.Derives.iffElimLeft
                (membership_right_iff_of_equality
                  (numₘ(index + 1))
                  (domₘ(sequence))
                  (numₘ(tokens.length))
                  (finite_numeral_term_admissible
                    (index + 1))
                  hDomainTerm
                  (finite_numeral_term_admissible
                    tokens.length)
                  hDomain)
                hNextNumeralMember
            have hNextDomain :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  Sₘ(numₘ(index)) ∈ₘ
                    domₘ(sequence) :=
              FirstOrder.Derives.context_weaken
                (Γ := []) (Δ := Δ)
                (by simp [Δ, Γ])
                (by
                  simpa [finite_numeral_term,
                    successor_term] using
                    hNextNumeralDomain)
            have hNextValueEquality :
                Derives fs_zfc_support_raw_theory [] (
                  (sequence ·ₘ Sₘ(numₘ(index))) ≐ₘ
                    numₘ(nextToken)) := by
              simpa [sequence, finite_numeral_term,
                successor_term] using
                fs_zfc_support_raw_derives_of_standard_sequence
                  (standard_token_sequence_apply_getElem?
                    tokens hNextGet)
            have hVariableNumeral :
                Derives fs_zfc_support_raw_theory [] (
                  fs_variable_token_condition
                    (numₘ(nextToken))) :=
              fs_zfc_support_raw_derives_of_godel_quotation
                (gq_fs_variable_token_condition_of_decode
                  hDecode)
            have hVariableAt :
                Derives fs_zfc_support_raw_theory [] (
                  fs_variable_token_condition
                    (sequence ·ₘ Sₘ(numₘ(index)))) :=
              FirstOrder.Derives.iffElimLeft
                (fs_variable_token_condition_iff_of_equality
                  (sequence ·ₘ Sₘ(numₘ(index)))
                  (numₘ(nextToken))
                  (function_application_term_admissible
                    sequence (Sₘ(numₘ(index)))
                    hSequence
                    (successor_term_admissible
                      (numₘ(index))
                      (finite_numeral_term_admissible
                        index)))
                  (finite_numeral_term_admissible
                    nextToken)
                  hNextValueEquality)
                hVariableNumeral
            exact FirstOrder.Derives.conjIntro
              hNextDomain
              (FirstOrder.Derives.context_weaken
                (Γ := []) (Δ := Δ)
                (by simp [Δ, Γ])
                hVariableAt)
          · let antecedent : SetFormula :=
              ((sequence ·ₘ numₘ(index)) ≐ₘ
                numₘ(Numbered.logical_token
                  .universal))
            let Δ : Context signature :=
              antecedent :: Γ
            nd_apply FirstOrder.Derives.impIntro
            have hAntecedent :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  antecedent :=
              FirstOrder.Derives.assumption
                (by simp [Δ])
            have hCurrentUniversal :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  (sequence ·ₘ numₘ(index)) ≐ₘ
                    numₘ(Numbered.logical_token
                      .universal) := by
              simpa [antecedent] using hAntecedent
            have hCurrentValue :
                Derives fs_zfc_support_raw_theory [] (
                  (sequence ·ₘ numₘ(index)) ≐ₘ
                    numₘ(token)) := by
              simpa [sequence] using
                fs_zfc_support_raw_derives_of_standard_sequence
                  (standard_token_sequence_apply_getElem?
                    tokens hGet)
            have hNumeralEquality :
                Δ ⊢ₘ[fs_zfc_support_raw_theory]
                  numₘ(token) ≐ₘ
                    numₘ(Numbered.logical_token
                      .universal) :=
              Metatheory.Derives.equality_trans
                (Metatheory.Derives.equality_symm
                  (FirstOrder.Derives.context_weaken
                    (Γ := []) (Δ := Δ)
                    (by simp [Δ, Γ])
                    hCurrentValue))
                hCurrentUniversal
            have hNumeralNot :
                Derives fs_zfc_support_raw_theory [] (
                  ¬ₘ (numₘ(token) ≐ₘ
                    numₘ(Numbered.logical_token
                      .universal))) :=
              fs_zfc_support_raw_derives_of_standard_sequence
                (standard_sequence_finite_numeral_ne
                  hUniversal)
            have hConsequent :
                Formula.Admissible
                  ((Sₘ(numₘ(index)) ∈ₘ
                      domₘ(sequence)) ∧ₘ
                    fs_variable_token_condition
                      (sequence ·ₘ
                        Sₘ(numₘ(index)))) :=
              Formula.Admissible.conj
                (membership_formula_admissible
                  (successor_term_admissible
                    (numₘ(index))
                    (finite_numeral_term_admissible
                      index))
                  hDomainTerm)
                (fs_variable_token_condition_admissible
                  (sequence ·ₘ Sₘ(numₘ(index)))
                  (function_application_term_admissible
                    sequence (Sₘ(numₘ(index)))
                    hSequence
                    (successor_term_admissible
                      (numₘ(index))
                      (finite_numeral_term_admissible
                        index))))
            exact FirstOrder.Derives.falsumElim
              (hCheck :=
                Formula.check_admissible_complete
                  hConsequent) <|
              FirstOrder.Derives.negElim
                hNumeralEquality
                (FirstOrder.Derives.context_weaken
                  (Γ := []) (Δ := Δ)
                  (by simp [Δ, Γ])
                  hNumeralNot)
        simpa [conclusion, nextValue] using
          FirstOrder.Derives.iffElimLeft
            hTransport hConcrete)
  simpa [fs_formula_binder_condition_with_id,
    conclusion, nextValue, sequence, point] using
    hForall

/-- 标准 token 序列满足规范 de Bruijn binder 条件。 -/
theorem fs_zfc_support_raw_standard_token_sequence_binder
    (tokens : List Nat)
    (hTokens : FSFormulaBinderTokens tokens) :
    Derives fs_zfc_support_raw_theory [] (
      fs_formula_binder_condition
        (standard_token_sequence tokens)) := by
  have hNamed :=
    fs_zfc_support_raw_standard_token_sequence_binder_with_id
      tokens hTokens 0
  rw [fs_formula_binder_condition_with_id_eq
    (standard_token_sequence tokens) 0
    (standard_token_sequence_admissible tokens)
    (by
      rw [standard_token_sequence_freeSupport_nil]
      exact List.not_mem_nil)] at hNamed
  exact hNamed

/-- 显式位置 binder 下，标准 token 序列满足完整 replay 词法条件。 -/
theorem
    fs_zfc_support_raw_standard_token_sequence_replay_with_id
    (tokens : List Nat)
    (hSignature : FSFormulaTokens tokens)
    (hBinder : FSFormulaBinderTokens tokens)
    (tokenIndexId : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_formula_replay_condition_with_id
        (standard_token_sequence tokens)
        tokenIndexId) := by
  exact FirstOrder.Derives.conjIntro
    (fs_zfc_support_raw_standard_token_sequence_signature_with_id
      tokens hSignature tokenIndexId)
    (fs_zfc_support_raw_standard_token_sequence_binder_with_id
      tokens hBinder tokenIndexId)

/-- 标准 token 序列满足 verifier 的完整 replay 词法条件。 -/
theorem fs_zfc_support_raw_standard_token_sequence_replay
    (tokens : List Nat)
    (hSignature : FSFormulaTokens tokens)
    (hBinder : FSFormulaBinderTokens tokens) :
    Derives fs_zfc_support_raw_theory [] (
      fs_formula_replay_condition
        (standard_token_sequence tokens)) := by
  have hNamed :=
    fs_zfc_support_raw_standard_token_sequence_replay_with_id
      tokens hSignature hBinder 0
  rw [fs_formula_replay_condition_with_id_eq
    (standard_token_sequence tokens) 0
    (standard_token_sequence_admissible tokens)
    (by
      rw [standard_token_sequence_freeSupport_nil]
      exact List.not_mem_nil)] at hNamed
  exact hNamed

/-- admissible 公式的规范 quotation 行满足完整 replay 词法条件。 -/
theorem fs_zfc_support_raw_quote_tokens_replay
    {formula : SetFormula} {tokens : List Nat}
    (hFormula : Formula.Admissible formula)
    (hQuote :
      Numbered.quote_tokens? formula = some tokens) :
    Derives fs_zfc_support_raw_theory [] (
      fs_formula_replay_condition
        (standard_token_sequence tokens)) :=
  fs_zfc_support_raw_standard_token_sequence_replay
    tokens
    (fs_quote_tokens_formula_tokens
      hFormula hQuote)
    (fs_quote_tokens_formula_binder_tokens
      hQuote)

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
