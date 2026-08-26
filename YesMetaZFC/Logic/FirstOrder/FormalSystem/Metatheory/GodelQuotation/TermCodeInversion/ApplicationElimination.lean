import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemTermCodeDecodeRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.TermCodeInversion.ApplicationSlice

/-!
# 项应用生成条件的有界消去

本模块保留参数族与逐子项项码证书，同时把动态元数前驱和函数编号消去为外部
自然数。分支持续式只暴露后续 checked replay 所需的四个数学事实，不暴露三层
存在量词的内部上下文布局。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/--
标准项应用生成条件的有界 continuation 消去。

首 token 把动态元数前驱与函数编号压入有限范围；参数族本身保持为对象项，
并向分支提供正序列、精确参数个数、逐子项项码和具体应用码等式。
-/
theorem gq_term_application_from_condition_elim_bounded
    {Γ : Context signature}
    (tokens : List Nat) (token : Nat)
    (hGet : tokens[0]? = some token)
    (conclusion : SetFormula)
    (hConclusion :
      Formula.Admissible conclusion)
    (hContextClosed :
      ∀ formula, formula ∈ Γ →
        Formula.freeSupport formula = [])
    (hConclusionClosed :
      Formula.freeSupport conclusion = [])
    (hApplication :
      Γ ⊢ₘ[godel_quotation_theory]
        term_application_from_condition
          TermCodeₘ
          (standard_token_sequence tokens))
    (hBranch :
      ∀ {Δ : Context signature}
          (arity index : Nat)
          (arguments : SetTerm),
        arity < token + 1 →
        index < token + 1 →
        Term.Admissible arguments SetSort.set →
        (SetSort.set, 213) ∉
          Term.freeSupport arguments →
        (∀ formula, formula ∈ Γ → formula ∈ Δ) →
        Δ ⊢ₘ[godel_quotation_theory]
          arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ) →
        Δ ⊢ₘ[godel_quotation_theory]
          domₘ(arguments) ≐ₘ numₘ(arity + 1) →
        Δ ⊢ₘ[godel_quotation_theory]
          ∀ₘ[SetSort.set, 213],
            (x#213 ∈ₘ domₘ(arguments)) ⟶ₘ
              ((arguments ·ₘ x#213) ∈ₘ TermCodeₘ) →
        Δ ⊢ₘ[godel_quotation_theory]
          sym_codeₘ(numₘ(token)) ≐ₘ
            coded_function_symbol_code_term
              (numₘ(arity)) (numₘ(index)) →
        Δ ⊢ₘ[godel_quotation_theory]
          standard_token_sequence tokens ≐ₘ
            term_application_code_term
              (numₘ(arity)) (numₘ(index))
              arguments →
        Δ ⊢ₘ[godel_quotation_theory]
          conclusion) :
    Γ ⊢ₘ[godel_quotation_theory]
      conclusion := by
  let code : SetTerm :=
    standard_token_sequence tokens
  let arityWitness : SetTerm := x#210
  let indexWitness : SetTerm := x#211
  let arguments : SetTerm := x#212
  let header : SetFormula :=
    (arityWitness ∈ₘ ωₘ) ∧ₘ
      ((indexWitness ∈ₘ ωₘ) ∧ₘ
        ((arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ)) ∧ₘ
          (domₘ(arguments) ≐ₘ
            Sₘ(arityWitness))))
  let values : SetFormula :=
    ∀ₘ[SetSort.set, 213],
      (x#213 ∈ₘ domₘ(arguments)) ⟶ₘ
        ((arguments ·ₘ x#213) ∈ₘ TermCodeₘ)
  let equality : SetFormula :=
    code ≐ₘ
      term_application_code_term
        arityWitness indexWitness arguments
  let body : SetFormula :=
    header ∧ₘ (values ∧ₘ equality)
  let argumentsExists : SetFormula :=
    ∃ₘ[SetSort.set, 212], body
  let indexExists : SetFormula :=
    ∃ₘ[SetSort.set, 211], argumentsExists
  let application : SetFormula :=
    ∃ₘ[SetSort.set, 210], indexExists
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible tokens
  have hArityWitness :
      Term.Admissible arityWitness SetSort.set := by
    simpa [arityWitness] using
      set_variable_admissible 210
  have hIndexWitness :
      Term.Admissible indexWitness SetSort.set := by
    simpa [indexWitness] using
      set_variable_admissible 211
  have hArguments :
      Term.Admissible arguments SetSort.set := by
    simpa [arguments] using
      set_variable_admissible 212
  have hBody :
      Formula.Admissible body := by
    dsimp only [body, header, values, equality]
    prove_admissible
  have hArgumentsExists :
      Formula.Admissible argumentsExists := by
    simpa [argumentsExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set 212 hBody
  have hIndexExists :
      Formula.Admissible indexExists := by
    simpa [indexExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set 211 hArgumentsExists
  have hApplicationAdmissible :
      Formula.Admissible application := by
    simpa [application] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set 210 hIndexExists
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        application := by
    simpa [application, indexExists,
      argumentsExists, body, header, values,
      equality, code,
      term_application_from_condition] using
      hApplication
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 210)
    (body := indexExists)
    (conclusion := conclusion)
    (hBodyCheck :=
      Formula.check_admissible_complete
        hIndexExists)
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence
      hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rw [hContextClosed formula hFormula]
    exact List.not_mem_nil
  · rw [hConclusionClosed]
    exact List.not_mem_nil
  · exact hExists
  · let Δ : Context signature :=
      indexExists :: Γ
    have hIndexExistsAt :
        Δ ⊢ₘ[godel_quotation_theory]
          indexExists :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (Formula.check_admissible_complete
          hIndexExists)
    apply FirstOrder.Derives.exists_elim
      (T := godel_quotation_theory)
      (Γ := Δ)
      (sort := SetSort.set)
      (eigen := 211)
      (body := argumentsExists)
      (conclusion := conclusion)
      (hBodyCheck :=
        Formula.check_admissible_complete
          hArgumentsExists)
    · intro formula hFormula
      rw [(godel_quotation_theory_sentence
        hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with
        rfl | hFormula
      · simpa [indexExists,
          Formula.freeSupport] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set 211 0 argumentsExists
      · rw [hContextClosed formula hFormula]
        exact List.not_mem_nil
    · rw [hConclusionClosed]
      exact List.not_mem_nil
    · exact hIndexExistsAt
    · let Ε : Context signature :=
        argumentsExists :: Δ
      have hArgumentsExistsAt :
          Ε ⊢ₘ[godel_quotation_theory]
            argumentsExists :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
          (Formula.check_admissible_complete
            hArgumentsExists)
      apply FirstOrder.Derives.exists_elim
        (T := godel_quotation_theory)
        (Γ := Ε)
        (sort := SetSort.set)
        (eigen := 212)
        (body := body)
        (conclusion := conclusion)
        (hBodyCheck :=
          Formula.check_admissible_complete hBody)
      · intro formula hFormula
        rw [(godel_quotation_theory_sentence
          hFormula).2]
        exact List.not_mem_nil
      · intro formula hFormula
        rcases List.mem_cons.mp hFormula with
          rfl | hFormula
        · simpa [argumentsExists,
            Formula.freeSupport] using
            Formula.not_mem_freeSupport_closeFreeAt
              SetSort.set 212 0 body
        · rcases List.mem_cons.mp hFormula with
            rfl | hFormula
          · have hFresh :
                (SetSort.set, 212) ∉
                  Formula.freeSupport
                    argumentsExists := by
              simpa [argumentsExists,
                Formula.freeSupport] using
                Formula.not_mem_freeSupport_closeFreeAt
                  SetSort.set 212 0 body
            simpa [indexExists] using
              Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
                (SetSort.set, 212)
                SetSort.set 211 0 argumentsExists
                hFresh
          · rw [hContextClosed formula hFormula]
            exact List.not_mem_nil
      · rw [hConclusionClosed]
        exact List.not_mem_nil
      · exact hArgumentsExistsAt
      · let Ζ : Context signature := body :: Ε
        have hBodyAt :
            Ζ ⊢ₘ[godel_quotation_theory]
              body :=
          FirstOrder.Derives.assumption
            (by simp [Ζ])
            (Formula.check_admissible_complete hBody)
        have hHeader :
            Ζ ⊢ₘ[godel_quotation_theory]
              header :=
          FirstOrder.Derives.conjElimLeft hBodyAt
        have hArityOmega :
            Ζ ⊢ₘ[godel_quotation_theory]
              arityWitness ∈ₘ ωₘ :=
          FirstOrder.Derives.conjElimLeft hHeader
        have hIndexOmega :
            Ζ ⊢ₘ[godel_quotation_theory]
              indexWitness ∈ₘ ωₘ :=
          FirstOrder.Derives.conjElimLeft <|
            FirstOrder.Derives.conjElimRight
              hHeader
        have hPositive :
            Ζ ⊢ₘ[godel_quotation_theory]
              arguments ∈ₘ
                seq₊_spaceₘ(CodeStrₘ) :=
          FirstOrder.Derives.conjElimLeft <|
            FirstOrder.Derives.conjElimRight <|
              FirstOrder.Derives.conjElimRight
                hHeader
        have hDomain :
            Ζ ⊢ₘ[godel_quotation_theory]
              domₘ(arguments) ≐ₘ
                Sₘ(arityWitness) :=
          FirstOrder.Derives.conjElimRight <|
            FirstOrder.Derives.conjElimRight <|
              FirstOrder.Derives.conjElimRight
                hHeader
        have hValues :
            Ζ ⊢ₘ[godel_quotation_theory]
              values := by
          simpa [body] using
            FirstOrder.Derives.conjElimLeft <|
              FirstOrder.Derives.conjElimRight
                hBodyAt
        have hEquality :
            Ζ ⊢ₘ[godel_quotation_theory]
              code ≐ₘ
                term_application_code_term
                  arityWitness indexWitness
                  arguments := by
          simpa [body, equality] using
            FirstOrder.Derives.conjElimRight <|
              FirstOrder.Derives.conjElimRight
                hBodyAt
        have hOpening :=
          FirstOrder.Derives.impElim
            (gq_term_application_code_opening
              (Γ := Ζ)
              arityWitness indexWitness arguments
              hArityWitness hIndexWitness hArguments
              (reserved_ids_fresh_cons_variable
                210
                (by
                  intro id hId
                  simp only [List.mem_cons,
                    List.not_mem_nil, or_false] at hId
                  rcases hId with
                    rfl | rfl | rfl <;> decide)
                (reserved_ids_fresh_cons_variable
                  211
                  (by
                    intro id hId
                    simp only [List.mem_cons,
                      List.not_mem_nil, or_false] at hId
                    rcases hId with
                      rfl | rfl | rfl <;> decide)
                  (reserved_ids_fresh_nil
                    [0, 1, 2]))))
            hPositive
        have hCodePoint :=
          gq_point_inversion_of_equality
            code
            (term_application_code_term
              arityWitness indexWitness arguments)
            (numₘ(0))
            (coded_function_symbol_number_term
              arityWitness indexWitness)
            hEquality
            (FirstOrder.Derives.conjElimLeft
              hOpening)
        have hStandardPoint :
            Ζ ⊢ₘ[godel_quotation_theory]
              ((numₘ(0) ∈ₘ domₘ(code)) ∧ₘ
                ((code ·ₘ numₘ(0)) ≐ₘ
                  numₘ(token))) := by
          simpa [code] using
            gq_standard_token_sequence_point_inversion
              code tokens
              (FirstOrder.Derives.context_weaken
                (Γ := []) (Δ := Ζ) (by simp)
                (FirstOrder.Derives.eq_refl_m
                  (sort := SetSort.set) code))
              hGet
        have hValueEquality :
            Ζ ⊢ₘ[godel_quotation_theory]
              numₘ(token) ≐ₘ
                coded_function_symbol_number_term
                  arityWitness indexWitness :=
          Metatheory.Derives.equality_trans
            (Metatheory.Derives.equality_symm
              (FirstOrder.Derives.conjElimRight
                hStandardPoint))
            (FirstOrder.Derives.conjElimRight
              hCodePoint)
        have hRawBounds :
            Ζ ⊢ₘ[godel_quotation_theory]
              ((arityWitness ∈ₘ
                  coded_function_symbol_number_term
                    arityWitness indexWitness) ∧ₘ
                (indexWitness ∈ₘ
                  coded_function_symbol_number_term
                    arityWitness indexWitness)) := by
          simpa [coded_function_symbol_number_term] using
            gq_indices_mem_indexed_prime_power_product
              (Γ := Ζ)
              3 5 arityWitness indexWitness
              (by omega) (by omega)
              hArityWitness hIndexWitness
              hArityOmega hIndexOmega
        have hArityToken :
            Ζ ⊢ₘ[godel_quotation_theory]
              arityWitness ∈ₘ numₘ(token) :=
          FirstOrder.Derives.iffElimLeft
            (membership_right_iff_of_equality
              arityWitness
              (numₘ(token))
              (coded_function_symbol_number_term
                arityWitness indexWitness)
              hArityWitness
              (finite_numeral_term_admissible token)
              (coded_function_symbol_number_term_admissible
                arityWitness indexWitness
                hArityWitness hIndexWitness)
              hValueEquality)
            (FirstOrder.Derives.conjElimLeft
              hRawBounds)
        have hIndexToken :
            Ζ ⊢ₘ[godel_quotation_theory]
              indexWitness ∈ₘ numₘ(token) :=
          FirstOrder.Derives.iffElimLeft
            (membership_right_iff_of_equality
              indexWitness
              (numₘ(token))
              (coded_function_symbol_number_term
                arityWitness indexWitness)
              hIndexWitness
              (finite_numeral_term_admissible token)
              (coded_function_symbol_number_term_admissible
                arityWitness indexWitness
                hArityWitness hIndexWitness)
              hValueEquality)
            (FirstOrder.Derives.conjElimRight
              hRawBounds)
        have hArityBound :
            Ζ ⊢ₘ[godel_quotation_theory]
              arityWitness ∈ₘ
                numₘ(token + 1) := by
          simpa [finite_numeral_term] using
            FirstOrder.Derives.impElim
              (FirstOrder.Derives.context_weaken
                (Γ := []) (Δ := Ζ) (by simp) <|
                  gq_weaken_standard_sequence <|
                    standard_sequence_weaken_successor <|
                      mem_successor_of_mem
                        (numₘ(token)) arityWitness
                        (finite_numeral_term_admissible
                          token)
                        hArityWitness)
              hArityToken
        have hIndexBound :
            Ζ ⊢ₘ[godel_quotation_theory]
              indexWitness ∈ₘ
                numₘ(token + 1) := by
          simpa [finite_numeral_term] using
            FirstOrder.Derives.impElim
              (FirstOrder.Derives.context_weaken
                (Γ := []) (Δ := Ζ) (by simp) <|
                  gq_weaken_standard_sequence <|
                    standard_sequence_weaken_successor <|
                      mem_successor_of_mem
                        (numₘ(token)) indexWitness
                        (finite_numeral_term_admissible
                          token)
                        hIndexWitness)
              hIndexToken
        apply gq_finite_numeral_member_elim_context
          (Γ := Ζ)
          (token + 1)
          arityWitness conclusion
          hArityWitness hConclusion hArityBound
        intro arity hArity
        let Η : Context signature :=
          (arityWitness ≐ₘ numₘ(arity)) :: Ζ
        have hArityEquality :
            Η ⊢ₘ[godel_quotation_theory]
              arityWitness ≐ₘ numₘ(arity) :=
          FirstOrder.Derives.assumption
            (by simp [Η])
        have hIndexBound' :
            Η ⊢ₘ[godel_quotation_theory]
              indexWitness ∈ₘ
                numₘ(token + 1) :=
          FirstOrder.Derives.context_weaken
            (Γ := Ζ) (Δ := Η)
            (by
              intro formula hFormula
              exact List.mem_cons_of_mem
                (arityWitness ≐ₘ numₘ(arity))
                hFormula)
            hIndexBound
        apply gq_finite_numeral_member_elim_context
          (Γ := Η)
          (token + 1)
          indexWitness conclusion
          hIndexWitness hConclusion hIndexBound'
        intro index hIndex
        let Θ : Context signature :=
          (indexWitness ≐ₘ numₘ(index)) :: Η
        have hIndexEquality :
            Θ ⊢ₘ[godel_quotation_theory]
              indexWitness ≐ₘ numₘ(index) :=
          FirstOrder.Derives.assumption
            (by simp [Θ])
        have hArityEquality' :
            Θ ⊢ₘ[godel_quotation_theory]
              arityWitness ≐ₘ numₘ(arity) :=
          FirstOrder.Derives.context_weaken
            (Γ := Η) (Δ := Θ)
            (by
              intro formula hFormula
              exact List.mem_cons_of_mem
                (indexWitness ≐ₘ numₘ(index))
                hFormula)
            hArityEquality
        have hWeakenΖΘ :
            ∀ formula, formula ∈ Ζ →
              formula ∈ Θ := by
          intro formula hFormula
          exact List.mem_cons_of_mem
            (indexWitness ≐ₘ numₘ(index)) <|
              List.mem_cons_of_mem
                (arityWitness ≐ₘ numₘ(arity))
                hFormula
        have hPositive' :
            Θ ⊢ₘ[godel_quotation_theory]
              arguments ∈ₘ
                seq₊_spaceₘ(CodeStrₘ) :=
          FirstOrder.Derives.context_weaken
            (Γ := Ζ) (Δ := Θ)
            hWeakenΖΘ hPositive
        have hDomain' :
            Θ ⊢ₘ[godel_quotation_theory]
              domₘ(arguments) ≐ₘ
                Sₘ(arityWitness) :=
          FirstOrder.Derives.context_weaken
            (Γ := Ζ) (Δ := Θ)
            hWeakenΖΘ hDomain
        have hValues' :
            Θ ⊢ₘ[godel_quotation_theory]
              ∀ₘ[SetSort.set, 213],
                (x#213 ∈ₘ domₘ(arguments)) ⟶ₘ
                  ((arguments ·ₘ x#213) ∈ₘ
                    TermCodeₘ) := by
          simpa [values] using
            FirstOrder.Derives.context_weaken
              (Γ := Ζ) (Δ := Θ)
              hWeakenΖΘ hValues
        have hEquality' :
            Θ ⊢ₘ[godel_quotation_theory]
              code ≐ₘ
                term_application_code_term
                  arityWitness indexWitness
                  arguments :=
          FirstOrder.Derives.context_weaken
            (Γ := Ζ) (Δ := Θ)
            hWeakenΖΘ hEquality
        have hSuccessorEquality :
            Θ ⊢ₘ[godel_quotation_theory]
              Sₘ(arityWitness) ≐ₘ
                Sₘ(numₘ(arity)) :=
          successor_term_congr_of_equality
            arityWitness (numₘ(arity))
            hArityWitness
            (finite_numeral_term_admissible arity)
            hArityEquality'
        have hConcreteDomain :
            Θ ⊢ₘ[godel_quotation_theory]
              domₘ(arguments) ≐ₘ
                numₘ(arity + 1) := by
          simpa [finite_numeral_term] using
            Metatheory.Derives.equality_trans
              hDomain' hSuccessorEquality
        have hValueEquality' :
            Θ ⊢ₘ[godel_quotation_theory]
              numₘ(token) ≐ₘ
                coded_function_symbol_number_term
                  arityWitness indexWitness :=
          FirstOrder.Derives.context_weaken
            (Γ := Ζ) (Δ := Θ)
            hWeakenΖΘ hValueEquality
        have hRawSymbolEquality :
            Θ ⊢ₘ[godel_quotation_theory]
              sym_codeₘ(numₘ(token)) ≐ₘ
                coded_function_symbol_code_term
                  arityWitness indexWitness := by
          simpa [coded_function_symbol_code_term] using
            gq_singleton_symbol_code_congr_of_equality
              (numₘ(token))
              (coded_function_symbol_number_term
                arityWitness indexWitness)
              hValueEquality'
        have hFunctionCodeCongruence :
            Θ ⊢ₘ[godel_quotation_theory]
              coded_function_symbol_code_term
                  arityWitness indexWitness ≐ₘ
                coded_function_symbol_code_term
                  (numₘ(arity)) (numₘ(index)) :=
          gq_coded_function_symbol_code_term_congr_of_equalities
            arityWitness (numₘ(arity))
            indexWitness (numₘ(index))
            hArityWitness
            (finite_numeral_term_admissible arity)
            hIndexWitness
            (finite_numeral_term_admissible index)
            hArityEquality' hIndexEquality
        have hConcreteSymbolEquality :
            Θ ⊢ₘ[godel_quotation_theory]
              sym_codeₘ(numₘ(token)) ≐ₘ
                coded_function_symbol_code_term
                  (numₘ(arity)) (numₘ(index)) :=
          Metatheory.Derives.equality_trans
            hRawSymbolEquality hFunctionCodeCongruence
        have hCodeCongruence :
            Θ ⊢ₘ[godel_quotation_theory]
              term_application_code_term
                  arityWitness indexWitness
                  arguments ≐ₘ
                term_application_code_term
                  (numₘ(arity)) (numₘ(index))
                  arguments :=
          gq_term_application_code_congr_indices
            arityWitness (numₘ(arity))
            indexWitness (numₘ(index))
            arguments
            hArityWitness
            (finite_numeral_term_admissible arity)
            hIndexWitness
            (finite_numeral_term_admissible index)
            hArguments
            hArityEquality' hIndexEquality
        have hConcreteEquality :
            Θ ⊢ₘ[godel_quotation_theory]
              standard_token_sequence tokens ≐ₘ
                term_application_code_term
                  (numₘ(arity)) (numₘ(index))
                  arguments := by
          simpa [code] using
            Metatheory.Derives.equality_trans
              hEquality' hCodeCongruence
        have hWeakenΓΘ :
            ∀ formula, formula ∈ Γ →
              formula ∈ Θ := by
          intro formula hFormula
          exact hWeakenΖΘ formula <|
            List.mem_cons_of_mem body <|
              List.mem_cons_of_mem argumentsExists <|
                List.mem_cons_of_mem indexExists
                  hFormula
        exact hBranch
          arity index arguments
          hArity hIndex hArguments
          (by
            simp only [arguments, Term.freeSupport]
            decide)
          hWeakenΓΘ
          hPositive' hConcreteDomain
          hValues' hConcreteSymbolEquality
          hConcreteEquality

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
