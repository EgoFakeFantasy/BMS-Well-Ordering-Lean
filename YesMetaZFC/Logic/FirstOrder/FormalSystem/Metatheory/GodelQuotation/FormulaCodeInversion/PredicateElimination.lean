import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemSymbolWitnessBound
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCodeReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.PredicateOpening

/-!
# 谓词应用公式码生成条件的有界消去

本模块把 `predicate_application_code_condition` 中的动态元数前驱和谓词编号，
经标准首 token 的对象算术上界消去为外部自然数。参数族仍保持为对象项，并只
向 continuation 暴露 `TermSeqₘ`、精确参数个数和具体应用码等式。
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

/-- 谓词应用码对元数前驱和谓词编号的已证等式保持合同。 -/
theorem gq_predicate_application_code_congr_indices
    {Γ : Context signature}
    (leftArity rightArity leftIndex rightIndex
      arguments : SetTerm)
    (hLeftArity :
      Term.Admissible leftArity SetSort.set)
    (hRightArity :
      Term.Admissible rightArity SetSort.set)
    (hLeftIndex :
      Term.Admissible leftIndex SetSort.set)
    (hRightIndex :
      Term.Admissible rightIndex SetSort.set)
    (hArguments :
      Term.Admissible arguments SetSort.set)
    (hArityEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftArity ≐ₘ rightArity)
    (hIndexEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftIndex ≐ₘ rightIndex) :
    Γ ⊢ₘ[godel_quotation_theory]
      predicate_application_code_term
          leftArity leftIndex arguments ≐ₘ
        predicate_application_code_term
          rightArity rightIndex arguments := by
  let leftPredicate : SetTerm :=
    coded_predicate_symbol_code_term
      leftArity leftIndex
  let rightPredicate : SetTerm :=
    coded_predicate_symbol_code_term
      rightArity rightIndex
  let leftParenthesis : SetTerm :=
    logical_symbol_code_term .leftParenthesis
  let flattened : SetTerm :=
    flattenₘ(arguments)
  let rightParenthesis : SetTerm :=
    logical_symbol_code_term .rightParenthesis
  have hLeftPredicate :
      Term.Admissible leftPredicate SetSort.set := by
    simpa [leftPredicate] using
      coded_predicate_symbol_code_term_admissible
        leftArity leftIndex hLeftArity hLeftIndex
  have hRightPredicate :
      Term.Admissible rightPredicate SetSort.set := by
    simpa [rightPredicate] using
      coded_predicate_symbol_code_term_admissible
        rightArity rightIndex hRightArity hRightIndex
  have hLeftParenthesis :
      Term.Admissible leftParenthesis SetSort.set := by
    simpa [leftParenthesis] using
      logical_symbol_code_term_admissible
        .leftParenthesis
  have hFlattened :
      Term.Admissible flattened SetSort.set := by
    simpa [flattened] using
      finite_sequence_flatten_term_admissible
        arguments hArguments
  have hRightParenthesis :
      Term.Admissible rightParenthesis SetSort.set := by
    simpa [rightParenthesis] using
      logical_symbol_code_term_admissible
        .rightParenthesis
  have hPredicateEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftPredicate ≐ₘ rightPredicate := by
    simpa [leftPredicate, rightPredicate] using
      gq_coded_predicate_symbol_code_term_congr_of_equalities
        leftArity rightArity leftIndex rightIndex
        hLeftArity hRightArity hLeftIndex hRightIndex
        hArityEquality hIndexEquality
  have hLeftEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftParenthesis ≐ₘ leftParenthesis :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) leftParenthesis
  have hFlattenedEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        flattened ≐ₘ flattened :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) flattened
  have hRightEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        rightParenthesis ≐ₘ rightParenthesis :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) rightParenthesis
  have hPrefixEquality :=
    finite_sequence_concatenation_term_congr_of_equalities
      leftPredicate rightPredicate
      leftParenthesis leftParenthesis
      hLeftPredicate hRightPredicate
      hLeftParenthesis hLeftParenthesis
      hPredicateEquality hLeftEquality
  have hMiddleEquality :=
    finite_sequence_concatenation_term_congr_of_equalities
      (leftPredicate ⌢ₘ leftParenthesis)
      (rightPredicate ⌢ₘ leftParenthesis)
      flattened flattened
      (finite_sequence_concatenation_term_admissible
        leftPredicate leftParenthesis
        hLeftPredicate hLeftParenthesis)
      (finite_sequence_concatenation_term_admissible
        rightPredicate leftParenthesis
        hRightPredicate hLeftParenthesis)
      hFlattened hFlattened
      hPrefixEquality hFlattenedEquality
  simpa [leftPredicate, rightPredicate,
    leftParenthesis, flattened, rightParenthesis,
    predicate_application_code_term] using
    finite_sequence_concatenation_term_congr_of_equalities
      ((leftPredicate ⌢ₘ leftParenthesis) ⌢ₘ
        flattened)
      ((rightPredicate ⌢ₘ leftParenthesis) ⌢ₘ
        flattened)
      rightParenthesis rightParenthesis
      (finite_sequence_concatenation_term_admissible
        (leftPredicate ⌢ₘ leftParenthesis)
        flattened
        (finite_sequence_concatenation_term_admissible
          leftPredicate leftParenthesis
          hLeftPredicate hLeftParenthesis)
        hFlattened)
      (finite_sequence_concatenation_term_admissible
        (rightPredicate ⌢ₘ leftParenthesis)
        flattened
        (finite_sequence_concatenation_term_admissible
          rightPredicate leftParenthesis
          hRightPredicate hLeftParenthesis)
        hFlattened)
      hRightParenthesis hRightParenthesis
      hMiddleEquality hRightEquality

/--
标准谓词应用生成条件的有界 continuation 消去。

首 token 把动态元数前驱与谓词编号压入有限范围；整个证明只使用对象算术的
素数幂乘积索引界和有限 numeral 成员消去。
-/
theorem gq_predicate_application_condition_elim_bounded
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
        predicate_application_code_condition
          (standard_token_sequence tokens))
    (hBranch :
      ∀ {Δ : Context signature}
          (arity index : Nat)
          (arguments : SetTerm),
        arity < token + 1 →
        index < token + 1 →
        Term.Admissible arguments SetSort.set →
        (SetSort.set, 220) ∉
          Term.freeSupport arguments →
        (∀ formula, formula ∈ Γ → formula ∈ Δ) →
        Δ ⊢ₘ[godel_quotation_theory]
          arguments ∈ₘ TermSeqₘ →
        Δ ⊢ₘ[godel_quotation_theory]
          domₘ(arguments) ≐ₘ numₘ(arity + 1) →
        Δ ⊢ₘ[godel_quotation_theory]
          sym_codeₘ(numₘ(token)) ≐ₘ
            coded_predicate_symbol_code_term
              (numₘ(arity)) (numₘ(index)) →
        Δ ⊢ₘ[godel_quotation_theory]
          standard_token_sequence tokens ≐ₘ
            predicate_application_code_term
              (numₘ(arity)) (numₘ(index))
              arguments →
        Δ ⊢ₘ[godel_quotation_theory]
          conclusion) :
    Γ ⊢ₘ[godel_quotation_theory]
      conclusion := by
  let code : SetTerm :=
    standard_token_sequence tokens
  let arityWitness : SetTerm := x#230
  let indexWitness : SetTerm := x#231
  let arguments : SetTerm := x#232
  let header : SetFormula :=
    (arityWitness ∈ₘ ωₘ) ∧ₘ
      ((indexWitness ∈ₘ ωₘ) ∧ₘ
        ((arguments ∈ₘ TermSeqₘ) ∧ₘ
          (domₘ(arguments) ≐ₘ
            Sₘ(arityWitness))))
  let equality : SetFormula :=
    code ≐ₘ
      predicate_application_code_term
        arityWitness indexWitness arguments
  let body : SetFormula :=
    header ∧ₘ equality
  let argumentsExists : SetFormula :=
    ∃ₘ[SetSort.set, 232], body
  let indexExists : SetFormula :=
    ∃ₘ[SetSort.set, 231], argumentsExists
  let application : SetFormula :=
    ∃ₘ[SetSort.set, 230], indexExists
  have hArityWitness :
      Term.Admissible arityWitness SetSort.set := by
    simpa [arityWitness] using
      set_variable_admissible 230
  have hIndexWitness :
      Term.Admissible indexWitness SetSort.set := by
    simpa [indexWitness] using
      set_variable_admissible 231
  have hArguments :
      Term.Admissible arguments SetSort.set := by
    simpa [arguments] using
      set_variable_admissible 232
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible tokens
  have hBody :
      Formula.Admissible body := by
    dsimp only [body, header, equality, code]
    prove_admissible
  have hArgumentsExists :
      Formula.Admissible argumentsExists := by
    simpa [argumentsExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set 232 hBody
  have hIndexExists :
      Formula.Admissible indexExists := by
    simpa [indexExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set 231 hArgumentsExists
  have hApplicationAdmissible :
      Formula.Admissible application := by
    simpa [application] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set 230 hIndexExists
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        application := by
    simpa [application, indexExists,
      argumentsExists, body, header, equality,
      code, predicate_application_code_condition] using
      hApplication
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 230)
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
      (eigen := 231)
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
            SetSort.set 231 0 argumentsExists
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
        (eigen := 232)
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
              SetSort.set 232 0 body
        · rcases List.mem_cons.mp hFormula with
            rfl | hFormula
          · have hFresh :
                (SetSort.set, 232) ∉
                  Formula.freeSupport
                    argumentsExists := by
              simpa [argumentsExists,
                Formula.freeSupport] using
                Formula.not_mem_freeSupport_closeFreeAt
                  SetSort.set 232 0 body
            simpa [indexExists] using
              Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
                (SetSort.set, 232)
                SetSort.set 231 0 argumentsExists
                hFresh
          · rw [hContextClosed formula hFormula]
            exact List.not_mem_nil
      · rw [hConclusionClosed]
        exact List.not_mem_nil
      · exact hArgumentsExistsAt
      · let Ζ : Context signature :=
          body :: Ε
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
        have hTermSequence :
            Ζ ⊢ₘ[godel_quotation_theory]
              arguments ∈ₘ TermSeqₘ :=
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
        have hEquality :
            Ζ ⊢ₘ[godel_quotation_theory]
              code ≐ₘ
                predicate_application_code_term
                  arityWitness indexWitness
                  arguments := by
          simpa [body, equality] using
            FirstOrder.Derives.conjElimRight hBodyAt
        have hOpening :=
          FirstOrder.Derives.impElim
            (gq_predicate_application_formula_opening_inversion
              (Γ := Ζ)
              arityWitness indexWitness arguments
              hArityWitness hIndexWitness hArguments
              (reserved_ids_fresh_cons_variable
                230
                (by
                  intro id hId
                  simp only [List.mem_cons,
                    List.not_mem_nil, or_false] at hId
                  rcases hId with
                    rfl | rfl | rfl <;> decide)
                (reserved_ids_fresh_cons_variable
                  231
                  (by
                    intro id hId
                    simp only [List.mem_cons,
                      List.not_mem_nil, or_false] at hId
                    rcases hId with
                      rfl | rfl | rfl <;> decide)
                  (reserved_ids_fresh_nil
                    [0, 1, 2])))
              (by
                simp only [arguments, Term.freeSupport]
                decide))
            hTermSequence
        have hCodePoint :=
          gq_point_inversion_of_equality
            code
            (predicate_application_code_term
              arityWitness indexWitness arguments)
            (numₘ(0))
            (coded_predicate_symbol_number_term
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
                coded_predicate_symbol_number_term
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
                  coded_predicate_symbol_number_term
                    arityWitness indexWitness) ∧ₘ
                (indexWitness ∈ₘ
                  coded_predicate_symbol_number_term
                    arityWitness indexWitness)) := by
          simpa [coded_predicate_symbol_number_term] using
            gq_indices_mem_indexed_prime_power_product
              (Γ := Ζ)
              3 7 arityWitness indexWitness
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
              (coded_predicate_symbol_number_term
                arityWitness indexWitness)
              hArityWitness
              (finite_numeral_term_admissible token)
              (coded_predicate_symbol_number_term_admissible
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
              (coded_predicate_symbol_number_term
                arityWitness indexWitness)
              hIndexWitness
              (finite_numeral_term_admissible token)
              (coded_predicate_symbol_number_term_admissible
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
        have hTermSequence' :
            Θ ⊢ₘ[godel_quotation_theory]
              arguments ∈ₘ TermSeqₘ :=
          FirstOrder.Derives.context_weaken
            (Γ := Ζ) (Δ := Θ)
            hWeakenΖΘ hTermSequence
        have hDomain' :
            Θ ⊢ₘ[godel_quotation_theory]
              domₘ(arguments) ≐ₘ
                Sₘ(arityWitness) :=
          FirstOrder.Derives.context_weaken
            (Γ := Ζ) (Δ := Θ)
            hWeakenΖΘ hDomain
        have hEquality' :
            Θ ⊢ₘ[godel_quotation_theory]
              code ≐ₘ
                predicate_application_code_term
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
                coded_predicate_symbol_number_term
                  arityWitness indexWitness :=
          FirstOrder.Derives.context_weaken
            (Γ := Ζ) (Δ := Θ)
            hWeakenΖΘ hValueEquality
        have hRawSymbolEquality :
            Θ ⊢ₘ[godel_quotation_theory]
              sym_codeₘ(numₘ(token)) ≐ₘ
                coded_predicate_symbol_code_term
                  arityWitness indexWitness := by
          simpa [coded_predicate_symbol_code_term] using
            gq_singleton_symbol_code_congr_of_equality
              (numₘ(token))
              (coded_predicate_symbol_number_term
                arityWitness indexWitness)
              hValueEquality'
        have hPredicateCodeCongruence :
            Θ ⊢ₘ[godel_quotation_theory]
              coded_predicate_symbol_code_term
                  arityWitness indexWitness ≐ₘ
                coded_predicate_symbol_code_term
                  (numₘ(arity)) (numₘ(index)) :=
          gq_coded_predicate_symbol_code_term_congr_of_equalities
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
                coded_predicate_symbol_code_term
                  (numₘ(arity)) (numₘ(index)) :=
          Metatheory.Derives.equality_trans
            hRawSymbolEquality hPredicateCodeCongruence
        have hCodeCongruence :
            Θ ⊢ₘ[godel_quotation_theory]
              predicate_application_code_term
                  arityWitness indexWitness
                  arguments ≐ₘ
                predicate_application_code_term
                  (numₘ(arity)) (numₘ(index))
                  arguments :=
          gq_predicate_application_code_congr_indices
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
                predicate_application_code_term
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
          hTermSequence' hConcreteDomain
          hConcreteSymbolEquality hConcreteEquality

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
