import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.AbstractFreeTopFormulaCorrectness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedLine

/-!
# ProofT 内在全称推广行

本模块把全称推广证书的两个有界见证直接装入 checked 行条件，并把 Quine
quotation 的 `abstractFreeTop` 正确性接到该分支。整个构造只使用类型化 bound
槽位，不引入变量编号、新鲜性或 admissibility 合同。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace IntrinsicForallGeneralization

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open StructuredCertificateCondition

set_option autoImplicit false

/-- 已验证的两个有界见证直接生成全称推广 checked 行。 -/
theorem line_instance_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (sequence certificates bodyCode : SetOpenTerm free)
    (premiseIndex index : Nat)
    (hPremiseBound :
      Γ ⊢ₘ[T] numₘ(premiseIndex) ∈ₘ numₘ(index))
    (hBodyBound :
      Γ ⊢ₘ[T] bodyCode ∈ₘ ωₘ)
    (hCertificate :
      Γ ⊢ₘ[T]
        (certificates ·ₘ numₘ(index)) ≐ₘ
          forall_generalization_certificate_code
            (numₘ(premiseIndex)) bodyCode)
    (hBodyCode :
      Γ ⊢ₘ[T] formula_code_atₘ(numₘ(1), bodyCode))
    (hAbstract :
      Γ ⊢ₘ[T]
        formula_abstract_free_top_condition
          (sequence ·ₘ numₘ(premiseIndex)) bodyCode)
    (hCurrent :
      Γ ⊢ₘ[T]
        (sequence ·ₘ numₘ(index)) ≐ₘ all_codeₘ(bodyCode)) :
    Γ ⊢ₘ[T]
      IntrinsicCheckedLine.line_instance
        verifier sequence certificates index := by
  let bodyVariable : SetTerm [SetSort.set] free := .bvar .here
  let bodyMatrix : SetFormula [SetSort.set] free :=
    ((certificates.weakenBound SetSort.set ·ₘ numₘ(index)) ≐ₘ
        forall_generalization_certificate_code
          (numₘ(premiseIndex)) bodyVariable) ∧ₘ
      ((formula_code_atₘ(numₘ(1), bodyVariable) ∧ₘ
        formula_abstract_free_top_condition
          (sequence.weakenBound SetSort.set ·ₘ numₘ(premiseIndex))
          bodyVariable) ∧ₘ
        ((sequence.weakenBound SetSort.set ·ₘ numₘ(index)) ≐ₘ
          all_codeₘ(bodyVariable)))
  have hMatrix : Γ ⊢ₘ[T] bodyMatrix.instantiateTop bodyCode := by
    simpa [bodyMatrix, bodyVariable, formula_abstract_free_top_condition,
      forall_generalization_certificate_code, universal_formula_code_term,
      structural_node_code_term, structural_raw_node_code_term,
      structural_list_code_term, Formula.substituteMapped,
      Term.instantiateTop, Term.substitute, Substitution.instantiateTop,
      Term.substituteMapped, Arguments.substituteMapped,
      VariableSubstitution.instantiateTop, VariableSubstitution.freeId,
      VariableSubstitution.cons, VariableSubstitution.empty,
      VariableSubstitution.liftBound, VariableSubstitution.boundId,
      Term.substituteMapped_weakenBound,
      finite_numeral_term_substituteMapped]
      using FirstOrder.Derives.conj_intro hCertificate
        (FirstOrder.Derives.conj_intro
          (FirstOrder.Derives.conj_intro hBodyCode hAbstract)
          hCurrent)
  have hBodyWitness : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedExists set_levy_bound ωₘ bodyMatrix :=
    bounded_exists_intro ωₘ bodyMatrix bodyCode hBodyBound hMatrix
  let sequenceOne : SetTerm [SetSort.set] free :=
    sequence.weakenBound SetSort.set
  let certificatesOne : SetTerm [SetSort.set] free :=
    certificates.weakenBound SetSort.set
  let indexOne : SetTerm [SetSort.set] free :=
    (numₘ(index) : SetOpenTerm free).weakenBound SetSort.set
  let sequenceTwo : SetTerm [SetSort.set, SetSort.set] free :=
    sequenceOne.weakenBound SetSort.set
  let certificatesTwo : SetTerm [SetSort.set, SetSort.set] free :=
    certificatesOne.weakenBound SetSort.set
  let indexTwo : SetTerm [SetSort.set, SetSort.set] free :=
    indexOne.weakenBound SetSort.set
  let premiseIndexTwo : SetTerm [SetSort.set, SetSort.set] free :=
    .bvar (.there .here)
  let bodyCodeTwo : SetTerm [SetSort.set, SetSort.set] free :=
    .bvar .here
  let innerBody : SetFormula [SetSort.set, SetSort.set] free :=
    ((certificatesTwo ·ₘ indexTwo) ≐ₘ
        forall_generalization_certificate_code
          premiseIndexTwo bodyCodeTwo) ∧ₘ
      ((formula_code_atₘ(numₘ(1), bodyCodeTwo) ∧ₘ
        formula_abstract_free_top_condition
          (sequenceTwo ·ₘ premiseIndexTwo) bodyCodeTwo) ∧ₘ
        ((sequenceTwo ·ₘ indexTwo) ≐ₘ all_codeₘ(bodyCodeTwo)))
  let premiseBody : SetFormula [SetSort.set] free :=
    Formula.LevyBound.boundedExists set_levy_bound
      (ωₘ : SetTerm [SetSort.set] free) innerBody
  have hPremiseBody : Γ ⊢ₘ[T]
      premiseBody.instantiateTop (numₘ(premiseIndex)) := by
    simpa [premiseBody, innerBody, bodyMatrix, bodyVariable,
      sequenceOne, certificatesOne, indexOne,
      sequenceTwo, certificatesTwo, indexTwo, premiseIndexTwo,
      bodyCodeTwo, Formula.LevyBound.boundedExists,
      formula_abstract_free_top_condition,
      forall_generalization_certificate_code, universal_formula_code_term,
      structural_node_code_term, structural_raw_node_code_term,
      structural_list_code_term, set_levy_bound,
      Formula.LevyBound.membership,
      Formula.instantiateTop, Formula.substitute,
      Formula.substituteMapped, Term.instantiateTop, Term.substitute,
      Substitution.instantiateTop, Term.substituteMapped,
      FormulaTemplate.term_substituteMapped_liftBound_instantiateTop_two_weakenBound,
      Arguments.substituteMapped, VariableSubstitution.instantiateTop,
      VariableSubstitution.cons, VariableSubstitution.empty,
      VariableSubstitution.liftBound, VariableSubstitution.weakenBound,
      VariableSubstitution.freeId, VariableSubstitution.boundId,
      Term.substituteMapped_weakenBound,
      Arguments.substituteMapped_weakenBound,
      finite_numeral_term_substituteMapped]
      using hBodyWitness
  have hBranch : Γ ⊢ₘ[T]
      forall_generalization_line_condition
        sequence certificates (numₘ(index)) := by
    have hExists := bounded_exists_intro
      (numₘ(index)) premiseBody (numₘ(premiseIndex))
      hPremiseBound hPremiseBody
    simpa [forall_generalization_line_condition, premiseBody,
      innerBody, sequenceOne, certificatesOne, indexOne,
      sequenceTwo, certificatesTwo, indexTwo, premiseIndexTwo,
      bodyCodeTwo] using hExists
  have hLine : Γ ⊢ₘ[T]
      verifier.line_condition
        sequence certificates (numₘ(index)) := by
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_right
    exact hBranch
  simpa [IntrinsicCheckedLine.line_instance] using hLine

/--
Quine quotation 直接生成全称推广 checked 行；公式码良构、码域成员和顶部抽象
正确性均由语法核自动提供。
-/
theorem quote_line_instance_intro
    {σ : Signature} [QuineEncoding.QuotationNumbering σ]
    {T : SetTheory}
    (hExpression : Theory.Extends T expression_encoding_theory)
    {Γ : Context signature []}
    (verifier : CheckedVerifier)
    (sequence certificates : SetOpenTerm [])
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (formula : Formula σ [] (sort :: free))
    (premiseIndex index : Nat)
    (hPremiseBound :
      Γ ⊢ₘ[T] numₘ(premiseIndex) ∈ₘ numₘ(index))
    (hCertificate :
      Γ ⊢ₘ[T]
        (certificates ·ₘ numₘ(index)) ≐ₘ
          forall_generalization_certificate_code
            (numₘ(premiseIndex))
            (QuineEncoding.quote formula.abstractFreeTop : SetOpenTerm []))
    (hPremise :
      Γ ⊢ₘ[T]
        (sequence ·ₘ numₘ(premiseIndex)) ≐ₘ
          (QuineEncoding.quote formula : SetOpenTerm []))
    (hCurrent :
      Γ ⊢ₘ[T]
        (sequence ·ₘ numₘ(index)) ≐ₘ
          all_codeₘ(
            (QuineEncoding.quote formula.abstractFreeTop : SetOpenTerm []))) :
    Γ ⊢ₘ[T]
      IntrinsicCheckedLine.line_instance
        verifier sequence certificates index := by
  let sourceCode : SetOpenTerm [] := QuineEncoding.quote formula
  let bodyCode : SetOpenTerm [] := QuineEncoding.quote formula.abstractFreeTop
  have hBodyCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(1), bodyCode) := by
    simpa [bodyCode] using
      (QuineEncoding.quote_formula_code_at formula.abstractFreeTop)
  have hBodyBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        bodyCode ∈ₘ ωₘ :=
    QuineEncoding.formula_code_at_code_mem_of_derives
      (numₘ(1)) bodyCode hBodyCodeFormal
  have hBodyCode : Γ ⊢ₘ[T]
      formula_code_atₘ(numₘ(1), bodyCode) := by
    exact FirstOrder.Derives.context_weaken
      (Γ := ([] : Context signature [])) (Δ := Γ) (by simp)
      (FirstOrder.Derives.theory_weaken hExpression
        (FirstOrder.Derives.theory_weaken
          formal_language_encoding_theory_subset_expression_encoding_theory
          hBodyCodeFormal))
  have hBodyBound : Γ ⊢ₘ[T] bodyCode ∈ₘ ωₘ := by
    exact FirstOrder.Derives.context_weaken
      (Γ := ([] : Context signature [])) (Δ := Γ) (by simp)
      (FirstOrder.Derives.theory_weaken hExpression
        (FirstOrder.Derives.theory_weaken
          formal_language_encoding_theory_subset_expression_encoding_theory
          hBodyBoundFormal))
  have hAbstractSource : Γ ⊢ₘ[T]
      formula_abstract_free_top_condition sourceCode bodyCode := by
    exact FirstOrder.Derives.context_weaken
      (Γ := ([] : Context signature [])) (Δ := Γ) (by simp)
      (FirstOrder.Derives.theory_weaken hExpression (by
        simpa [sourceCode, bodyCode] using
          (QuineEncoding.quote_formula_abstract_free_top formula)))
  let abstractBody : SetFormula [SetSort.set] [] :=
    formula_abstract_free_top_condition
      (.bvar .here) (bodyCode.weakenBound SetSort.set)
  have hSource : Γ ⊢ₘ[T] abstractBody.instantiateTop sourceCode := by
    simpa [abstractBody, formula_abstract_free_top_condition,
      Formula.instantiateTop, Formula.substitute,
      Substitution.instantiateTop, Formula.substituteMapped,
      Term.substitute, Term.substituteMapped, Arguments.substituteMapped,
      VariableSubstitution.instantiateTop, VariableSubstitution.freeId,
      VariableSubstitution.liftBound, VariableSubstitution.weakenBound,
      finite_numeral_term_substituteMapped]
      using hAbstractSource
  have hPremise' : Γ ⊢ₘ[T]
      (sequence ·ₘ numₘ(premiseIndex)) ≐ₘ sourceCode := by
    simpa [sourceCode] using hPremise
  have hAbstractTarget := FirstOrder.Derives.eq_subst
    (body := abstractBody)
    (Metatheory.Derives.equality_symm hPremise') hSource
  have hAbstract : Γ ⊢ₘ[T]
      formula_abstract_free_top_condition
        (sequence ·ₘ numₘ(premiseIndex)) bodyCode := by
    simpa [abstractBody, formula_abstract_free_top_condition,
      Formula.instantiateTop, Formula.substitute,
      Substitution.instantiateTop, Formula.substituteMapped,
      Term.substitute, Term.substituteMapped, Arguments.substituteMapped,
      VariableSubstitution.instantiateTop, VariableSubstitution.freeId,
      VariableSubstitution.liftBound, VariableSubstitution.weakenBound,
      finite_numeral_term_substituteMapped]
      using hAbstractTarget
  apply line_instance_intro verifier sequence certificates bodyCode
    premiseIndex index hPremiseBound hBodyBound
  · simpa [bodyCode] using hCertificate
  · exact hBodyCode
  · exact hAbstract
  · simpa [bodyCode] using hCurrent

end IntrinsicForallGeneralization
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
