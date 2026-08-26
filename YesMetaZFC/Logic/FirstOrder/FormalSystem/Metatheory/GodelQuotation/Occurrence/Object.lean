import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Occurrence.Quotation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.StandardTokenSequenceConcatenation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.ExpressionEncodingSupport
/-!
# Gödel quotation 的对象 occurrence 理论
本模块承接 quotation occurrence 联合理论、标准序列反演与量词前缀对象语义。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
universe u v w
set_option autoImplicit false
/-! ## 对象层 token 非出现 -/
/--
标准序列语义与表达式出现性定义的公共联合理论。
`occurrence_theory` 已经包含公式码、替换与变量收集定义；因此本层只额外并入标准
有限序列语义，不另加任何出现性公理。
-/
def quotation_occurrence_theory : SetTheory :=
  Theory.union standard_sequence_semantics_theory occurrence_theory
/-- quotation 出现性理论只含闭句。 -/
@[derive_close_sentence]
theorem quotation_occurrence_theory_sentence
    {formula : SetFormula} (hFormula : quotation_occurrence_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with hStandard | hOccurrence
  · exact standard_sequence_semantics_theory_sentence hStandard
  · exact occurrence_theory_sentence hOccurrence
/-- 标准序列语义嵌入 quotation 出现性理论。 -/
theorem qo_weaken_standard_sequence
    {formula : SetFormula} (hDerives :
      ⊢ₘ[standard_sequence_semantics_theory] formula) :
    ⊢ₘ[quotation_occurrence_theory] formula :=
  FirstOrder.Derives.theory_weaken (fun _ hFormula => Or.inl hFormula) hDerives
/-- Gödel quotation 的原有构造理论嵌入出现性联合理论。 -/
theorem qo_weaken_godel_quotation
    {formula : SetFormula} (hDerives : ⊢ₘ[godel_quotation_theory] formula) :
    ⊢ₘ[quotation_occurrence_theory] formula := by
  exact FirstOrder.Derives.theory_weaken (fun _ hFormula => by
      rcases hFormula with hStandard | hSubstitution
      · exact Or.inl hStandard
      · exact Or.inr <|
          substitution_variable_theory_subset_expression_encoding_theory
            hSubstitution)
    hDerives

/--
外部列表分解 `prefixTokens ++ middleTokens ++ suffixTokens` 直接给出对象子串证书。
位置取中段的实际有限偏移，不引入额外编码见证。
-/
theorem standard_token_sequence_middle_substring
    (prefixTokens middleTokens suffixTokens : List Nat) :
    ⊢ₘ[quotation_occurrence_theory]
      code_substring_at_condition
        (standard_token_sequence
          (prefixTokens ++ middleTokens ++ suffixTokens))
        (standard_token_sequence middleTokens)
        (numₘ(prefixTokens.length)) := by
  have hStart :
      ⊢ₘ[quotation_occurrence_theory]
        numₘ(prefixTokens.length) ∈ₘ ωₘ :=
    qo_weaken_standard_sequence <|
      standard_sequence_finite_numeral_mem_omega
        prefixTokens.length
  have hPointwise :=
    qo_weaken_standard_sequence <|
      standard_token_sequence_middle_forall
        prefixTokens middleTokens suffixTokens
  simpa [code_substring_at_condition,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt, set_variable] using
      FirstOrder.Derives.conjIntro hStart hPointwise

/-- 具名变量码在位置零处求值为它的标准变量 token。 -/
theorem named_variable_code_apply_zero (name : Nat) :
    ⊢ₘ[quotation_occurrence_theory]
      ((Numbered.named_variable_code name) ·ₘ numₘ(0)) ≐ₘ
        numₘ(Numbered.variable_token name) := by
  let variableCode := Numbered.named_variable_code name
  let standardCode :=
    standard_token_sequence [Numbered.variable_token name]
  have hVariableCheck :
      Term.CheckCertificate variableCode SetSort.set :=
    Term.check_admissible_complete <|
      variable_code_term_admissible
        (numₘ(name)) (finite_numeral_term_admissible name)
  have hStandardCheck :
      Term.CheckCertificate standardCode SetSort.set := by
    simpa [standardCode] using
      standard_token_sequence_check
        [Numbered.variable_token name]
  have hCodeEquality :
      ⊢ₘ[quotation_occurrence_theory]
        variableCode ≐ₘ standardCode := by
    simpa [variableCode, standardCode] using
      qo_weaken_godel_quotation
        (named_variable_code_eq_standard_token_sequence name)
  have hApplicationEquality :
      ⊢ₘ[quotation_occurrence_theory]
        (variableCode ·ₘ numₘ(0)) ≐ₘ
          (standardCode ·ₘ numₘ(0)) :=
    function_application_term_congr_function_of_equality
      variableCode standardCode (numₘ(0))
      hVariableCheck.admissible hStandardCheck.admissible
      (finite_numeral_term_check 0).admissible hCodeEquality
  have hStandardValue :
      ⊢ₘ[quotation_occurrence_theory]
        (standardCode ·ₘ numₘ(0)) ≐ₘ
          numₘ(Numbered.variable_token name) := by
    simpa [standardCode] using
      qo_weaken_standard_sequence
        (standard_token_sequence_apply_getElem?
          [Numbered.variable_token name] (by simp))
  exact Metatheory.Derives.equality_trans
    hApplicationEquality hStandardValue

/-- 标准 token 串中的具名变量 token 给出对象层变量符号出现证书。 -/
theorem standard_token_sequence_variable_symbol_occurs
    (tokens : List Nat) (name : Nat)
    (hToken : Numbered.variable_token name ∈ tokens) :
    ⊢ₘ[quotation_occurrence_theory]
      variable_symbol_occurs_condition
        (Numbered.named_variable_code name)
        (standard_token_sequence tokens) := by
  rcases List.mem_iff_getElem?.mp hToken with ⟨index, hGet⟩
  have hIndex : index < tokens.length :=
    (List.getElem?_eq_some_iff.mp hGet).1
  have hDomainEquality :=
    qo_weaken_standard_sequence
      (standard_token_sequence_domain_eq_length tokens)
  have hDomain :
      ⊢ₘ[quotation_occurrence_theory]
        numₘ(index) ∈ₘ domₘ(standard_token_sequence tokens) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(index)) (domₘ(standard_token_sequence tokens))
        (numₘ(tokens.length))
        (finite_numeral_term_admissible index)
        (domain_term_admissible
          (standard_token_sequence tokens)
          (standard_token_sequence_admissible tokens))
        (finite_numeral_term_admissible tokens.length)
        hDomainEquality)
      (qo_weaken_standard_sequence
        (standard_sequence_finite_numeral_mem_of_lt
          index tokens.length hIndex))
  have hValue :
      ⊢ₘ[quotation_occurrence_theory]
        (standard_token_sequence tokens ·ₘ numₘ(index)) ≐ₘ
          ((Numbered.named_variable_code name) ·ₘ numₘ(0)) :=
    Metatheory.Derives.equality_trans
      (qo_weaken_standard_sequence
        (standard_token_sequence_apply_getElem? tokens hGet))
      (Metatheory.Derives.equality_symm
        (named_variable_code_apply_zero name))
  have hSequenceBoundary :
      Numbered.CodeBoundary (standard_token_sequence tokens) :=
    ⟨standard_token_sequence_admissible tokens,
      standard_token_sequence_freeSupport_nil tokens⟩
  have hVariableBoundary :
      Numbered.CodeBoundary (Numbered.named_variable_code name) :=
    ⟨variable_code_term_admissible
        (numₘ(name)) (finite_numeral_term_admissible name),
      named_variable_code_freeSupport name⟩
  have hPosition :
      ⊢ₘ[quotation_occurrence_theory]
        ∃ₘ[SetSort.set, 312],
          ((x#312 ∈ₘ domₘ(standard_token_sequence tokens)) ∧ₘ
            ((standard_token_sequence tokens ·ₘ x#312) ≐ₘ
              (Numbered.named_variable_code name ·ₘ numₘ(0)))) := by
    nd_apply FirstOrder.Derives.exists_intro
      (term := numₘ(index))
    simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.substituteFree, Term.substituteFree,
      set_variable,
      Numbered.CodeBoundary.substituteFree_eq hSequenceBoundary,
      Numbered.CodeBoundary.substituteFree_eq hVariableBoundary,
      Numbered.CodeBoundary.substituteFree_eq
        ⟨finite_numeral_term_admissible 0,
          finite_numeral_term_freeSupport 0⟩] using
      FirstOrder.Derives.conjIntro hDomain hValue
  exact FirstOrder.Derives.conjIntro
    (qo_weaken_godel_quotation
      (named_variable_code_mem_variable_symbols name))
    (by simpa [variable_symbol_occurs_condition] using hPosition)

/--
标准 token 串在一个具体有限位置上的变量 token，直接给出逐点出现证书。
该接口保留位置，不把它隐藏到 `variable_symbol_occurs_condition` 的存在量词中。
-/
theorem standard_token_sequence_variable_occurs_at_position
    (tokens : List Nat) (name index : Nat)
    (hGet :
      tokens[index]? = some (Numbered.variable_token name)) :
    ⊢ₘ[quotation_occurrence_theory]
      variable_occurs_at_position_condition
        (Numbered.named_variable_code name)
        (standard_token_sequence tokens)
        (numₘ(index)) := by
  have hIndex : index < tokens.length :=
    (List.getElem?_eq_some_iff.mp hGet).1
  have hDomainEquality :=
    qo_weaken_standard_sequence
      (standard_token_sequence_domain_eq_length tokens)
  have hDomain :
      ⊢ₘ[quotation_occurrence_theory]
        numₘ(index) ∈ₘ domₘ(standard_token_sequence tokens) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(index)) (domₘ(standard_token_sequence tokens))
        (numₘ(tokens.length))
        (finite_numeral_term_admissible index)
        (domain_term_admissible
          (standard_token_sequence tokens)
          (standard_token_sequence_admissible tokens))
        (finite_numeral_term_admissible tokens.length)
        hDomainEquality)
      (qo_weaken_standard_sequence
        (standard_sequence_finite_numeral_mem_of_lt
          index tokens.length hIndex))
  have hValue :
      ⊢ₘ[quotation_occurrence_theory]
        (standard_token_sequence tokens ·ₘ numₘ(index)) ≐ₘ
          (Numbered.named_variable_code name ·ₘ numₘ(0)) :=
    Metatheory.Derives.equality_trans
      (qo_weaken_standard_sequence
        (standard_token_sequence_apply_getElem? tokens hGet))
      (Metatheory.Derives.equality_symm
        (named_variable_code_apply_zero name))
  simpa [variable_occurs_at_position_condition] using
    FirstOrder.Derives.conjIntro hDomain hValue

/--
规范公式串中显式出现的全称 binder，连同其体的公式码证书，
直接给出该 binder 在规范起点处的对象证书。
-/
theorem standard_token_sequence_universal_binder_at_of_formula_code
    (prefixTokens bodyTokens suffixTokens : List Nat)
    (name : Nat)
    (hBodyMember :
      ⊢ₘ[quotation_occurrence_theory]
        standard_token_sequence bodyTokens ∈ₘ FormulaCodeₘ) :
    ⊢ₘ[quotation_occurrence_theory]
      universal_binder_at_condition
        (Numbered.named_variable_code name)
        (standard_token_sequence
          (prefixTokens ++
            Numbered.universal_tokens name bodyTokens ++
              suffixTokens))
        (standard_token_sequence bodyTokens)
        (numₘ(prefixTokens.length)) := by
  let variableCode := Numbered.named_variable_code name
  let bodyCode := standard_token_sequence bodyTokens
  let binderTokens := Numbered.universal_tokens name bodyTokens
  let formulaCode :=
    standard_token_sequence
      (prefixTokens ++ binderTokens ++ suffixTokens)
  let startCode := numₘ(prefixTokens.length)
  let binderCode := forall_codeₘ(variableCode, bodyCode)
  let standardBinderCode := standard_token_sequence binderTokens
  have hVariableBoundary :
      Numbered.CodeBoundary variableCode :=
    ⟨variable_code_term_admissible
        (numₘ(name)) (finite_numeral_term_admissible name),
      by simp [variableCode]⟩
  have hBodyBoundary :
      Numbered.CodeBoundary bodyCode :=
    ⟨standard_token_sequence_admissible bodyTokens,
      by
        dsimp [bodyCode]
        exact standard_token_sequence_freeSupport_nil bodyTokens⟩
  have hFormulaBoundary :
      Numbered.CodeBoundary formulaCode :=
    ⟨standard_token_sequence_admissible
        (prefixTokens ++ binderTokens ++ suffixTokens),
      by
        dsimp [formulaCode]
        exact standard_token_sequence_freeSupport_nil
          (prefixTokens ++ binderTokens ++ suffixTokens)⟩
  have hStartBoundary :
      Numbered.CodeBoundary startCode :=
    ⟨finite_numeral_term_admissible prefixTokens.length,
      finite_numeral_term_freeSupport prefixTokens.length⟩
  have hVariableMember :
      ⊢ₘ[quotation_occurrence_theory]
        variableCode ∈ₘ VarSymₘ := by
    simpa [variableCode] using
      qo_weaken_godel_quotation
        (named_variable_code_mem_variable_symbols name)
  have hBodyFormula :
      ⊢ₘ[quotation_occurrence_theory]
        formula_codeₘ(bodyCode) := by
    exact FirstOrder.Derives.iffElimLeft
      (qo_weaken_godel_quotation <| by
        simpa [bodyCode] using
          gq_formula_code_definition_instance
            bodyCode (standard_token_sequence_admissible bodyTokens))
      (by simpa [bodyCode] using hBodyMember)
  have hBodyString :
      ⊢ₘ[quotation_occurrence_theory]
        bodyCode ∈ₘ CodeStrₘ := by
    exact FirstOrder.Derives.impElim
      (qo_weaken_godel_quotation <| by
        simpa [bodyCode] using
          gq_formula_code_member_implies_code_string
            bodyCode (standard_token_sequence_admissible bodyTokens))
      (by simpa [bodyCode] using hBodyMember)
  have hBinderEquality :
      ⊢ₘ[quotation_occurrence_theory]
        binderCode ≐ₘ standardBinderCode := by
    simpa [binderCode, standardBinderCode, variableCode,
      bodyCode, binderTokens] using
      qo_weaken_godel_quotation
        (universal_formula_code_eq_standard_token_sequence
          name bodyTokens (standard_token_sequence bodyTokens)
          (FirstOrder.Derives.eq_refl_m
            (standard_token_sequence bodyTokens)))
  have hSubstringStandard :
      ⊢ₘ[quotation_occurrence_theory]
        code_substring_at_condition
          formulaCode standardBinderCode startCode := by
    simpa [formulaCode, standardBinderCode,
      binderTokens, startCode] using
      standard_token_sequence_middle_substring
        prefixTokens binderTokens suffixTokens
  let parameter : FreeVarId := 494
  let template : SetFormula :=
    code_substring_at_condition
      formulaCode (x#parameter) startCode
  have hFormulaFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement formulaCode =
        formulaCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter replacement formulaCode <| by
        dsimp [formulaCode]
        rw [standard_token_sequence_freeSupport_nil]
        exact List.not_mem_nil
  have hStartFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement startCode =
        startCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter replacement startCode <| by
        simp [startCode, finite_numeral_term_freeSupport]
  have hNormalize
      (replacement : SetTerm)
      (hReplacement : Term.Admissible replacement SetSort.set)
      (hReplacementFresh :
        (SetSort.set, 320) ∉ Term.freeSupport replacement) :
      Formula.substituteFree SetSort.set parameter replacement template =
        code_substring_at_condition
          formulaCode replacement startCode := by
    dsimp only [template, code_substring_at_condition]
    simp only [Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set parameter 320 0 replacement _
      (by decide) hReplacement.2 hReplacementFresh]
    simp [Formula.substituteFree, Term.substituteFree,
      set_variable, parameter, hFormulaFixed, hStartFixed]
  have hBinderAdmissible :
      Term.Admissible binderCode SetSort.set := by
    dsimp [binderCode, variableCode, bodyCode]
    exact universal_formula_code_term_admissible _ _
      (variable_code_term_admissible
        (numₘ(name)) (finite_numeral_term_admissible name))
      (standard_token_sequence_admissible bodyTokens)
  have hBinderFresh :
      (SetSort.set, 320) ∉ Term.freeSupport binderCode := by
    dsimp [binderCode]
    simp only [Term.freeSupport, Term.freeSupportList]
    rw [hVariableBoundary.2, hBodyBoundary.2]
    exact List.not_mem_nil
  have hStandardBinderAdmissible :
      Term.Admissible standardBinderCode SetSort.set := by
    exact standard_token_sequence_admissible binderTokens
  have hStandardBinderFresh :
      (SetSort.set, 320) ∉
        Term.freeSupport standardBinderCode := by
    dsimp [standardBinderCode]
    rw [standard_token_sequence_freeSupport_nil]
    exact List.not_mem_nil
  have hSubstringIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := quotation_occurrence_theory) (Γ := [])
      (sort := SetSort.set) (eigen := parameter)
      (left := binderCode) (right := standardBinderCode)
      (body := template) hBinderEquality
      (hBodyCheck := Formula.check_certificate_of_admissible <| by
        dsimp [template]
        exact code_substring_at_condition_admissible
          formulaCode (x#parameter) startCode
          hFormulaBoundary.1 (set_variable_admissible parameter)
          hStartBoundary.1)
  have hSubstring :
      ⊢ₘ[quotation_occurrence_theory]
        code_substring_at_condition
          formulaCode binderCode startCode := by
    apply FirstOrder.Derives.iffElimLeft
      (by
        simpa only [
          hNormalize binderCode hBinderAdmissible hBinderFresh,
          hNormalize standardBinderCode
            hStandardBinderAdmissible hStandardBinderFresh] using
          hSubstringIffRaw)
    exact hSubstringStandard
  have hBinder :
      ⊢ₘ[quotation_occurrence_theory]
        universal_binder_at_condition
          variableCode formulaCode bodyCode startCode := by
    simpa [universal_binder_at_condition, binderCode] using
      FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjIntro hVariableMember
          (FirstOrder.Derives.conjIntro hBodyFormula hBodyString))
        hSubstring
  simpa [variableCode, formulaCode, bodyCode, startCode,
    binderTokens] using hBinder

/--
规范公式串中显式出现的全称 binder，连同其体的公式码证书，
直接给出对应的对象层量词出现证书。
-/
theorem standard_token_sequence_quantifier_occurs_of_formula_code
    (prefixTokens bodyTokens suffixTokens : List Nat)
    (name : Nat)
    (hBodyMember :
      ⊢ₘ[quotation_occurrence_theory]
        standard_token_sequence bodyTokens ∈ₘ FormulaCodeₘ) :
    ⊢ₘ[quotation_occurrence_theory]
      quantifier_occurs_condition
        (Numbered.named_variable_code name)
        (standard_token_sequence
          (prefixTokens ++
            Numbered.universal_tokens name bodyTokens ++
              suffixTokens)) := by
  let variableCode := Numbered.named_variable_code name
  let bodyCode := standard_token_sequence bodyTokens
  let binderTokens := Numbered.universal_tokens name bodyTokens
  let formulaCode :=
    standard_token_sequence
      (prefixTokens ++ binderTokens ++ suffixTokens)
  let startCode := numₘ(prefixTokens.length)
  have hVariableBoundary :
      Numbered.CodeBoundary variableCode :=
    ⟨variable_code_term_admissible
        (numₘ(name)) (finite_numeral_term_admissible name),
      by simp [variableCode]⟩
  have hBodyBoundary :
      Numbered.CodeBoundary bodyCode :=
    ⟨standard_token_sequence_admissible bodyTokens,
      by
        dsimp [bodyCode]
        exact standard_token_sequence_freeSupport_nil bodyTokens⟩
  have hFormulaBoundary :
      Numbered.CodeBoundary formulaCode :=
    ⟨standard_token_sequence_admissible
        (prefixTokens ++ binderTokens ++ suffixTokens),
      by
        dsimp [formulaCode]
        exact standard_token_sequence_freeSupport_nil
          (prefixTokens ++ binderTokens ++ suffixTokens)⟩
  have hStartBoundary :
      Numbered.CodeBoundary startCode :=
    ⟨finite_numeral_term_admissible prefixTokens.length,
      finite_numeral_term_freeSupport prefixTokens.length⟩
  have hBinder :
      ⊢ₘ[quotation_occurrence_theory]
        universal_binder_at_condition
          variableCode formulaCode bodyCode startCode := by
    simpa [variableCode, formulaCode, bodyCode, startCode,
      binderTokens] using
      standard_token_sequence_universal_binder_at_of_formula_code
        prefixTokens bodyTokens suffixTokens name hBodyMember
  have hStartSubstitution :
      Formula.substituteFree SetSort.set 322 startCode
          (universal_binder_at_condition
            variableCode formulaCode bodyCode (x#322)) =
        universal_binder_at_condition
          variableCode formulaCode bodyCode startCode := by
    dsimp only [universal_binder_at_condition,
      code_substring_at_condition]
    simp only [Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 322 320 0 startCode _
      (by decide) hStartBoundary.1.2 (by
        rw [hStartBoundary.2]
        exact List.not_mem_nil)]
    simp [Formula.substituteFree, Term.substituteFree,
      set_variable,
      Numbered.CodeBoundary.substituteFree_eq hVariableBoundary,
      Numbered.CodeBoundary.substituteFree_eq hFormulaBoundary,
      Numbered.CodeBoundary.substituteFree_eq hBodyBoundary
      ]
  have hStartExists :
      ⊢ₘ[quotation_occurrence_theory]
        ∃ₘ[SetSort.set, 322],
          universal_binder_at_condition
            variableCode formulaCode bodyCode (x#322) := by
    nd_apply FirstOrder.Derives.exists_intro
      (term := startCode)
    simpa only [Formula.openAt_closeFreeAt_eq_substituteFree,
      hStartSubstitution] using hBinder
  have hBodySubstitution :
      Formula.substituteFree SetSort.set 321 bodyCode
          (∃ₘ[SetSort.set, 322],
            universal_binder_at_condition
              variableCode formulaCode (x#321) (x#322)) =
        (∃ₘ[SetSort.set, 322],
          universal_binder_at_condition
            variableCode formulaCode bodyCode (x#322)) := by
    simp only [Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 321 322 0 bodyCode _
      (by decide) hBodyBoundary.1.2 (by
        rw [hBodyBoundary.2]
        exact List.not_mem_nil)]
    simp only [universal_binder_at_condition,
      code_substring_at_condition, Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 321 320 0 bodyCode _
      (by decide) hBodyBoundary.1.2 (by
        rw [hBodyBoundary.2]
        exact List.not_mem_nil)]
    simp [Formula.substituteFree, Term.substituteFree,
      set_variable,
      Numbered.CodeBoundary.substituteFree_eq hVariableBoundary,
      Numbered.CodeBoundary.substituteFree_eq hFormulaBoundary
      ]
  have hBodyExists :
      ⊢ₘ[quotation_occurrence_theory]
        ∃ₘ[SetSort.set, 321],
          ∃ₘ[SetSort.set, 322],
            universal_binder_at_condition
              variableCode formulaCode (x#321) (x#322) := by
    nd_apply FirstOrder.Derives.exists_intro
      (term := bodyCode)
    simpa only [Formula.openAt_closeFreeAt_eq_substituteFree,
      hBodySubstitution] using hStartExists
  simpa [quantifier_occurs_condition, variableCode,
    formulaCode, binderTokens] using hBodyExists

/--
规范全称 binder 的体内有限位置，给出整个公式串中的量词体位置证书。
全局位置按对象定义的偏移方向写成 `index + (3 + prefix.length)`。
-/
theorem standard_token_sequence_quantifier_body_position_of_formula_code
    (prefixTokens bodyTokens suffixTokens : List Nat)
    (name index : Nat)
    (hIndex : index < bodyTokens.length)
    (hBodyMember :
      ⊢ₘ[quotation_occurrence_theory]
        standard_token_sequence bodyTokens ∈ₘ FormulaCodeₘ) :
    ⊢ₘ[quotation_occurrence_theory]
      quantifier_body_position_condition
        (Numbered.named_variable_code name)
        (standard_token_sequence
          (prefixTokens ++
            Numbered.universal_tokens name bodyTokens ++
              suffixTokens))
        (numₘ(index + (3 + prefixTokens.length))) := by
  let variableCode := Numbered.named_variable_code name
  let bodyCode := standard_token_sequence bodyTokens
  let binderTokens := Numbered.universal_tokens name bodyTokens
  let formulaCode :=
    standard_token_sequence
      (prefixTokens ++ binderTokens ++ suffixTokens)
  let startCode := numₘ(prefixTokens.length)
  let relativeCode := numₘ(index)
  let positionCode := numₘ(index + (3 + prefixTokens.length))
  have hVariableBoundary :
      Numbered.CodeBoundary variableCode :=
    ⟨variable_code_term_admissible
        (numₘ(name)) (finite_numeral_term_admissible name),
      by simp [variableCode]⟩
  have hBodyBoundary :
      Numbered.CodeBoundary bodyCode :=
    ⟨standard_token_sequence_admissible bodyTokens,
      by
        dsimp [bodyCode]
        exact standard_token_sequence_freeSupport_nil bodyTokens⟩
  have hFormulaBoundary :
      Numbered.CodeBoundary formulaCode :=
    ⟨standard_token_sequence_admissible
        (prefixTokens ++ binderTokens ++ suffixTokens),
      by
        dsimp [formulaCode]
        exact standard_token_sequence_freeSupport_nil
          (prefixTokens ++ binderTokens ++ suffixTokens)⟩
  have hStartBoundary :
      Numbered.CodeBoundary startCode :=
    ⟨finite_numeral_term_admissible prefixTokens.length,
      finite_numeral_term_freeSupport prefixTokens.length⟩
  have hRelativeBoundary :
      Numbered.CodeBoundary relativeCode :=
    ⟨finite_numeral_term_admissible index,
      finite_numeral_term_freeSupport index⟩
  have hPositionBoundary :
      Numbered.CodeBoundary positionCode :=
    ⟨finite_numeral_term_admissible
        (index + (3 + prefixTokens.length)),
      finite_numeral_term_freeSupport
        (index + (3 + prefixTokens.length))⟩
  have hBinder :
      ⊢ₘ[quotation_occurrence_theory]
        universal_binder_at_condition
          variableCode formulaCode bodyCode startCode := by
    simpa [variableCode, formulaCode, bodyCode, startCode,
      binderTokens] using
      standard_token_sequence_universal_binder_at_of_formula_code
        prefixTokens bodyTokens suffixTokens name hBodyMember
  have hDomainEquality :=
    qo_weaken_standard_sequence
      (standard_token_sequence_domain_eq_length bodyTokens)
  have hRelativeDomain :
      ⊢ₘ[quotation_occurrence_theory]
        relativeCode ∈ₘ domₘ(bodyCode) := by
    exact FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        relativeCode (domₘ(bodyCode)) (numₘ(bodyTokens.length))
        (finite_numeral_term_admissible index)
        (domain_term_admissible bodyCode
          (standard_token_sequence_admissible bodyTokens))
        (finite_numeral_term_admissible bodyTokens.length)
        (by simpa [bodyCode] using hDomainEquality))
      (by
        simpa [relativeCode] using
          qo_weaken_standard_sequence
            (standard_sequence_finite_numeral_mem_of_lt
              index bodyTokens.length hIndex))
  have hInnerAddition :
      ⊢ₘ[quotation_occurrence_theory]
        numₘ(3 + prefixTokens.length) ≐ₘ
          (numₘ(3) +ₘ numₘ(prefixTokens.length)) :=
    qo_weaken_standard_sequence
      (standard_token_sequence_finite_numeral_addition
        3 prefixTokens.length)
  have hOuterAddition :
      ⊢ₘ[quotation_occurrence_theory]
        positionCode ≐ₘ
          (relativeCode +ₘ numₘ(3 + prefixTokens.length)) := by
    simpa [positionCode, relativeCode] using
      qo_weaken_standard_sequence
        (standard_token_sequence_finite_numeral_addition
          index (3 + prefixTokens.length))
  have hAdditionCongruence :
      ⊢ₘ[quotation_occurrence_theory]
        (relativeCode +ₘ numₘ(3 + prefixTokens.length)) ≐ₘ
          (relativeCode +ₘ (numₘ(3) +ₘ startCode)) := by
    simpa [startCode] using
      natural_addition_term_congr_of_equalities
        relativeCode relativeCode
        (numₘ(3 + prefixTokens.length))
        (numₘ(3) +ₘ numₘ(prefixTokens.length))
        (finite_numeral_term_admissible index)
        (finite_numeral_term_admissible index)
        (finite_numeral_term_admissible
          (3 + prefixTokens.length))
        (natural_addition_term_admissible
          (numₘ(3)) (numₘ(prefixTokens.length))
          (finite_numeral_term_admissible 3)
          (finite_numeral_term_admissible prefixTokens.length))
        (FirstOrder.Derives.eq_refl_m relativeCode)
        hInnerAddition
  have hPositionEquality :
      ⊢ₘ[quotation_occurrence_theory]
        positionCode ≐ₘ
          (relativeCode +ₘ (numₘ(3) +ₘ startCode)) :=
    Metatheory.Derives.equality_trans
      hOuterAddition hAdditionCongruence
  have hCore :
      ⊢ₘ[quotation_occurrence_theory]
        ((universal_binder_at_condition
              variableCode formulaCode bodyCode startCode ∧ₘ
            (relativeCode ∈ₘ domₘ(bodyCode))) ∧ₘ
          (positionCode ≐ₘ
            (relativeCode +ₘ (numₘ(3) +ₘ startCode)))) :=
    FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro hBinder hRelativeDomain)
      hPositionEquality
  have hNumeralBoundary (value : Nat) :
      Numbered.CodeBoundary (numₘ(value)) :=
    ⟨finite_numeral_term_admissible value,
      finite_numeral_term_freeSupport value⟩
  have hNumeralOpen (value depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement (numₘ(value)) =
        numₘ(value) :=
    Numbered.CodeBoundary.openAt_eq
      (hNumeralBoundary value) depth replacement
  have hNumeralClose (value id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth (numₘ(value)) =
        numₘ(value) :=
    Numbered.CodeBoundary.closeFreeAt_eq
      (hNumeralBoundary value) id depth
  have hNumeralSubstitute
      (value : Nat) (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement (numₘ(value)) =
        numₘ(value) :=
    Numbered.CodeBoundary.substituteFree_eq
      (hNumeralBoundary value) id replacement
  have hStandardBoundary (tokens : List Nat) :
      Numbered.CodeBoundary (standard_token_sequence tokens) :=
    ⟨standard_token_sequence_admissible tokens,
      standard_token_sequence_freeSupport_nil tokens⟩
  have hStandardOpen
      (tokens : List Nat) (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement
          (standard_token_sequence tokens) =
        standard_token_sequence tokens :=
    Numbered.CodeBoundary.openAt_eq
      (hStandardBoundary tokens) depth replacement
  have hStandardClose
      (tokens : List Nat) (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth
          (standard_token_sequence tokens) =
        standard_token_sequence tokens :=
    Numbered.CodeBoundary.closeFreeAt_eq
      (hStandardBoundary tokens) id depth
  have hStandardSubstitute
      (tokens : List Nat) (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement
          (standard_token_sequence tokens) =
        standard_token_sequence tokens :=
    Numbered.CodeBoundary.substituteFree_eq
      (hStandardBoundary tokens) id replacement
  unfold quantifier_body_position_condition
  nd_apply FirstOrder.Derives.exists_intro
    (term := bodyCode)
  nd_apply FirstOrder.Derives.exists_intro
    (term := startCode)
  nd_apply FirstOrder.Derives.exists_intro
    (term := relativeCode)
  simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
    Term.openAt_closeFreeAt_eq_substituteFree,
    universal_binder_at_condition, code_substring_at_condition,
    Formula.openAt, Formula.closeFreeAt, Formula.next_depth,
    Formula.substituteFree, Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable, set_bound_variable,
    hNumeralOpen, hNumeralClose, hNumeralSubstitute,
    hStandardOpen, hStandardClose, hStandardSubstitute,
    variableCode, formulaCode, bodyCode, startCode,
    relativeCode, positionCode, binderTokens,
    Numbered.CodeBoundary.openAt_eq hVariableBoundary,
    Numbered.CodeBoundary.openAt_eq hFormulaBoundary,
    Numbered.CodeBoundary.openAt_eq hBodyBoundary,
    Numbered.CodeBoundary.openAt_eq hStartBoundary,
    Numbered.CodeBoundary.openAt_eq hRelativeBoundary,
    Numbered.CodeBoundary.openAt_eq hPositionBoundary,
    Numbered.CodeBoundary.closeFreeAt_eq hVariableBoundary,
    Numbered.CodeBoundary.closeFreeAt_eq hFormulaBoundary,
    Numbered.CodeBoundary.closeFreeAt_eq hBodyBoundary,
    Numbered.CodeBoundary.closeFreeAt_eq hStartBoundary,
    Numbered.CodeBoundary.closeFreeAt_eq hRelativeBoundary,
    Numbered.CodeBoundary.closeFreeAt_eq hPositionBoundary,
    Numbered.CodeBoundary.substituteFree_eq hVariableBoundary,
    Numbered.CodeBoundary.substituteFree_eq hFormulaBoundary,
    Numbered.CodeBoundary.substituteFree_eq hBodyBoundary,
    Numbered.CodeBoundary.substituteFree_eq hStartBoundary,
    Numbered.CodeBoundary.substituteFree_eq hRelativeBoundary,
    Numbered.CodeBoundary.substituteFree_eq hPositionBoundary] using
      hCore

/--
量词体位置见证本身已经携带一个全称 binder，故必然蕴含对应量词出现。
这里只消去定义中的三个存在量词，不使用任何 quotation 反演。
-/
theorem quantifier_body_position_imp_quantifier_occurs
    (boundVariable formula position : SetTerm)
    (hBoundVariable : Numbered.CodeBoundary boundVariable)
    (hFormula : Numbered.CodeBoundary formula)
    (hPosition : Numbered.CodeBoundary position) :
    ⊢ₘ[quotation_occurrence_theory]
      quantifier_body_position_condition
          boundVariable formula position ⟶ₘ
        quantifier_occurs_condition boundVariable formula := by
  let binder : SetFormula :=
    universal_binder_at_condition
      boundVariable formula (x#325) (x#326)
  let inner : SetFormula :=
    ((binder ∧ₘ ((x#327) ∈ₘ domₘ(x#325))) ∧ₘ
      (position ≐ₘ ((x#327) +ₘ (numₘ(3) +ₘ (x#326)))))
  let body₂ : SetFormula :=
    ∃ₘ[SetSort.set, 327], inner
  let body₁ : SetFormula :=
    ∃ₘ[SetSort.set, 326], body₂
  let conclusion : SetFormula :=
    quantifier_occurs_condition boundVariable formula
  have hTheoryFresh (id : FreeVarId) :
      ∀ φ, quotation_occurrence_theory φ →
        (SetSort.set, id) ∉ Formula.freeSupport φ := by
    intro φ hφ
    rw [(quotation_occurrence_theory_sentence hφ).2]
    exact List.not_mem_nil
  have hEmptyFresh (id : FreeVarId) :
      ∀ φ, φ ∈ ([] : Context signature) →
        (SetSort.set, id) ∉ Formula.freeSupport φ := by
    intro φ hφ
    exact False.elim (List.not_mem_nil hφ)
  have hConclusionFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Formula.freeSupport conclusion := by
    intro hMember
    rcases quantifier_occurs_condition_freeSupport_subset
        boundVariable formula (SetSort.set, id) <| by
          simpa [conclusion] using hMember with hMember | hMember
    · rw [hBoundVariable.2] at hMember
      exact List.not_mem_nil hMember
    · rw [hFormula.2] at hMember
      exact List.not_mem_nil hMember
  have hInnerCheck : Formula.CheckCertificate inner := by
    apply Formula.check_admissible_complete
    have hBody :
        Term.Admissible (x#325) SetSort.set :=
      set_variable_admissible 325
    have hStart :
        Term.Admissible (x#326) SetSort.set :=
      set_variable_admissible 326
    have hIndex :
        Term.Admissible (x#327) SetSort.set :=
      set_variable_admissible 327
    have hBinder :=
      universal_binder_at_condition_admissible
        boundVariable formula (x#325) (x#326)
        hBoundVariable.1 hFormula.1 hBody hStart
    have hIndexBody :=
      membership_formula_admissible hIndex
        (domain_term_admissible (x#325) hBody)
    have hBodyOffset :=
      natural_addition_term_admissible
        (numₘ(3)) (x#326)
        (finite_numeral_term_admissible 3) hStart
    have hAbsolutePosition :=
      natural_addition_term_admissible
        (x#327) (numₘ(3) +ₘ x#326)
        hIndex hBodyOffset
    simpa [inner, binder] using
      Formula.Admissible.conj
        (Formula.Admissible.conj hBinder hIndexBody)
        (Formula.Admissible.equal hPosition.1 hAbsolutePosition)
  have hInnerImp :
      ⊢ₘ[quotation_occurrence_theory]
        inner ⟶ₘ conclusion := by
    nd_apply FirstOrder.Derives.impIntro
      (hAntecedentCheck := hInnerCheck)
    let Γ : Context signature := [inner]
    have hInner :
        Γ ⊢ₘ[quotation_occurrence_theory] inner :=
      FirstOrder.Derives.assumption (by simp [Γ])
    have hBinder :
        Γ ⊢ₘ[quotation_occurrence_theory] binder :=
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimLeft hInner
    have hStartExists :
        Γ ⊢ₘ[quotation_occurrence_theory]
          ∃ₘ[SetSort.set, 322],
            universal_binder_at_condition
              boundVariable formula (x#325) (x#322) := by
      nd_apply FirstOrder.Derives.exists_intro
        (term := x#326)
      simpa [binder,
        Formula.openAt_closeFreeAt_eq_substituteFree,
        Formula.openAt, Formula.closeFreeAt, Formula.next_depth,
        Formula.substituteFree, Term.openAt, Term.closeFreeAt,
        Term.substituteFree, set_variable, set_bound_variable,
        universal_binder_at_condition, code_substring_at_condition,
        Numbered.CodeBoundary.openAt_eq hBoundVariable,
        Numbered.CodeBoundary.openAt_eq hFormula,
        Numbered.CodeBoundary.closeFreeAt_eq hBoundVariable,
        Numbered.CodeBoundary.closeFreeAt_eq hFormula,
        Numbered.CodeBoundary.substituteFree_eq hBoundVariable,
        Numbered.CodeBoundary.substituteFree_eq hFormula] using
          hBinder
    have hBodyExists :
        Γ ⊢ₘ[quotation_occurrence_theory]
          ∃ₘ[SetSort.set, 321],
            ∃ₘ[SetSort.set, 322],
              universal_binder_at_condition
                boundVariable formula (x#321) (x#322) := by
      nd_apply FirstOrder.Derives.exists_intro
        (term := x#325)
      simpa [
        Formula.openAt_closeFreeAt_eq_substituteFree,
        Formula.openAt, Formula.closeFreeAt, Formula.next_depth,
        Formula.substituteFree, Term.openAt, Term.closeFreeAt,
        Term.substituteFree, set_variable, set_bound_variable,
        universal_binder_at_condition, code_substring_at_condition,
        Numbered.CodeBoundary.openAt_eq hBoundVariable,
        Numbered.CodeBoundary.openAt_eq hFormula,
        Numbered.CodeBoundary.closeFreeAt_eq hBoundVariable,
        Numbered.CodeBoundary.closeFreeAt_eq hFormula,
        Numbered.CodeBoundary.substituteFree_eq hBoundVariable,
        Numbered.CodeBoundary.substituteFree_eq hFormula] using
          hStartExists
    simpa [conclusion, quantifier_occurs_condition] using
      hBodyExists
  have hRelativeImp :=
    FirstOrder.Derives.exists_imp_of_imp
      (T := quotation_occurrence_theory)
      (Γ := ([] : Context signature))
      (sort := SetSort.set) (eigen := 327)
      (body := inner) (conclusion := conclusion)
      (hTheoryFresh 327) (hEmptyFresh 327)
      (hConclusionFresh 327) hInnerImp
  have hStartImp :=
    FirstOrder.Derives.exists_imp_of_imp
      (T := quotation_occurrence_theory)
      (Γ := ([] : Context signature))
      (sort := SetSort.set) (eigen := 326)
      (body := body₂) (conclusion := conclusion)
      (hTheoryFresh 326) (hEmptyFresh 326)
      (hConclusionFresh 326)
      (by simpa [body₂] using hRelativeImp)
  have hBodyImp :=
    FirstOrder.Derives.exists_imp_of_imp
      (T := quotation_occurrence_theory)
      (Γ := ([] : Context signature))
      (sort := SetSort.set) (eigen := 325)
      (body := body₁) (conclusion := conclusion)
      (hTheoryFresh 325) (hEmptyFresh 325)
      (hConclusionFresh 325)
      (by simpa [body₁] using hStartImp)
  simpa [quantifier_body_position_condition, binder,
    inner, body₂, body₁, conclusion] using hBodyImp

/-- 全称 binder 条件的合法性由四个对象项证书计算。 -/
@[formula_check]
theorem qo_universal_binder_at_condition_check
    (boundVariable formula body start : SetTerm)
    (hBoundVariable : Term.CheckCertificate boundVariable SetSort.set)
    (hFormula : Term.CheckCertificate formula SetSort.set)
    (hBody : Term.CheckCertificate body SetSort.set)
    (hStart : Term.CheckCertificate start SetSort.set) :
    Formula.CheckCertificate
      (universal_binder_at_condition
        boundVariable formula body start) :=
  Formula.check_admissible_complete
    (universal_binder_at_condition_admissible
      boundVariable formula body start
      hBoundVariable.admissible hFormula.admissible
      hBody.admissible hStart.admissible)

/-- 变量符号出现条件的合法性由两个对象项证书计算。 -/
@[formula_check]
theorem qo_variable_symbol_occurs_condition_check
    (boundVariable formula : SetTerm)
    (hBoundVariable : Term.CheckCertificate boundVariable SetSort.set)
    (hFormula : Term.CheckCertificate formula SetSort.set) :
    Formula.CheckCertificate
      (variable_symbol_occurs_condition boundVariable formula) :=
  Formula.check_admissible_complete
    (variable_symbol_occurs_condition_admissible
      boundVariable formula hBoundVariable.admissible
      hFormula.admissible)

/-! ## 子串与量词前缀反演 -/
/--
有限 numeral 成员条件可在保留任意 Hilbert 上下文的情况下逐分支消去。
标准序列语义原有的空上下文版本适合构造全局证书；本版本负责 quotation
反演中已经携带若干局部假设的场景。
-/
private theorem qo_stdseq_numeral_member_condition_elim_context
    {Γ : Context signature} (number : Nat) (point : SetTerm)
    (conclusion : SetFormula) (hCondition :
      Γ ⊢ₘ[quotation_occurrence_theory]
        stdseq_numeral_member_condition number point) (hBranch :
      ∀ index, index < number → (point ≐ₘ numₘ(index)) :: Γ
          ⊢ₘ[quotation_occurrence_theory] conclusion)
    (hConclusionCheck : Formula.CheckCertificate conclusion := by
      prove_nd_formula_check) :
    Γ ⊢ₘ[quotation_occurrence_theory] conclusion := by
  induction number generalizing Γ with
  | zero =>
      exact FirstOrder.Derives.falsumElim <| by
        simpa [stdseq_numeral_member_condition] using hCondition
  | succ number ih =>
      let equality : SetFormula := point ≐ₘ numₘ(number)
      let tailCondition : SetFormula :=
        stdseq_numeral_member_condition number point
      have hCases :
          Γ ⊢ₘ[quotation_occurrence_theory]
            equality ∨ₘ tailCondition := by
        simpa [equality, tailCondition,
          stdseq_numeral_member_condition] using hCondition
      apply FirstOrder.Derives.disjElim hCases
      · exact hBranch number (Nat.lt_succ_self number)
      · let Δ : Context signature := tailCondition :: Γ
        apply ih (Γ := Δ) (hCondition := by
            simpa [Δ, tailCondition] using
              (FirstOrder.Derives.assumption
                (T := quotation_occurrence_theory)
                (Γ := Δ) (φ := tailCondition) (by simp [Δ])))
        intro index hIndex
        exact FirstOrder.Derives.context_weaken (Γ := (point ≐ₘ numₘ(index)) :: Γ) (Δ := (point ≐ₘ numₘ(index)) :: Δ) (by
            intro formula hFormula
            simp only [Δ, List.mem_cons] at hFormula ⊢
            rcases hFormula with hFormula | hFormula
            · exact Or.inl hFormula
            · exact Or.inr (Or.inr hFormula)) (hBranch index (Nat.lt_trans hIndex (Nat.lt_succ_self number)))
/--
子串规格把片段中的一个已知点运输到整串中的平移位置。
`320` 是 `code_substring_at_condition` 内部的保留下标；显式新鲜性条件只负责防止
定义实例化捕获，不进入对象结论。
-/
theorem qo_code_substring_point_inversion
    {Γ : Context signature} (whole segment start index value : SetTerm)
    (hFresh :
      ReservedIdsFresh [320] [whole, segment, start]) (hSubstring :
      Γ ⊢ₘ[quotation_occurrence_theory]
        code_substring_at_condition whole segment start) (hSegmentPoint :
      Γ ⊢ₘ[quotation_occurrence_theory]
        ((index ∈ₘ domₘ(segment)) ∧ₘ
          ((segment ·ₘ index) ≐ₘ value)))
    (hIndexCheck : Term.CheckCertificate index SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[quotation_occurrence_theory] ((((index +ₘ start) ∈ₘ domₘ(whole)) ∧ₘ ((whole ·ₘ (index +ₘ start)) ≐ₘ value))) := by
  have hPointwise :
      Γ ⊢ₘ[quotation_occurrence_theory]
        ∀ₘ[SetSort.set, 320],
          ((x#320 ∈ₘ domₘ(segment)) ⟶ₘ
            (((x#320 +ₘ start) ∈ₘ domₘ(whole)) ∧ₘ
              ((whole ·ₘ (x#320 +ₘ start)) ≐ₘ
                (segment ·ₘ x#320)))) := by
    simpa [code_substring_at_condition] using
      FirstOrder.Derives.conjElimRight hSubstring
  have hWholeFresh : (SetSort.set, 320) ∉ Term.freeSupport whole :=
    hFresh whole (by simp) 320 (by simp)
  have hSegmentFresh : (SetSort.set, 320) ∉ Term.freeSupport segment :=
    hFresh segment (by simp) 320 (by simp)
  have hStartFresh : (SetSort.set, 320) ∉ Term.freeSupport start :=
    hFresh start (by simp) 320 (by simp)
  have hWholeFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 320 replacement whole =
        whole :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 320 replacement whole hWholeFresh
  have hSegmentFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 320 replacement segment =
        segment :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 320 replacement segment hSegmentFresh
  have hStartFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 320 replacement start =
        start :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 320 replacement start hStartFresh
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := index) hPointwise
  have hAt :
      Γ ⊢ₘ[quotation_occurrence_theory] (index ∈ₘ domₘ(segment)) ⟶ₘ ((((index +ₘ start) ∈ₘ domₘ(whole)) ∧ₘ ((whole ·ₘ (index +ₘ start)) ≐ₘ
              (segment ·ₘ index)))) := by
    simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.substituteFree, Term.substituteFree,
      set_variable, hWholeFixed, hSegmentFixed,
      hStartFixed] using hAtRaw
  have hWholePoint :=
    FirstOrder.Derives.impElim hAt (FirstOrder.Derives.conjElimLeft hSegmentPoint)
  have hWholeValue :
      Γ ⊢ₘ[quotation_occurrence_theory] (whole ·ₘ (index +ₘ start)) ≐ₘ value :=
    Metatheory.Derives.equality_trans
      (FirstOrder.Derives.conjElimRight hWholePoint)
      (FirstOrder.Derives.conjElimRight hSegmentPoint)
  exact FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjElimLeft hWholePoint)
    hWholeValue
/--
`universal_binder_at_condition` 的固定 token 前缀反演。
对象条件一旦成立，量词 token 位于 `1 + start`，声明变量的首 token 位于
`2 + start`；两者都同时返回整串定义域成员证书。
-/
theorem qo_universal_binder_at_prefix_inversion
    {Γ : Context signature} (boundVariable formula body start : SetTerm)
    (hFresh :
      ReservedIdsFresh [200, 320]
        [boundVariable, formula, body, start]) (hBinder :
      Γ ⊢ₘ[quotation_occurrence_theory]
        universal_binder_at_condition
          boundVariable formula body start)
    (hBoundVariableCheck :
      Term.CheckCertificate boundVariable SetSort.set := by
        prove_term_check)
    (hBodyCheck : Term.CheckCertificate body SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[quotation_occurrence_theory] (((((numₘ(1) +ₘ start) ∈ₘ domₘ(formula)) ∧ₘ ((formula ·ₘ (numₘ(1) +ₘ start)) ≐ₘ
            numₘ(logical_token .universal))) ∧ₘ (((numₘ(2) +ₘ start) ∈ₘ domₘ(formula)) ∧ₘ ((formula ·ₘ (numₘ(2) +ₘ start)) ≐ₘ
            (boundVariable ·ₘ numₘ(0)))))) := by
  let segment := forall_codeₘ(boundVariable, body)
  have hSegmentCheck :
      Term.CheckCertificate segment SetSort.set := by
    simpa [segment] using
      (Term.check_admissible_complete <|
        universal_formula_code_term_admissible
          boundVariable body hBoundVariableCheck.admissible
          hBodyCheck.admissible)
  have hSyntax :
      Γ ⊢ₘ[quotation_occurrence_theory] (boundVariable ∈ₘ VarSymₘ) ∧ₘ (formula_codeₘ(body) ∧ₘ (body ∈ₘ CodeStrₘ)) := by
    simpa [universal_binder_at_condition] using
      FirstOrder.Derives.conjElimLeft hBinder
  have hSubstring :
      Γ ⊢ₘ[quotation_occurrence_theory]
        code_substring_at_condition
          formula segment start := by
    simpa [universal_binder_at_condition, segment] using
      FirstOrder.Derives.conjElimRight hBinder
  have hPrefixPrecondition :
      Γ ⊢ₘ[quotation_occurrence_theory] (boundVariable ∈ₘ VarSymₘ) ∧ₘ (body ∈ₘ CodeStrₘ) :=
    FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjElimLeft hSyntax) (FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight hSyntax)
  have hBoundVariableFresh : (SetSort.set, 200) ∉
        Term.freeSupport boundVariable :=
    hFresh boundVariable (by simp) 200 (by simp)
  have hPrefix :
      Γ ⊢ₘ[quotation_occurrence_theory]
        (((numₘ(1) ∈ₘ domₘ(segment)) ∧ₘ
            ((segment ·ₘ numₘ(1)) ≐ₘ
              numₘ(logical_token .universal))) ∧ₘ
          ((numₘ(2) ∈ₘ domₘ(segment)) ∧ₘ
            ((segment ·ₘ numₘ(2)) ≐ₘ
              (boundVariable ·ₘ numₘ(0))))) := by
    have hImp :=
      qo_weaken_godel_quotation <|
        gq_universal_formula_prefix_inversion
          boundVariable body
          (hBoundVariable := hBoundVariableCheck)
          (hBody := hBodyCheck)
    simpa [segment] using
      FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) hImp)
        hPrefixPrecondition
  have hSegmentFresh : (SetSort.set, 320) ∉
        Term.freeSupport segment := by
    simp [segment, Term.freeSupport,
      Term.freeSupportList]
    intro hMember
    rcases List.mem_append.mp hMember with hMember | hMember
    · exact hFresh boundVariable (by simp) 320 (by simp) hMember
    · exact hFresh body (by simp) 320 (by simp) hMember
  have hSubstringFresh :
      ReservedIdsFresh [320]
        [formula, segment, start] := by
    intro candidate hCandidate reserved hReserved
    have hReservedEq : reserved = 320 := by
      simpa using hReserved
    subst reserved
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hCandidate
    rcases hCandidate with hCandidate | hCandidate | hCandidate
    · rw [hCandidate]
      exact hFresh formula (by simp) 320 (by simp)
    · rw [hCandidate]
      exact hSegmentFresh
    · rw [hCandidate]
      exact hFresh start (by simp) 320 (by simp)
  have hWholeOne :=
    qo_code_substring_point_inversion
      formula segment start (numₘ(1)) (numₘ(logical_token .universal))
      hSubstringFresh hSubstring (FirstOrder.Derives.conjElimLeft hPrefix)
  have hWholeTwo :=
    qo_code_substring_point_inversion
      formula segment start (numₘ(2)) (boundVariable ·ₘ numₘ(0))
      hSubstringFresh hSubstring (FirstOrder.Derives.conjElimRight hPrefix)
  exact FirstOrder.Derives.conjIntro
    hWholeOne hWholeTwo
/--
若标准序列中的对象位置已经识别为具体 numeral 下标，则该点求值为对应外部元素。
-/
private theorem standard_token_sequence_value_of_index_equality
    (tokens : List Nat) (index : Nat) (point : SetTerm)
    (hIndex : index < tokens.length)
    (hPointCheck : Term.CheckCertificate point SetSort.set := by
      prove_term_check) :
    ⊢ₘ[quotation_occurrence_theory] (point ≐ₘ numₘ(index)) ⟶ₘ ((standard_token_sequence tokens ·ₘ point) ≐ₘ
          numₘ(tokens[index])) := by
  let sequence := standard_token_sequence tokens
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  have hSequenceCheck :
      Term.CheckCertificate sequence SetSort.set := by
    prove_term_check
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[quotation_occurrence_theory]
        point ≐ₘ numₘ(index) := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := quotation_occurrence_theory)
        (Γ := Γ) (φ := equality) (by simp [Γ]))
  have hApplication :
      Γ ⊢ₘ[quotation_occurrence_theory] (sequence ·ₘ point) ≐ₘ (sequence ·ₘ numₘ(index)) :=
    function_application_term_congr_argument_of_equality
      sequence point (numₘ(index))
      hSequenceCheck.admissible hPointCheck.admissible
      (finite_numeral_term_check index).admissible
      hEquality
  have hConcrete :
      Γ ⊢ₘ[quotation_occurrence_theory] (sequence ·ₘ numₘ(index)) ≐ₘ
          numₘ(tokens[index]) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
        simpa [sequence] using
          qo_weaken_standard_sequence <|
            standard_token_sequence_apply_getElem?
              tokens (List.getElem?_eq_some_iff.mpr
                ⟨hIndex, rfl⟩)
  have hResult :=
    Metatheory.Derives.equality_trans
      hApplication hConcrete
  simpa [sequence, equality, Γ] using hResult
/--
若某外部 token 不在标准串中，则任意具体标准下标分支都不能把该位置读成该 token。
-/
private theorem standard_token_sequence_avoidance_branch
    (tokens : List Nat) (token index : Nat) (point : SetTerm)
    (hIndex : index < tokens.length) (hToken : token ∉ tokens)
    (hPointCheck : Term.CheckCertificate point SetSort.set := by
      prove_term_check) :
    ⊢ₘ[quotation_occurrence_theory] (point ≐ₘ numₘ(index)) ⟶ₘ
        ¬ₘ ((standard_token_sequence tokens ·ₘ point) ≐ₘ
          numₘ(token)) := by
  let current := tokens[index]
  have hCurrentGet :
      tokens[index]? = some current :=
    List.getElem?_eq_some_iff.mpr ⟨hIndex, rfl⟩
  have hCurrentMem : current ∈ tokens :=
    List.getElem_mem hIndex
  have hCurrentNe : current ≠ token := by
    intro hEqual
    apply hToken
    rw [← hEqual]
    exact hCurrentMem
  let sequence := standard_token_sequence tokens
  let indexEquality : SetFormula := point ≐ₘ numₘ(index)
  let valueEquality : SetFormula := (sequence ·ₘ point) ≐ₘ numₘ(token)
  let Γ : Context signature := [valueEquality, indexEquality]
  have hSequenceCheck :
      Term.CheckCertificate sequence SetSort.set := by
    prove_term_check
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.negIntro
  have hIndexEquality :
      Γ ⊢ₘ[quotation_occurrence_theory] indexEquality :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hValueEquality :
      Γ ⊢ₘ[quotation_occurrence_theory] valueEquality :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hApplicationCongruence :
      Γ ⊢ₘ[quotation_occurrence_theory] (sequence ·ₘ point) ≐ₘ (sequence ·ₘ numₘ(index)) :=
    function_application_term_congr_argument_of_equality
      sequence point (numₘ(index))
      hSequenceCheck.admissible hPointCheck.admissible
      (finite_numeral_term_check index).admissible
      (by simpa [indexEquality] using hIndexEquality)
  have hIndexValue :
      Γ ⊢ₘ[quotation_occurrence_theory] (sequence ·ₘ numₘ(index)) ≐ₘ
          numₘ(current) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
        simpa [sequence, current] using
          qo_weaken_standard_sequence (standard_token_sequence_apply_getElem?
              tokens hCurrentGet)
  have hPointValue :
      Γ ⊢ₘ[quotation_occurrence_theory] (sequence ·ₘ point) ≐ₘ numₘ(current) :=
    Metatheory.Derives.equality_trans
      hApplicationCongruence hIndexValue
  have hCurrentPoint :
      Γ ⊢ₘ[quotation_occurrence_theory]
        numₘ(current) ≐ₘ (sequence ·ₘ point) :=
    Metatheory.Derives.equality_symm hPointValue
  have hNumeralEquality :
      Γ ⊢ₘ[quotation_occurrence_theory]
        numₘ(current) ≐ₘ numₘ(token) :=
    Metatheory.Derives.equality_trans
      hCurrentPoint (by simpa [valueEquality] using hValueEquality)
  exact FirstOrder.Derives.negElim hNumeralEquality <|
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <|
        qo_weaken_standard_sequence (standard_sequence_finite_numeral_ne hCurrentNe)
/--
标准 token 序列在整个对象定义域上避开一个未出现的外部 token。
-/
theorem standard_token_sequence_avoids_token (tokens : List Nat) (token : Nat) (hToken : token ∉ tokens) :
    ⊢ₘ[quotation_occurrence_theory]
      ∀ₘ[SetSort.set, 460], ((x#460 ∈ₘ
            domₘ(standard_token_sequence tokens)) ⟶ₘ
          ¬ₘ (((standard_token_sequence tokens) ·ₘ x#460) ≐ₘ
            numₘ(token))) := by
  let sequence := standard_token_sequence tokens
  let point : SetTerm := x#460
  let conclusion : SetFormula :=
    ¬ₘ ((sequence ·ₘ point) ≐ₘ numₘ(token))
  have hPointCheck :
      Term.CheckCertificate point SetSort.set := by
    prove_term_check
  have hSequenceCheck :
      Term.CheckCertificate sequence SetSort.set := by
    prove_term_check
  have hCases :
      ⊢ₘ[quotation_occurrence_theory]
        stdseq_numeral_member_condition
            tokens.length point ⟶ₘ conclusion :=
    stdseq_numeral_member_condition_elim_of_theory
      tokens.length point conclusion
      (fun index hIndex => by
        simpa [point, conclusion, sequence] using
          standard_token_sequence_avoidance_branch
            tokens token index point hIndex hToken)
  have hNumeralIff :
      ⊢ₘ[quotation_occurrence_theory] (point ∈ₘ numₘ(tokens.length)) ↔ₘ
          stdseq_numeral_member_condition
            tokens.length point :=
    qo_weaken_standard_sequence (stdseq_numeral_member_iff
        tokens.length point hPointCheck.admissible)
  have hDomain :
      ⊢ₘ[quotation_occurrence_theory]
        domₘ(sequence) ≐ₘ numₘ(tokens.length) := by
    simpa [sequence] using
      qo_weaken_standard_sequence (standard_token_sequence_domain_eq_length tokens)
  have hDomainIff :
      ⊢ₘ[quotation_occurrence_theory] (point ∈ₘ domₘ(sequence)) ↔ₘ (point ∈ₘ numₘ(tokens.length)) :=
    membership_right_iff_of_equality
      point (domₘ(sequence)) (numₘ(tokens.length))
      hPointCheck.admissible
      (domain_term_check hSequenceCheck).admissible
      (finite_numeral_term_check tokens.length).admissible
      hDomain
  have hOpen :
      ⊢ₘ[quotation_occurrence_theory] (point ∈ₘ domₘ(sequence)) ⟶ₘ conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    have hMembership :
        [point ∈ₘ domₘ(sequence)]
          ⊢ₘ[quotation_occurrence_theory]
            point ∈ₘ domₘ(sequence) :=
      FirstOrder.Derives.assumption (by simp)
    have hNumeralMembership :
        [point ∈ₘ domₘ(sequence)]
          ⊢ₘ[quotation_occurrence_theory]
            point ∈ₘ numₘ(tokens.length) :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hDomainIff)
        hMembership
    have hCondition :
        [point ∈ₘ domₘ(sequence)]
          ⊢ₘ[quotation_occurrence_theory]
            stdseq_numeral_member_condition
              tokens.length point :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hNumeralIff)
        hNumeralMembership
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hCases)
      hCondition
  have hTheoryFresh :
      ∀ formula, quotation_occurrence_theory formula → (SetSort.set, 460) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    rw [(quotation_occurrence_theory_sentence hFormula).2]
    exact List.not_mem_nil
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := quotation_occurrence_theory) (Γ := []) (sort := SetSort.set) (eigen := 460)
      hTheoryFresh (by simp) hOpen
  simpa [sequence, point, conclusion] using hGeneralized
/--
规范公式串中的全称量词 binder token 不会同时作为规范项串中的变量 token 出现。
证明只使用三类已经内部化的事实：
* quotation 的量词直接后继在元层避开项 token；
* 标准序列的有限定义域与逐点求值；
* `1 + start`、`2 + start` 的对象加法固定实例。
-/
theorem standard_token_sequences_universal_binder_separation (formulaTokens replacementTokens : List Nat) (hFollower :
      gq_universal_follower_condition (fun token => token ∉ replacementTokens)
        formulaTokens) (boundVariable body start : SetTerm) (hFresh :
      ReservedIdsFresh [200, 312, 320]
        [boundVariable, body, start])
    (hBoundVariableCheck :
      Term.CheckCertificate boundVariable SetSort.set := by
        prove_term_check)
    (hBodyCheck : Term.CheckCertificate body SetSort.set := by
      prove_term_check)
    (hStartCheck : Term.CheckCertificate start SetSort.set := by
      prove_term_check) :
    ⊢ₘ[quotation_occurrence_theory]
      universal_binder_at_condition
          boundVariable (standard_token_sequence formulaTokens)
          body start ⟶ₘ
        ¬ₘ variable_symbol_occurs_condition
          boundVariable (standard_token_sequence replacementTokens) := by
  let formulaCode := standard_token_sequence formulaTokens
  let replacementCode :=
    standard_token_sequence replacementTokens
  let binder : SetFormula :=
    universal_binder_at_condition
      boundVariable formulaCode body start
  let occurrence : SetFormula :=
    variable_symbol_occurs_condition
      boundVariable replacementCode
  let Γ : Context signature := [occurrence, binder]
  have hFormulaCodeCheck :
      Term.CheckCertificate formulaCode SetSort.set := by
    prove_term_check
  have hReplacementCodeCheck :
      Term.CheckCertificate replacementCode SetSort.set := by
    prove_term_check
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.negIntro
  have hBinder :
      Γ ⊢ₘ[quotation_occurrence_theory] binder :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hOccurrence :
      Γ ⊢ₘ[quotation_occurrence_theory] occurrence :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hPrefixFresh :
      ReservedIdsFresh [200, 320]
        [boundVariable, formulaCode, body, start] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hTerm
    have hId' : id ∈ [200, 312, 320] := by
      simp only [List.mem_cons, List.not_mem_nil,
        or_false] at hId ⊢
      rcases hId with hId | hId
      · exact Or.inl hId
      · exact Or.inr (Or.inr hId)
    rcases hTerm with hTerm | hTerm | hTerm | hTerm
    · simpa [hTerm] using
        hFresh boundVariable (by simp) id hId'
    · simpa [hTerm, formulaCode] using (show (SetSort.set, id) ∉
            Term.freeSupport (standard_token_sequence formulaTokens) by
          rw [standard_token_sequence_freeSupport_nil]
          exact List.not_mem_nil)
    · simpa [hTerm] using
        hFresh body (by simp) id hId'
    · simpa [hTerm] using
        hFresh start (by simp) id hId'
  have hPrefix :=
    qo_universal_binder_at_prefix_inversion
      boundVariable formulaCode body start
      hPrefixFresh <| by
        simpa [binder] using hBinder
  let firstPoint : SetTerm := numₘ(1) +ₘ start
  let secondPoint : SetTerm := numₘ(2) +ₘ start
  have hFirstPointCheck :
      Term.CheckCertificate firstPoint SetSort.set := by
    prove_term_check
  have hFirstMember :
      Γ ⊢ₘ[quotation_occurrence_theory]
        firstPoint ∈ₘ domₘ(formulaCode) := by
    simpa [firstPoint, formulaCode] using (FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimLeft hPrefix)
  have hFirstUniversal :
      Γ ⊢ₘ[quotation_occurrence_theory] (formulaCode ·ₘ firstPoint) ≐ₘ
          numₘ(logical_token .universal) := by
    simpa [firstPoint, formulaCode] using (FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimLeft hPrefix)
  have hSecondMember :
      Γ ⊢ₘ[quotation_occurrence_theory]
        secondPoint ∈ₘ domₘ(formulaCode) := by
    simpa [secondPoint, formulaCode] using (FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight hPrefix)
  have hSecondBinder :
      Γ ⊢ₘ[quotation_occurrence_theory] (formulaCode ·ₘ secondPoint) ≐ₘ (boundVariable ·ₘ numₘ(0)) := by
    simpa [secondPoint, formulaCode] using (FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight hPrefix)
  have hSubstring :
      Γ ⊢ₘ[quotation_occurrence_theory]
        code_substring_at_condition
          formulaCode (forall_codeₘ(boundVariable, body))
          start := by
    simpa [binder, universal_binder_at_condition] using
      FirstOrder.Derives.conjElimRight hBinder
  have hStartOmega :
      Γ ⊢ₘ[quotation_occurrence_theory]
        start ∈ₘ ωₘ := by
    simpa [code_substring_at_condition] using
      FirstOrder.Derives.conjElimLeft hSubstring
  have hSuccessor :
      Γ ⊢ₘ[quotation_occurrence_theory]
        secondPoint ≐ₘ Sₘ(firstPoint) := by
    have hImp :=
      qo_weaken_standard_sequence <|
        standard_sequence_two_addition_eq_successor_one
          start hStartCheck.admissible
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
          simpa [firstPoint, secondPoint] using hImp)
      hStartOmega
  have domain_condition_of_member (point : SetTerm) (hMember :
        Γ ⊢ₘ[quotation_occurrence_theory]
          point ∈ₘ domₘ(formulaCode))
      (hPointCheck : Term.CheckCertificate point SetSort.set := by
        prove_term_check) :
      Γ ⊢ₘ[quotation_occurrence_theory]
        stdseq_numeral_member_condition
          formulaTokens.length point := by
    have hDomainEquality :
        Γ ⊢ₘ[quotation_occurrence_theory]
          domₘ(formulaCode) ≐ₘ
            numₘ(formulaTokens.length) :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
          simpa [formulaCode] using
            qo_weaken_standard_sequence <|
              standard_token_sequence_domain_eq_length
                formulaTokens
    have hDomainIff :
        Γ ⊢ₘ[quotation_occurrence_theory] (point ∈ₘ domₘ(formulaCode)) ↔ₘ (point ∈ₘ numₘ(formulaTokens.length)) :=
      membership_right_iff_of_equality
        point (domₘ(formulaCode)) (numₘ(formulaTokens.length))
        hPointCheck.admissible
        (domain_term_check hFormulaCodeCheck).admissible
        (finite_numeral_term_check
          formulaTokens.length).admissible
        hDomainEquality
    have hNumeralIff :
        Γ ⊢ₘ[quotation_occurrence_theory] (point ∈ₘ numₘ(formulaTokens.length)) ↔ₘ
            stdseq_numeral_member_condition
              formulaTokens.length point :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          qo_weaken_standard_sequence <|
            stdseq_numeral_member_iff
              formulaTokens.length point hPointCheck.admissible
    exact FirstOrder.Derives.iffElimRight hNumeralIff <|
      FirstOrder.Derives.iffElimRight hDomainIff hMember
  have hFirstCondition :=
    domain_condition_of_member
      firstPoint hFirstMember
  have hSecondCondition :=
    domain_condition_of_member
      secondPoint hSecondMember
  apply qo_stdseq_numeral_member_condition_elim_context
      formulaTokens.length firstPoint Formula.falsum
      hFirstCondition
  intro firstIndex hFirstIndex
  let firstEquality : SetFormula :=
    firstPoint ≐ₘ numₘ(firstIndex)
  let Γ₁ : Context signature := firstEquality :: Γ
  have hFirstEquality :
      Γ₁ ⊢ₘ[quotation_occurrence_theory]
        firstPoint ≐ₘ numₘ(firstIndex) := by
    simpa [Γ₁, firstEquality] using
      (FirstOrder.Derives.assumption
        (T := quotation_occurrence_theory)
        (Γ := Γ₁) (φ := firstEquality) (by simp [Γ₁]))
  have hFirstValue :
      Γ₁ ⊢ₘ[quotation_occurrence_theory] (formulaCode ·ₘ firstPoint) ≐ₘ
          numₘ(formulaTokens[firstIndex]) := by
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ₁) (by simp [Γ₁, Γ]) <| by
          simpa [formulaCode] using
            standard_token_sequence_value_of_index_equality
              formulaTokens firstIndex firstPoint
              hFirstIndex)
      hFirstEquality
  have hFirstUniversal₁ :
      Γ₁ ⊢ₘ[quotation_occurrence_theory] (formulaCode ·ₘ firstPoint) ≐ₘ
          numₘ(logical_token .universal) :=
    FirstOrder.Derives.context_weaken (Γ := Γ) (Δ := Γ₁) (by
        intro formula hFormula
        simpa [Γ₁] using
          List.mem_cons_of_mem firstEquality hFormula)
      hFirstUniversal
  have hCurrentUniversalNumeral :
      Γ₁ ⊢ₘ[quotation_occurrence_theory]
        numₘ(formulaTokens[firstIndex]) ≐ₘ
          numₘ(logical_token .universal) := by
    have hBack :=
      Metatheory.Derives.equality_symm hFirstValue
    exact Metatheory.Derives.equality_trans hBack hFirstUniversal₁
  by_cases hCurrentUniversal :
      formulaTokens[firstIndex] =
        logical_token .universal
  · have hSecondCondition₁ :
        Γ₁ ⊢ₘ[quotation_occurrence_theory]
          stdseq_numeral_member_condition
            formulaTokens.length secondPoint :=
      FirstOrder.Derives.context_weaken (Γ := Γ) (Δ := Γ₁) (by
          intro formula hFormula
          simpa [Γ₁] using
            List.mem_cons_of_mem firstEquality hFormula)
        hSecondCondition
    apply qo_stdseq_numeral_member_condition_elim_context
        formulaTokens.length secondPoint Formula.falsum
        hSecondCondition₁
    intro secondIndex hSecondIndex
    let secondEquality : SetFormula :=
      secondPoint ≐ₘ numₘ(secondIndex)
    let Γ₂ : Context signature := secondEquality :: Γ₁
    have hSecondEquality :
        Γ₂ ⊢ₘ[quotation_occurrence_theory]
          secondPoint ≐ₘ numₘ(secondIndex) := by
      simpa [Γ₂, secondEquality] using
        (FirstOrder.Derives.assumption
          (T := quotation_occurrence_theory)
          (Γ := Γ₂) (φ := secondEquality) (by simp [Γ₂]))
    have hFirstEquality₂ :
        Γ₂ ⊢ₘ[quotation_occurrence_theory]
          firstPoint ≐ₘ numₘ(firstIndex) :=
      FirstOrder.Derives.context_weaken (Γ := Γ₁) (Δ := Γ₂) (by
          intro formula hFormula
          simpa [Γ₂] using
            List.mem_cons_of_mem secondEquality hFormula)
        hFirstEquality
    have hSuccessor₂ :
        Γ₂ ⊢ₘ[quotation_occurrence_theory]
          secondPoint ≐ₘ Sₘ(firstPoint) :=
      FirstOrder.Derives.context_weaken (Γ := Γ) (Δ := Γ₂) (by
          intro formula hFormula
          simp only [Γ₂, Γ₁, List.mem_cons]
          exact Or.inr (Or.inr hFormula))
        hSuccessor
    have hSuccessorFirst :
        Γ₂ ⊢ₘ[quotation_occurrence_theory]
          Sₘ(firstPoint) ≐ₘ Sₘ(numₘ(firstIndex)) :=
      successor_term_congr_of_equality
        firstPoint (numₘ(firstIndex))
        hFirstPointCheck.admissible
        (finite_numeral_term_check firstIndex).admissible
        hFirstEquality₂
    have hSecondSuccessor :
        Γ₂ ⊢ₘ[quotation_occurrence_theory]
          secondPoint ≐ₘ numₘ(firstIndex + 1) := by
      have hStep :=
        Metatheory.Derives.equality_trans
          hSuccessor₂ hSuccessorFirst
      simpa [finite_numeral_term] using hStep
    have hSecondIndexNumeral :
        Γ₂ ⊢ₘ[quotation_occurrence_theory]
          numₘ(secondIndex) ≐ₘ
            numₘ(firstIndex + 1) := by
      have hBack :=
        Metatheory.Derives.equality_symm hSecondEquality
      exact Metatheory.Derives.equality_trans hBack hSecondSuccessor
    by_cases hAdjacent :
        secondIndex = firstIndex + 1
    · subst secondIndex
      let nextToken := formulaTokens[firstIndex + 1]
      have hCurrentGet :
          formulaTokens[firstIndex]? =
            some formulaTokens[firstIndex] :=
        List.getElem?_eq_some_iff.mpr
          ⟨hFirstIndex, rfl⟩
      have hNextGet :
          formulaTokens[firstIndex + 1]? =
            some nextToken :=
        List.getElem?_eq_some_iff.mpr
          ⟨hSecondIndex, rfl⟩
      have hNextAvoids :
          nextToken ∉ replacementTokens :=
        gq_universal_follower_condition_getElem? (fun token => token ∉ replacementTokens)
          formulaTokens firstIndex
          formulaTokens[firstIndex] nextToken
          hFollower hCurrentGet hNextGet
          hCurrentUniversal
      have hSecondValue :
          Γ₂ ⊢ₘ[quotation_occurrence_theory] (formulaCode ·ₘ secondPoint) ≐ₘ
              numₘ(nextToken) := by
        exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ₂) (by simp [Γ₂, Γ₁, Γ]) <| by
              simpa [formulaCode, nextToken] using
                standard_token_sequence_value_of_index_equality
                  formulaTokens (firstIndex + 1)
                  secondPoint hSecondIndex)
          hSecondEquality
      have hSecondBinder₂ :
          Γ₂ ⊢ₘ[quotation_occurrence_theory] (formulaCode ·ₘ secondPoint) ≐ₘ (boundVariable ·ₘ numₘ(0)) :=
        FirstOrder.Derives.context_weaken (Γ := Γ) (Δ := Γ₂) (by
            intro formula hFormula
            simp only [Γ₂, Γ₁, List.mem_cons]
            exact Or.inr (Or.inr hFormula))
          hSecondBinder
      have hBoundTokenNext :
          Γ₂ ⊢ₘ[quotation_occurrence_theory] (boundVariable ·ₘ numₘ(0)) ≐ₘ
              numₘ(nextToken) := by
        have hBack :=
          Metatheory.Derives.equality_symm hSecondBinder₂
        exact Metatheory.Derives.equality_trans hBack hSecondValue
      have hOccurrence₂ :
          Γ₂ ⊢ₘ[quotation_occurrence_theory]
            occurrence :=
        FirstOrder.Derives.context_weaken (Γ := Γ) (Δ := Γ₂) (by
            intro formula hFormula
            simp only [Γ₂, Γ₁, List.mem_cons]
            exact Or.inr (Or.inr hFormula))
          hOccurrence
      have hPositionExists :
          Γ₂ ⊢ₘ[quotation_occurrence_theory]
            ∃ₘ[SetSort.set, 312], (((x#312) ∈ₘ domₘ(replacementCode)) ∧ₘ ((replacementCode ·ₘ (x#312)) ≐ₘ (boundVariable ·ₘ numₘ(0)))) := by
        simpa [occurrence,
          variable_symbol_occurs_condition] using (FirstOrder.Derives.conjElimRight hOccurrence₂)
      let position : SetTerm := x#312
      let positionCondition : SetFormula :=
        (position ∈ₘ domₘ(replacementCode)) ∧ₘ
          ((replacementCode ·ₘ position) ≐ₘ
            (boundVariable ·ₘ numₘ(0)))
      have hPositionExists' :
          Γ₂ ⊢ₘ[quotation_occurrence_theory]
            ∃ₘ[SetSort.set, 312], positionCondition := by
        simpa [positionCondition, position] using
          hPositionExists
      have hBoundFresh : (SetSort.set, 312) ∉
            Term.freeSupport boundVariable :=
        hFresh boundVariable (by simp) 312 (by simp)
      have hBodyFresh : (SetSort.set, 312) ∉
            Term.freeSupport body :=
        hFresh body (by simp) 312 (by simp)
      have hStartFresh : (SetSort.set, 312) ∉
            Term.freeSupport start :=
        hFresh start (by simp) 312 (by simp)
      nd_apply FirstOrder.Derives.exists_elim
          (T := quotation_occurrence_theory) (Γ := Γ₂)
          (sort := SetSort.set) (eigen := 312)
          (body := positionCondition)
          (conclusion := Formula.falsum)
      · intro formula hFormula
        rw [(quotation_occurrence_theory_sentence hFormula).2]
        exact List.not_mem_nil
      · intro formula hFormula
        simp only [Γ₂, Γ₁, Γ, List.mem_cons,
          List.not_mem_nil, or_false] at hFormula
        rcases hFormula with
          rfl | rfl | rfl | rfl
        · simpa [secondEquality, secondPoint,
            Formula.freeSupport, Term.freeSupport,
            Term.freeSupportList,
            finite_numeral_term_freeSupport] using
              hStartFresh
        · simpa [firstEquality, firstPoint,
            Formula.freeSupport, Term.freeSupport,
            Term.freeSupportList,
            finite_numeral_term_freeSupport] using
              hStartFresh
        · simpa [occurrence,
            variable_symbol_occurs_condition,
            Formula.freeSupport, Term.freeSupport,
            Term.freeSupportList,
            Formula.not_mem_freeSupport_closeFreeAt] using
              hBoundFresh
        · have hClosedFresh : (SetSort.set, 312) ∉
                Formula.freeSupport
                  (Formula.closeFreeAt SetSort.set 320 0
                    ((x#320 ∈ₘ
                        domₘ(forall_codeₘ(boundVariable, body))) ⟶ₘ
                      (((x#320 +ₘ start) ∈ₘ domₘ(formulaCode)) ∧ₘ
                        ((formulaCode ·ₘ (x#320 +ₘ start)) ≐ₘ
                          (forall_codeₘ(boundVariable, body) ·ₘ
                            x#320))))) := by
            refine
              Formula.not_mem_freeSupport_closeFreeAt_of_not_mem (σ := signature) (SetSort.set, 312) SetSort.set 320 0 _ ?_
            simpa [Formula.freeSupport, Term.freeSupport,
              Term.freeSupportList, formulaCode,
              standard_token_sequence_freeSupport_nil] using (And.intro hBoundFresh (And.intro hBodyFresh (And.intro hStartFresh
                      (And.intro hBoundFresh hBodyFresh))))
          have hAllFresh : (SetSort.set, 312) ∉
                  Term.freeSupport boundVariable ∧ (SetSort.set, 312) ∉
                    Term.freeSupport body ∧ (SetSort.set, 312) ∉
                      Term.freeSupport start ∧ (SetSort.set, 312) ∉
                      Formula.freeSupport (Formula.closeFreeAt SetSort.set 320 0 (((x#320) ∈ₘ
                              domₘ(forall_codeₘ(
                                boundVariable, body))) ⟶ₘ ((((x#320 +ₘ start) ∈ₘ
                                  domₘ(formulaCode)) ∧ₘ ((formulaCode ·ₘ (x#320 +ₘ start)) ≐ₘ (forall_codeₘ(
                                    boundVariable, body) ·ₘ
                                  x#320)))))) :=
            ⟨hBoundFresh, hBodyFresh, hStartFresh,
              hClosedFresh⟩
          simpa [binder,
            universal_binder_at_condition,
            code_substring_at_condition,
            Formula.freeSupport, Term.freeSupport,
            Term.freeSupportList, formulaCode,
            standard_token_sequence_freeSupport_nil] using
              hAllFresh
      · exact List.not_mem_nil
      · exact hPositionExists'
      · let Δ : Context signature :=
          positionCondition :: Γ₂
        have hPositionCondition :
            Δ ⊢ₘ[quotation_occurrence_theory]
              positionCondition :=
          FirstOrder.Derives.assumption (by simp [Δ])
        have hPositionMember :
            Δ ⊢ₘ[quotation_occurrence_theory]
              position ∈ₘ domₘ(replacementCode) :=
          FirstOrder.Derives.conjElimLeft
            hPositionCondition
        have hPositionValue :
            Δ ⊢ₘ[quotation_occurrence_theory] (replacementCode ·ₘ position) ≐ₘ (boundVariable ·ₘ numₘ(0)) :=
          FirstOrder.Derives.conjElimRight
            hPositionCondition
        have hBoundTokenNextΔ :
            Δ ⊢ₘ[quotation_occurrence_theory] (boundVariable ·ₘ numₘ(0)) ≐ₘ
                numₘ(nextToken) :=
          FirstOrder.Derives.context_weaken (Γ := Γ₂) (Δ := Δ) (by
              intro formula hFormula
              simpa [Δ] using
                List.mem_cons_of_mem
                  positionCondition hFormula)
            hBoundTokenNext
        have hReplacementValue :
            Δ ⊢ₘ[quotation_occurrence_theory] (replacementCode ·ₘ position) ≐ₘ
                numₘ(nextToken) :=
          Metatheory.Derives.equality_trans
            hPositionValue hBoundTokenNextΔ
        have hAvoidanceUniversal :=
          standard_token_sequence_avoids_token
            replacementTokens nextToken hNextAvoids
        have hAvoidanceAtRaw :=
          FirstOrder.Derives.forall_elim
            (term := position)
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Δ)
              (by simp [Δ, Γ₂, Γ₁, Γ])
              hAvoidanceUniversal)
        have hAvoidanceAt :
            Δ ⊢ₘ[quotation_occurrence_theory] (position ∈ₘ domₘ(replacementCode)) ⟶ₘ
                ¬ₘ ((replacementCode ·ₘ position) ≐ₘ
                  numₘ(nextToken)) := by
          have hReplacementFixed :
              Term.substituteFree SetSort.set 460
                  position replacementCode =
                replacementCode := by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [replacementCode]
          have hNumeralFixed :
              Term.substituteFree SetSort.set 460
                  position (numₘ(nextToken)) =
                numₘ(nextToken) := by
            apply Term.substituteFree_eq_self_of_not_mem
            rw [finite_numeral_term_freeSupport]
            exact List.not_mem_nil
          have hReplacementFixed' :
              Term.substituteFree SetSort.set 460 (x#312) (standard_token_sequence replacementTokens) =
                standard_token_sequence replacementTokens := by
            simpa [position, replacementCode] using
              hReplacementFixed
          have hNumeralFixed' :
              Term.substituteFree SetSort.set 460 (x#312) (numₘ(nextToken)) =
                numₘ(nextToken) := by
            simpa [position] using hNumeralFixed
          simp only [
            Formula.openAt_closeFreeAt_eq_substituteFree,
            Formula.substituteFree, Term.substituteFree,
            List.map_cons, List.map_nil, set_variable] at hAvoidanceAtRaw
          simpa only [position, replacementCode,
            hReplacementFixed', hNumeralFixed'] using
              hAvoidanceAtRaw
        exact FirstOrder.Derives.negElim
          hReplacementValue (FirstOrder.Derives.impElim
            hAvoidanceAt hPositionMember)
    · exact FirstOrder.Derives.negElim
        hSecondIndexNumeral <|
          FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ₂) (by simp [Γ₂, Γ₁, Γ]) <|
              qo_weaken_standard_sequence <|
                standard_sequence_finite_numeral_ne
                  hAdjacent
  · exact FirstOrder.Derives.negElim
      hCurrentUniversalNumeral <|
        FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ₁) (by simp [Γ₁, Γ]) <|
            qo_weaken_standard_sequence <|
              standard_sequence_finite_numeral_ne
                hCurrentUniversal
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
