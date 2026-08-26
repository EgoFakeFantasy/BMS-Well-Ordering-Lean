import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Occurrence.Object
/-!
# Gödel quotation 的自由出现语义
本模块建立具名变量码、自由出现否定及 quotation 代码等式运输。
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

/-- 自由出现原子的合法性由两个对象项证书计算。 -/
@[formula_check]
theorem qo_free_occurrence_formula_check
    (boundVariable formula : SetTerm)
    (hBoundVariable : Term.CheckCertificate boundVariable SetSort.set)
    (hFormula : Term.CheckCertificate formula SetSort.set) :
    Formula.CheckCertificate
      (free_occursₘ(boundVariable, formula)) :=
  Formula.check_admissible_complete
    (free_occurrence_formula_admissible
      hBoundVariable.admissible hFormula.admissible)

/-- 自由出现位置条件的合法性由三个对象项证书计算。 -/
@[formula_check]
theorem qo_free_occurrence_position_condition_check
    (boundVariable formula position : SetTerm)
    (hBoundVariable : Term.CheckCertificate boundVariable SetSort.set)
    (hFormula : Term.CheckCertificate formula SetSort.set)
    (hPosition : Term.CheckCertificate position SetSort.set) :
    Formula.CheckCertificate
      (free_occurrence_position_condition
        boundVariable formula position) :=
  Formula.check_admissible_complete
    (free_occurrence_position_condition_admissible
      boundVariable formula position
      hBoundVariable.admissible hFormula.admissible
      hPosition.admissible)

/-- occurrence 定义公理由固定公式的纯检查证书注册。 -/
@[formula_check]
theorem qo_occurrence_definition_axiom_check :
    Formula.CheckCertificate occurrence_definition_axiom :=
  Formula.check_admissible_complete
    occurrence_definition_axiom_admissible

/--
量词声明位置见证携带对应 binder，因此必然蕴含该量词在公式码中出现。
证明只消去定义中的两个存在量词。
-/
theorem binder_declaration_position_imp_quantifier_occurs
    (boundVariable formula position : SetTerm)
    (hBoundVariable : Numbered.CodeBoundary boundVariable)
    (hFormula : Numbered.CodeBoundary formula)
    (hPosition : Numbered.CodeBoundary position) :
    ⊢ₘ[quotation_occurrence_theory]
      binder_declaration_position_condition
          boundVariable formula position ⟶ₘ
        quantifier_occurs_condition boundVariable formula := by
  let binder : SetFormula :=
    universal_binder_at_condition
      boundVariable formula (x#323) (x#324)
  let inner : SetFormula :=
    binder ∧ₘ (position ≐ₘ (numₘ(2) +ₘ x#324))
  let body₁ : SetFormula :=
    ∃ₘ[SetSort.set, 324], inner
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
        Term.Admissible (x#323) SetSort.set :=
      set_variable_admissible 323
    have hStart :
        Term.Admissible (x#324) SetSort.set :=
      set_variable_admissible 324
    have hBinder :=
      universal_binder_at_condition_admissible
        boundVariable formula (x#323) (x#324)
        hBoundVariable.1 hFormula.1 hBody hStart
    have hDeclaredPosition :=
      natural_addition_term_admissible
        (numₘ(2)) (x#324)
        (finite_numeral_term_admissible 2) hStart
    simpa [inner, binder] using
      Formula.Admissible.conj hBinder
        (Formula.Admissible.equal hPosition.1 hDeclaredPosition)
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
      FirstOrder.Derives.conjElimLeft hInner
    have hStartExists :
        Γ ⊢ₘ[quotation_occurrence_theory]
          ∃ₘ[SetSort.set, 322],
            universal_binder_at_condition
              boundVariable formula (x#323) (x#322) := by
      nd_apply FirstOrder.Derives.exists_intro
        (term := x#324)
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
        (term := x#323)
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
  have hStartImp :=
    FirstOrder.Derives.exists_imp_of_imp
      (T := quotation_occurrence_theory)
      (Γ := ([] : Context signature))
      (sort := SetSort.set) (eigen := 324)
      (body := inner) (conclusion := conclusion)
      (hTheoryFresh 324) (hEmptyFresh 324)
      (hConclusionFresh 324) hInnerImp
  have hBodyImp :=
    FirstOrder.Derives.exists_imp_of_imp
      (T := quotation_occurrence_theory)
      (Γ := ([] : Context signature))
      (sort := SetSort.set) (eigen := 323)
      (body := body₁) (conclusion := conclusion)
      (hTheoryFresh 323) (hEmptyFresh 323)
      (hConclusionFresh 323)
      (by simpa [body₁] using hStartImp)
  simpa [binder_declaration_position_condition,
    binder, inner, body₁, conclusion] using hBodyImp

/--
受约束出现的两种来源都会给出同名量词出现。
-/
theorem bound_occurrence_position_imp_quantifier_occurs
    (boundVariable formula position : SetTerm)
    (hBoundVariable : Numbered.CodeBoundary boundVariable)
    (hFormula : Numbered.CodeBoundary formula)
    (hPosition : Numbered.CodeBoundary position) :
    ⊢ₘ[quotation_occurrence_theory]
      bound_occurrence_position_condition
          boundVariable formula position ⟶ₘ
        quantifier_occurs_condition boundVariable formula := by
  have hDeclaration :=
    binder_declaration_position_imp_quantifier_occurs
      boundVariable formula position
      hBoundVariable hFormula hPosition
  have hBody :=
    quantifier_body_position_imp_quantifier_occurs
      boundVariable formula position
      hBoundVariable hFormula hPosition
  let antecedent : SetFormula :=
    bound_occurrence_position_condition
      boundVariable formula position
  let declaration : SetFormula :=
    binder_declaration_position_condition
      boundVariable formula position
  let bodyPosition : SetFormula :=
    quantifier_body_position_condition
      boundVariable formula position
  let conclusion : SetFormula :=
    quantifier_occurs_condition boundVariable formula
  have hAntecedentCheck : Formula.CheckCertificate antecedent :=
    Formula.check_admissible_complete <| by
      simpa [antecedent] using
        bound_occurrence_position_condition_admissible
          boundVariable formula position
          hBoundVariable.1 hFormula.1 hPosition.1
  nd_apply FirstOrder.Derives.impIntro
    (hAntecedentCheck := hAntecedentCheck)
  let Γ : Context signature := [antecedent]
  have hAntecedent :
      Γ ⊢ₘ[quotation_occurrence_theory] antecedent :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hCases :
      Γ ⊢ₘ[quotation_occurrence_theory]
        declaration ∨ₘ bodyPosition := by
    simpa [antecedent, declaration, bodyPosition,
      bound_occurrence_position_condition] using
        FirstOrder.Derives.conjElimRight hAntecedent
  apply FirstOrder.Derives.disjElim hCases
  · exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := declaration :: Γ) (by simp)
        (by simpa [declaration, conclusion] using hDeclaration))
      (FirstOrder.Derives.assumption (by simp [declaration]))
  · exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := bodyPosition :: Γ) (by simp)
        (by simpa [bodyPosition, conclusion] using hBody))
      (FirstOrder.Derives.assumption (by simp [bodyPosition]))

/--
若同名量词在公式码中完全不出现，则一个具体变量位置必为自由出现位置。
-/
theorem free_occurrence_position_of_not_quantifier
    (boundVariable formula position : SetTerm)
    (hBoundVariable : Numbered.CodeBoundary boundVariable)
    (hFormula : Numbered.CodeBoundary formula)
    (hPosition : Numbered.CodeBoundary position) :
    ⊢ₘ[quotation_occurrence_theory]
      (¬ₘ quantifier_occurs_condition boundVariable formula) ⟶ₘ
        variable_occurs_at_position_condition
            boundVariable formula position ⟶ₘ
          free_occurrence_position_condition
            boundVariable formula position := by
  have hBound :=
    bound_occurrence_position_imp_quantifier_occurs
      boundVariable formula position
      hBoundVariable hFormula hPosition
  let noQuantifier : SetFormula :=
    ¬ₘ quantifier_occurs_condition boundVariable formula
  let occurrence : SetFormula :=
    variable_occurs_at_position_condition
      boundVariable formula position
  let boundOccurrence : SetFormula :=
    bound_occurrence_position_condition
      boundVariable formula position
  have hNoQuantifierCheck : Formula.CheckCertificate noQuantifier :=
    Formula.check_admissible_complete <| by
      dsimp [noQuantifier]
      exact Formula.Admissible.neg <|
        quantifier_occurs_condition_admissible
          boundVariable formula hBoundVariable.1 hFormula.1
  have hOccurrenceCheck : Formula.CheckCertificate occurrence :=
    Formula.check_admissible_complete <| by
      dsimp [occurrence]
      exact variable_occurs_at_position_condition_admissible
        boundVariable formula position
        hBoundVariable.1 hFormula.1 hPosition.1
  have hBoundCheck : Formula.CheckCertificate boundOccurrence :=
    Formula.check_admissible_complete <| by
      dsimp [boundOccurrence]
      exact bound_occurrence_position_condition_admissible
        boundVariable formula position
        hBoundVariable.1 hFormula.1 hPosition.1
  nd_apply FirstOrder.Derives.impIntro
    (hAntecedentCheck := hNoQuantifierCheck)
  let Γ : Context signature := [noQuantifier]
  nd_apply FirstOrder.Derives.impIntro
    (hAntecedentCheck := hOccurrenceCheck)
  let Δ : Context signature := [occurrence, noQuantifier]
  have hOccurrence :
      Δ ⊢ₘ[quotation_occurrence_theory] occurrence :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hNotBound :
      Δ ⊢ₘ[quotation_occurrence_theory] ¬ₘ boundOccurrence := by
    nd_apply FirstOrder.Derives.negIntro
      (hBodyCheck := hBoundCheck)
    let Ξ : Context signature :=
      [boundOccurrence, occurrence, noQuantifier]
    have hBoundOccurrence :
        Ξ ⊢ₘ[quotation_occurrence_theory] boundOccurrence :=
      FirstOrder.Derives.assumption (by simp [Ξ])
    have hQuantifier :
        Ξ ⊢ₘ[quotation_occurrence_theory]
          quantifier_occurs_condition boundVariable formula :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Ξ) (by simp [Ξ])
          (by simpa [boundOccurrence] using hBound))
        hBoundOccurrence
    have hNoQuantifier :
        Ξ ⊢ₘ[quotation_occurrence_theory] noQuantifier :=
      FirstOrder.Derives.assumption (by simp [Ξ])
    exact FirstOrder.Derives.negElim hQuantifier <| by
      simpa [noQuantifier] using hNoQuantifier
  simpa [occurrence, boundOccurrence,
    free_occurrence_position_condition] using
      FirstOrder.Derives.conjIntro hOccurrence hNotBound

/--
量词出现条件逐变量码与公式码等式运输。
它只消费已有对象证书，不检查 token 树。
-/
theorem quantifier_occurs_of_equalities
    {T : Theory signature} {Γ : Context signature}
    (leftVariable rightVariable leftFormula rightFormula : SetTerm)
    (hLeftVariable : Term.Admissible leftVariable SetSort.set)
    (hRightVariable : Term.Admissible rightVariable SetSort.set)
    (hLeftFormula : Term.Admissible leftFormula SetSort.set)
    (hRightFormula : Term.Admissible rightFormula SetSort.set)
    (hFresh :
      ReservedIdsFresh [320, 321, 322, 460, 461]
        [leftVariable, rightVariable, leftFormula, rightFormula])
    (hVariableEquality :
      Γ ⊢ₘ[T] leftVariable ≐ₘ rightVariable)
    (hFormulaEquality :
      Γ ⊢ₘ[T] leftFormula ≐ₘ rightFormula)
    (hRight :
      Γ ⊢ₘ[T]
        quantifier_occurs_condition rightVariable rightFormula) :
    Γ ⊢ₘ[T]
      quantifier_occurs_condition leftVariable leftFormula := by
  have hSourceFresh460 : 460 ∉ [320, 321, 322] := by
    simp
  have hSourceFresh461 : 461 ∉ [320, 321, 322] := by
    simp
  have hReplacementFresh (term : SetTerm)
      (hTerm : term ∈
        [leftVariable, rightVariable, leftFormula, rightFormula])
      (id : FreeVarId) (hId : id ∈ [320, 321, 322]) :
      (SetSort.set, id) ∉ Term.freeSupport term :=
    hFresh term hTerm id <| by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hId ⊢
      rcases hId with hId | hId | hId
      · exact Or.inl hId
      · exact Or.inr (Or.inl hId)
      · exact Or.inr (Or.inr (Or.inl hId))
  have hRightVariableFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 460
          replacement rightVariable = rightVariable :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 460 replacement rightVariable <|
        hFresh rightVariable (by simp) 460 (by simp)
  have hLeftFormulaFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 461
          replacement leftFormula = leftFormula :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 461 replacement leftFormula <|
        hFresh leftFormula (by simp) 461 (by simp)
  have hFormulaIffRaw :
      Γ ⊢ₘ[T]
        (quantifier_occurs_condition rightVariable (x#460))⟪
            SetSort.set, 460 ↦ leftFormula⟫ₘ ↔ₘ
          (quantifier_occurs_condition rightVariable (x#460))⟪
            SetSort.set, 460 ↦ rightFormula⟫ₘ :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := 460)
      (left := leftFormula) (right := rightFormula)
      (body := quantifier_occurs_condition rightVariable (x#460))
      hFormulaEquality
  have hFormulaNormalize (replacement : SetTerm)
      (hReplacement : Term.Admissible replacement SetSort.set)
      (hReplacementMember :
        replacement ∈
          [leftVariable, rightVariable, leftFormula, rightFormula]) :
      Formula.substituteFree SetSort.set 460 replacement
          (quantifier_occurs_condition rightVariable (x#460)) =
        quantifier_occurs_condition rightVariable replacement :=
    quantifier_occurs_condition_substituteFree
      460 replacement rightVariable (x#460)
        rightVariable replacement
      hSourceFresh460
      hReplacement
      (hReplacementFresh replacement hReplacementMember)
      (by
        simpa using hRightVariableFixed replacement)
      (by simp [Term.substituteFree, set_variable])
  have hFormulaIff :
      Γ ⊢ₘ[T]
        quantifier_occurs_condition rightVariable leftFormula ↔ₘ
          quantifier_occurs_condition rightVariable rightFormula := by
    simpa only [
      hFormulaNormalize leftFormula hLeftFormula (by simp),
      hFormulaNormalize rightFormula hRightFormula (by simp)] using
      hFormulaIffRaw
  have hRightFormulaLeft :
      Γ ⊢ₘ[T]
        quantifier_occurs_condition rightVariable leftFormula :=
    FirstOrder.Derives.iffElimLeft hFormulaIff hRight
  have hVariableIffRaw :
      Γ ⊢ₘ[T]
        (quantifier_occurs_condition (x#461) leftFormula)⟪
            SetSort.set, 461 ↦ leftVariable⟫ₘ ↔ₘ
          (quantifier_occurs_condition (x#461) leftFormula)⟪
            SetSort.set, 461 ↦ rightVariable⟫ₘ :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := 461)
      (left := leftVariable) (right := rightVariable)
      (body := quantifier_occurs_condition (x#461) leftFormula)
      hVariableEquality
  have hVariableNormalize (replacement : SetTerm)
      (hReplacement : Term.Admissible replacement SetSort.set)
      (hReplacementMember :
        replacement ∈
          [leftVariable, rightVariable, leftFormula, rightFormula]) :
      Formula.substituteFree SetSort.set 461 replacement
          (quantifier_occurs_condition (x#461) leftFormula) =
        quantifier_occurs_condition replacement leftFormula :=
    quantifier_occurs_condition_substituteFree
      461 replacement (x#461) leftFormula
        replacement leftFormula
      hSourceFresh461
      hReplacement
      (hReplacementFresh replacement hReplacementMember)
      (by simp [Term.substituteFree, set_variable])
      (by
        simpa using hLeftFormulaFixed replacement)
  have hVariableIff :
      Γ ⊢ₘ[T]
        quantifier_occurs_condition leftVariable leftFormula ↔ₘ
          quantifier_occurs_condition rightVariable leftFormula := by
    simpa only [
      hVariableNormalize leftVariable hLeftVariable (by simp),
      hVariableNormalize rightVariable hRightVariable (by simp)] using
      hVariableIffRaw
  exact FirstOrder.Derives.iffElimLeft
    hVariableIff hRightFormulaLeft

/-- “自由出现”定义在两个闭代码项处的实例。 -/
private theorem free_occurrence_definition_instance_derives
    (boundVariable formula : SetTerm)
    (hBoundVariable : Numbered.CodeBoundary boundVariable)
    (hFormula : Numbered.CodeBoundary formula) :
    ⊢ₘ[quotation_occurrence_theory] ((free_occursₘ(boundVariable, formula)) ↔ₘ (∃ₘ[SetSort.set, 329],
          free_occurrence_position_condition
            boundVariable formula (x#329))) := by
  have hBoundVariableCheck :
      Term.CheckCertificate boundVariable SetSort.set :=
    Term.check_admissible_complete hBoundVariable.1
  have hFormulaCheck :
      Term.CheckCertificate formula SetSort.set :=
    Term.check_admissible_complete hFormula.1
  have hOccurrenceDefinition :
      ⊢ₘ[quotation_occurrence_theory]
        occurrence_definition_axiom :=
    FirstOrder.Derives.theoryAxiom
      (Or.inr <| Or.inl rfl)
  have hUniversal :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight
          hOccurrenceDefinition
  have hAtVariable :=
    FirstOrder.Derives.forall_elim
      (term := boundVariable) hUniversal
  have hAtFormula :=
    FirstOrder.Derives.forall_elim
      (term := formula) hAtVariable
  have hBoundVariableOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term boundVariable =
        boundVariable :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term boundVariable hBoundVariable.1.2
  have hFormulaOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term formula = formula :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term formula hFormula.1.2
  have hNumeralBoundary (value : Nat) :
      Numbered.CodeBoundary (numₘ(value)) :=
    ⟨finite_numeral_term_admissible value,
      finite_numeral_term_freeSupport value⟩
  have hNumeralOpen (value depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement (numₘ(value)) =
        numₘ(value) :=
    Numbered.CodeBoundary.openAt_eq (hNumeralBoundary value) depth replacement
  have hNumeralSubstitute (value : Nat) (freeId : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set freeId replacement (numₘ(value)) =
        numₘ(value) :=
    Numbered.CodeBoundary.substituteFree_eq (hNumeralBoundary value) freeId replacement
  have hNumeralClose (value : Nat) (freeId : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set freeId depth (numₘ(value)) =
        numₘ(value) :=
    Numbered.CodeBoundary.closeFreeAt_eq (hNumeralBoundary value) freeId depth
  simpa [free_occurrence_definition_axiom,
    free_occurrence_position_condition,
    bound_occurrence_position_condition,
    binder_declaration_position_condition,
    quantifier_body_position_condition,
    universal_binder_at_condition,
    code_substring_at_condition,
    variable_occurs_at_position_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Term.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt, Term.substituteFree,
    set_variable, set_bound_variable,
    hBoundVariableOpen, hFormulaOpen,
    hNumeralOpen, hNumeralSubstitute, hNumeralClose,
    Numbered.CodeBoundary.substituteFree_eq hBoundVariable,
    Numbered.CodeBoundary.substituteFree_eq hFormula,
    Numbered.CodeBoundary.closeFreeAt_eq hBoundVariable,
    Numbered.CodeBoundary.closeFreeAt_eq hFormula] using
      hAtFormula
/--
若变量 token 不在标准串中，则该变量不在相应对象公式码中自由出现。
证明使用真正的 `free_occursₘ` 定义：任意自由出现见证首先给出一个逐点 token 等式，
再与标准序列的全域避让证书矛盾。
-/
theorem standard_token_sequence_not_free_occurs (tokens : List Nat) (name : Nat) (hToken :
      Numbered.variable_token name ∉ tokens) :
    ⊢ₘ[quotation_occurrence_theory]
      ¬ₘ free_occursₘ(
        Numbered.named_variable_code name,
        standard_token_sequence tokens) := by
  let variableCode := Numbered.named_variable_code name
  let formulaCode := standard_token_sequence tokens
  let occurrence : SetFormula :=
    free_occursₘ(variableCode, formulaCode)
  let Γ : Context signature := [occurrence]
  have hVariableBoundary :
      Numbered.CodeBoundary variableCode :=
    ⟨variable_code_term_admissible (numₘ(name)) (finite_numeral_term_admissible name),
      named_variable_code_freeSupport name⟩
  have hFormulaBoundary :
      Numbered.CodeBoundary formulaCode :=
    ⟨standard_token_sequence_admissible tokens,
      standard_token_sequence_freeSupport_nil tokens⟩
  have hVariableCheck :
      Term.CheckCertificate variableCode SetSort.set :=
    Term.check_admissible_complete hVariableBoundary.1
  have hFormulaCheck :
      Term.CheckCertificate formulaCode SetSort.set :=
    Term.check_admissible_complete hFormulaBoundary.1
  have hDefinition :=
    free_occurrence_definition_instance_derives
      variableCode formulaCode
      hVariableBoundary hFormulaBoundary
  nd_apply FirstOrder.Derives.negIntro
  have hOccurrence :
      Γ ⊢ₘ[quotation_occurrence_theory] occurrence :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hExists :
      Γ ⊢ₘ[quotation_occurrence_theory]
        ∃ₘ[SetSort.set, 329],
          free_occurrence_position_condition
            variableCode formulaCode (x#329) :=
    FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hDefinition)
      hOccurrence
  nd_apply FirstOrder.Derives.exists_elim
      (T := quotation_occurrence_theory) (Γ := Γ)
      (sort := SetSort.set) (eigen := 329)
      (body := free_occurrence_position_condition
        variableCode formulaCode (x#329))
      (conclusion := Formula.falsum)
  · intro formula hFormula
    rw [(quotation_occurrence_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simp [occurrence, Formula.freeSupport,
      Term.freeSupportList,
      hVariableBoundary.2, hFormulaBoundary.2]
  · exact List.not_mem_nil
  · exact hExists
  · let position : SetTerm := x#329
    let positionCondition : SetFormula :=
      free_occurrence_position_condition
        variableCode formulaCode position
    let Δ : Context signature := [positionCondition, occurrence]
    have hPositionCondition :
        Δ ⊢ₘ[quotation_occurrence_theory]
          positionCondition :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hVariableOccurrence :
        Δ ⊢ₘ[quotation_occurrence_theory]
          variable_occurs_at_position_condition
            variableCode formulaCode position :=
      FirstOrder.Derives.conjElimLeft <| by
        simpa [positionCondition,
          free_occurrence_position_condition] using
          hPositionCondition
    have hPositionMember :
        Δ ⊢ₘ[quotation_occurrence_theory]
          position ∈ₘ domₘ(formulaCode) :=
      FirstOrder.Derives.conjElimLeft <| by
        simpa [variable_occurs_at_position_condition] using
          hVariableOccurrence
    have hValueEquality :
        Δ ⊢ₘ[quotation_occurrence_theory] (formulaCode ·ₘ position) ≐ₘ (variableCode ·ₘ numₘ(0)) :=
      FirstOrder.Derives.conjElimRight <| by
        simpa [variable_occurs_at_position_condition] using
          hVariableOccurrence
    have hAvoidanceUniversal :=
      standard_token_sequence_avoids_token
        tokens (Numbered.variable_token name) hToken
    have hAvoidanceAtRaw :=
      FirstOrder.Derives.forall_elim
        (term := position)
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ])
          hAvoidanceUniversal)
    have hTokenBoundary :
        Numbered.CodeBoundary (numₘ(Numbered.variable_token name)) :=
      ⟨finite_numeral_term_admissible (Numbered.variable_token name),
        finite_numeral_term_freeSupport (Numbered.variable_token name)⟩
    have hAvoidanceAt :
        Δ ⊢ₘ[quotation_occurrence_theory] (position ∈ₘ domₘ(formulaCode)) ⟶ₘ
            ¬ₘ ((formulaCode ·ₘ position) ≐ₘ
              numₘ(Numbered.variable_token name)) := by
      simpa [position, formulaCode,
        Formula.openAt_closeFreeAt_eq_substituteFree,
        Formula.openAt, Formula.substituteFree,
        Term.openAt, Term.substituteFree,
        set_variable,
        Numbered.CodeBoundary.substituteFree_eq
          hFormulaBoundary,
        Numbered.CodeBoundary.substituteFree_eq
          hTokenBoundary] using hAvoidanceAtRaw
    have hNotTokenValue :
        Δ ⊢ₘ[quotation_occurrence_theory]
          ¬ₘ ((formulaCode ·ₘ position) ≐ₘ
            numₘ(Numbered.variable_token name)) :=
      FirstOrder.Derives.impElim
        hAvoidanceAt hPositionMember
    have hVariableValue :
        Δ ⊢ₘ[quotation_occurrence_theory] (variableCode ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.variable_token name) :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp [Δ]) <| by
          simpa [variableCode] using
            named_variable_code_apply_zero name
    have hTokenValue :
        Δ ⊢ₘ[quotation_occurrence_theory] (formulaCode ·ₘ position) ≐ₘ
            numₘ(Numbered.variable_token name) :=
      Metatheory.Derives.equality_trans
        hValueEquality hVariableValue
    exact FirstOrder.Derives.negElim
      hTokenValue hNotTokenValue
/-!
## 规范 quotation 的对象自由出现否定
-/
/-- 对象代码等式可运输自由出现谓词的否定。 -/
theorem not_free_occurs_congr_formula_code (boundVariable left right : SetTerm) (hBoundVariable : Numbered.CodeBoundary boundVariable)
    (hLeft : Numbered.CodeBoundary left) (hRight : Numbered.CodeBoundary right) (hEquality :
      ⊢ₘ[quotation_occurrence_theory] left ≐ₘ right) (hNotRight :
      ⊢ₘ[quotation_occurrence_theory]
        ¬ₘ free_occursₘ(boundVariable, right)) :
    ⊢ₘ[quotation_occurrence_theory]
      ¬ₘ free_occursₘ(boundVariable, left) := by
  let parameter : FreeVarId := 461
  let body : SetFormula :=
    ¬ₘ free_occursₘ(boundVariable, x#parameter)
  have hRightLeft :
      ⊢ₘ[quotation_occurrence_theory] right ≐ₘ left :=
    Metatheory.Derives.equality_symm hEquality
  have hTransport :=
    FirstOrder.Derives.eq_subst_m (T := quotation_occurrence_theory) (Γ := []) (sort := SetSort.set) (eigen := parameter)
      (left := right) (right := left) (body := body)
      hRightLeft (by
        simpa [body, parameter,
          Formula.substituteFree, Term.substituteFree,
          set_variable,
          Numbered.CodeBoundary.substituteFree_eq
            hBoundVariable,
          Numbered.CodeBoundary.substituteFree_eq hRight] using
          hNotRight)
  simpa [body, parameter,
    Formula.substituteFree, Term.substituteFree,
    set_variable,
    Numbered.CodeBoundary.substituteFree_eq
      hBoundVariable,
    Numbered.CodeBoundary.substituteFree_eq hLeft] using
    hTransport
/-- 变量代码等式同样可运输自由出现谓词的否定。 -/
theorem not_free_occurs_congr_variable_code
    (left right formula : SetTerm)
    (hLeft : Numbered.CodeBoundary left)
    (hRight : Numbered.CodeBoundary right)
    (hFormula : Numbered.CodeBoundary formula) (hEquality :
      ⊢ₘ[quotation_occurrence_theory] left ≐ₘ right) (hNotRight :
      ⊢ₘ[quotation_occurrence_theory]
        ¬ₘ free_occursₘ(right, formula)) :
    ⊢ₘ[quotation_occurrence_theory]
      ¬ₘ free_occursₘ(left, formula) := by
  let parameter : FreeVarId := 462
  let body : SetFormula :=
    ¬ₘ free_occursₘ(x#parameter, formula)
  have hRightLeft :
      ⊢ₘ[quotation_occurrence_theory] right ≐ₘ left :=
    Metatheory.Derives.equality_symm hEquality
  have hTransport :=
    FirstOrder.Derives.eq_subst_m (T := quotation_occurrence_theory) (Γ := []) (sort := SetSort.set) (eigen := parameter)
      (left := right) (right := left) (body := body)
      hRightLeft (by
        simpa [body, parameter,
          Formula.substituteFree, Term.substituteFree,
          set_variable,
          Numbered.CodeBoundary.substituteFree_eq hRight,
          Numbered.CodeBoundary.substituteFree_eq hFormula] using
          hNotRight)
  simpa [body, parameter,
    Formula.substituteFree, Term.substituteFree,
    set_variable,
    Numbered.CodeBoundary.substituteFree_eq hLeft,
    Numbered.CodeBoundary.substituteFree_eq hFormula] using
    hTransport
/--
显式 Hilbert quotation 避开绝对 binder 深度时，对应变量在对象公式码中不自由出现。
证明先取同步 token quotation，再把元层深度避让转换为 token 非出现，最后通过
quotation 值等式运输到实际代码。
-/
theorem quote_hilbert_with?_not_free_occurs_of_avoid_bound_depth
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (entryDepth targetDepth : Nat)
    {formula : Formula σ} {code : SetTerm} (hCore : Numbered.HilbertCore formula) (hWellFormed : FormulaWellFormed formula) (hAvoid :
      quotation_formula_avoids_bound_depth
        entryDepth targetDepth formula) (hCode :
      Numbered.quote_hilbert_with?
          free_name bound_name (canonical_bound_names entryDepth)
          entryDepth formula =
        some code) :
    ⊢ₘ[quotation_occurrence_theory]
      ¬ₘ free_occursₘ(
        Numbered.named_variable_code (bound_name targetDepth),
        code) := by
  rcases Numbered.quote_hilbert_tokens_with?_exists
      free_name bound_name hCore hWellFormed (Numbered.quote_hilbert_with?_scoped
        free_name bound_name hCode) with
    ⟨tokens, hTokens⟩
  let variableCode :=
    Numbered.named_variable_code (bound_name targetDepth)
  let standardCode :=
    standard_token_sequence tokens
  have hToken :
      Numbered.variable_token (bound_name targetDepth) ∉ tokens :=
    quote_hilbert_tokens_with?_avoid_bound_depth
      entryDepth targetDepth hAvoid hTokens
  have hVariableBoundary :
      Numbered.CodeBoundary variableCode := by
    exact
      ⟨variable_code_term_admissible (numₘ(bound_name targetDepth)) (finite_numeral_term_admissible (bound_name targetDepth)),
        named_variable_code_freeSupport (bound_name targetDepth)⟩
  have hCodeBoundary :
      Numbered.CodeBoundary code :=
    Numbered.quote_hilbert_with?_code_boundary
      free_name bound_name hCode
  have hStandardBoundary :
      Numbered.CodeBoundary standardCode := by
    exact
      ⟨standard_token_sequence_admissible tokens,
        standard_token_sequence_freeSupport_nil tokens⟩
  have hCodeEquality :
      ⊢ₘ[quotation_occurrence_theory]
        code ≐ₘ standardCode := by
    simpa [standardCode] using
      qo_weaken_godel_quotation <|
        quote_hilbert_with?_eq_standard_token_sequence
          free_name bound_name hTokens hCode
  have hNotStandard :
      ⊢ₘ[quotation_occurrence_theory]
        ¬ₘ free_occursₘ(variableCode, standardCode) := by
    simpa [variableCode, standardCode] using
      standard_token_sequence_not_free_occurs
        tokens (bound_name targetDepth) hToken
  simpa [variableCode] using
    not_free_occurs_congr_formula_code
      variableCode code standardCode
      hVariableBoundary hCodeBoundary hStandardBoundary
      hCodeEquality hNotStandard
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
