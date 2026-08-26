import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCodeReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.MinimumLength.Closure

/-!
# FormalSystem 有限签名 token 的反向拒绝

本模块把宿主层可计算的 `¬ FSFormulaToken token` 精确翻译为对象层
`¬ fs_formula_token_condition (numₘ(token))`。四个分支分别由有限逻辑符号表、
隶属 singleton、变量名字的有界搜索和当前有限非逻辑签名处理。

证明只使用闭的标准 token 序列、有限枚举与对象等式运输。
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

/-! ## 宿主失败证书 -/

/-- 一个自然数无法落入当前公式签名时的四路精确失败数据。 -/
structure FSFormulaTokenFailure (token : Nat) : Prop where
  logical_ne :
    ∀ symbol : LogicalSymbolKind,
      token ≠ Numbered.logical_token symbol
  membership_ne :
    token ≠ Numbered.membership_token
  variable_none :
    fs_variable_name_decode token = none
  nonlogical_not_mem :
    token ∉ fs_nonlogical_symbol_tokens

/-- `FSFormulaToken` 的否定可计算地分解为四路失败证书。 -/
theorem fs_formula_token_failure_of_not
    {token : Nat}
    (hToken : ¬ FSFormulaToken token) :
    FSFormulaTokenFailure token := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro symbol hEquality
    apply hToken
    rw [hEquality]
    exact FSFormulaToken.logical symbol
  · intro hEquality
    apply hToken
    rw [hEquality]
    exact FSFormulaToken.membership
  · cases hDecode :
        fs_variable_name_decode token with
    | none =>
        rfl
    | some name =>
        exfalso
        apply hToken
        have hValue :
            Numbered.variable_token name = token :=
          fs_variable_name_decode_value_of_some hDecode
        rw [← hValue]
        exact FSFormulaToken.var name
  · intro hMember
    rcases List.mem_append.mp hMember with
      hFunction | hPredicate
    · rcases List.mem_map.mp hFunction with
        ⟨symbol, _, hValue⟩
      apply hToken
      rw [← hValue]
      exact FSFormulaToken.func symbol
    · rcases List.mem_map.mp hPredicate with
        ⟨symbol, hSymbol, hValue⟩
      have hNe :
          symbol ≠ RelationSymbol.membership :=
        of_decide_eq_true
          (List.mem_filter.mp hSymbol).2
      apply hToken
      rw [← hValue]
      exact FSFormulaToken.pred symbol hNe

/-! ## 对象集合上的否定运输 -/

/--
集合项等式可把右侧的闭成员否定运输回左侧。该引理只封装对象等式替换，
不增加理论前提。
-/
private theorem gq_not_mem_left_of_set_equality
    (element left right : SetTerm)
    (hElement : Term.Admissible element SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEquality :
      Derives godel_quotation_theory [] (
        left ≐ₘ right))
    (hNotRight :
      Derives godel_quotation_theory [] (
        ¬ₘ (element ∈ₘ right))) :
    Derives godel_quotation_theory [] (
      ¬ₘ (element ∈ₘ left)) := by
  nd_apply FirstOrder.Derives.negIntro
  have hMember :
      [element ∈ₘ left]
        ⊢ₘ[godel_quotation_theory]
          element ∈ₘ left :=
    FirstOrder.Derives.assumption (by simp)
  have hRightMember :
      [element ∈ₘ left]
        ⊢ₘ[godel_quotation_theory]
          element ∈ₘ right :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken_cons
        (membership_right_iff_of_equality
          element left right
          hElement hLeft hRight hEquality))
      hMember
  exact FirstOrder.Derives.negElim
    hRightMember
    (FirstOrder.Derives.context_weaken_cons
      hNotRight)

/-- 与 singleton 中心对象层互异的项不属于该 singleton。 -/
private theorem gq_singleton_not_mem_of_ne
    (element center : SetTerm)
    (hElement : Term.Admissible element SetSort.set)
    (hCenter : Term.Admissible center SetSort.set)
    (hNe :
      Derives godel_quotation_theory [] (
        ¬ₘ (element ≐ₘ center))) :
    Derives godel_quotation_theory [] (
      ¬ₘ (element ∈ₘ {center}ₘ)) := by
  have hSpec :
      Derives godel_quotation_theory [] (
        singleton_spec center {center}ₘ) :=
    gq_weaken_singleton
      (singleton_term_spec_derives center hCenter)
  nd_apply FirstOrder.Derives.negIntro
  have hMember :
      [element ∈ₘ {center}ₘ]
        ⊢ₘ[godel_quotation_theory]
          element ∈ₘ {center}ₘ :=
    FirstOrder.Derives.assumption (by simp)
  have hEquality :
      [element ∈ₘ {center}ₘ]
        ⊢ₘ[godel_quotation_theory]
          element ≐ₘ center :=
    FirstOrder.Derives.iffElimRight
      (singleton_spec_membership_iff
        center {center}ₘ element
        hCenter
        (singleton_term_admissible center hCenter)
        hElement
        (FirstOrder.Derives.context_weaken_cons hSpec))
      hMember
  exact FirstOrder.Derives.negElim
    hEquality
    (FirstOrder.Derives.context_weaken_cons hNe)

/-! ## 四类对象层拒绝 -/

/-- 非逻辑 token 的规范符号码不属于对象逻辑符号有限集。 -/
theorem gq_logical_symbol_code_not_mem
    (token : Nat)
    (hToken :
      ∀ symbol : LogicalSymbolKind,
        token ≠ Numbered.logical_token symbol) :
    Derives godel_quotation_theory [] (
      ¬ₘ (sym_codeₘ(numₘ(token)) ∈ₘ LogicSymₘ)) := by
  have hCode :
      Term.Admissible
        (sym_codeₘ(numₘ(token))) SetSort.set :=
    singleton_symbol_code_term_admissible
      (numₘ(token))
      (finite_numeral_term_admissible token)
  have hLiteralNot :
      Derives godel_quotation_theory [] (
        ¬ₘ (sym_codeₘ(numₘ(token)) ∈ₘ
          finite_set_literal_term
            logical_symbol_code_terms)) := by
    apply gq_finite_set_literal_not_mem_of_forall_ne
      logical_symbol_code_terms
      (sym_codeₘ(numₘ(token)))
      (by
        intro code hMember
        rcases List.mem_map.mp hMember with
          ⟨symbol, _, rfl⟩
        exact logical_symbol_code_term_admissible symbol)
      hCode
    intro code hMember
    rcases List.mem_map.mp hMember with
      ⟨symbol, _, rfl⟩
    exact gq_symbol_code_ne_of_token_ne
      (logical_symbol_code_term symbol)
      token (Numbered.logical_token symbol)
      (logical_symbol_code_term_admissible symbol)
      (logical_symbol_code_eq_standard_token_sequence
        symbol)
      (hToken symbol)
  have hDefinition :
      Derives godel_quotation_theory [] (
        LogicSymₘ ≐ₘ
          finite_set_literal_term
            logical_symbol_code_terms) := by
    apply gq_weaken_logical_symbol
    exact FirstOrder.Derives.theoryAxiom
      (Or.inl rfl)
  exact gq_not_mem_left_of_set_equality
    (sym_codeₘ(numₘ(token)))
    LogicSymₘ
    (finite_set_literal_term
      logical_symbol_code_terms)
    hCode
    logical_symbol_set_term_admissible
    (finite_set_literal_term_admissible
      logical_symbol_code_terms <| by
        intro code hMember
        rcases List.mem_map.mp hMember with
          ⟨symbol, _, rfl⟩
        exact logical_symbol_code_term_admissible symbol)
    hDefinition hLiteralNot

/-- 非隶属 token 的规范符号码不属于对象隶属符号 singleton。 -/
theorem gq_membership_symbol_code_not_mem
    (token : Nat)
    (hToken :
      token ≠ Numbered.membership_token) :
    Derives godel_quotation_theory [] (
      ¬ₘ (sym_codeₘ(numₘ(token)) ∈ₘ
        MembershipSymₘ)) := by
  have hCode :
      Term.Admissible
        (sym_codeₘ(numₘ(token))) SetSort.set :=
    singleton_symbol_code_term_admissible
      (numₘ(token))
      (finite_numeral_term_admissible token)
  have hSingletonNot :
      Derives godel_quotation_theory [] (
        ¬ₘ (sym_codeₘ(numₘ(token)) ∈ₘ
          {membership_symbol_code_term}ₘ)) :=
    gq_singleton_not_mem_of_ne
      (sym_codeₘ(numₘ(token)))
      membership_symbol_code_term
      hCode
      membership_symbol_code_term_admissible
      (gq_symbol_code_ne_of_token_ne
        membership_symbol_code_term
        token Numbered.membership_token
        membership_symbol_code_term_admissible
        membership_symbol_code_eq_standard_token_sequence
        hToken)
  have hDefinition :
      Derives godel_quotation_theory [] (
        MembershipSymₘ ≐ₘ
          {membership_symbol_code_term}ₘ) := by
    apply gq_weaken_membership_symbol
    exact FirstOrder.Derives.theoryAxiom
      (Or.inl rfl)
  exact gq_not_mem_left_of_set_equality
    (sym_codeₘ(numₘ(token)))
    MembershipSymₘ
    {membership_symbol_code_term}ₘ
    hCode
    membership_symbol_set_term_admissible
    (singleton_term_admissible
      membership_symbol_code_term
      membership_symbol_code_term_admissible)
    hDefinition hSingletonNot

/-! ## 完整 token 条件 -/

/--
宿主层 token 分类失败时，对象层有限签名 token 条件为假。

这里四个析取分支分别消费上面的闭否定；变量分支只依赖输入 token 内的有限搜索。
-/
theorem gq_fs_formula_token_condition_not
    {token : Nat}
    (hToken : ¬ FSFormulaToken token) :
    Derives godel_quotation_theory [] (
      ¬ₘ fs_formula_token_condition
        (numₘ(token))) := by
  let logicalMember : SetFormula :=
    sym_codeₘ(numₘ(token)) ∈ₘ LogicSymₘ
  let membershipMember : SetFormula :=
    sym_codeₘ(numₘ(token)) ∈ₘ MembershipSymₘ
  let variableCondition : SetFormula :=
    fs_variable_token_condition (numₘ(token))
  let nonlogicalMember : SetFormula :=
    sym_codeₘ(numₘ(token)) ∈ₘ
      fs_nonlogical_symbol_code_set_term
  let left : SetFormula :=
    logicalMember ∨ₘ membershipMember
  let right : SetFormula :=
    variableCondition ∨ₘ nonlogicalMember
  let condition : SetFormula :=
    left ∨ₘ right
  have hFailure :=
    fs_formula_token_failure_of_not hToken
  have hLogicalNot :
      Derives godel_quotation_theory [] (
        ¬ₘ logicalMember) := by
    simpa [logicalMember] using
      gq_logical_symbol_code_not_mem
        token hFailure.logical_ne
  have hMembershipNot :
      Derives godel_quotation_theory [] (
        ¬ₘ membershipMember) := by
    simpa [membershipMember] using
      gq_membership_symbol_code_not_mem
        token hFailure.membership_ne
  have hVariableNot :
      Derives godel_quotation_theory [] (
        ¬ₘ variableCondition) := by
    simpa [variableCondition] using
      gq_fs_variable_token_condition_not
        token hFailure.variable_none
  have hNonlogicalNot :
      Derives godel_quotation_theory [] (
        ¬ₘ nonlogicalMember) := by
    simpa [nonlogicalMember] using
      gq_fs_nonlogical_symbol_code_not_mem
        token hFailure.nonlogical_not_mem
  have hConditionAdmissible :
      Formula.Admissible condition := by
    simpa [condition, left, right,
      logicalMember, membershipMember,
      variableCondition, nonlogicalMember,
      fs_formula_token_condition,
      fs_formula_token_condition_lifted] using
      fs_formula_token_condition_admissible
        (numₘ(token))
        (finite_numeral_term_admissible token)
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete
        hConditionAdmissible)
  have hCondition :
      [condition] ⊢ₘ[godel_quotation_theory]
        condition :=
    FirstOrder.Derives.assumption
      (by simp)
      (Formula.check_admissible_complete
        hConditionAdmissible)
  apply FirstOrder.Derives.disjElim hCondition
  · have hLeft :
        left :: [condition]
          ⊢ₘ[godel_quotation_theory] left :=
      FirstOrder.Derives.assumption (by simp)
    apply FirstOrder.Derives.disjElim hLeft
    · exact FirstOrder.Derives.negElim
        (FirstOrder.Derives.assumption
          (by simp))
        (FirstOrder.Derives.context_weaken
          (Γ := [])
          (Δ := logicalMember :: left :: [condition])
          (by simp)
          hLogicalNot)
    · exact FirstOrder.Derives.negElim
        (FirstOrder.Derives.assumption
          (by simp))
        (FirstOrder.Derives.context_weaken
          (Γ := [])
          (Δ := membershipMember :: left :: [condition])
          (by simp)
          hMembershipNot)
  · have hRight :
        right :: [condition]
          ⊢ₘ[godel_quotation_theory] right :=
      FirstOrder.Derives.assumption (by simp)
    apply FirstOrder.Derives.disjElim hRight
    · exact FirstOrder.Derives.negElim
        (FirstOrder.Derives.assumption
          (by simp))
        (FirstOrder.Derives.context_weaken
          (Γ := [])
          (Δ := variableCondition :: right :: [condition])
          (by simp)
          hVariableNot)
    · exact FirstOrder.Derives.negElim
        (FirstOrder.Derives.assumption
          (by simp))
        (FirstOrder.Derives.context_weaken
          (Γ := [])
          (Δ := nonlogicalMember :: right :: [condition])
          (by simp)
          hNonlogicalNot)

/-! ## 完整公式条件的结构拒绝 -/

/--
任意标准 token 行只要已在对象层排除 `FormulaCodeₘ` 成员，就可排除完整有限签名
公式条件。有限签名分量不参与该提升。
-/
theorem
    gq_fs_formula_code_condition_not_of_formula_code_not
    (tokens : List Nat)
    (hMemberNot :
      ⊢ₘ[godel_quotation_theory]
        ¬ₘ (standard_token_sequence tokens ∈ₘ
          FormulaCodeₘ)) :
    ⊢ₘ[godel_quotation_theory]
      ¬ₘ fs_formula_code_condition
        (standard_token_sequence tokens) := by
  let code : SetTerm := standard_token_sequence tokens
  let condition : SetFormula :=
    fs_formula_code_condition code
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible tokens
  have hConditionAdmissible :
      Formula.Admissible condition := by
    simpa [condition] using
      fs_formula_code_condition_admissible
        code hCode
  change ⊢ₘ[godel_quotation_theory] ¬ₘ condition
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete
        hConditionAdmissible)
  let Γ : Context signature := [condition]
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hConditionAdmissible)
  have hFormulaPredicate :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_codeₘ(code) := by
    simpa [condition, fs_formula_code_condition] using
      FirstOrder.Derives.conjElimLeft hCondition
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        code ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ])
        (gq_formula_code_definition_instance
          code hCode))
      hFormulaPredicate
  exact FirstOrder.Derives.negElim
    hMember
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
        simpa [code] using hMemberNot)

/--
标准 token 行在第零、第一位都不以左括号开头时，完整有限签名公式条件为假。

这里只使用条件的公式码分量；有限签名分量不参与结构矛盾。
-/
theorem
    gq_fs_formula_code_condition_not_of_no_left_opening
    (tokens : List Nat)
    (hZero :
      tokens[0]? ≠
        some (Numbered.logical_token
          .leftParenthesis))
    (hOne :
      tokens[1]? ≠
        some (Numbered.logical_token
          .leftParenthesis)) :
    Derives godel_quotation_theory [] (
      ¬ₘ fs_formula_code_condition
        (standard_token_sequence tokens)) := by
  exact
    gq_fs_formula_code_condition_not_of_formula_code_not
      tokens <|
        gq_standard_token_sequence_formula_code_not_of_no_left_opening
          tokens hZero hOne

/--
标准 token 行缺少第一号位置时，完整有限签名公式条件为假。
-/
theorem
    gq_fs_formula_code_condition_not_of_one_absent
    (tokens : List Nat)
    (hOne : tokens[1]? = none) :
    ⊢ₘ[godel_quotation_theory]
      ¬ₘ fs_formula_code_condition
        (standard_token_sequence tokens) :=
  gq_fs_formula_code_condition_not_of_formula_code_not
    tokens <|
      gq_standard_token_sequence_formula_code_not_of_one_absent
        tokens hOne

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
