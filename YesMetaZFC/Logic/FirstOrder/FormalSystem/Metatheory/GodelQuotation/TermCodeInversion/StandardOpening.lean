import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.TermCodeInversion.Opening
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.Opening
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.VariableSymbolInversion

/-!
# 标准 token 串上的项码根反演

本模块把一般对象项码的根点证书与标准 token 串的可计算位置事实连接起来，
并排除编码构造本身不可能匹配的分支。
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
标准 token 串的第二位不是左括号时，它不可能满足正元函数应用生成条件。

该接口同时覆盖第二位存在但值错误以及第二位超出输入长度两种 checked parser
失败；对象层只消费应用编码的一位固定开口。
-/
theorem
    gq_standard_token_sequence_term_application_falsum_of_second_not_left
    {Γ : Context signature}
    (tokens : List Nat)
    (hOne :
      tokens[1]? ≠
        some (Numbered.logical_token
          .leftParenthesis))
    (hApplication :
      Γ ⊢ₘ[godel_quotation_theory]
        term_application_from_condition
          TermCodeₘ
          (standard_token_sequence tokens)) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  let code : SetTerm :=
    standard_token_sequence tokens
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible tokens
  have hClosed :
      Term.freeSupport code = [] := by
    simp [code]
  have hFresh :
      ReservedIdsFresh [210, 211, 212] [code] :=
    reserved_ids_fresh_cons_closed hClosed <|
      reserved_ids_fresh_nil [210, 211, 212]
  have hOpening :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(code)) ∧ₘ
          ((numₘ(1) ∈ₘ domₘ(code)) ∧ₘ
            ((code ·ₘ numₘ(1)) ≐ₘ
              numₘ(Numbered.logical_token
                .leftParenthesis)))) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (gq_term_application_from_condition_implies_opening
          code hCode hFresh))
      (by simpa [code] using hApplication)
  exact
    gq_standard_token_sequence_falsum_of_point_not_expected
      tokens code 1
      (Numbered.logical_token .leftParenthesis)
      hOne
      (by
        simpa [code] using
          FirstOrder.Derives.eq_refl_m
            (T := godel_quotation_theory)
            (Γ := Γ)
            (sort := SetSort.set)
            (standard_token_sequence tokens))
      (FirstOrder.Derives.conjElimRight hOpening)

/--
第二位不是左括号的标准 token 串若是项码，则它只能来自变量或常元两个 singleton
基础分支。正元函数应用分支由上一条固定开口拒绝，不需要分析参数列。
-/
theorem
    gq_standard_token_sequence_term_code_implies_base_symbol_of_second_not_left
    (tokens : List Nat)
    (hOne :
      tokens[1]? ≠
        some (Numbered.logical_token
          .leftParenthesis)) :
    ⊢ₘ[godel_quotation_theory]
      (standard_token_sequence tokens ∈ₘ TermCodeₘ) ⟶ₘ
        ((standard_token_sequence tokens ∈ₘ VarSymₘ) ∨ₘ
          (standard_token_sequence tokens ∈ₘ ConstSymₘ)) := by
  let code : SetTerm :=
    standard_token_sequence tokens
  let membership : SetFormula :=
    code ∈ₘ TermCodeₘ
  let baseSymbol : SetFormula :=
    (code ∈ₘ VarSymₘ) ∨ₘ
      (code ∈ₘ ConstSymₘ)
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible tokens
  have hClosed :
      Term.freeSupport code = [] := by
    simp [code]
  have hMembershipAdmissible :
      Formula.Admissible membership := by
    simpa [membership] using
      membership_formula_admissible
        hCode term_code_set_term_admissible
  change
    ⊢ₘ[godel_quotation_theory]
      membership ⟶ₘ baseSymbol
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [membership]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        membership :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hMembershipAdmissible)
  have hGeneration :
      Γ ⊢ₘ[godel_quotation_theory]
        term_code_generation_condition
          TermCodeₘ code :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ])
        (gq_term_code_member_implies_generation
          code hCode hClosed))
      (by simpa [membership] using hMember)
  unfold term_code_generation_condition at hGeneration
  apply FirstOrder.Derives.disjElim hGeneration
  · let Δ : Context signature :=
      (code ∈ₘ VarSymₘ) :: Γ
    have hVariable :
        Δ ⊢ₘ[godel_quotation_theory]
          code ∈ₘ VarSymₘ :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    simpa [baseSymbol] using
      FirstOrder.Derives.disjIntroLeft hVariable
  · let tail : SetFormula :=
      (code ∈ₘ ConstSymₘ) ∨ₘ
        term_application_from_condition
          TermCodeₘ code
    let Δ : Context signature := tail :: Γ
    have hTail :
        Δ ⊢ₘ[godel_quotation_theory]
          tail :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    apply FirstOrder.Derives.disjElim hTail
    · let Ε : Context signature :=
        (code ∈ₘ ConstSymₘ) :: Δ
      have hConstant :
          Ε ⊢ₘ[godel_quotation_theory]
            code ∈ₘ ConstSymₘ :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
      simpa [baseSymbol] using
        FirstOrder.Derives.disjIntroRight hConstant
    · let application : SetFormula :=
        term_application_from_condition
          TermCodeₘ code
      let Ε : Context signature :=
        application :: Δ
      have hApplication :
          Ε ⊢ₘ[godel_quotation_theory]
            term_application_from_condition
              TermCodeₘ
              (standard_token_sequence tokens) := by
        simpa [application, code] using
          FirstOrder.Derives.assumption
            (T := godel_quotation_theory)
            (Γ := Ε)
            (φ := application)
            (by simp [Ε])
      exact FirstOrder.Derives.falsumElim <|
        gq_standard_token_sequence_term_application_falsum_of_second_not_left
          tokens hOne hApplication

/--
标准 token 串的对象定义域若为 `1`，则外部输入长度也必须为 `1`。

该辅助结论只比较两个标准 numeral，不依赖串内 token 的具体值。
-/
private theorem
    gq_standard_token_sequence_falsum_of_domain_one_of_length_ne_one
    {Γ : Context signature}
    (tokens : List Nat)
    (hLength : tokens.length ≠ 1)
    (hDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(standard_token_sequence tokens) ≐ₘ
          numₘ(1)) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  have hStandardDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(standard_token_sequence tokens) ≐ₘ
          numₘ(tokens.length) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_token_sequence_domain_eq_length tokens
  have hNumeralEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(tokens.length) ≐ₘ numₘ(1) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm
        hStandardDomain)
      hDomain
  exact FirstOrder.Derives.negElim
    hNumeralEquality
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_ne
            hLength)

/--
非 singleton 的标准 token 串不可能来自变量或常元两个基础项分支。

这里只消费符号码的有限 singleton 结构，不反演其中的对象自然数编号。
-/
theorem
    gq_standard_token_sequence_base_symbol_falsum_of_length_ne_one
    {Γ : Context signature}
    (tokens : List Nat)
    (hLength : tokens.length ≠ 1)
    (hBase :
      Γ ⊢ₘ[godel_quotation_theory]
        ((standard_token_sequence tokens ∈ₘ VarSymₘ) ∨ₘ
          (standard_token_sequence tokens ∈ₘ ConstSymₘ))) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  let code : SetTerm :=
    standard_token_sequence tokens
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible tokens
  have hClosed :
      Term.freeSupport code = [] := by
    simp [code]
  apply FirstOrder.Derives.disjElim hBase
  · let Δ : Context signature :=
      (code ∈ₘ VarSymₘ) :: Γ
    have hVariable :
        Δ ⊢ₘ[godel_quotation_theory]
          code ∈ₘ VarSymₘ :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hStructure :
        Δ ⊢ₘ[godel_quotation_theory]
          (finite_sequence_condition code ∧ₘ
            (domₘ(code) ≐ₘ numₘ(1))) :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ])
          (gq_variable_symbol_member_implies_finite_domain_one
            code hCode))
        hVariable
    exact
      gq_standard_token_sequence_falsum_of_domain_one_of_length_ne_one
        tokens hLength
        (by
          simpa [code] using
            FirstOrder.Derives.conjElimRight
              hStructure)
  · let Δ : Context signature :=
      (code ∈ₘ ConstSymₘ) :: Γ
    have hConstant :
        Δ ⊢ₘ[godel_quotation_theory]
          code ∈ₘ ConstSymₘ :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hStructure :
        Δ ⊢ₘ[godel_quotation_theory]
          (finite_sequence_condition code ∧ₘ
            (domₘ(code) ≐ₘ numₘ(1))) :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ])
          (gq_constant_symbol_member_implies_finite_domain_one
            code hCode
            (by rw [hClosed]; exact List.not_mem_nil)))
        hConstant
    exact
      gq_standard_token_sequence_falsum_of_domain_one_of_length_ne_one
        tokens hLength
        (by
          simpa [code] using
            FirstOrder.Derives.conjElimRight
              hStructure)

/--
第二位不是左括号且长度不为 `1` 时，标准 token 串不可能是项码。

这是 raw term parser 的 atom 失败分支：应用分支由固定左括号拒绝，两个基础分支
由 singleton 定义域拒绝。
-/
theorem
    gq_standard_token_sequence_term_code_not_of_second_not_left_of_length_ne_one
    (tokens : List Nat)
    (hOne :
      tokens[1]? ≠
        some (Numbered.logical_token
          .leftParenthesis))
    (hLength : tokens.length ≠ 1) :
    ⊢ₘ[godel_quotation_theory]
      ¬ₘ (standard_token_sequence tokens ∈ₘ
        TermCodeₘ) := by
  let membership : SetFormula :=
    standard_token_sequence tokens ∈ₘ TermCodeₘ
  nd_apply FirstOrder.Derives.negIntro
  let Γ : Context signature := [membership]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ∈ₘ
          TermCodeₘ := by
    simpa [Γ, membership] using
      FirstOrder.Derives.assumption
        (T := godel_quotation_theory)
        (Γ := Γ)
        (φ := membership)
        (by simp [Γ])
  have hBase :
      Γ ⊢ₘ[godel_quotation_theory]
        ((standard_token_sequence tokens ∈ₘ VarSymₘ) ∨ₘ
          (standard_token_sequence tokens ∈ₘ ConstSymₘ)) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ])
        (gq_standard_token_sequence_term_code_implies_base_symbol_of_second_not_left
          tokens hOne))
      hMember
  exact
    gq_standard_token_sequence_base_symbol_falsum_of_length_ne_one
      tokens hLength hBase

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
