import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceConditionRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.CheckedSyntax
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Substitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CertifiedSequenceCodeSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.Failure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.Opening

/-!
# ZFC 逻辑证书条件的对象层拒绝

本模块处理完整逻辑证书条件的负向回放。空 payload 分支中，
自然数序列码 `0` 把证书序列定义域压入 `S(0)`，而逻辑 transcript 主体又要求
该定义域等于某个后继；二者在对象层直接矛盾。非全称首行分支则只恢复
payload 的规范序列，在索引 `0` 读取一次闭包关系，并比较首两个 token。

证明只读取现有二元序列码关系的有界字段，不反演整条递归 trace，也不引入
模型、标准性或额外的内部验证层。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation
open Rosser

set_option autoImplicit false

namespace CertifiedProof

/--
成功行的头部 mismatch 排除该行标准 token 序列等于任意合法全称公式码。

证明只比较第 `0` 或第 `1` 个 token，不反演正文、替换或完整逻辑 transcript。
-/
theorem fs_zfc_support_raw_standard_row_falsum_of_universal_equality
    {Γ : Context signature}
    (tokens : List Nat)
    (hMismatch :
      FSFormulaUniversalHeadMismatch tokens)
    (boundVariable body : SetTerm)
    (hBoundVariable :
      Term.Admissible boundVariable SetSort.set)
    (hBody :
      Term.Admissible body SetSort.set)
    (hBoundVariableMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        boundVariable ∈ₘ VarSymₘ)
    (hBodyMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        body ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          forall_codeₘ(boundVariable, body)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hBodyCodeString :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        body ∈ₘ CodeStrₘ :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation
            (gq_formula_code_member_implies_code_string
              body hBody))
      hBodyMember
  have hUniversalOpening :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (((numₘ(0) ∈ₘ
              domₘ(forall_codeₘ(boundVariable, body))) ∧ₘ
            ((forall_codeₘ(boundVariable, body) ·ₘ
                numₘ(0)) ≐ₘ
              numₘ(Numbered.logical_token
                .leftParenthesis))) ∧ₘ
          (((numₘ(1) ∈ₘ
                domₘ(forall_codeₘ(boundVariable, body))) ∧ₘ
              ((forall_codeₘ(boundVariable, body) ·ₘ
                  numₘ(1)) ≐ₘ
                numₘ(Numbered.logical_token
                  .universal))) ∧ₘ
            ((numₘ(2) ∈ₘ
                domₘ(forall_codeₘ(boundVariable, body))) ∧ₘ
              ((forall_codeₘ(boundVariable, body) ·ₘ
                  numₘ(2)) ≐ₘ
                (boundVariable ·ₘ numₘ(0)))))) := by
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          FirstOrder.Derives.theory_weaken
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_godel_quotation
                hFormula)
            (gq_universal_formula_opening_inversion
              boundVariable body
              (hBoundVariable :=
                Term.check_admissible_complete
                  hBoundVariable)
              (hBody :=
                Term.check_admissible_complete hBody)))
      (FirstOrder.Derives.conjIntro
        hBoundVariableMember hBodyCodeString)
  cases hMismatch with
  | first actual hGet hNe =>
      have hUniversalPoint :=
        FirstOrder.Derives.conjElimLeft
          hUniversalOpening
      have hEqualityPoint :=
        gq_point_inversion_of_equality_of_theory
          (standard_token_sequence tokens)
          (forall_codeₘ(boundVariable, body))
          (numₘ(0))
          (numₘ(Numbered.logical_token
            .leftParenthesis))
          hEquality hUniversalPoint
          (hLeft := Term.check_admissible_complete <|
            standard_token_sequence_admissible tokens)
          (hRight := Term.check_admissible_complete <|
            universal_formula_code_term_admissible
              boundVariable body hBoundVariable hBody)
      have hStandardPoint :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            (standard_token_sequence tokens ·ₘ
                numₘ(0)) ≐ₘ
              numₘ(actual) :=
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            fs_zfc_support_raw_derives_of_standard_sequence
              (standard_token_sequence_apply_getElem?
                tokens hGet)
      have hTokenEquality :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            numₘ(actual) ≐ₘ
              numₘ(Numbered.logical_token
                .leftParenthesis) :=
        Metatheory.Derives.equality_trans
          (Metatheory.Derives.equality_symm
            hStandardPoint)
          (FirstOrder.Derives.conjElimRight
            hEqualityPoint)
      exact fs_zfc_support_raw_falsum_of_numeral_equality
        hNe hTokenEquality
  | second actual hGet hNe =>
      have hUniversalPoint :=
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight
            hUniversalOpening
      have hEqualityPoint :=
        gq_point_inversion_of_equality_of_theory
          (standard_token_sequence tokens)
          (forall_codeₘ(boundVariable, body))
          (numₘ(1))
          (numₘ(Numbered.logical_token .universal))
          hEquality hUniversalPoint
          (hLeft := Term.check_admissible_complete <|
            standard_token_sequence_admissible tokens)
          (hRight := Term.check_admissible_complete <|
            universal_formula_code_term_admissible
              boundVariable body hBoundVariable hBody)
      have hStandardPoint :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            (standard_token_sequence tokens ·ₘ
                numₘ(1)) ≐ₘ
              numₘ(actual) :=
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            fs_zfc_support_raw_derives_of_standard_sequence
              (standard_token_sequence_apply_getElem?
                tokens hGet)
      have hTokenEquality :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            numₘ(actual) ≐ₘ
              numₘ(Numbered.logical_token .universal) :=
        Metatheory.Derives.equality_trans
          (Metatheory.Derives.equality_symm
            hStandardPoint)
          (FirstOrder.Derives.conjElimRight
            hEqualityPoint)
      exact fs_zfc_support_raw_falsum_of_numeral_equality
        hNe hTokenEquality

/-!
## Canonical 全称闭包的有限负向反演
-/

/--
标准非全称行不能成为 canonical 全称闭包关系的目标。

这里只打开 closure 自身的两个局部见证，并读取 body 的公式码字段与最终目标等式；
binder shift、替换 trace 与源码内容均不参与反演。
-/
private theorem
    fs_zfc_support_raw_canonical_forall_closure_falsum_of_standard_row_core
    {Γ : Context signature}
    (tokens : List Nat)
    (hReject :
      ∀ {Δ : Context signature} (body : SetTerm),
        Term.Admissible body SetSort.set →
          Δ ⊢ₘ[fs_zfc_support_raw_theory]
            canonical_outer_binder_variable_code_term ∈ₘ VarSymₘ →
          Δ ⊢ₘ[fs_zfc_support_raw_theory] body ∈ₘ FormulaCodeₘ →
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
                standard_token_sequence tokens ≐ₘ
                  forall_codeₘ(
                    canonical_outer_binder_variable_code_term,
                    body) →
              Δ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum)
    (sourceCode variableCode targetCode : SetTerm)
    (hSourceCode :
      Term.Admissible sourceCode SetSort.set)
    (hVariableCode :
      Term.Admissible variableCode SetSort.set)
    (hTargetCode :
      Term.Admissible targetCode SetSort.set)
    (hShiftedFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, 460) ∉
          Formula.freeSupport formula)
    (hBodyFresh :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, 461) ∉
          Formula.freeSupport formula)
    (hTargetEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ targetCode)
    (hClosure :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_forall_closure_code_condition
          sourceCode variableCode targetCode) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  let closureBody : SetFormula :=
    (((canonical_free_variable_code_condition_with_id
          variableCode 470 ∧ₘ
        canonical_binder_shift_code_condition_with_ids
          sourceCode (x#460)
          462 463 464 465 466 467 468 469) ∧ₘ
      (code_substitution_spec
          (x#460) variableCode
          canonical_outer_binder_variable_code_term
          (x#461) ∧ₘ
        formula_codeₘ(x#461))) ∧ₘ
      (targetCode ≐ₘ
        forall_codeₘ(
          canonical_outer_binder_variable_code_term,
          x#461)))
  let bodyExists : SetFormula :=
    ∃ₘ[SetSort.set, 461], closureBody
  have hClosureAdmissible :
      Formula.Admissible
        (canonical_forall_closure_code_condition
          sourceCode variableCode targetCode) :=
    canonical_forall_closure_code_condition_admissible
      sourceCode variableCode targetCode
      hSourceCode hVariableCode hTargetCode
  have hBodyExistsAdmissible :
      Formula.Admissible bodyExists := by
    have hOpened :=
      Formula.Admissible.exists_openAt
        (term := (x#460 : SetTerm))
        SetSort.set hClosureAdmissible
        (set_variable_admissible 460)
    simpa [bodyExists, closureBody,
      canonical_forall_closure_code_condition,
      canonical_forall_closure_code_condition_with_ids,
      Formula.openAt_closeFreeAt] using hOpened
  have hClosureBodyAdmissible :
      Formula.Admissible closureBody := by
    have hOpened :=
      Formula.Admissible.exists_openAt
        (term := (x#461 : SetTerm))
        SetSort.set hBodyExistsAdmissible
        (set_variable_admissible 461)
    simpa [bodyExists, closureBody,
      Formula.openAt_closeFreeAt] using hOpened
  nd_apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 460)
    (body := bodyExists)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete
        hBodyExistsAdmissible)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · exact hShiftedFresh
  · exact List.not_mem_nil
  · simpa [bodyExists, closureBody,
      canonical_forall_closure_code_condition,
      canonical_forall_closure_code_condition_with_ids] using
      hClosure
  · let Δ₁ : Context signature := bodyExists :: Γ
    have hBodyExistsAt :
        Δ₁ ⊢ₘ[fs_zfc_support_raw_theory]
          bodyExists :=
      FirstOrder.Derives.assumption (by simp [Δ₁])
    nd_apply FirstOrder.Derives.exists_elim
      (T := fs_zfc_support_raw_theory)
      (Γ := Δ₁)
      (sort := SetSort.set)
      (eigen := 461)
      (body := closureBody)
      (conclusion := Formula.falsum)
      (hBodyCheck :=
        Formula.check_admissible_complete
          hClosureBodyAdmissible)
    · intro formula hFormula
      rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      simp only [Δ₁, List.mem_cons] at hFormula
      rcases hFormula with rfl | hFormula
      · simpa [bodyExists] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set 461 0 closureBody
      · exact hBodyFresh formula hFormula
    · exact List.not_mem_nil
    · simpa [bodyExists, closureBody] using hBodyExistsAt
    · let Δ₂ : Context signature := closureBody :: Δ₁
      have hClosureBodyAt :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            closureBody :=
        FirstOrder.Derives.assumption (by simp [Δ₂])
      have hBodyMember :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            x#461 ∈ₘ FormulaCodeₘ := by
        have hBodyCode :
            Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
              formula_codeₘ(x#461) := by
          simpa [closureBody] using
            FirstOrder.Derives.conjElimRight
              (FirstOrder.Derives.conjElimRight
                (FirstOrder.Derives.conjElimLeft
                  hClosureBodyAt))
        exact FirstOrder.Derives.iffElimRight
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Δ₂) (by simp) <|
              FirstOrder.Derives.theory_weaken
                (fun _ hFormula =>
                  fs_zfc_support_raw_contains_godel_quotation
                    hFormula)
                (gq_formula_code_definition_instance
                  (x#461)
                  (set_variable_admissible 461)))
          hBodyCode
      have hUniversalEquality :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            targetCode ≐ₘ
              forall_codeₘ(
                canonical_outer_binder_variable_code_term,
                x#461) := by
        simpa [closureBody] using
          FirstOrder.Derives.conjElimRight
            hClosureBodyAt
      have hRowEquality :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            standard_token_sequence tokens ≐ₘ
              forall_codeₘ(
                canonical_outer_binder_variable_code_term,
                x#461) :=
        Metatheory.Derives.equality_trans
          (FirstOrder.Derives.context_weaken
            (Γ := Γ) (Δ := Δ₂)
            (by
              intro formula hFormula
              simp [Δ₂, Δ₁, hFormula])
            hTargetEquality)
          hUniversalEquality
      have hBoundMember :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory]
            canonical_outer_binder_variable_code_term ∈ₘ
              VarSymₘ :=
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ₂) (by simp) <| by
            simpa [canonical_outer_binder_variable_code_term] using
              fs_zfc_support_raw_derives_of_godel_quotation
                (GodelQuotation.named_variable_code_mem_variable_symbols 1)
      exact hReject (x#461) (set_variable_admissible 461)
        hBoundMember hBodyMember hRowEquality

/--
Canonical closure 的公开负向接口。

内部见证新鲜性通过只含目标等式与 closure 条件的双前提上下文局部完成；
调用方只需证明三个公开项不含 `460/461`。
-/
private theorem
    fs_zfc_support_raw_canonical_forall_closure_falsum_of_standard_row_of_reject
    {Γ : Context signature}
    (tokens : List Nat)
    (hReject :
      ∀ {Δ : Context signature} (body : SetTerm),
        Term.Admissible body SetSort.set →
          Δ ⊢ₘ[fs_zfc_support_raw_theory]
            canonical_outer_binder_variable_code_term ∈ₘ VarSymₘ →
          Δ ⊢ₘ[fs_zfc_support_raw_theory] body ∈ₘ FormulaCodeₘ →
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
                standard_token_sequence tokens ≐ₘ
                  forall_codeₘ(
                    canonical_outer_binder_variable_code_term,
                    body) →
              Δ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum)
    (sourceCode variableCode targetCode : SetTerm)
    (hSourceCode :
      Term.Admissible sourceCode SetSort.set)
    (hVariableCode :
      Term.Admissible variableCode SetSort.set)
    (hTargetCode :
      Term.Admissible targetCode SetSort.set)
    (hShiftedFreshSource :
      (SetSort.set, 460) ∉
        Term.freeSupport sourceCode)
    (hShiftedFreshVariable :
      (SetSort.set, 460) ∉
        Term.freeSupport variableCode)
    (hShiftedFreshTarget :
      (SetSort.set, 460) ∉
        Term.freeSupport targetCode)
    (hBodyFreshSource :
      (SetSort.set, 461) ∉
        Term.freeSupport sourceCode)
    (hBodyFreshVariable :
      (SetSort.set, 461) ∉
        Term.freeSupport variableCode)
    (hBodyFreshTarget :
      (SetSort.set, 461) ∉
        Term.freeSupport targetCode)
    (hTargetEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ targetCode)
    (hClosure :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_forall_closure_code_condition
          sourceCode variableCode targetCode) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  let targetEquality : SetFormula :=
    standard_token_sequence tokens ≐ₘ targetCode
  let closure : SetFormula :=
    canonical_forall_closure_code_condition
      sourceCode variableCode targetCode
  let Δ : Context signature :=
    [closure, targetEquality]
  have hTargetEqualityAdmissible :
      Formula.Admissible targetEquality := by
    simpa [targetEquality] using
      Formula.Admissible.equal
        (standard_token_sequence_admissible tokens)
        hTargetCode
  have hClosureAdmissible :
      Formula.Admissible closure := by
    simpa [closure] using
      canonical_forall_closure_code_condition_admissible
        sourceCode variableCode targetCode
        hSourceCode hVariableCode hTargetCode
  have hFalsum :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        Formula.falsum := by
    apply
      fs_zfc_support_raw_canonical_forall_closure_falsum_of_standard_row_core
        tokens hReject
        sourceCode variableCode targetCode
        hSourceCode hVariableCode hTargetCode
    · intro formula hFormula
      simp only [Δ, List.mem_cons, List.not_mem_nil,
        or_false] at hFormula
      rcases hFormula with rfl | rfl
      · exact
          not_mem_freeSupport_canonical_forall_closure_code_condition
            (SetSort.set, 460)
            sourceCode variableCode targetCode
            hShiftedFreshSource
            hShiftedFreshVariable
            hShiftedFreshTarget
      · simpa [targetEquality, Formula.freeSupport,
          Term.freeSupport, Term.freeSupportList,
          standard_token_sequence_freeSupport_nil] using
          hShiftedFreshTarget
    · intro formula hFormula
      simp only [Δ, List.mem_cons, List.not_mem_nil,
        or_false] at hFormula
      rcases hFormula with rfl | rfl
      · exact
          not_mem_freeSupport_canonical_forall_closure_code_condition
            (SetSort.set, 461)
            sourceCode variableCode targetCode
            hBodyFreshSource
            hBodyFreshVariable
            hBodyFreshTarget
      · simpa [targetEquality, Formula.freeSupport,
          Term.freeSupport, Term.freeSupportList,
          standard_token_sequence_freeSupport_nil] using
          hBodyFreshTarget
    · simpa [Δ, targetEquality] using
        (FirstOrder.Derives.assumption
          (T := fs_zfc_support_raw_theory)
          (Γ := Δ)
          (φ := targetEquality)
          (by simp [Δ]))
    · simpa [Δ, closure] using
        (FirstOrder.Derives.assumption
          (T := fs_zfc_support_raw_theory)
          (Γ := Δ)
          (φ := closure)
          (by simp [Δ]))
  have hClosureImp :
      [targetEquality]
        ⊢ₘ[fs_zfc_support_raw_theory]
          closure ⟶ₘ Formula.falsum := by
    simpa [Δ] using
      FirstOrder.Derives.impIntro
        hFalsum
        (Formula.check_admissible_complete
          hClosureAdmissible)
  have hTargetImp :
      Derives fs_zfc_support_raw_theory [] (
        targetEquality ⟶ₘ
          (closure ⟶ₘ Formula.falsum)) :=
    FirstOrder.Derives.impIntro
      hClosureImp
      (Formula.check_admissible_complete
        hTargetEqualityAdmissible)
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        hTargetImp)
      (by simpa [targetEquality] using
        hTargetEquality))
    (by simpa [closure] using hClosure)

/-- 标准全称行的 binder 名不是 `1` 时，不能等于 canonical 全称构造码。 -/
theorem fs_zfc_support_raw_standard_universal_row_falsum_of_canonical_binder_ne
    {Γ : Context signature}
    (name : Nat)
    (bodyTokens : List Nat)
    (hName : name ≠ 1)
    (body : SetTerm)
    (hBody : Term.Admissible body SetSort.set)
    (hBoundMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_outer_binder_variable_code_term ∈ₘ VarSymₘ)
    (hBodyMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] body ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence
            (Numbered.universal_tokens name bodyTokens) ≐ₘ
          forall_codeₘ(
            canonical_outer_binder_variable_code_term,
            body)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  have hBodyCodeString :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] body ∈ₘ CodeStrₘ :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          fs_zfc_support_raw_derives_of_godel_quotation
            (gq_formula_code_member_implies_code_string body hBody))
      hBodyMember
  have hOpening :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (((numₘ(0) ∈ₘ
              domₘ(forall_codeₘ(
                canonical_outer_binder_variable_code_term,
                body))) ∧ₘ
            ((forall_codeₘ(
                canonical_outer_binder_variable_code_term,
                body) ·ₘ numₘ(0)) ≐ₘ
              numₘ(Numbered.logical_token .leftParenthesis))) ∧ₘ
          (((numₘ(1) ∈ₘ
                domₘ(forall_codeₘ(
                  canonical_outer_binder_variable_code_term,
                  body))) ∧ₘ
              ((forall_codeₘ(
                  canonical_outer_binder_variable_code_term,
                  body) ·ₘ numₘ(1)) ≐ₘ
                numₘ(Numbered.logical_token .universal))) ∧ₘ
            ((numₘ(2) ∈ₘ
                domₘ(forall_codeₘ(
                  canonical_outer_binder_variable_code_term,
                  body))) ∧ₘ
              ((forall_codeₘ(
                  canonical_outer_binder_variable_code_term,
                  body) ·ₘ numₘ(2)) ≐ₘ
                (canonical_outer_binder_variable_code_term ·ₘ
                  numₘ(0)))))) := by
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          FirstOrder.Derives.theory_weaken
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_godel_quotation hFormula)
            (gq_universal_formula_opening_inversion
              canonical_outer_binder_variable_code_term body))
      (FirstOrder.Derives.conjIntro
        hBoundMember hBodyCodeString)
  have hPoint :=
    gq_point_inversion_of_equality_of_theory
      (standard_token_sequence
        (Numbered.universal_tokens name bodyTokens))
      (forall_codeₘ(
        canonical_outer_binder_variable_code_term,
        body))
      (numₘ(2))
      (canonical_outer_binder_variable_code_term ·ₘ numₘ(0))
      hEquality
      (FirstOrder.Derives.conjElimRight
        (FirstOrder.Derives.conjElimRight hOpening))
  have hStandardPoint :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (standard_token_sequence
            (Numbered.universal_tokens name bodyTokens) ·ₘ
          numₘ(2)) ≐ₘ
            numₘ(Numbered.variable_token name) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_standard_sequence
          (standard_token_sequence_apply_getElem?
            (Numbered.universal_tokens name bodyTokens) (by
              simp [Numbered.universal_tokens]))
  have hOuterPoint :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (canonical_outer_binder_variable_code_term ·ₘ numₘ(0)) ≐ₘ
          numₘ(Numbered.variable_token 1) := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
    exact FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_quotation_occurrence hFormula) <| by
          simpa [canonical_outer_binder_variable_code_term,
            Numbered.named_variable_code, bound_name] using
            named_variable_code_apply_zero 1
  have hTokenEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(Numbered.variable_token name) ≐ₘ
          numₘ(Numbered.variable_token 1) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hStandardPoint) <|
        Metatheory.Derives.equality_trans
          (FirstOrder.Derives.conjElimRight hPoint)
          hOuterPoint
  exact fs_zfc_support_raw_falsum_of_numeral_equality
    (variable_token_ne_variable_token hName) hTokenEquality

/-- Canonical closure 的公开非全称头错配出口。 -/
theorem
    fs_zfc_support_raw_canonical_forall_closure_falsum_of_standard_row
    {Γ : Context signature}
    (tokens : List Nat)
    (hMismatch :
      FSFormulaUniversalHeadMismatch tokens)
    (sourceCode variableCode targetCode : SetTerm)
    (hSourceCode :
      Term.Admissible sourceCode SetSort.set)
    (hVariableCode :
      Term.Admissible variableCode SetSort.set)
    (hTargetCode :
      Term.Admissible targetCode SetSort.set)
    (hShiftedFreshSource :
      (SetSort.set, 460) ∉ Term.freeSupport sourceCode)
    (hShiftedFreshVariable :
      (SetSort.set, 460) ∉ Term.freeSupport variableCode)
    (hShiftedFreshTarget :
      (SetSort.set, 460) ∉ Term.freeSupport targetCode)
    (hBodyFreshSource :
      (SetSort.set, 461) ∉ Term.freeSupport sourceCode)
    (hBodyFreshVariable :
      (SetSort.set, 461) ∉ Term.freeSupport variableCode)
    (hBodyFreshTarget :
      (SetSort.set, 461) ∉ Term.freeSupport targetCode)
    (hTargetEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ targetCode)
    (hClosure :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_forall_closure_code_condition
          sourceCode variableCode targetCode) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum :=
  fs_zfc_support_raw_canonical_forall_closure_falsum_of_standard_row_of_reject
    tokens
    (fun body hBody hBoundMember hBodyMember hEquality =>
      fs_zfc_support_raw_standard_row_falsum_of_universal_equality
        tokens hMismatch
        canonical_outer_binder_variable_code_term body
        (variable_code_term_admissible
          (numₘ(1)) (finite_numeral_term_admissible 1))
        hBody hBoundMember hBodyMember hEquality)
    sourceCode variableCode targetCode
    hSourceCode hVariableCode hTargetCode
    hShiftedFreshSource hShiftedFreshVariable hShiftedFreshTarget
    hBodyFreshSource hBodyFreshVariable hBodyFreshTarget
    hTargetEquality hClosure

/-- Canonical closure 的公开 binder 名错配出口。 -/
theorem fs_zfc_support_raw_canonical_forall_closure_falsum_of_binder_ne
    {Γ : Context signature}
    (name : Nat)
    (bodyTokens : List Nat)
    (hName : name ≠ 1)
    (sourceCode variableCode targetCode : SetTerm)
    (hSourceCode :
      Term.Admissible sourceCode SetSort.set)
    (hVariableCode :
      Term.Admissible variableCode SetSort.set)
    (hTargetCode :
      Term.Admissible targetCode SetSort.set)
    (hShiftedFreshSource :
      (SetSort.set, 460) ∉ Term.freeSupport sourceCode)
    (hShiftedFreshVariable :
      (SetSort.set, 460) ∉ Term.freeSupport variableCode)
    (hShiftedFreshTarget :
      (SetSort.set, 460) ∉ Term.freeSupport targetCode)
    (hBodyFreshSource :
      (SetSort.set, 461) ∉ Term.freeSupport sourceCode)
    (hBodyFreshVariable :
      (SetSort.set, 461) ∉ Term.freeSupport variableCode)
    (hBodyFreshTarget :
      (SetSort.set, 461) ∉ Term.freeSupport targetCode)
    (hTargetEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence
            (Numbered.universal_tokens name bodyTokens) ≐ₘ
          targetCode)
    (hClosure :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_forall_closure_code_condition
          sourceCode variableCode targetCode) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum :=
  fs_zfc_support_raw_canonical_forall_closure_falsum_of_standard_row_of_reject
    (Numbered.universal_tokens name bodyTokens)
    (fun body hBody hBoundMember hBodyMember hEquality =>
      fs_zfc_support_raw_standard_universal_row_falsum_of_canonical_binder_ne
        name bodyTokens hName body hBody
        hBoundMember hBodyMember hEquality)
    sourceCode variableCode targetCode
    hSourceCode hVariableCode hTargetCode
    hShiftedFreshSource hShiftedFreshVariable hShiftedFreshTarget
    hBodyFreshSource hBodyFreshVariable hBodyFreshTarget
    hTargetEquality hClosure

theorem fs_zfc_support_raw_logical_mem_successor_self
    {Γ : Context signature}
    (source : SetTerm)
    (hSource : Term.Admissible source SetSort.set) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      source ∈ₘ Sₘ(source) := by
  apply FirstOrder.Derives.context_weaken
    (Γ := [])
    (Δ := Γ)
    (by simp)
  apply fs_zfc_support_raw_derives_of_standard_sequence
  apply FirstOrder.Derives.theory_weaken
    (fun _ hFormula =>
      Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inl hFormula)
  exact mem_successor_self source hSource

/-! ## Numeral payload 的规范定义域 -/

/--
Numeral payload 的自然数序列条件直接推出规范序列等式。

把唯一性定理隔离在单前提上下文中，可使 trace 新鲜性只依赖编码条件自身的
自由支持收缩，而不传播调用方上下文。
-/
theorem
    fs_zfc_support_raw_nat_sequence_condition_unique_imp
    (sequence : SetTerm)
    (tokens : List Nat)
    (traceId indexId : FreeVarId)
    (hSequence :
      Term.Admissible sequence SetSort.set)
    (hTraceNeIndex :
      traceId ≠ indexId)
    (hTraceFreshSequence :
      (SetSort.set, traceId) ∉
        Term.freeSupport sequence)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉
        Term.freeSupport sequence) :
    Derives fs_zfc_support_raw_theory [] (
      nat_sequence_code_condition_with_ids
          sequence
          (numₘ(nat_sequence_code_value tokens))
          traceId indexId ⟶ₘ
        sequence ≐ₘ
          standard_token_sequence tokens) := by
  let condition : SetFormula :=
    nat_sequence_code_condition_with_ids
      sequence
      (numₘ(nat_sequence_code_value tokens))
      traceId indexId
  have hConditionAdmissible :
      Formula.Admissible condition := by
    simpa [condition] using
      nat_sequence_code_condition_with_ids_admissible
        sequence
        (numₘ(nat_sequence_code_value tokens))
        traceId indexId
        hSequence
        (finite_numeral_term_admissible
          (nat_sequence_code_value tokens))
  nd_apply FirstOrder.Derives.impIntro
    (hAntecedentCheck :=
      Formula.check_admissible_complete
        hConditionAdmissible)
  let Γ : Context signature := [condition]
  apply
    fs_zfc_support_raw_nat_sequence_code_condition_unique_of_code_equality
      sequence
      (numₘ(nat_sequence_code_value tokens))
      tokens traceId indexId
      hSequence
      (finite_numeral_term_admissible
        (nat_sequence_code_value tokens))
      hTraceNeIndex
      hTraceFreshSequence
      hIndexFreshSequence
  · rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  · intro formula hFormula
    simp only [List.mem_singleton] at hFormula
    subst formula
    intro hMember
    rcases
        nat_sequence_code_condition_with_ids_freeSupport_subset
          sequence
          (numₘ(nat_sequence_code_value tokens))
          traceId indexId
          (SetSort.set, traceId) hMember with
      hMember | hMember
    · exact hTraceFreshSequence hMember
    · simp [finite_numeral_term_freeSupport] at hMember
  · simpa [condition] using
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ)
        (φ := condition)
        (by simp [Γ])
        (Formula.check_admissible_complete
          hConditionAdmissible))
  · exact FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set)
      (numₘ(nat_sequence_code_value tokens))

/--
长度至少二的规范序列若定义域等于某个后继，则该末索引严格大于 `0`。

证明只有限枚举末索引在规范定义域中的 numeral 值。
-/
theorem
    fs_zfc_support_raw_zero_mem_last_of_standard_sequence
    {Γ : Context signature}
    (sequence lastIndex : SetTerm)
    (tokens : List Nat)
    (hSequence :
      Term.Admissible sequence SetSort.set)
    (hLastIndex :
      Term.Admissible lastIndex SetSort.set)
    (hLength :
      2 ≤ tokens.length)
    (hSequenceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence ≐ₘ standard_token_sequence tokens)
    (hDomainSuccessor :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ Sₘ(lastIndex)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      numₘ(0) ∈ₘ lastIndex := by
  have hDomainEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ
          domₘ(standard_token_sequence tokens) :=
    domain_term_congr_of_equality
      sequence (standard_token_sequence tokens)
      hSequence
      (standard_token_sequence_admissible tokens)
      hSequenceEquality
  have hStandardDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(standard_token_sequence tokens) ≐ₘ
          numₘ(tokens.length) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_standard_sequence
          (standard_token_sequence_domain_eq_length tokens)
  have hDomainLength :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ numₘ(tokens.length) :=
    Metatheory.Derives.equality_trans
      hDomainEquality hStandardDomain
  have hLastMemberSuccessor :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        lastIndex ∈ₘ Sₘ(lastIndex) :=
    fs_zfc_support_raw_logical_mem_successor_self
      lastIndex hLastIndex
  have hLastMemberDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        lastIndex ∈ₘ domₘ(sequence) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        lastIndex
        (domₘ(sequence)) (Sₘ(lastIndex))
        hLastIndex
        (domain_term_admissible sequence hSequence)
        (successor_term_admissible
          lastIndex hLastIndex)
        hDomainSuccessor)
      hLastMemberSuccessor
  have hLastMemberLength :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        lastIndex ∈ₘ numₘ(tokens.length) :=
    FirstOrder.Derives.iffElimRight
      (membership_right_iff_of_equality
        lastIndex
        (domₘ(sequence)) (numₘ(tokens.length))
        hLastIndex
        (domain_term_admissible sequence hSequence)
        (finite_numeral_term_admissible tokens.length)
        hDomainLength)
      hLastMemberDomain
  apply
    fs_zfc_support_raw_finite_numeral_member_elim_context
      tokens.length lastIndex
      (numₘ(0) ∈ₘ lastIndex)
      hLastIndex
      (membership_formula_admissible
        (finite_numeral_term_admissible 0)
        hLastIndex)
      hLastMemberLength
  intro index hIndex
  let Δ : Context signature :=
    (lastIndex ≐ₘ numₘ(index)) :: Γ
  have hIndexEquality :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        lastIndex ≐ₘ numₘ(index) :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hSuccessorEquality :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        Sₘ(lastIndex) ≐ₘ Sₘ(numₘ(index)) :=
    successor_term_congr_of_equality
      lastIndex (numₘ(index))
      hLastIndex
      (finite_numeral_term_admissible index)
      hIndexEquality
  have hDomainIndex :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sequence) ≐ₘ numₘ(index + 1) := by
    simpa [finite_numeral_term, successor_term] using
      Metatheory.Derives.equality_trans
        (FirstOrder.Derives.context_weaken_cons
          hDomainSuccessor)
        hSuccessorEquality
  have hLengthEquality :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(tokens.length) ≐ₘ numₘ(index + 1) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm
        (FirstOrder.Derives.context_weaken_cons
          hDomainLength))
      hDomainIndex
  by_cases hLast : tokens.length = index + 1
  · have hZeroIndex :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(0) ∈ₘ numₘ(index) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) <|
          fs_zfc_support_raw_derives_of_standard_sequence
            (standard_sequence_finite_numeral_mem_of_lt
              0 index (by omega))
    exact FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(0)) lastIndex (numₘ(index))
        (finite_numeral_term_admissible 0)
        hLastIndex
        (finite_numeral_term_admissible index)
        hIndexEquality)
      hZeroIndex
  · exact FirstOrder.Derives.falsumElim
      (fs_zfc_support_raw_falsum_of_numeral_equality
        hLast hLengthEquality)

/-! ## 三层有界存在见证的反证封装 -/

/--
一次性打开逻辑 transcript 的三层有界见证并闭合否定。

每层 guard 与其 witness 同时进入分支上下文；末层只把主体投影给调用方，
因此负向算法无需重新证明序列空间事实。
-/
theorem fs_zfc_support_raw_logical_exists_three_neg
    (body : SetFormula)
    (hBody : Formula.Admissible body)
    (hCase :
      ((x#ProofT.lc_last_index_id ∈ₘ
          domₘ(x#ProofT.lc_sequence_id)) ∧ₘ body) ::
        ((x#ProofT.lc_formula_trace_id ∈ₘ
            seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
          (∃ₘ[SetSort.set, ProofT.lc_last_index_id],
            (x#ProofT.lc_last_index_id ∈ₘ
                domₘ(x#ProofT.lc_sequence_id)) ∧ₘ body)) ::
        ((x#ProofT.lc_sequence_id ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
          (∃ₘ[SetSort.set, ProofT.lc_formula_trace_id],
            (x#ProofT.lc_formula_trace_id ∈ₘ
                seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
              (∃ₘ[SetSort.set, ProofT.lc_last_index_id],
                (x#ProofT.lc_last_index_id ∈ₘ
                    domₘ(x#ProofT.lc_sequence_id)) ∧ₘ body))) ::
        [(∃ₘ[SetSort.set, ProofT.lc_sequence_id],
          (x#ProofT.lc_sequence_id ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
            (∃ₘ[SetSort.set, ProofT.lc_formula_trace_id],
              (x#ProofT.lc_formula_trace_id ∈ₘ
                  seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
                (∃ₘ[SetSort.set, ProofT.lc_last_index_id],
                  (x#ProofT.lc_last_index_id ∈ₘ
                      domₘ(x#ProofT.lc_sequence_id)) ∧ₘ body)))]
        ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ (∃ₘ[SetSort.set, ProofT.lc_sequence_id],
        (x#ProofT.lc_sequence_id ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
          (∃ₘ[SetSort.set, ProofT.lc_formula_trace_id],
            (x#ProofT.lc_formula_trace_id ∈ₘ
                seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
              (∃ₘ[SetSort.set, ProofT.lc_last_index_id],
                (x#ProofT.lc_last_index_id ∈ₘ
                    domₘ(x#ProofT.lc_sequence_id)) ∧ₘ body)))) := by
  let thirdMatrix : SetFormula :=
    (x#ProofT.lc_last_index_id ∈ₘ
        domₘ(x#ProofT.lc_sequence_id)) ∧ₘ body
  let thirdExists : SetFormula :=
    ∃ₘ[SetSort.set, ProofT.lc_last_index_id], thirdMatrix
  let secondMatrix : SetFormula :=
    (x#ProofT.lc_formula_trace_id ∈ₘ
        seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ thirdExists
  let secondExists : SetFormula :=
    ∃ₘ[SetSort.set, ProofT.lc_formula_trace_id], secondMatrix
  let firstMatrix : SetFormula :=
    (x#ProofT.lc_sequence_id ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
      secondExists
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, ProofT.lc_sequence_id], firstMatrix
  have hThirdMatrix :
      Formula.Admissible thirdMatrix := by
    unfold thirdMatrix
    exact Formula.Admissible.conj
      (membership_formula_admissible
        (set_variable_admissible ProofT.lc_last_index_id)
        (domain_term_admissible
          (x#ProofT.lc_sequence_id)
          (set_variable_admissible ProofT.lc_sequence_id)))
      hBody
  have hThirdExists :
      Formula.Admissible thirdExists := by
    simpa [thirdExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set ProofT.lc_last_index_id hThirdMatrix
  have hSecondMatrix :
      Formula.Admissible secondMatrix := by
    unfold secondMatrix
    exact Formula.Admissible.conj
      (membership_formula_admissible
        (set_variable_admissible ProofT.lc_formula_trace_id)
        (nonempty_finite_sequence_space_term_admissible
          FormulaCodeₘ formula_code_set_term_admissible))
      hThirdExists
  have hSecondExists :
      Formula.Admissible secondExists := by
    simpa [secondExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set ProofT.lc_formula_trace_id hSecondMatrix
  have hFirstMatrix :
      Formula.Admissible firstMatrix := by
    unfold firstMatrix
    exact Formula.Admissible.conj
      (membership_formula_admissible
        (set_variable_admissible ProofT.lc_sequence_id)
        (finite_sequence_space_term_admissible
          ωₘ omega_term_admissible))
      hSecondExists
  have hCondition :
      Formula.Admissible condition := by
    simpa [condition] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set ProofT.lc_sequence_id hFirstMatrix
  have hFirstFreshCondition :
      (SetSort.set, ProofT.lc_sequence_id) ∉
        Formula.freeSupport condition := by
    simpa [condition] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set ProofT.lc_sequence_id 0 firstMatrix
  have hSecondOwnFresh :
      (SetSort.set, ProofT.lc_formula_trace_id) ∉
        Formula.freeSupport secondExists := by
    simpa [secondExists] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set ProofT.lc_formula_trace_id 0 secondMatrix
  have hSecondFreshFirstMatrix :
      (SetSort.set, ProofT.lc_formula_trace_id) ∉
        Formula.freeSupport firstMatrix := by
    intro hMember
    change
      (SetSort.set, ProofT.lc_formula_trace_id) ∈
        (SetSort.set, ProofT.lc_sequence_id) ::
          Formula.freeSupport secondExists at hMember
    rcases List.mem_cons.mp hMember with hEqual | hTail
    · have hNe :
          (SetSort.set, ProofT.lc_formula_trace_id) ≠
            (SetSort.set, ProofT.lc_sequence_id) := by
        native_decide
      exact hNe hEqual
    · exact hSecondOwnFresh hTail
  have hSecondFreshCondition :
      (SetSort.set, ProofT.lc_formula_trace_id) ∉
        Formula.freeSupport condition := by
    simpa [condition] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, ProofT.lc_formula_trace_id)
        SetSort.set ProofT.lc_sequence_id 0 firstMatrix
        hSecondFreshFirstMatrix
  have hThirdOwnFresh :
      (SetSort.set, ProofT.lc_last_index_id) ∉
        Formula.freeSupport thirdExists := by
    simpa [thirdExists] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set ProofT.lc_last_index_id 0 thirdMatrix
  have hThirdFreshSecondMatrix :
      (SetSort.set, ProofT.lc_last_index_id) ∉
        Formula.freeSupport secondMatrix := by
    intro hMember
    change
      (SetSort.set, ProofT.lc_last_index_id) ∈
        (SetSort.set, ProofT.lc_formula_trace_id) ::
          Formula.freeSupport thirdExists at hMember
    rcases List.mem_cons.mp hMember with hEqual | hTail
    · have hNe :
          (SetSort.set, ProofT.lc_last_index_id) ≠
            (SetSort.set, ProofT.lc_formula_trace_id) := by
        native_decide
      exact hNe hEqual
    · exact hThirdOwnFresh hTail
  have hThirdFreshSecondExists :
      (SetSort.set, ProofT.lc_last_index_id) ∉
        Formula.freeSupport secondExists := by
    simpa [secondExists] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, ProofT.lc_last_index_id)
        SetSort.set ProofT.lc_formula_trace_id 0 secondMatrix
        hThirdFreshSecondMatrix
  have hThirdFreshFirstMatrix :
      (SetSort.set, ProofT.lc_last_index_id) ∉
        Formula.freeSupport firstMatrix := by
    intro hMember
    change
      (SetSort.set, ProofT.lc_last_index_id) ∈
        (SetSort.set, ProofT.lc_sequence_id) ::
          Formula.freeSupport secondExists at hMember
    rcases List.mem_cons.mp hMember with hEqual | hTail
    · have hNe :
          (SetSort.set, ProofT.lc_last_index_id) ≠
            (SetSort.set, ProofT.lc_sequence_id) := by
        native_decide
      exact hNe hEqual
    · exact hThirdFreshSecondExists hTail
  have hThirdFreshCondition :
      (SetSort.set, ProofT.lc_last_index_id) ∉
        Formula.freeSupport condition := by
    simpa [condition] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, ProofT.lc_last_index_id)
        SetSort.set ProofT.lc_sequence_id 0 firstMatrix
        hThirdFreshFirstMatrix
  nd_apply FirstOrder.Derives.negIntro
    (T := fs_zfc_support_raw_theory)
    (Γ := ([] : Context signature))
    (body := condition)
    (hBodyCheck := Formula.check_admissible_complete hCondition)
  let Γ : Context signature := [condition]
  have hConditionAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] condition :=
    FirstOrder.Derives.assumption (by simp [Γ])
  nd_apply FirstOrder.Derives.exists_elim
    (T := fs_zfc_support_raw_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := ProofT.lc_sequence_id)
    (body := firstMatrix)
    (conclusion := Formula.falsum)
    (hBodyCheck := Formula.check_admissible_complete hFirstMatrix)
  · intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    simp only [Γ, List.mem_singleton] at hFormula
    subst formula
    exact hFirstFreshCondition
  · exact List.not_mem_nil
  · simpa [condition, firstMatrix] using hConditionAt
  · let Δ₁ : Context signature := firstMatrix :: Γ
    have hFirstMatrixAt :
        Δ₁ ⊢ₘ[fs_zfc_support_raw_theory] firstMatrix :=
      FirstOrder.Derives.assumption (by simp [Δ₁])
    have hSecondExistsAt :
        Δ₁ ⊢ₘ[fs_zfc_support_raw_theory] secondExists :=
      FirstOrder.Derives.conjElimRight hFirstMatrixAt
    nd_apply FirstOrder.Derives.exists_elim
      (T := fs_zfc_support_raw_theory)
      (Γ := Δ₁)
      (sort := SetSort.set)
      (eigen := ProofT.lc_formula_trace_id)
      (body := secondMatrix)
      (conclusion := Formula.falsum)
      (hBodyCheck := Formula.check_admissible_complete hSecondMatrix)
    · intro formula hFormula
      rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      simp only [Δ₁, Γ, List.mem_cons,
        List.not_mem_nil, or_false] at hFormula
      rcases hFormula with rfl | rfl
      · exact hSecondFreshFirstMatrix
      · exact hSecondFreshCondition
    · exact List.not_mem_nil
    · exact hSecondExistsAt
    · let Δ₂ : Context signature := secondMatrix :: Δ₁
      have hSecondMatrixAt :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory] secondMatrix :=
        FirstOrder.Derives.assumption (by simp [Δ₂])
      have hThirdExistsAt :
          Δ₂ ⊢ₘ[fs_zfc_support_raw_theory] thirdExists :=
        FirstOrder.Derives.conjElimRight hSecondMatrixAt
      nd_apply FirstOrder.Derives.exists_elim
        (T := fs_zfc_support_raw_theory)
        (Γ := Δ₂)
        (sort := SetSort.set)
        (eigen := ProofT.lc_last_index_id)
        (body := thirdMatrix)
        (conclusion := Formula.falsum)
        (hBodyCheck := Formula.check_admissible_complete hThirdMatrix)
      · intro formula hFormula
        rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
        exact List.not_mem_nil
      · intro formula hFormula
        simp only [Δ₂, Δ₁, Γ, List.mem_cons,
          List.not_mem_nil, or_false] at hFormula
        rcases hFormula with rfl | rfl | rfl
        · exact hThirdFreshSecondMatrix
        · exact hThirdFreshFirstMatrix
        · exact hThirdFreshCondition
      · exact List.not_mem_nil
      · exact hThirdExistsAt
      · simpa [Δ₂, Δ₁, Γ, condition, firstMatrix,
          secondExists, secondMatrix, thirdExists, thirdMatrix] using
          hCase

/-! ## 完整逻辑证书主体的规范打开 -/

/--
从完整逻辑证书条件的可容许性中规范打开三个外层 witness。

该引理只处理语法构造，不使用任何对象理论结论。
-/
theorem fs_zfc_logical_certificate_body_admissible
    (formulaCode certificatePayload : SetTerm)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hCertificatePayload :
      Term.Admissible certificatePayload SetSort.set) :
    Formula.Admissible
      (logical_certificate_body_with_ids
        formulaCode certificatePayload
        (x#ProofT.lc_sequence_id)
        (x#ProofT.lc_formula_trace_id)
        (x#ProofT.lc_last_index_id)
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id) := by
  let body : SetFormula :=
    logical_certificate_body_with_ids
      formulaCode certificatePayload
      (x#ProofT.lc_sequence_id)
      (x#ProofT.lc_formula_trace_id)
      (x#ProofT.lc_last_index_id)
      ProofT.lc_sequence_id
      ProofT.lc_formula_trace_id
      ProofT.lc_last_index_id
      ProofT.lc_line_index_id
      ProofT.lc_code_trace_id
      ProofT.lc_code_index_id
  let thirdMatrix : SetFormula :=
    (x#ProofT.lc_last_index_id ∈ₘ
        domₘ(x#ProofT.lc_sequence_id)) ∧ₘ body
  let thirdExists : SetFormula :=
    ∃ₘ[SetSort.set, ProofT.lc_last_index_id], thirdMatrix
  let secondMatrix : SetFormula :=
    (x#ProofT.lc_formula_trace_id ∈ₘ
        seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ thirdExists
  let secondExists : SetFormula :=
    ∃ₘ[SetSort.set, ProofT.lc_formula_trace_id], secondMatrix
  let firstMatrix : SetFormula :=
    (x#ProofT.lc_sequence_id ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
      secondExists
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, ProofT.lc_sequence_id], firstMatrix
  have hCondition :
      Formula.Admissible condition := by
    simpa [condition, firstMatrix, secondExists, secondMatrix,
      thirdExists, thirdMatrix,
      logical_certificate_condition_with_ids, body] using
      logical_certificate_condition_with_ids_admissible
        formulaCode certificatePayload
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id
        hFormulaCode hCertificatePayload
  have hFirstOpen :=
    Formula.Admissible.exists_openAt
      (term := (x#ProofT.lc_sequence_id : SetTerm))
      SetSort.set hCondition
      (set_variable_admissible ProofT.lc_sequence_id)
  have hFirstMatrix :
      Formula.Admissible firstMatrix := by
    simpa [condition, firstMatrix,
      Formula.openAt_closeFreeAt] using hFirstOpen
  have hSecondExists :
      Formula.Admissible secondExists :=
    Formula.Admissible.conj_right hFirstMatrix
  have hSecondOpen :=
    Formula.Admissible.exists_openAt
      (term := (x#ProofT.lc_formula_trace_id : SetTerm))
      SetSort.set hSecondExists
      (set_variable_admissible ProofT.lc_formula_trace_id)
  have hSecondMatrix :
      Formula.Admissible secondMatrix := by
    simpa [secondExists, secondMatrix,
      Formula.openAt_closeFreeAt] using hSecondOpen
  have hThirdExists :
      Formula.Admissible thirdExists :=
    Formula.Admissible.conj_right hSecondMatrix
  have hThirdOpen :=
    Formula.Admissible.exists_openAt
      (term := (x#ProofT.lc_last_index_id : SetTerm))
      SetSort.set hThirdExists
      (set_variable_admissible ProofT.lc_last_index_id)
  have hThirdMatrix :
      Formula.Admissible thirdMatrix := by
    simpa [thirdExists, thirdMatrix,
      Formula.openAt_closeFreeAt] using hThirdOpen
  simpa [thirdMatrix, body] using
    Formula.Admissible.conj_right hThirdMatrix

/-! ## 空 payload 拒绝 -/

/--
自然数序列 payload 为 `0` 时，完整逻辑证书条件不可成立。

这是完整 logical checker 的空证书失败分支所需的地面对象层接口。它只消费
序列码关系中的定义域上界，不调用序列唯一性或递归 trace 反演。
-/
theorem fs_zfc_support_raw_logical_certificate_condition_neg_of_empty_payload
    (formulaCode : SetTerm)
    (hFormulaCode :
      GodelQuotation.Numbered.CodeBoundary formulaCode) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_certificate_condition_with_ids
        formulaCode (numₘ(0))
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id) := by
  let body : SetFormula :=
    logical_certificate_body_with_ids
      formulaCode (numₘ(0))
      (x#ProofT.lc_sequence_id)
      (x#ProofT.lc_formula_trace_id)
      (x#ProofT.lc_last_index_id)
      ProofT.lc_sequence_id
      ProofT.lc_formula_trace_id
      ProofT.lc_last_index_id
      ProofT.lc_line_index_id
      ProofT.lc_code_trace_id
      ProofT.lc_code_index_id
  have hBodyAdmissible :
      Formula.Admissible body := by
    simpa [body] using
      fs_zfc_logical_certificate_body_admissible
        formulaCode (numₘ(0))
        hFormulaCode.1
        (finite_numeral_term_admissible 0)
  simpa [logical_certificate_condition_with_ids, body] using
    fs_zfc_support_raw_logical_exists_three_neg
      body hBodyAdmissible (by
        let thirdMatrix : SetFormula :=
          (x#ProofT.lc_last_index_id ∈ₘ
              domₘ(x#ProofT.lc_sequence_id)) ∧ₘ body
        let thirdExists : SetFormula :=
          ∃ₘ[SetSort.set, ProofT.lc_last_index_id], thirdMatrix
        let secondMatrix : SetFormula :=
          (x#ProofT.lc_formula_trace_id ∈ₘ
              seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ thirdExists
        let secondExists : SetFormula :=
          ∃ₘ[SetSort.set, ProofT.lc_formula_trace_id],
            secondMatrix
        let firstMatrix : SetFormula :=
          (x#ProofT.lc_sequence_id ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
            secondExists
        let condition : SetFormula :=
          ∃ₘ[SetSort.set, ProofT.lc_sequence_id],
            firstMatrix
        let Δ : Context signature :=
          thirdMatrix :: secondMatrix :: firstMatrix :: [condition]
        change Δ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum
        have hThirdMatrixAt :
            Δ ⊢ₘ[fs_zfc_support_raw_theory] thirdMatrix :=
          FirstOrder.Derives.assumption (by simp [Δ])
        have hBodyAt :
            Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
          FirstOrder.Derives.conjElimRight hThirdMatrixAt
        have hCertificateCondition :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              nat_sequence_code_condition_with_ids
                (x#ProofT.lc_sequence_id)
                (numₘ(0))
                ProofT.lc_code_trace_id
                ProofT.lc_code_index_id := by
          simpa [body, logical_certificate_body_with_ids,
            logical_certificate_conjunction] using
            FirstOrder.Derives.conjElimLeft hBodyAt
        have hDomainSuccessor :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              domₘ(x#ProofT.lc_sequence_id) ≐ₘ
                Sₘ(x#ProofT.lc_last_index_id) := by
          simpa [body, logical_certificate_body_with_ids,
            logical_certificate_conjunction] using
            FirstOrder.Derives.conjElimLeft
              (FirstOrder.Derives.conjElimRight
                (FirstOrder.Derives.conjElimRight
                  (FirstOrder.Derives.conjElimRight hBodyAt)))
        have hParts :=
          fs_zfc_support_raw_nat_sequence_code_condition_parts
            (x#ProofT.lc_sequence_id)
            (numₘ(0))
            ProofT.lc_code_trace_id
            ProofT.lc_code_index_id
            hCertificateCondition
        have hDomainBound :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              domₘ(x#ProofT.lc_sequence_id) ∈ₘ
                numₘ(1) := by
          simpa [sequence_domain_code_bound,
            finite_numeral_term, successor_term] using
            hParts.2.2.1
        apply
          fs_zfc_support_raw_finite_numeral_member_elim_context
            1
            (domₘ(x#ProofT.lc_sequence_id))
            Formula.falsum
            (domain_term_admissible
              (x#ProofT.lc_sequence_id)
              (set_variable_admissible
                ProofT.lc_sequence_id))
            Formula.Admissible.falsum
            hDomainBound
        intro index hIndex
        have hIndexZero : index = 0 := by omega
        subst index
        let Ε : Context signature :=
          (domₘ(x#ProofT.lc_sequence_id) ≐ₘ
            numₘ(0)) :: Δ
        change Ε ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum
        have hDomainZero :
            Ε ⊢ₘ[fs_zfc_support_raw_theory]
              domₘ(x#ProofT.lc_sequence_id) ≐ₘ
                numₘ(0) :=
          FirstOrder.Derives.assumption (by simp [Ε])
        have hDomainSuccessorAt :
            Ε ⊢ₘ[fs_zfc_support_raw_theory]
              domₘ(x#ProofT.lc_sequence_id) ≐ₘ
                Sₘ(x#ProofT.lc_last_index_id) :=
          FirstOrder.Derives.context_weaken_cons
            hDomainSuccessor
        have hLastMemberSuccessor :
            Ε ⊢ₘ[fs_zfc_support_raw_theory]
              x#ProofT.lc_last_index_id ∈ₘ
                Sₘ(x#ProofT.lc_last_index_id) :=
          fs_zfc_support_raw_logical_mem_successor_self
            (x#ProofT.lc_last_index_id)
            (set_variable_admissible
              ProofT.lc_last_index_id)
        have hLastMemberDomain :
            Ε ⊢ₘ[fs_zfc_support_raw_theory]
              x#ProofT.lc_last_index_id ∈ₘ
                domₘ(x#ProofT.lc_sequence_id) :=
          FirstOrder.Derives.iffElimLeft
            (membership_right_iff_of_equality
              (x#ProofT.lc_last_index_id)
              (domₘ(x#ProofT.lc_sequence_id))
              (Sₘ(x#ProofT.lc_last_index_id))
              (set_variable_admissible
                ProofT.lc_last_index_id)
              (domain_term_admissible
                (x#ProofT.lc_sequence_id)
                (set_variable_admissible
                  ProofT.lc_sequence_id))
              (successor_term_admissible
                (x#ProofT.lc_last_index_id)
                (set_variable_admissible
                  ProofT.lc_last_index_id))
              hDomainSuccessorAt)
            hLastMemberSuccessor
        have hLastMemberZero :
            Ε ⊢ₘ[fs_zfc_support_raw_theory]
              x#ProofT.lc_last_index_id ∈ₘ
                numₘ(0) :=
          FirstOrder.Derives.iffElimRight
            (membership_right_iff_of_equality
              (x#ProofT.lc_last_index_id)
              (domₘ(x#ProofT.lc_sequence_id))
              (numₘ(0))
              (set_variable_admissible
                ProofT.lc_last_index_id)
              (domain_term_admissible
                (x#ProofT.lc_sequence_id)
                (set_variable_admissible
                  ProofT.lc_sequence_id))
              (finite_numeral_term_admissible 0)
              hDomainZero)
            hLastMemberDomain
        exact
          fs_zfc_support_raw_finite_numeral_member_elim_context
            0
            (x#ProofT.lc_last_index_id)
            Formula.falsum
            (set_variable_admissible
              ProofT.lc_last_index_id)
            Formula.Admissible.falsum
            hLastMemberZero
            (by intro _ hImpossible; omega))

/-! ## 非全称首行拒绝 -/

/--
若候选公式的标准 token 行在全称公式头部已经 mismatch，则任何长度至少二的
逻辑证书 payload 都不能证明该候选公式是逻辑公理。

证明由二元自然数序列码关系恢复规范 payload 序列，在索引 `0` 读取唯一一条
全称闭包边，并与候选公式首行的有限头部 mismatch 冲突。
-/
theorem
    fs_zfc_support_raw_logical_certificate_condition_neg_of_non_forall_row
    (formulaCode : SetTerm)
    (hFormulaCode :
      GodelQuotation.Numbered.CodeBoundary formulaCode)
    (tokens payload : List Nat)
    (hPayloadLength : 2 ≤ payload.length)
    (hMismatch :
      FSFormulaUniversalHeadMismatch tokens)
    (hFormulaToRow :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ standard_token_sequence tokens)) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_certificate_condition_with_ids
        formulaCode
        (numₘ(nat_sequence_code_value payload))
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id) := by
  let body : SetFormula :=
    logical_certificate_body_with_ids
      formulaCode
      (numₘ(nat_sequence_code_value payload))
      (x#ProofT.lc_sequence_id)
      (x#ProofT.lc_formula_trace_id)
      (x#ProofT.lc_last_index_id)
      ProofT.lc_sequence_id
      ProofT.lc_formula_trace_id
      ProofT.lc_last_index_id
      ProofT.lc_line_index_id
      ProofT.lc_code_trace_id
      ProofT.lc_code_index_id
  have hBodyAdmissible :
      Formula.Admissible body := by
    simpa [body] using
      fs_zfc_logical_certificate_body_admissible
        formulaCode
        (numₘ(nat_sequence_code_value payload))
        hFormulaCode.1
        (finite_numeral_term_admissible
          (nat_sequence_code_value payload))
  simpa [logical_certificate_condition_with_ids, body] using
    fs_zfc_support_raw_logical_exists_three_neg
      body hBodyAdmissible (by
        let thirdMatrix : SetFormula :=
          (x#ProofT.lc_last_index_id ∈ₘ
              domₘ(x#ProofT.lc_sequence_id)) ∧ₘ body
        let thirdExists : SetFormula :=
          ∃ₘ[SetSort.set, ProofT.lc_last_index_id], thirdMatrix
        let secondMatrix : SetFormula :=
          (x#ProofT.lc_formula_trace_id ∈ₘ
              seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ thirdExists
        let secondExists : SetFormula :=
          ∃ₘ[SetSort.set, ProofT.lc_formula_trace_id],
            secondMatrix
        let firstMatrix : SetFormula :=
          (x#ProofT.lc_sequence_id ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
            secondExists
        let condition : SetFormula :=
          ∃ₘ[SetSort.set, ProofT.lc_sequence_id],
            firstMatrix
        let Δ : Context signature :=
          thirdMatrix :: secondMatrix :: firstMatrix :: [condition]
        change Δ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum
        have hThirdMatrixAt :
            Δ ⊢ₘ[fs_zfc_support_raw_theory] thirdMatrix :=
          FirstOrder.Derives.assumption (by simp [Δ])
        have hBodyAt :
            Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
          FirstOrder.Derives.conjElimRight hThirdMatrixAt
        have hCertificateCondition :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              nat_sequence_code_condition_with_ids
                (x#ProofT.lc_sequence_id)
                (numₘ(nat_sequence_code_value payload))
                ProofT.lc_code_trace_id
                ProofT.lc_code_index_id := by
          simpa [body, logical_certificate_body_with_ids,
            logical_certificate_conjunction] using
            FirstOrder.Derives.conjElimLeft hBodyAt
        have hDomainSuccessor :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              domₘ(x#ProofT.lc_sequence_id) ≐ₘ
                Sₘ(x#ProofT.lc_last_index_id) := by
          simpa [body, logical_certificate_body_with_ids,
            logical_certificate_conjunction] using
            FirstOrder.Derives.conjElimLeft
              (FirstOrder.Derives.conjElimRight
                (FirstOrder.Derives.conjElimRight
                  (FirstOrder.Derives.conjElimRight hBodyAt)))
        have hInitialFormula :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              formulaCode ≐ₘ
                (x#ProofT.lc_formula_trace_id ·ₘ
                  numₘ(0)) := by
          simpa [body, logical_certificate_body_with_ids,
            logical_certificate_conjunction] using
            FirstOrder.Derives.conjElimLeft
              (FirstOrder.Derives.conjElimRight
                (FirstOrder.Derives.conjElimRight
                  (FirstOrder.Derives.conjElimRight
                    (FirstOrder.Derives.conjElimRight hBodyAt))))
        have hAllClosureSteps :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              ∀ₘ[SetSort.set, ProofT.lc_line_index_id],
                (x#ProofT.lc_line_index_id ∈ₘ
                    x#ProofT.lc_last_index_id) ⟶ₘ
                  logical_closure_certificate_step_condition
                    (x#ProofT.lc_sequence_id)
                    (x#ProofT.lc_formula_trace_id)
                    (x#ProofT.lc_line_index_id) := by
          simpa [body, logical_certificate_body_with_ids,
            logical_certificate_conjunction] using
            FirstOrder.Derives.conjElimRight
              (FirstOrder.Derives.conjElimRight
                (FirstOrder.Derives.conjElimRight
                  (FirstOrder.Derives.conjElimRight
                    (FirstOrder.Derives.conjElimRight
                      (FirstOrder.Derives.conjElimRight hBodyAt)))))
        have hSequenceEquality :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              x#ProofT.lc_sequence_id ≐ₘ
                standard_token_sequence payload :=
          FirstOrder.Derives.impElim
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Δ) (by simp) <|
                fs_zfc_support_raw_nat_sequence_condition_unique_imp
                  (x#ProofT.lc_sequence_id)
                  payload
                  ProofT.lc_code_trace_id
                  ProofT.lc_code_index_id
                  (set_variable_admissible
                    ProofT.lc_sequence_id)
                  (by native_decide)
                  (by
                    simp [Term.freeSupport]
                    native_decide)
                  (by
                    simp [Term.freeSupport]
                    native_decide))
            hCertificateCondition
        have hZeroLast :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              numₘ(0) ∈ₘ
                x#ProofT.lc_last_index_id :=
          fs_zfc_support_raw_zero_mem_last_of_standard_sequence
            (x#ProofT.lc_sequence_id)
            (x#ProofT.lc_last_index_id)
            payload
            (set_variable_admissible
              ProofT.lc_sequence_id)
            (set_variable_admissible
              ProofT.lc_last_index_id)
            hPayloadLength hSequenceEquality hDomainSuccessor
        have hSequenceSubstitution :
            Term.substituteFree SetSort.set
                ProofT.lc_line_index_id (numₘ(0))
                (x#ProofT.lc_sequence_id) =
              x#ProofT.lc_sequence_id := by
          simp [Term.substituteFree, set_variable,
            show ProofT.lc_sequence_id ≠
              ProofT.lc_line_index_id by native_decide]
        have hFormulaTraceSubstitution :
            Term.substituteFree SetSort.set
                ProofT.lc_line_index_id (numₘ(0))
                (x#ProofT.lc_formula_trace_id) =
              x#ProofT.lc_formula_trace_id := by
          simp [Term.substituteFree, set_variable,
            show ProofT.lc_formula_trace_id ≠
              ProofT.lc_line_index_id by native_decide]
        have hLastIndexSubstitution :
            Term.substituteFree SetSort.set
                ProofT.lc_line_index_id (numₘ(0))
                (x#ProofT.lc_last_index_id) =
              x#ProofT.lc_last_index_id := by
          simp [Term.substituteFree, set_variable,
            show ProofT.lc_last_index_id ≠
              ProofT.lc_line_index_id by native_decide]
        have hLineIndexSubstitution :
            Term.substituteFree SetSort.set
                ProofT.lc_line_index_id (numₘ(0))
                (x#ProofT.lc_line_index_id) =
              numₘ(0) := by
          simp [Term.substituteFree, set_variable]
        have hStepSubstitution :=
          logical_closure_certificate_step_condition_substitute_closed
            (x#ProofT.lc_sequence_id)
            (x#ProofT.lc_formula_trace_id)
            (x#ProofT.lc_line_index_id)
            (numₘ(0))
            (x#ProofT.lc_sequence_id)
            (x#ProofT.lc_formula_trace_id)
            (numₘ(0))
            ProofT.lc_line_index_id
            (by native_decide)
            (finite_numeral_term_admissible 0)
            (finite_numeral_term_freeSupport 0)
            hSequenceSubstitution
            hFormulaTraceSubstitution
            hLineIndexSubstitution
        have hClosureAtRaw :=
          FirstOrder.Derives.forall_elim
            (term := numₘ(0)) hAllClosureSteps
        rw [Formula.openAt_closeFreeAt_eq_substituteFree]
          at hClosureAtRaw
        have hClosureAt :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              (numₘ(0) ∈ₘ
                  x#ProofT.lc_last_index_id) ⟶ₘ
                logical_closure_certificate_step_condition
                  (x#ProofT.lc_sequence_id)
                  (x#ProofT.lc_formula_trace_id)
                  (numₘ(0)) := by
          simpa [Formula.substituteFree, Term.substituteFree,
            set_variable, hSequenceSubstitution,
            hFormulaTraceSubstitution,
            hLastIndexSubstitution,
            hLineIndexSubstitution,
            hStepSubstitution] using hClosureAtRaw
        have hClosure :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              logical_closure_certificate_step_condition
                (x#ProofT.lc_sequence_id)
                (x#ProofT.lc_formula_trace_id)
                (numₘ(0)) :=
          FirstOrder.Derives.impElim hClosureAt hZeroLast
        have hRowTarget :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              standard_token_sequence tokens ≐ₘ
                (x#ProofT.lc_formula_trace_id ·ₘ
                  numₘ(0)) :=
          Metatheory.Derives.equality_trans
            (Metatheory.Derives.equality_symm
              (FirstOrder.Derives.context_weaken
                (Γ := []) (Δ := Δ) (by simp)
                hFormulaToRow))
            hInitialFormula
        apply
          fs_zfc_support_raw_canonical_forall_closure_falsum_of_standard_row
            tokens hMismatch
            (x#ProofT.lc_formula_trace_id ·ₘ
              Sₘ(numₘ(0)))
            (var_codeₘ(numₘ(2) *ₘ
              (x#ProofT.lc_sequence_id ·ₘ
                numₘ(0))))
            (x#ProofT.lc_formula_trace_id ·ₘ
              numₘ(0))
        · exact function_application_term_admissible
            (x#ProofT.lc_formula_trace_id)
            (Sₘ(numₘ(0)))
            (set_variable_admissible
              ProofT.lc_formula_trace_id)
            (successor_term_admissible
              (numₘ(0))
              (finite_numeral_term_admissible 0))
        · exact variable_code_term_admissible
            (numₘ(2) *ₘ
              (x#ProofT.lc_sequence_id ·ₘ
                numₘ(0)))
            (natural_multiplication_term_admissible
              (numₘ(2))
              (x#ProofT.lc_sequence_id ·ₘ
                numₘ(0))
              (finite_numeral_term_admissible 2)
              (function_application_term_admissible
                (x#ProofT.lc_sequence_id)
                (numₘ(0))
                (set_variable_admissible
                  ProofT.lc_sequence_id)
                (finite_numeral_term_admissible 0)))
        · exact function_application_term_admissible
            (x#ProofT.lc_formula_trace_id)
            (numₘ(0))
            (set_variable_admissible
              ProofT.lc_formula_trace_id)
            (finite_numeral_term_admissible 0)
        all_goals
          first
          | exact hRowTarget
          | exact FirstOrder.Derives.conjElimRight
              (FirstOrder.Derives.conjElimLeft hClosure)
          | native_decide)

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
