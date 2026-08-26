import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCodeReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceReplay

/-!
# ZFC 中的 FormalSystem 有限签名回放

本模块只负责把宿主 token 分类经标准序列语义提升为对象层
`fs_formula_signature_condition`。公式语法闭包仍由公共 `FormulaCodeₘ` 处理。
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

/-! ## 单个标准位置 -/

/-- 一个已分类 token 在标准序列对应位置满足对象层 token 条件。 -/
theorem fs_zfc_support_raw_standard_token_condition_at
    (tokens : List Nat)
    (hTokens : FSFormulaTokens tokens)
    (index : Nat) (hIndex : index < tokens.length) :
    Derives fs_zfc_support_raw_theory [] (
      fs_formula_token_condition
        (standard_token_sequence tokens ·ₘ
          numₘ(index))) := by
  let token := tokens[index]
  have hGet :
      tokens[index]? = some token :=
    List.getElem?_eq_some_iff.mpr
      ⟨hIndex, rfl⟩
  have hToken :
      FSFormulaToken token :=
    hTokens token (by
      simp [token])
  have hNumeral :
      Derives fs_zfc_support_raw_theory [] (
        fs_formula_token_condition
          (numₘ(token))) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (gq_fs_formula_token_condition hToken)
  have hValue :
      Derives fs_zfc_support_raw_theory [] (
        (standard_token_sequence tokens ·ₘ
          numₘ(index)) ≐ₘ
            numₘ(token)) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_token_sequence_apply_getElem?
        tokens hGet)
  have hIff :=
    fs_formula_token_condition_iff_of_equality
      (standard_token_sequence tokens ·ₘ
        numₘ(index))
      (numₘ(token))
      (function_application_term_admissible
        (standard_token_sequence tokens)
        (numₘ(index))
        (standard_token_sequence_admissible tokens)
        (finite_numeral_term_admissible index))
      (finite_numeral_term_admissible token)
      hValue
  exact FirstOrder.Derives.iffElimLeft
    hIff hNumeral

/-! ## 单行标准 token 序列 -/

private theorem
    fs_zfc_support_raw_standard_token_condition_of_index_equality
    (tokens : List Nat)
    (hTokens : FSFormulaTokens tokens)
    (tokenIndexId : FreeVarId)
    (index : Nat) (hIndex : index < tokens.length) :
    Derives fs_zfc_support_raw_theory [] (
      ((x#tokenIndexId ≐ₘ numₘ(index)) ⟶ₘ
        fs_formula_token_condition
          (standard_token_sequence tokens ·ₘ
            x#tokenIndexId))) := by
  let point : SetTerm := x#tokenIndexId
  let equality : SetFormula :=
    point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  have hSequence :
      Term.Admissible
        (standard_token_sequence tokens)
        SetSort.set :=
    standard_token_sequence_admissible tokens
  have hPoint :
      Term.Admissible point SetSort.set := by
    simpa [point] using
      set_variable_admissible tokenIndexId
  have hPointValue :
      Term.Admissible
        (standard_token_sequence tokens ·ₘ point)
        SetSort.set :=
    function_application_term_admissible
      (standard_token_sequence tokens) point
      hSequence hPoint
  have hNumeralValue :
      Term.Admissible
        (standard_token_sequence tokens ·ₘ
          numₘ(index)) SetSort.set :=
    function_application_term_admissible
      (standard_token_sequence tokens)
      (numₘ(index)) hSequence
      (finite_numeral_term_admissible index)
  have hConclusion :
      Formula.Admissible
        (fs_formula_token_condition
          (standard_token_sequence tokens ·ₘ
            point)) :=
    fs_formula_token_condition_admissible
      (standard_token_sequence tokens ·ₘ point)
      hPointValue
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        point ≐ₘ numₘ(index) := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ) (φ := equality)
        (by simp [Γ]))
  have hApplication :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (standard_token_sequence tokens ·ₘ point) ≐ₘ
          (standard_token_sequence tokens ·ₘ
            numₘ(index)) :=
    function_application_term_congr_argument_of_equality
      (standard_token_sequence tokens)
      point (numₘ(index))
      hSequence hPoint
      (finite_numeral_term_admissible index)
      hEquality
  have hIff :=
    fs_formula_token_condition_iff_of_equality
      (standard_token_sequence tokens ·ₘ point)
      (standard_token_sequence tokens ·ₘ
        numₘ(index))
      hPointValue hNumeralValue hApplication
  have hConcrete :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        fs_formula_token_condition
          (standard_token_sequence tokens ·ₘ
            numₘ(index)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ)
      (by simp [Γ])
      (fs_zfc_support_raw_standard_token_condition_at
        tokens hTokens index hIndex)
  simpa [Γ, equality, point] using
    FirstOrder.Derives.iffElimLeft
      hIff hConcrete

/-- 显式 token binder 下，标准 token 序列满足有限签名条件。 -/
theorem
    fs_zfc_support_raw_standard_token_sequence_signature_with_id
    (tokens : List Nat)
    (hTokens : FSFormulaTokens tokens)
    (tokenIndexId : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_formula_signature_condition_with_id
        (standard_token_sequence tokens)
        tokenIndexId) := by
  have hSequence :
      Term.Admissible
        (standard_token_sequence tokens)
        SetSort.set :=
    standard_token_sequence_admissible tokens
  have hConclusion :
      Formula.Admissible
        (fs_formula_token_condition
          (standard_token_sequence tokens ·ₘ
            x#tokenIndexId)) :=
    fs_formula_token_condition_admissible
      (standard_token_sequence tokens ·ₘ
        x#tokenIndexId)
      (function_application_term_admissible
        (standard_token_sequence tokens)
        (x#tokenIndexId)
        hSequence
        (set_variable_admissible tokenIndexId))
  have hDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(standard_token_sequence tokens) ≐ₘ
          numₘ(tokens.length)) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_token_sequence_domain_eq_length
        tokens)
  have hForall :=
    fs_zfc_support_raw_finite_domain_forall_imp
      (standard_token_sequence tokens)
      tokens.length tokenIndexId
      (fs_formula_token_condition
        (standard_token_sequence tokens ·ₘ
          x#tokenIndexId))
      hSequence hConclusion hDomain
      (fun index hIndex =>
        fs_zfc_support_raw_standard_token_condition_of_index_equality
          tokens hTokens tokenIndexId
          index hIndex)
  simpa [fs_formula_signature_condition_with_id]
    using hForall

/-- 标准 token 序列满足规范 de Bruijn binder 下的有限签名条件。 -/
theorem fs_zfc_support_raw_standard_token_sequence_signature
    (tokens : List Nat)
    (hTokens : FSFormulaTokens tokens) :
    Derives fs_zfc_support_raw_theory [] (
      fs_formula_signature_condition
        (standard_token_sequence tokens)) := by
  have hNamed :=
    fs_zfc_support_raw_standard_token_sequence_signature_with_id
      tokens hTokens 0
  rw [fs_formula_signature_condition_with_id_eq
    (standard_token_sequence tokens) 0
    (standard_token_sequence_admissible tokens)
    (by
      rw [standard_token_sequence_freeSupport_nil]
      exact List.not_mem_nil)] at hNamed
  exact hNamed

/-- admissible 公式的规范 quotation 行满足有限签名条件。 -/
theorem fs_zfc_support_raw_quote_tokens_signature
    {formula : SetFormula} {tokens : List Nat}
    (hFormula : Formula.Admissible formula)
    (hQuote :
      Numbered.quote_tokens? formula =
        some tokens) :
    Derives fs_zfc_support_raw_theory [] (
      fs_formula_signature_condition
        (standard_token_sequence tokens)) :=
  fs_zfc_support_raw_standard_token_sequence_signature
    tokens
    (fs_quote_tokens_formula_tokens
      hFormula hQuote)

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
