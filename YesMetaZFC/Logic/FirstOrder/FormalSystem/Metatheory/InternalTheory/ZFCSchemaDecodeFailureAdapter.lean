import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectCertificateSchemaRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCProjectDecodeConditionFailureAdapter
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateConditionRejection

/-!
# ZFC schema 解码失败适配器

本模块只处理终局失败视图：当 separation 或 collection 的宿主生成器因 body
Project 解码失败而返回 `none` 时，从既有对象证书条件中取出规范 token 序列与
公式分类器，并导出对象层否定。成功反演、trace 回放与 Rosser 的公开二元关系
均不在此扩展。
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

private theorem fs_zfc_schema_offset_ne_offset
    (base left right : FreeVarId)
    (hNe : left ≠ right) :
    base + left ≠ base + right := by
  intro hEquality
  exact hNe (Nat.add_left_cancel hEquality)

private theorem fs_zfc_schema_base_ne_offset
    (base offset : FreeVarId)
    (hPositive : 0 < offset) :
    base ≠ base + offset :=
  Nat.ne_of_lt (Nat.lt_add_of_pos_right hPositive)

private theorem fs_zfc_schema_set_variable_fresh_of_ne
    (left right : FreeVarId)
    (hNe : left ≠ right) :
    (SetSort.set, left) ∉
      Term.freeSupport (x#right) := by
  intro hMember
  change (SetSort.set, left) ∈
    [(SetSort.set, right)] at hMember
  exact hNe <| congrArg Prod.snd <|
    List.mem_singleton.mp hMember

private def fs_zfc_schema_body_context
    (body : SetFormula)
    (base : FreeVarId) :
    Context signature :=
  body ::
    (∃ₘ[SetSort.set, base + 4], body) ::
    (∃ₘ[SetSort.set, base + 3],
      ∃ₘ[SetSort.set, base + 4], body) ::
    (∃ₘ[SetSort.set, base + 2],
      ∃ₘ[SetSort.set, base + 3],
        ∃ₘ[SetSort.set, base + 4], body) ::
    (∃ₘ[SetSort.set, base + 1],
      ∃ₘ[SetSort.set, base + 2],
        ∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4], body) ::
    [(∃ₘ[SetSort.set, base],
      ∃ₘ[SetSort.set, base + 1],
        ∃ₘ[SetSort.set, base + 2],
          ∃ₘ[SetSort.set, base + 3],
            ∃ₘ[SetSort.set, base + 4], body)]

private def fs_zfc_schema_coordinate_context
    (body : SetFormula)
    (parameterValue bodyTokenValue : Nat)
    (base : FreeVarId) :
    Context signature :=
  (x#(base + 1) ≐ₘ numₘ(bodyTokenValue)) ::
    (x#base ≐ₘ numₘ(parameterValue)) ::
      fs_zfc_schema_body_context body base

/--
五重 schema witness 上下文及其两个规范坐标等式不会捕获首个序列 trace 编号。
这里只使用打开体的公共支持集界，不读取 separation/collection 的内部细节。
-/
private theorem fs_zfc_schema_coordinate_context_trace_fresh
    (formula : SetTerm)
    (body : SetFormula)
    (parameterValue bodyTokenValue : Nat)
    (base : FreeVarId)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hBodySupport :
      ∀ freeVariable,
        freeVariable ∈ Formula.freeSupport body →
          freeVariable ∈ fs_zfc_schema_open_support formula base) :
    ∀ f,
      f ∈ fs_zfc_schema_coordinate_context
          body parameterValue bodyTokenValue base →
        (SetSort.set, base + 5) ∉ Formula.freeSupport f := by
  have hBodyFresh :
      (SetSort.set, base + 5) ∉ Formula.freeSupport body := by
    intro hMember
    have hSupport := hBodySupport _ hMember
    rw [fs_zfc_schema_open_support, hFormulaClosed] at hSupport
    simp only [List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hSupport
    rcases hSupport with h0 | h1 | h2 | h3 | h4
    · exact
        fs_zfc_schema_offset_ne_offset base 5 0 (by decide) <|
          congrArg Prod.snd h0
    · exact
        fs_zfc_schema_offset_ne_offset base 5 1 (by decide) <|
          congrArg Prod.snd h1
    · exact
        fs_zfc_schema_offset_ne_offset base 5 2 (by decide) <|
          congrArg Prod.snd h2
    · exact
        fs_zfc_schema_offset_ne_offset base 5 3 (by decide) <|
          congrArg Prod.snd h3
    · exact
        fs_zfc_schema_offset_ne_offset base 5 4 (by decide) <|
          congrArg Prod.snd h4
  have hCloseFresh
      (binder : FreeVarId)
      (source : SetFormula)
      (hSourceFresh :
        (SetSort.set, base + 5) ∉ Formula.freeSupport source) :
      (SetSort.set, base + 5) ∉
        Formula.freeSupport
          (∃ₘ[SetSort.set, binder], source) := by
    simpa only [Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, base + 5) SetSort.set binder 0
        source hSourceFresh
  have h4 := hCloseFresh (base + 4) body hBodyFresh
  have h34 := hCloseFresh (base + 3)
    (∃ₘ[SetSort.set, base + 4], body) h4
  have h234 := hCloseFresh (base + 2)
    (∃ₘ[SetSort.set, base + 3],
      ∃ₘ[SetSort.set, base + 4], body) h34
  have h1234 := hCloseFresh (base + 1)
    (∃ₘ[SetSort.set, base + 2],
      ∃ₘ[SetSort.set, base + 3],
        ∃ₘ[SetSort.set, base + 4], body) h234
  have h01234 := hCloseFresh base
    (∃ₘ[SetSort.set, base + 1],
      ∃ₘ[SetSort.set, base + 2],
        ∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4], body) h1234
  intro f hf
  simp only [fs_zfc_schema_coordinate_context,
    fs_zfc_schema_body_context, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · simpa only [Formula.freeSupport,
      finite_numeral_term_freeSupport, List.append_nil] using
      fs_zfc_schema_set_variable_fresh_of_ne
        (base + 5) (base + 1)
        (fs_zfc_schema_offset_ne_offset base 5 1 (by decide))
  · simpa only [Formula.freeSupport,
      finite_numeral_term_freeSupport, List.append_nil] using
      fs_zfc_schema_set_variable_fresh_of_ne
        (base + 5) base
        (by simp)
  · exact hBodyFresh
  · exact h4
  · exact h34
  · exact h234
  · exact h1234
  · exact h01234

/-- 用参数坐标等式把 schema 分类器的入口深度实例化为 numeral 表达式。 -/
private theorem fs_zfc_support_raw_schema_classifier_of_parameter_equality
    {Γ : Context signature}
    (entryDepth entryDepthResult : SetTerm)
    (parameterValue : Nat)
    (base : FreeVarId)
    (hEntryDepthSubstitution :
      Term.substituteFree SetSort.set base
          (numₘ(parameterValue)) entryDepth =
        entryDepthResult)
    (hParameterEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#base ≐ₘ numₘ(parameterValue))
    (hClassifier :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_project_formula_code_condition_with_ids
          entryDepth (x#(base + 2))
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      canonical_project_formula_code_condition_with_ids
        entryDepthResult (x#(base + 2))
        (base + 7) (base + 8)
        (base + 9) (base + 10)
        (base + 11) (base + 12)
        (base + 13) (base + 14)
        (base + 15) (base + 16) := by
  let source : SetFormula :=
    canonical_project_formula_code_condition_with_ids
      entryDepth (x#(base + 2))
      (base + 7) (base + 8)
      (base + 9) (base + 10)
      (base + 11) (base + 12)
      (base + 13) (base + 14)
      (base + 15) (base + 16)
  have hSubstitution :
      Formula.substituteFree SetSort.set base
          (numₘ(parameterValue)) source =
        canonical_project_formula_code_condition_with_ids
          entryDepthResult (x#(base + 2))
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16) := by
    simpa [source] using
      canonical_project_formula_code_condition_with_ids_substitute_closed
        entryDepth (x#(base + 2))
        (numₘ(parameterValue))
        entryDepthResult (x#(base + 2))
        base
        (base + 7) (base + 8)
        (base + 9) (base + 10)
        (base + 11) (base + 12)
        (base + 13) (base + 14)
        (base + 15) (base + 16)
        (fs_zfc_schema_base_ne_offset base 7 (by decide))
        (fs_zfc_schema_base_ne_offset base 8 (by decide))
        (fs_zfc_schema_base_ne_offset base 9 (by decide))
        (fs_zfc_schema_base_ne_offset base 10 (by decide))
        (fs_zfc_schema_base_ne_offset base 11 (by decide))
        (fs_zfc_schema_base_ne_offset base 12 (by decide))
        (fs_zfc_schema_base_ne_offset base 13 (by decide))
        (fs_zfc_schema_base_ne_offset base 14 (by decide))
        (fs_zfc_schema_base_ne_offset base 15 (by decide))
        (fs_zfc_schema_base_ne_offset base 16 (by decide))
        ⟨finite_numeral_term_admissible parameterValue,
          finite_numeral_term_freeSupport parameterValue⟩
        hEntryDepthSubstitution
        (by simp [Term.substituteFree, set_variable])
  have hSource :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        Formula.substituteFree SetSort.set base
          (x#base) source := by
    simpa [source, Formula.substituteFree_self] using hClassifier
  have hTransport :=
    FirstOrder.Derives.eq_subst_m
      hParameterEquality hSource
  simpa only [hSubstitution] using hTransport

/--
规范序列条件把分类器的公式码坐标固定到宿主解码所见 token 串；若该串解码失败，
既有 Project 失败适配器立即给出矛盾。
-/
private theorem fs_zfc_support_raw_schema_classifier_falsum_of_decode_none
    {Γ : Context signature}
    (entryDepth bodyTokenValue : Nat)
    (base : FreeVarId)
    (hTraceFreshContext :
      ∀ f, f ∈ Γ →
        (SetSort.set, base + 5) ∉ Formula.freeSupport f)
    (hSequence :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        nat_sequence_code_condition_with_ids
          (x#(base + 2)) (x#(base + 1))
          (base + 5) (base + 6))
    (hBodyTokenEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#(base + 1) ≐ₘ numₘ(bodyTokenValue))
    (hClassifier :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_project_formula_code_condition_with_ids
          (numₘ(entryDepth)) (x#(base + 2))
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16))
    (hDecode :
      fs_project_hilbert_code_decode
        entryDepth bodyTokenValue = none) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  let tokens : List Nat := nat_sequence_decode bodyTokenValue
  have hBodyTokenCodeEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#(base + 1) ≐ₘ
          numₘ(nat_sequence_code_value tokens) := by
    simpa [tokens, nat_sequence_code_value_decode] using
      hBodyTokenEquality
  have hSequenceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#(base + 2) ≐ₘ standard_token_sequence tokens := by
    apply
      fs_zfc_support_raw_nat_sequence_code_condition_unique_of_code_equality
        (x#(base + 2)) (x#(base + 1)) tokens
        (base + 5) (base + 6)
        (set_variable_admissible (base + 2))
        (set_variable_admissible (base + 1))
    · exact
        fs_zfc_schema_offset_ne_offset base 5 6 (by decide)
    · exact fs_zfc_schema_set_variable_fresh_of_ne
        (base + 5) (base + 2)
        (fs_zfc_schema_offset_ne_offset base 5 2 (by decide))
    · exact fs_zfc_schema_set_variable_fresh_of_ne
        (base + 6) (base + 2)
        (fs_zfc_schema_offset_ne_offset base 6 2 (by decide))
    · exact fs_zfc_schema_set_variable_fresh_of_ne
        (base + 6) (base + 1)
        (fs_zfc_schema_offset_ne_offset base 6 1 (by decide))
    · exact hTraceFreshContext
    · exact hSequence
    · exact hBodyTokenCodeEquality
  let source : SetFormula :=
    canonical_project_formula_code_condition_with_ids
      (numₘ(entryDepth)) (x#(base + 2))
      (base + 7) (base + 8)
      (base + 9) (base + 10)
      (base + 11) (base + 12)
      (base + 13) (base + 14)
      (base + 15) (base + 16)
  have hSubstitution :
      Formula.substituteFree SetSort.set (base + 2)
          (standard_token_sequence tokens) source =
        canonical_project_formula_code_condition_with_ids
          (numₘ(entryDepth)) (standard_token_sequence tokens)
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16) := by
    simpa [source] using
      canonical_project_formula_code_condition_with_ids_substitute_closed
        (numₘ(entryDepth)) (x#(base + 2))
        (standard_token_sequence tokens)
        (numₘ(entryDepth)) (standard_token_sequence tokens)
        (base + 2)
        (base + 7) (base + 8)
        (base + 9) (base + 10)
        (base + 11) (base + 12)
        (base + 13) (base + 14)
        (base + 15) (base + 16)
        (fs_zfc_schema_offset_ne_offset base 2 7 (by decide))
        (fs_zfc_schema_offset_ne_offset base 2 8 (by decide))
        (fs_zfc_schema_offset_ne_offset base 2 9 (by decide))
        (fs_zfc_schema_offset_ne_offset base 2 10 (by decide))
        (fs_zfc_schema_offset_ne_offset base 2 11 (by decide))
        (fs_zfc_schema_offset_ne_offset base 2 12 (by decide))
        (fs_zfc_schema_offset_ne_offset base 2 13 (by decide))
        (fs_zfc_schema_offset_ne_offset base 2 14 (by decide))
        (fs_zfc_schema_offset_ne_offset base 2 15 (by decide))
        (fs_zfc_schema_offset_ne_offset base 2 16 (by decide))
        ⟨standard_token_sequence_admissible tokens,
          standard_token_sequence_freeSupport_nil tokens⟩
        (by
          apply Term.substituteFree_eq_self_of_not_mem
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
        (by simp [Term.substituteFree, set_variable])
  have hSource :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        Formula.substituteFree SetSort.set (base + 2)
          (x#(base + 2)) source := by
    simpa [source, Formula.substituteFree_self] using hClassifier
  have hClassifierGround :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_project_formula_code_condition_with_ids
          (numₘ(entryDepth)) (standard_token_sequence tokens)
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16) := by
    have hTransport :=
      FirstOrder.Derives.eq_subst_m hSequenceEquality hSource
    simpa only [hSubstitution] using hTransport
  have hDecodeTokens :
      fs_project_hilbert_tokens_decode entryDepth tokens = none := by
    simpa [fs_project_hilbert_code_decode, tokens] using hDecode
  exact FirstOrder.Derives.negElim
    hClassifierGround
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_canonical_project_formula_code_condition_from_base_neg_of_project_decode_none
          entryDepth tokens (base + 7) hDecodeTokens)

/--
一元 schema 的 body Project 解码失败时，对象 separation 条件不可成立。
-/
theorem
    fs_zfc_support_raw_separation_condition_with_base_neg_of_project_decode_none
    (formula : SetTerm)
    (parameterValue bodyTokenValue : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hDecode :
      fs_project_hilbert_code_decode
        (parameterValue + 1) bodyTokenValue = none) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_separation_condition_with_base
        formula
        (numₘ(godel_pair_value 1
          (godel_pair_value 0
            (godel_pair_value parameterValue bodyTokenValue))))
        base) := by
  let raw : Nat :=
    godel_pair_value 1
      (godel_pair_value 0
        (godel_pair_value parameterValue bodyTokenValue))
  let body : SetFormula :=
    fs_zfc_separation_condition_open_body formula raw base
  have hExistsAdmissible :
      Formula.Admissible
        (∃ₘ[SetSort.set, base],
          ∃ₘ[SetSort.set, base + 1],
            ∃ₘ[SetSort.set, base + 2],
              ∃ₘ[SetSort.set, base + 3],
                ∃ₘ[SetSort.set, base + 4], body) := by
    rw [← fs_zfc_separation_condition_exists_shape
      formula raw base]
    exact fs_zfc_separation_condition_with_base_admissible
      formula (numₘ(raw)) base hFormula
      (finite_numeral_term_admissible raw)
  have hBody : Formula.Admissible body :=
    fs_zfc_exists_five_body_admissible
      base (base + 1) (base + 2)
      (base + 3) (base + 4)
      body hExistsAdmissible
  have hCase :
      fs_zfc_schema_body_context body base
        ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
    let Γ : Context signature :=
      fs_zfc_schema_body_context body base
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ, fs_zfc_schema_body_context])
    have hCertificateEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            fs_zfc_schema_certificate_term
              (numₘ(0)) (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_separation_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hBounds :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_schema_certificate_bounds
            (numₘ(raw)) (numₘ(0))
            (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_separation_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hBodyAt)
    apply fs_zfc_support_raw_schema_certificate_coordinates_elim
      raw 0 (x#base) (x#(base + 1))
      Formula.falsum
      (set_variable_admissible base)
      (set_variable_admissible (base + 1))
      Formula.Admissible.falsum
      hCertificateEquality hBounds
    intro decodedParameter decodedBodyToken hRaw
    have hRaw' :
        godel_pair_value 1
            (godel_pair_value 0
              (godel_pair_value parameterValue bodyTokenValue)) =
          godel_pair_value 1
            (godel_pair_value 0
              (godel_pair_value
                decodedParameter decodedBodyToken)) := by
      simpa [raw] using hRaw
    have hCoordinates :
        parameterValue = decodedParameter ∧
          bodyTokenValue = decodedBodyToken :=
      godel_pair_value_eq_iff.mp <|
        (godel_pair_value_eq_iff.mp <|
          (godel_pair_value_eq_iff.mp hRaw').2).2
    rcases hCoordinates with
      ⟨hParameter, hBodyToken⟩
    subst decodedParameter
    subst decodedBodyToken
    let Δ : Context signature :=
      fs_zfc_schema_coordinate_context
        body parameterValue bodyTokenValue base
    change Δ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum
    have hBodyAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Δ, fs_zfc_schema_coordinate_context,
          fs_zfc_schema_body_context])
    have hBodyTokenEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 1) ≐ₘ numₘ(bodyTokenValue) :=
      FirstOrder.Derives.assumption
        (by simp [Δ, fs_zfc_schema_coordinate_context])
    have hParameterEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#base ≐ₘ numₘ(parameterValue) :=
      FirstOrder.Derives.assumption
        (by simp [Δ, fs_zfc_schema_coordinate_context])
    have hRest :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_separation_condition_open_rest formula base := by
      simpa only [body,
        fs_zfc_separation_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight hBodyAt)
    have hSequence :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          nat_sequence_code_condition_with_ids
            (x#(base + 2)) (x#(base + 1))
            (base + 5) (base + 6) := by
      simpa only [fs_zfc_separation_condition_open_rest] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hRest)
    have hClassifier :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_formula_code_condition_with_ids
            (Sₘ(x#base)) (x#(base + 2))
            (base + 7) (base + 8)
            (base + 9) (base + 10)
            (base + 11) (base + 12)
            (base + 13) (base + 14)
            (base + 15) (base + 16) := by
      simpa only [fs_zfc_separation_condition_open_rest] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight
            (FirstOrder.Derives.conjElimRight hRest))
    have hClassifierParameter :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_formula_code_condition_with_ids
            (Sₘ(numₘ(parameterValue))) (x#(base + 2))
            (base + 7) (base + 8)
            (base + 9) (base + 10)
            (base + 11) (base + 12)
            (base + 13) (base + 14)
            (base + 15) (base + 16) :=
      fs_zfc_support_raw_schema_classifier_of_parameter_equality
        (Sₘ(x#base)) (Sₘ(numₘ(parameterValue)))
        parameterValue base
        (by simp [Term.substituteFree, set_variable])
        hParameterEquality hClassifier
    have hClassifierNumeral :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_formula_code_condition_with_ids
            (numₘ(parameterValue + 1)) (x#(base + 2))
            (base + 7) (base + 8)
            (base + 9) (base + 10)
            (base + 11) (base + 12)
            (base + 13) (base + 14)
            (base + 15) (base + 16) := by
      simpa [finite_numeral_term] using hClassifierParameter
    exact fs_zfc_support_raw_schema_classifier_falsum_of_decode_none
      (parameterValue + 1) bodyTokenValue base
      (fs_zfc_schema_coordinate_context_trace_fresh
        formula body parameterValue bodyTokenValue base
        hFormulaClosed
        (fs_zfc_separation_condition_open_body_freeSupport_subset
          formula raw base))
      hSequence hBodyTokenEquality hClassifierNumeral hDecode
  rw [fs_zfc_separation_condition_exists_shape
    formula raw base]
  simpa [raw, fs_zfc_schema_body_context] using
    fs_zfc_support_raw_exists_five_neg
      base (base + 1) (base + 2)
      (base + 3) (base + 4)
      body hBody hCase

/--
二元 schema 的 body Project 解码失败时，对象 collection 条件不可成立。
-/
theorem
    fs_zfc_support_raw_collection_condition_with_base_neg_of_project_decode_none
    (formula : SetTerm)
    (parameterValue bodyTokenValue : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hDecode :
      fs_project_hilbert_code_decode
        (parameterValue + 2) bodyTokenValue = none) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_collection_condition_with_base
        formula
        (numₘ(godel_pair_value 1
          (godel_pair_value 1
            (godel_pair_value parameterValue bodyTokenValue))))
        base) := by
  let raw : Nat :=
    godel_pair_value 1
      (godel_pair_value 1
        (godel_pair_value parameterValue bodyTokenValue))
  let body : SetFormula :=
    fs_zfc_collection_condition_open_body formula raw base
  have hExistsAdmissible :
      Formula.Admissible
        (∃ₘ[SetSort.set, base],
          ∃ₘ[SetSort.set, base + 1],
            ∃ₘ[SetSort.set, base + 2],
              ∃ₘ[SetSort.set, base + 3],
                ∃ₘ[SetSort.set, base + 4], body) := by
    rw [← fs_zfc_collection_condition_exists_shape
      formula raw base]
    exact fs_zfc_collection_condition_with_base_admissible
      formula (numₘ(raw)) base hFormula
      (finite_numeral_term_admissible raw)
  have hBody : Formula.Admissible body :=
    fs_zfc_exists_five_body_admissible
      base (base + 1) (base + 2)
      (base + 3) (base + 4)
      body hExistsAdmissible
  have hCase :
      fs_zfc_schema_body_context body base
        ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
    let Γ : Context signature :=
      fs_zfc_schema_body_context body base
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ, fs_zfc_schema_body_context])
    have hCertificateEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            fs_zfc_schema_certificate_term
              (numₘ(1)) (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_collection_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hBounds :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_schema_certificate_bounds
            (numₘ(raw)) (numₘ(1))
            (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_collection_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hBodyAt)
    apply fs_zfc_support_raw_schema_certificate_coordinates_elim
      raw 1 (x#base) (x#(base + 1))
      Formula.falsum
      (set_variable_admissible base)
      (set_variable_admissible (base + 1))
      Formula.Admissible.falsum
      hCertificateEquality hBounds
    intro decodedParameter decodedBodyToken hRaw
    have hRaw' :
        godel_pair_value 1
            (godel_pair_value 1
              (godel_pair_value parameterValue bodyTokenValue)) =
          godel_pair_value 1
            (godel_pair_value 1
              (godel_pair_value
                decodedParameter decodedBodyToken)) := by
      simpa [raw] using hRaw
    have hCoordinates :
        parameterValue = decodedParameter ∧
          bodyTokenValue = decodedBodyToken :=
      godel_pair_value_eq_iff.mp <|
        (godel_pair_value_eq_iff.mp <|
          (godel_pair_value_eq_iff.mp hRaw').2).2
    rcases hCoordinates with
      ⟨hParameter, hBodyToken⟩
    subst decodedParameter
    subst decodedBodyToken
    let Δ : Context signature :=
      fs_zfc_schema_coordinate_context
        body parameterValue bodyTokenValue base
    change Δ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum
    have hBodyAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Δ, fs_zfc_schema_coordinate_context,
          fs_zfc_schema_body_context])
    have hBodyTokenEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 1) ≐ₘ numₘ(bodyTokenValue) :=
      FirstOrder.Derives.assumption
        (by simp [Δ, fs_zfc_schema_coordinate_context])
    have hParameterEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#base ≐ₘ numₘ(parameterValue) :=
      FirstOrder.Derives.assumption
        (by simp [Δ, fs_zfc_schema_coordinate_context])
    have hRest :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_collection_condition_open_rest formula base := by
      simpa only [body,
        fs_zfc_collection_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight hBodyAt)
    have hSequence :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          nat_sequence_code_condition_with_ids
            (x#(base + 2)) (x#(base + 1))
            (base + 5) (base + 6) := by
      simpa only [fs_zfc_collection_condition_open_rest] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hRest)
    have hClassifier :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_formula_code_condition_with_ids
            (Sₘ(Sₘ(x#base))) (x#(base + 2))
            (base + 7) (base + 8)
            (base + 9) (base + 10)
            (base + 11) (base + 12)
            (base + 13) (base + 14)
            (base + 15) (base + 16) := by
      simpa only [fs_zfc_collection_condition_open_rest] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight
            (FirstOrder.Derives.conjElimRight hRest))
    have hClassifierParameter :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_formula_code_condition_with_ids
            (Sₘ(Sₘ(numₘ(parameterValue)))) (x#(base + 2))
            (base + 7) (base + 8)
            (base + 9) (base + 10)
            (base + 11) (base + 12)
            (base + 13) (base + 14)
            (base + 15) (base + 16) :=
      fs_zfc_support_raw_schema_classifier_of_parameter_equality
        (Sₘ(Sₘ(x#base))) (Sₘ(Sₘ(numₘ(parameterValue))))
        parameterValue base
        (by simp [Term.substituteFree, set_variable])
        hParameterEquality hClassifier
    have hClassifierNumeral :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_formula_code_condition_with_ids
            (numₘ(parameterValue + 2)) (x#(base + 2))
            (base + 7) (base + 8)
            (base + 9) (base + 10)
            (base + 11) (base + 12)
            (base + 13) (base + 14)
            (base + 15) (base + 16) := by
      simpa [finite_numeral_term] using hClassifierParameter
    exact fs_zfc_support_raw_schema_classifier_falsum_of_decode_none
      (parameterValue + 2) bodyTokenValue base
      (fs_zfc_schema_coordinate_context_trace_fresh
        formula body parameterValue bodyTokenValue base
        hFormulaClosed
        (fs_zfc_collection_condition_open_body_freeSupport_subset
          formula raw base))
      hSequence hBodyTokenEquality hClassifierNumeral hDecode
  rw [fs_zfc_collection_condition_exists_shape
    formula raw base]
  simpa [raw, fs_zfc_schema_body_context] using
    fs_zfc_support_raw_exists_five_neg
      base (base + 1) (base + 2)
      (base + 3) (base + 4)
      body hBody hCase

/--
二元 schema 的 body Project 解码失败时，对象 replacement 条件不可成立。

这里只消费 replacement 开放体最前面的序列与 classifier；后续四段 shift 和三段
substitution 在该失败分支中无需展开。
-/
theorem
    fs_zfc_support_raw_replacement_condition_with_base_neg_of_project_decode_none
    (formula : SetTerm)
    (parameterValue bodyTokenValue : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hDecode :
      fs_project_hilbert_code_decode
        (parameterValue + 2) bodyTokenValue = none) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_condition_with_base
        formula
        (numₘ(godel_pair_value 1
          (godel_pair_value 2
            (godel_pair_value parameterValue bodyTokenValue))))
        base) := by
  let raw : Nat :=
    godel_pair_value 1
      (godel_pair_value 2
        (godel_pair_value parameterValue bodyTokenValue))
  let ids : List FreeVarId :=
    List.range 10 |>.map (base + ·)
  let body : SetFormula :=
    fs_zfc_replacement_condition_open_body formula (numₘ(raw)) base
  have hClosure :
      Formula.Admissible
        (ProofT.SchemaPlugin.witness_closure ids body) := by
    rw [← fs_zfc_replacement_condition_exists_shape
      formula (numₘ(raw)) base]
    exact
      fs_zfc_replacement_condition_with_base_admissible
        formula (numₘ(raw)) base hFormula
        (finite_numeral_term_admissible raw)
  have hBody :
      Formula.Admissible body :=
    ProofT.SchemaPlugin.witness_closure_body_admissible
      ids hClosure
  have hBodyNeg :
      Derives fs_zfc_support_raw_theory [] (¬ₘ body) := by
    nd_apply FirstOrder.Derives.negIntro
      (hBodyCheck :=
        Formula.check_admissible_complete hBody)
    let Γ : Context signature := [body]
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption (by simp [Γ])
    have hCertificateEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            fs_zfc_schema_certificate_term
              (numₘ(2)) (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_replacement_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hBounds :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_schema_certificate_bounds
            (numₘ(raw)) (numₘ(2))
            (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_replacement_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hBodyAt)
    apply fs_zfc_support_raw_schema_certificate_coordinates_elim
      raw 2 (x#base) (x#(base + 1))
      Formula.falsum
      (set_variable_admissible base)
      (set_variable_admissible (base + 1))
      Formula.Admissible.falsum
      hCertificateEquality hBounds
    intro decodedParameter decodedBodyToken hRaw
    have hRaw' :
        godel_pair_value 1
            (godel_pair_value 2
              (godel_pair_value parameterValue bodyTokenValue)) =
          godel_pair_value 1
            (godel_pair_value 2
              (godel_pair_value
                decodedParameter decodedBodyToken)) := by
      simpa [raw] using hRaw
    have hCoordinates :
        parameterValue = decodedParameter ∧
          bodyTokenValue = decodedBodyToken :=
      godel_pair_value_eq_iff.mp <|
        (godel_pair_value_eq_iff.mp <|
          (godel_pair_value_eq_iff.mp hRaw').2).2
    rcases hCoordinates with
      ⟨hParameter, hBodyToken⟩
    subst decodedParameter
    subst decodedBodyToken
    let Δ : Context signature :=
      (x#(base + 1) ≐ₘ numₘ(bodyTokenValue)) ::
        (x#base ≐ₘ numₘ(parameterValue)) :: Γ
    change Δ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum
    have hBodyAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption (by simp [Δ, Γ])
    have hBodyTokenEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 1) ≐ₘ numₘ(bodyTokenValue) :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hParameterEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#base ≐ₘ numₘ(parameterValue) :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hRest :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_replacement_condition_open_rest formula base := by
      simpa only [body,
        fs_zfc_replacement_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight hBodyAt)
    have hSequence :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          nat_sequence_code_condition_with_ids
            (x#(base + 2)) (x#(base + 1))
            (base + 10) (base + 11) := by
      simpa only [fs_zfc_replacement_condition_open_rest,
        fs_zfc_replacement_condition_rest] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hRest)
    have hClassifier :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_formula_code_condition_with_ids
            (Sₘ(Sₘ(x#base))) (x#(base + 2))
            (base + 12) (base + 13)
            (base + 14) (base + 15)
            (base + 16) (base + 17)
            (base + 18) (base + 19)
            (base + 20) (base + 21) := by
      simpa only [fs_zfc_replacement_condition_open_rest,
        fs_zfc_replacement_condition_rest] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight
            (FirstOrder.Derives.conjElimRight hRest))
    let classifier : SetFormula :=
      canonical_project_formula_code_condition_with_ids
        (Sₘ(Sₘ(x#base))) (x#(base + 2))
        (base + 12) (base + 13)
        (base + 14) (base + 15)
        (base + 16) (base + 17)
        (base + 18) (base + 19)
        (base + 20) (base + 21)
    have hClassifierSubstitution :
        Formula.substituteFree SetSort.set base
            (numₘ(parameterValue)) classifier =
          canonical_project_formula_code_condition_with_ids
            (Sₘ(Sₘ(numₘ(parameterValue)))) (x#(base + 2))
            (base + 12) (base + 13)
            (base + 14) (base + 15)
            (base + 16) (base + 17)
            (base + 18) (base + 19)
            (base + 20) (base + 21) := by
      simpa [classifier] using
        canonical_project_formula_code_condition_with_ids_substitute_closed
          (Sₘ(Sₘ(x#base))) (x#(base + 2))
          (numₘ(parameterValue))
          (Sₘ(Sₘ(numₘ(parameterValue)))) (x#(base + 2))
          base
          (base + 12) (base + 13)
          (base + 14) (base + 15)
          (base + 16) (base + 17)
          (base + 18) (base + 19)
          (base + 20) (base + 21)
          (fs_zfc_schema_base_ne_offset base 12 (by decide))
          (fs_zfc_schema_base_ne_offset base 13 (by decide))
          (fs_zfc_schema_base_ne_offset base 14 (by decide))
          (fs_zfc_schema_base_ne_offset base 15 (by decide))
          (fs_zfc_schema_base_ne_offset base 16 (by decide))
          (fs_zfc_schema_base_ne_offset base 17 (by decide))
          (fs_zfc_schema_base_ne_offset base 18 (by decide))
          (fs_zfc_schema_base_ne_offset base 19 (by decide))
          (fs_zfc_schema_base_ne_offset base 20 (by decide))
          (fs_zfc_schema_base_ne_offset base 21 (by decide))
          ⟨finite_numeral_term_admissible parameterValue,
            finite_numeral_term_freeSupport parameterValue⟩
          (by simp [Term.substituteFree, set_variable])
          (by simp [Term.substituteFree, set_variable])
    have hClassifierAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          Formula.substituteFree SetSort.set base
            (x#base) classifier := by
      simpa [classifier, Formula.substituteFree_self] using
        hClassifier
    have hClassifierParameter :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_formula_code_condition_with_ids
            (numₘ(parameterValue + 2)) (x#(base + 2))
            (base + 12) (base + 13)
            (base + 14) (base + 15)
            (base + 16) (base + 17)
            (base + 18) (base + 19)
            (base + 20) (base + 21) := by
      have hTransport :=
        FirstOrder.Derives.eq_subst_m
          hParameterEquality hClassifierAt
      rw [hClassifierSubstitution] at hTransport
      simpa [finite_numeral_term] using hTransport
    let tokens : List Nat :=
      nat_sequence_decode bodyTokenValue
    have hBodyTokenCodeEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 1) ≐ₘ
            numₘ(nat_sequence_code_value tokens) := by
      simpa [tokens, nat_sequence_code_value_decode] using
        hBodyTokenEquality
    let sequenceCondition : SetFormula :=
      nat_sequence_code_condition_with_ids
        (x#(base + 2)) (x#(base + 1))
        (base + 10) (base + 11)
    have hSequenceSubstitution :
        Formula.substituteFree SetSort.set (base + 1)
            (numₘ(nat_sequence_code_value tokens))
            sequenceCondition =
          nat_sequence_code_condition_with_ids
            (x#(base + 2))
            (numₘ(nat_sequence_code_value tokens))
            (base + 10) (base + 11) := by
      simpa [sequenceCondition] using
        nat_sequence_code_condition_with_ids_substitute_closed
          (x#(base + 2)) (x#(base + 1))
          (numₘ(nat_sequence_code_value tokens))
          (x#(base + 2))
          (numₘ(nat_sequence_code_value tokens))
          (base + 1) (base + 10) (base + 11)
          (fs_zfc_schema_offset_ne_offset base 1 10 (by decide))
          (fs_zfc_schema_offset_ne_offset base 1 11 (by decide))
          (finite_numeral_term_admissible
            (nat_sequence_code_value tokens)).2
          (by
            rw [finite_numeral_term_freeSupport]
            exact List.not_mem_nil)
          (by
            rw [finite_numeral_term_freeSupport]
            exact List.not_mem_nil)
          (by simp [Term.substituteFree, set_variable])
          (by simp [Term.substituteFree, set_variable])
    have hSequenceAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          Formula.substituteFree SetSort.set (base + 1)
            (x#(base + 1)) sequenceCondition := by
      simpa [sequenceCondition,
        Formula.substituteFree_self] using hSequence
    have hSequenceNumeral :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          nat_sequence_code_condition_with_ids
            (x#(base + 2))
            (numₘ(nat_sequence_code_value tokens))
            (base + 10) (base + 11) := by
      have hTransport :=
        FirstOrder.Derives.eq_subst_m
          hBodyTokenCodeEquality hSequenceAt
      simpa only [hSequenceSubstitution] using hTransport
    have hSequenceEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 2) ≐ₘ
            standard_token_sequence tokens := by
      exact FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp) <|
            CertifiedProof.fs_zfc_support_raw_nat_sequence_condition_unique_imp
              (x#(base + 2)) tokens
              (base + 10) (base + 11)
              (set_variable_admissible (base + 2))
              (fs_zfc_schema_offset_ne_offset base 10 11 (by decide))
              (fs_zfc_schema_set_variable_fresh_of_ne
                (base + 10) (base + 2)
                (fs_zfc_schema_offset_ne_offset base 10 2 (by decide)))
              (fs_zfc_schema_set_variable_fresh_of_ne
                (base + 11) (base + 2)
                (fs_zfc_schema_offset_ne_offset base 11 2 (by decide))))
        hSequenceNumeral
    let classifierGround : SetFormula :=
      canonical_project_formula_code_condition_with_ids
        (numₘ(parameterValue + 2))
        (standard_token_sequence tokens)
        (base + 12) (base + 13)
        (base + 14) (base + 15)
        (base + 16) (base + 17)
        (base + 18) (base + 19)
        (base + 20) (base + 21)
    have hClassifierGroundSubstitution :
        Formula.substituteFree SetSort.set (base + 2)
            (standard_token_sequence tokens)
            (canonical_project_formula_code_condition_with_ids
              (numₘ(parameterValue + 2)) (x#(base + 2))
              (base + 12) (base + 13)
              (base + 14) (base + 15)
              (base + 16) (base + 17)
              (base + 18) (base + 19)
              (base + 20) (base + 21)) =
          classifierGround := by
      simpa [classifierGround] using
        canonical_project_formula_code_condition_with_ids_substitute_closed
          (numₘ(parameterValue + 2)) (x#(base + 2))
          (standard_token_sequence tokens)
          (numₘ(parameterValue + 2))
          (standard_token_sequence tokens)
          (base + 2)
          (base + 12) (base + 13)
          (base + 14) (base + 15)
          (base + 16) (base + 17)
          (base + 18) (base + 19)
          (base + 20) (base + 21)
          (fs_zfc_schema_offset_ne_offset base 2 12 (by decide))
          (fs_zfc_schema_offset_ne_offset base 2 13 (by decide))
          (fs_zfc_schema_offset_ne_offset base 2 14 (by decide))
          (fs_zfc_schema_offset_ne_offset base 2 15 (by decide))
          (fs_zfc_schema_offset_ne_offset base 2 16 (by decide))
          (fs_zfc_schema_offset_ne_offset base 2 17 (by decide))
          (fs_zfc_schema_offset_ne_offset base 2 18 (by decide))
          (fs_zfc_schema_offset_ne_offset base 2 19 (by decide))
          (fs_zfc_schema_offset_ne_offset base 2 20 (by decide))
          (fs_zfc_schema_offset_ne_offset base 2 21 (by decide))
          ⟨standard_token_sequence_admissible tokens,
            standard_token_sequence_freeSupport_nil tokens⟩
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            rw [finite_numeral_term_freeSupport]
            exact List.not_mem_nil)
          (by simp [Term.substituteFree, set_variable])
    have hClassifierParameterAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          Formula.substituteFree SetSort.set (base + 2)
            (x#(base + 2))
            (canonical_project_formula_code_condition_with_ids
              (numₘ(parameterValue + 2)) (x#(base + 2))
              (base + 12) (base + 13)
              (base + 14) (base + 15)
              (base + 16) (base + 17)
              (base + 18) (base + 19)
              (base + 20) (base + 21)) := by
      simpa [Formula.substituteFree_self] using
        hClassifierParameter
    have hClassifierGround :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] classifierGround := by
      have hTransport :=
        FirstOrder.Derives.eq_subst_m
          hSequenceEquality hClassifierParameterAt
      simpa only [hClassifierGroundSubstitution] using
        hTransport
    have hDecodeTokens :
        fs_project_hilbert_tokens_decode
          (parameterValue + 2) tokens = none := by
      simpa [fs_project_hilbert_code_decode, tokens] using
        hDecode
    exact FirstOrder.Derives.negElim
      hClassifierGround
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) <| by
          simpa [classifierGround] using
            fs_zfc_support_raw_canonical_project_formula_code_condition_from_base_neg_of_project_decode_none
              (parameterValue + 2) tokens (base + 12)
              hDecodeTokens)
  rw [fs_zfc_replacement_condition_exists_shape
    formula (numₘ(raw)) base]
  exact ProofT.SchemaPlugin.witness_closure_neg
    (fun hAxiom =>
      (fs_zfc_support_raw_theory_sentence hAxiom).2)
    ids hBody hBodyNeg

/--
分离生成器失败且证书标签已确定时，完整显式-base 对象证书条件被否定。
-/
theorem
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_separation_generate_none
    (formula : SetTerm)
    (certificate : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_support_generate certificate = none)
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hSeparation :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 0) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition_with_base
        formula (numₘ(certificate)) base) := by
  let payload : Nat := (godel_unpair_value certificate).2
  let schemaPayload : Nat := (godel_unpair_value payload).2
  let parameterValue : Nat := (godel_unpair_value schemaPayload).1
  let bodyTokenValue : Nat := (godel_unpair_value schemaPayload).2
  have hPayload :
      payload = godel_pair_value 0 schemaPayload := by
    calc
      payload =
          godel_pair_value
            (godel_unpair_value payload).1
            (godel_unpair_value payload).2 :=
        (godel_unpair_value_spec payload).symm
      _ = godel_pair_value 0 schemaPayload := by
        simp [payload, schemaPayload, hSeparation]
  have hSchemaPayload :
      schemaPayload =
        godel_pair_value parameterValue bodyTokenValue := by
    exact (godel_unpair_value_spec schemaPayload).symm
  have hRaw :
      certificate =
        godel_pair_value 1
          (godel_pair_value 0
            (godel_pair_value parameterValue bodyTokenValue)) := by
    calc
      certificate =
          godel_pair_value
            (godel_unpair_value certificate).1
            (godel_unpair_value certificate).2 :=
        (godel_unpair_value_spec certificate).symm
      _ = godel_pair_value 1 payload := by
        simp [payload, hOuter]
      _ = godel_pair_value 1
          (godel_pair_value 0 schemaPayload) := by
        rw [hPayload]
      _ = godel_pair_value 1
          (godel_pair_value 0
            (godel_pair_value parameterValue bodyTokenValue)) := by
        rw [hSchemaPayload]
  rw [hRaw] at hGenerate
  have hSchemaGenerate :
      (fs_zfc_separation_generate
        (godel_pair_value parameterValue bodyTokenValue)).map
          (fun sentence =>
            Formula.hilbertize SetSort.set
              (fs_embed_project_sentence sentence)) =
        none := by
    simpa [fs_zfc_support_generate,
      fs_zfc_embedded_hilbert_generator,
      fs_zfc_axiom_generate,
      godel_unpair_value_pair] using hGenerate
  have hUnaryDecode :
      fs_project_unary_schema_hilbert_decode
        parameterValue bodyTokenValue = none := by
    unfold fs_zfc_separation_generate at hSchemaGenerate
    rw [godel_unpair_value_pair] at hSchemaGenerate
    simpa using hSchemaGenerate
  have hDecode :
      fs_project_hilbert_code_decode
        (parameterValue + 1) bodyTokenValue = none :=
    (fs_project_unary_schema_hilbert_decode_eq_none_iff
      parameterValue bodyTokenValue).mp hUnaryDecode
  rw [hRaw]
  apply
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_branch_negs
      formula
      (numₘ(godel_pair_value 1
        (godel_pair_value 0
          (godel_pair_value parameterValue bodyTokenValue))))
      base hFormula
      (finite_numeral_term_admissible _)
  · exact
      fs_zfc_support_raw_fixed_table_condition_neg_of_schema_code
        formula
        (godel_pair_value 0
          (godel_pair_value parameterValue bodyTokenValue))
        hFormula
  · exact
      fs_zfc_schema_plugins_elim
        (fs_zfc_support_raw_separation_condition_with_base_neg_of_project_decode_none
          formula parameterValue bodyTokenValue base
          hFormula hFormulaClosed hDecode)
        (by
          apply
            fs_zfc_support_raw_collection_condition_with_base_neg_of_code_ne
              formula
              (godel_pair_value 1
                (godel_pair_value 0
                  (godel_pair_value parameterValue bodyTokenValue)))
              base hFormula
          intro parameter bodyToken hEquality
          exact Nat.zero_ne_one <|
            (godel_pair_value_eq_iff.mp <|
              (godel_pair_value_eq_iff.mp hEquality).2).1)

/--
收集生成器失败且证书标签已确定时，完整显式-base 对象证书条件被否定。
-/
theorem
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_collection_generate_none
    (formula : SetTerm)
    (certificate : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_support_generate certificate = none)
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hCollection :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 1) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition_with_base
        formula (numₘ(certificate)) base) := by
  let payload : Nat := (godel_unpair_value certificate).2
  let schemaPayload : Nat := (godel_unpair_value payload).2
  let parameterValue : Nat := (godel_unpair_value schemaPayload).1
  let bodyTokenValue : Nat := (godel_unpair_value schemaPayload).2
  have hPayload :
      payload = godel_pair_value 1 schemaPayload := by
    calc
      payload =
          godel_pair_value
            (godel_unpair_value payload).1
            (godel_unpair_value payload).2 :=
        (godel_unpair_value_spec payload).symm
      _ = godel_pair_value 1 schemaPayload := by
        simp [payload, schemaPayload, hCollection]
  have hSchemaPayload :
      schemaPayload =
        godel_pair_value parameterValue bodyTokenValue := by
    exact (godel_unpair_value_spec schemaPayload).symm
  have hRaw :
      certificate =
        godel_pair_value 1
          (godel_pair_value 1
            (godel_pair_value parameterValue bodyTokenValue)) := by
    calc
      certificate =
          godel_pair_value
            (godel_unpair_value certificate).1
            (godel_unpair_value certificate).2 :=
        (godel_unpair_value_spec certificate).symm
      _ = godel_pair_value 1 payload := by
        simp [payload, hOuter]
      _ = godel_pair_value 1
          (godel_pair_value 1 schemaPayload) := by
        rw [hPayload]
      _ = godel_pair_value 1
          (godel_pair_value 1
            (godel_pair_value parameterValue bodyTokenValue)) := by
        rw [hSchemaPayload]
  rw [hRaw] at hGenerate
  have hSchemaGenerate :
      (fs_zfc_collection_generate
        (godel_pair_value parameterValue bodyTokenValue)).map
          (fun sentence =>
            Formula.hilbertize SetSort.set
              (fs_embed_project_sentence sentence)) =
        none := by
    simpa [fs_zfc_support_generate,
      fs_zfc_embedded_hilbert_generator,
      fs_zfc_axiom_generate,
      godel_unpair_value_pair] using hGenerate
  have hBinaryDecode :
      fs_project_binary_schema_hilbert_decode
        parameterValue bodyTokenValue = none := by
    unfold fs_zfc_collection_generate at hSchemaGenerate
    rw [godel_unpair_value_pair] at hSchemaGenerate
    simpa using hSchemaGenerate
  have hDecode :
      fs_project_hilbert_code_decode
        (parameterValue + 2) bodyTokenValue = none :=
    (fs_project_binary_schema_hilbert_decode_eq_none_iff
      parameterValue bodyTokenValue).mp hBinaryDecode
  rw [hRaw]
  apply
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_branch_negs
      formula
      (numₘ(godel_pair_value 1
        (godel_pair_value 1
          (godel_pair_value parameterValue bodyTokenValue))))
      base hFormula
      (finite_numeral_term_admissible _)
  · exact
      fs_zfc_support_raw_fixed_table_condition_neg_of_schema_code
        formula
        (godel_pair_value 1
          (godel_pair_value parameterValue bodyTokenValue))
        hFormula
  · exact
      fs_zfc_schema_plugins_elim
        (by
          apply
            fs_zfc_support_raw_separation_condition_with_base_neg_of_code_ne
              formula
              (godel_pair_value 1
                (godel_pair_value 1
                  (godel_pair_value parameterValue bodyTokenValue)))
              base hFormula
          intro parameter bodyToken hEquality
          exact Nat.one_ne_zero <|
            (godel_pair_value_eq_iff.mp <|
              (godel_pair_value_eq_iff.mp hEquality).2).1)
        (fs_zfc_support_raw_collection_condition_with_base_neg_of_project_decode_none
          formula parameterValue bodyTokenValue base
          hFormula hFormulaClosed hDecode)

/-- 分离生成失败分支的动态 fresh-base 包装。 -/
theorem
    fs_zfc_support_raw_object_certificate_condition_neg_of_separation_generate_none
    (formula : SetTerm)
    (certificate : Nat)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_support_generate certificate = none)
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hSeparation :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 0) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition
        formula (numₘ(certificate))) := by
  exact
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_separation_generate_none
      formula certificate
      (ProofT.schema_base [formula, numₘ(certificate)])
      hFormula hFormulaClosed hGenerate hOuter hSeparation

/-- 收集生成失败分支的动态 fresh-base 包装。 -/
theorem
    fs_zfc_support_raw_object_certificate_condition_neg_of_collection_generate_none
    (formula : SetTerm)
    (certificate : Nat)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_support_generate certificate = none)
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hCollection :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 1) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition
        formula (numₘ(certificate))) := by
  exact
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_collection_generate_none
      formula certificate
      (ProofT.schema_base [formula, numₘ(certificate)])
      hFormula hFormulaClosed hGenerate hOuter hCollection

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
