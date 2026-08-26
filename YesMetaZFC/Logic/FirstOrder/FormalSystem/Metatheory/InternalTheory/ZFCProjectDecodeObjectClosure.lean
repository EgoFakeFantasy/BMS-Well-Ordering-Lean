import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCProjectDecodeHostClosure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalFirstOrderFailureAdapter

/-!
# Project 构造码反演在 ZFC raw theory 上的包装

本模块只把既有 Gödel quotation 构造反演提升到 `fs_zfc_support_raw_theory`。
所有结论均为非递归构造等式或直接拒绝，不包含 replay trace。
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

theorem fs_zfc_support_raw_lift_gq_premises
    {Γ premises :
      Context Nonlogical.BasicSetTheory.signature}
    {conclusion : SetFormula}
    (hPremises :
      ∀ formula, formula ∈ premises →
        Γ ⊢ₘ[fs_zfc_support_raw_theory] formula)
    (hGQ :
      premises ⊢ₘ[godel_quotation_theory] conclusion) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] conclusion := by
  apply FirstOrder.Derives.multi_cut
    (premises := premises)
  · exact hPremises
  · exact
      (FirstOrder.Derives.theory_weaken
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_godel_quotation
            hFormula)
        hGQ).context_weaken_append

/--
规范原子分类条件对一个外部自由变量的替换只作用于深度与公式码参数。
四个局部见证仍由原条件内部绑定，因此这里显式记录替换项对这些 binder 的新鲜性。
-/
theorem canonical_project_atomic_code_condition_with_ids_substitute_free
    (depth code replacement depthResult codeResult : SetTerm)
    (sourceId leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId)
    (hSourceNeLeftCode :
      sourceId ≠ leftVariableCodeId)
    (hSourceNeRightCode :
      sourceId ≠ rightVariableCodeId)
    (hSourceNeLeftDepth :
      sourceId ≠ leftVariableDepthId)
    (hSourceNeRightDepth :
      sourceId ≠ rightVariableDepthId)
    (hReplacement :
      Term.Admissible replacement
        Nonlogical.BasicSetTheory.SetSort.set)
    (hReplacementFreshLeftCode :
      (Nonlogical.BasicSetTheory.SetSort.set,
        leftVariableCodeId) ∉
        Term.freeSupport replacement)
    (hReplacementFreshRightCode :
      (Nonlogical.BasicSetTheory.SetSort.set,
        rightVariableCodeId) ∉
        Term.freeSupport replacement)
    (hReplacementFreshLeftDepth :
      (Nonlogical.BasicSetTheory.SetSort.set,
        leftVariableDepthId) ∉
        Term.freeSupport replacement)
    (hReplacementFreshRightDepth :
      (Nonlogical.BasicSetTheory.SetSort.set,
        rightVariableDepthId) ∉
        Term.freeSupport replacement)
    (hDepthSubstitution :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          sourceId replacement depth =
        depthResult)
    (hCodeSubstitution :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          sourceId replacement code =
        codeResult) :
    Formula.substituteFree
        Nonlogical.BasicSetTheory.SetSort.set
        sourceId replacement
        (canonical_project_atomic_code_condition_with_ids
          depth code
          leftVariableCodeId rightVariableCodeId
          leftVariableDepthId rightVariableDepthId) =
      canonical_project_atomic_code_condition_with_ids
        depthResult codeResult
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId := by
  have hNumeralFixed (number : Nat) :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          sourceId replacement (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hComm
      (binderId : FreeVarId)
      (hNe : sourceId ≠ binderId)
      (hFresh :
        (Nonlogical.BasicSetTheory.SetSort.set,
          binderId) ∉
          Term.freeSupport replacement)
      (formula : SetFormula) :
      Formula.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          sourceId replacement
          (Formula.closeFreeAt
            Nonlogical.BasicSetTheory.SetSort.set
            binderId 0 formula) =
        Formula.closeFreeAt
          Nonlogical.BasicSetTheory.SetSort.set
          binderId 0
          (Formula.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set
            sourceId replacement formula) :=
    (Formula.closeFreeAt_substituteFree_comm
      Nonlogical.BasicSetTheory.SetSort.set
      sourceId binderId 0 replacement formula
      hNe hReplacement.2 hFresh).symm
  simp [
    canonical_project_atomic_code_condition_with_ids,
    canonical_scoped_variable_code_condition_with_id,
    Formula.substituteFree, Term.substituteFree,
    GodelQuotation.Numbered.argument_sequence,
    GodelQuotation.standard_sequence_from,
    set_variable,
    hComm leftVariableCodeId hSourceNeLeftCode
      hReplacementFreshLeftCode,
    hComm rightVariableCodeId hSourceNeRightCode
      hReplacementFreshRightCode,
    hComm leftVariableDepthId hSourceNeLeftDepth
      hReplacementFreshLeftDepth,
    hComm rightVariableDepthId hSourceNeRightDepth
      hReplacementFreshRightDepth,
    hDepthSubstitution, hCodeSubstitution,
    hNumeralFixed,
    Ne.symm hSourceNeLeftCode,
    Ne.symm hSourceNeRightCode,
    Ne.symm hSourceNeLeftDepth,
    Ne.symm hSourceNeRightDepth]
  rfl

theorem
    fs_zfc_support_raw_formula_child_falsum_of_named_decode_none
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (freeBase : Nat) (boundNames : List Nat)
    (child : SetTerm) (tokens : List Nat)
    (hChild :
      Term.CheckCertificate child SetSort.set)
    (hMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        child ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        child ≐ₘ standard_token_sequence tokens)
    (hTokens : FSFormulaTokens tokens)
    (hBinders : FSFormulaBinderTokens tokens)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hStandardMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ∈ₘ
          FormulaCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (membership_left_iff_of_equality
        child
        (standard_token_sequence tokens)
        FormulaCodeₘ
        hChild.admissible
        (standard_token_sequence_admissible tokens)
        formula_code_set_term_admissible
        hEquality)
      hMember
  have hNotMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ¬ₘ (standard_token_sequence tokens ∈ₘ
          FormulaCodeₘ) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <|
          gq_standard_formula_code_not_of_decode_none
            freeBase boundNames tokens
            hTokens hBinders hDecode
  exact FirstOrder.Derives.negElim
    hStandardMember hNotMember

theorem fs_zfc_support_raw_negation_body_eq_standard
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (body : SetTerm) (bodyTokens : List Nat)
    (hBody : Term.CheckCertificate body SetSort.set)
    (hBodyMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        body ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence
            (Numbered.negation_tokens bodyTokens) ≐ₘ
          neg_codeₘ(body)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      body ≐ₘ standard_token_sequence bodyTokens := by
  have hBodyFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition body :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      body hBody.admissible hBodyMember
  let premises :
      Context Nonlogical.BasicSetTheory.signature := [
    finite_sequence_condition body,
    standard_token_sequence
        (Numbered.negation_tokens bodyTokens) ≐ₘ
      neg_codeₘ(body)]
  have hGQ :
      premises ⊢ₘ[godel_quotation_theory]
        body ≐ₘ standard_token_sequence bodyTokens :=
    gq_negation_body_eq_standard_token_sequence
      body bodyTokens
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      (hBody := hBody)
      (FirstOrder.Derives.assumption
        (by simp [premises]))
  exact fs_zfc_support_raw_lift_gq_premises
    (premises := premises)
    (by
      intro formula hFormula
      simp only [premises, List.mem_cons,
        List.not_mem_nil, or_false] at hFormula
      rcases hFormula with rfl | rfl
      · exact hBodyFinite
      · exact hEquality)
    hGQ

theorem fs_zfc_support_raw_negation_falsum_of_not_shape
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (body : SetTerm) (tokens : List Nat)
    (hBody : Term.CheckCertificate body SetSort.set)
    (hBodyMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        body ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          neg_codeₘ(body))
    (hShape :
      tokens ≠
        Numbered.negation_tokens
          ((tokens.drop 2).take
            (tokens.length - 3))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hBodyFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition body :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      body hBody.admissible hBodyMember
  let premises :
      Context Nonlogical.BasicSetTheory.signature := [
    finite_sequence_condition body,
    standard_token_sequence tokens ≐ₘ
      neg_codeₘ(body)]
  have hGQ :
      premises ⊢ₘ[godel_quotation_theory]
        Formula.falsum :=
    gq_negation_standard_code_falsum_of_not_slice_shape
      body tokens
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      hShape (hBody := hBody)
  exact fs_zfc_support_raw_lift_gq_premises
    (premises := premises)
    (by
      intro formula hFormula
      simp only [premises, List.mem_cons,
        List.not_mem_nil, or_false] at hFormula
      rcases hFormula with rfl | rfl
      · exact hBodyFinite
      · exact hEquality)
    hGQ

theorem fs_zfc_support_raw_implication_bodies_eq_standard
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (left right : SetTerm) (tokens : List Nat)
    (leftLength rightLength : Nat)
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set)
    (hLeftMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        left ∈ₘ FormulaCodeₘ)
    (hRightMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        right ∈ₘ FormulaCodeₘ)
    (hLeftDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(left) ≐ₘ numₘ(leftLength))
    (hRightDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(right) ≐ₘ numₘ(rightLength))
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          imp_codeₘ(left, right)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (left ≐ₘ standard_token_sequence
        ((tokens.drop 1).take leftLength)) ∧ₘ
      (right ≐ₘ standard_token_sequence
        ((tokens.drop (leftLength + 2)).take rightLength)) := by
  have hLeftFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition left :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      left hLeft.admissible hLeftMember
  have hRightFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition right :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      right hRight.admissible hRightMember
  let premises :
      Context Nonlogical.BasicSetTheory.signature := [
    finite_sequence_condition left,
    finite_sequence_condition right,
    domₘ(left) ≐ₘ numₘ(leftLength),
    domₘ(right) ≐ₘ numₘ(rightLength),
    standard_token_sequence tokens ≐ₘ
      imp_codeₘ(left, right)]
  have hGQ :
      premises ⊢ₘ[godel_quotation_theory]
        (left ≐ₘ standard_token_sequence
          ((tokens.drop 1).take leftLength)) ∧ₘ
        (right ≐ₘ standard_token_sequence
          ((tokens.drop (leftLength + 2)).take rightLength)) :=
      gq_implication_bodies_eq_standard_token_slices_of_domains
        left right tokens leftLength rightLength
        (FirstOrder.Derives.assumption
          (by simp [premises]))
        (FirstOrder.Derives.assumption
          (by simp [premises]))
        (FirstOrder.Derives.assumption
          (by simp [premises]))
        (FirstOrder.Derives.assumption
          (by simp [premises]))
        (FirstOrder.Derives.assumption
          (by simp [premises]))
        (hLeft := hLeft) (hRight := hRight)
  exact fs_zfc_support_raw_lift_gq_premises
    (premises := premises)
    (by
      intro formula hFormula
      simp only [premises, List.mem_cons,
        List.not_mem_nil, or_false] at hFormula
      rcases hFormula with
        rfl | rfl | rfl | rfl | rfl
      · exact hLeftFinite
      · exact hRightFinite
      · exact hLeftDomain
      · exact hRightDomain
      · exact hEquality)
    hGQ

theorem fs_zfc_support_raw_implication_left_domain_mem
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (left right : SetTerm)
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set)
    (hLeftMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        left ∈ₘ FormulaCodeₘ)
    (hRightMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        right ∈ₘ FormulaCodeₘ) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      domₘ(left) ∈ₘ
        domₘ(imp_codeₘ(left, right)) := by
  have hLeftFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition left :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      left hLeft.admissible hLeftMember
  have hRightFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition right :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      right hRight.admissible hRightMember
  let premises :
      Context Nonlogical.BasicSetTheory.signature := [
    finite_sequence_condition left,
    finite_sequence_condition right]
  have hGQ :
      premises ⊢ₘ[godel_quotation_theory]
        domₘ(left) ∈ₘ
          domₘ(imp_codeₘ(left, right)) :=
    gq_implication_left_domain_mem_code_domain
      left right
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      (hLeft := hLeft) (hRight := hRight)
  exact fs_zfc_support_raw_lift_gq_premises
    (premises := premises)
    (by
      intro formula hFormula
      simp only [premises, List.mem_cons,
        List.not_mem_nil, or_false] at hFormula
      rcases hFormula with rfl | rfl
      · exact hLeftFinite
      · exact hRightFinite)
    hGQ

theorem fs_zfc_support_raw_implication_right_domain_mem
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (left right : SetTerm) (leftLength : Nat)
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set)
    (hLeftMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        left ∈ₘ FormulaCodeₘ)
    (hRightMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        right ∈ₘ FormulaCodeₘ)
    (hLeftDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(left) ≐ₘ numₘ(leftLength)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      domₘ(right) ∈ₘ
        domₘ(imp_codeₘ(left, right)) := by
  have hLeftFinite :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      left hLeft.admissible hLeftMember
  have hRightFinite :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      right hRight.admissible hRightMember
  let premises :
      Context Nonlogical.BasicSetTheory.signature := [
    finite_sequence_condition left,
    finite_sequence_condition right,
    domₘ(left) ≐ₘ numₘ(leftLength)]
  have hGQ :
      premises ⊢ₘ[godel_quotation_theory]
        domₘ(right) ∈ₘ
          domₘ(imp_codeₘ(left, right)) :=
    gq_implication_right_domain_mem_code_domain
      left right leftLength
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      (hLeft := hLeft) (hRight := hRight)
  exact fs_zfc_support_raw_lift_gq_premises
    (premises := premises)
    (by
      intro formula hFormula
      simp only [premises, List.mem_cons,
        List.not_mem_nil, or_false] at hFormula
      rcases hFormula with rfl | rfl | rfl
      · exact hLeftFinite
      · exact hRightFinite
      · exact hLeftDomain)
    hGQ

theorem fs_zfc_support_raw_implication_falsum_of_not_shape
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (left right : SetTerm) (tokens : List Nat)
    (leftLength rightLength : Nat)
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set)
    (hLeftMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        left ∈ₘ FormulaCodeₘ)
    (hRightMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        right ∈ₘ FormulaCodeₘ)
    (hLeftDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(left) ≐ₘ numₘ(leftLength))
    (hRightDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(right) ≐ₘ numₘ(rightLength))
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          imp_codeₘ(left, right))
    (hShape :
      tokens ≠
        Numbered.implication_tokens
          ((tokens.drop 1).take leftLength)
          ((tokens.drop (leftLength + 2)).take rightLength)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hLeftFinite :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      left hLeft.admissible hLeftMember
  have hRightFinite :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      right hRight.admissible hRightMember
  let premises :
      Context Nonlogical.BasicSetTheory.signature := [
    finite_sequence_condition left,
    finite_sequence_condition right,
    domₘ(left) ≐ₘ numₘ(leftLength),
    domₘ(right) ≐ₘ numₘ(rightLength),
    standard_token_sequence tokens ≐ₘ
      imp_codeₘ(left, right)]
  have hGQ :
      premises ⊢ₘ[godel_quotation_theory]
        Formula.falsum :=
    gq_implication_standard_code_falsum_of_not_slice_shape
      left right tokens leftLength rightLength
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      hShape (hLeft := hLeft) (hRight := hRight)
  exact fs_zfc_support_raw_lift_gq_premises
    (premises := premises)
    (by
      intro formula hFormula
      simp only [premises, List.mem_cons,
        List.not_mem_nil, or_false] at hFormula
      rcases hFormula with
        rfl | rfl | rfl | rfl | rfl
      · exact hLeftFinite
      · exact hRightFinite
      · exact hLeftDomain
      · exact hRightDomain
      · exact hEquality)
    hGQ

theorem fs_zfc_support_raw_universal_body_eq_standard
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (name : Nat) (body : SetTerm)
    (bodyTokens : List Nat)
    (hBody : Term.CheckCertificate body SetSort.set)
    (hBodyMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        body ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence
            (Numbered.universal_tokens name bodyTokens) ≐ₘ
          forall_codeₘ(
            Numbered.named_variable_code name, body)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      body ≐ₘ standard_token_sequence bodyTokens := by
  have hBodyFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition body :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      body hBody.admissible hBodyMember
  let premises :
      Context Nonlogical.BasicSetTheory.signature := [
    finite_sequence_condition body,
    standard_token_sequence
        (Numbered.universal_tokens name bodyTokens) ≐ₘ
      forall_codeₘ(
        Numbered.named_variable_code name, body)]
  have hGQ :
      premises ⊢ₘ[godel_quotation_theory]
        body ≐ₘ standard_token_sequence bodyTokens :=
    gq_universal_body_eq_standard_token_sequence_of_standard_equality
      name body bodyTokens
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      (hBody := hBody)
      (FirstOrder.Derives.assumption
        (by simp [premises]))
  exact fs_zfc_support_raw_lift_gq_premises
    (premises := premises)
    (by
      intro formula hFormula
      simp only [premises, List.mem_cons,
        List.not_mem_nil, or_false] at hFormula
      rcases hFormula with rfl | rfl
      · exact hBodyFinite
      · exact hEquality)
    hGQ

theorem fs_zfc_support_raw_universal_body_domain_mem
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (name : Nat) (body : SetTerm)
    (hBody : Term.CheckCertificate body SetSort.set)
    (hBodyMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        body ∈ₘ FormulaCodeₘ) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      domₘ(body) ∈ₘ
        domₘ(forall_codeₘ(
          Numbered.named_variable_code name, body)) := by
  have hBodyFinite :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        finite_sequence_condition body :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      body hBody.admissible hBodyMember
  let premises :
      Context Nonlogical.BasicSetTheory.signature := [
    finite_sequence_condition body]
  have hGQ :
      premises ⊢ₘ[godel_quotation_theory]
        domₘ(body) ∈ₘ
          domₘ(forall_codeₘ(
            Numbered.named_variable_code name, body)) :=
    gq_universal_body_domain_mem_code_domain
      name body
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      (hBody := hBody)
  exact fs_zfc_support_raw_lift_gq_premises
    (premises := premises)
    (by
      intro formula hFormula
      simp only [premises, List.mem_cons,
        List.not_mem_nil, or_false] at hFormula
      rcases hFormula with rfl
      exact hBodyFinite)
    hGQ

theorem fs_zfc_support_raw_universal_falsum_of_not_shape
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (name : Nat) (body : SetTerm)
    (tokens : List Nat) (bodyLength : Nat)
    (hBody : Term.CheckCertificate body SetSort.set)
    (hBodyMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        body ∈ₘ FormulaCodeₘ)
    (hBodyDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(body) ≐ₘ numₘ(bodyLength))
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ
          forall_codeₘ(
            Numbered.named_variable_code name, body))
    (hShape :
      tokens ≠
        Numbered.universal_tokens name
          ((tokens.drop 3).take bodyLength)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hBodyFinite :=
    fs_zfc_support_raw_formula_code_member_implies_finite_sequence
      body hBody.admissible hBodyMember
  let premises :
      Context Nonlogical.BasicSetTheory.signature := [
    finite_sequence_condition body,
    domₘ(body) ≐ₘ numₘ(bodyLength),
    standard_token_sequence tokens ≐ₘ
      forall_codeₘ(
        Numbered.named_variable_code name, body)]
  have hGQ :
      premises ⊢ₘ[godel_quotation_theory]
        Formula.falsum :=
    gq_universal_standard_code_falsum_of_not_slice_shape
      name body tokens bodyLength
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      (FirstOrder.Derives.assumption
        (by simp [premises]))
      hShape (hBody := hBody)
  exact fs_zfc_support_raw_lift_gq_premises
    (premises := premises)
    (by
      intro formula hFormula
      simp only [premises, List.mem_cons,
        List.not_mem_nil, or_false] at hFormula
      rcases hFormula with rfl | rfl | rfl
      · exact hBodyFinite
      · exact hBodyDomain
      · exact hEquality)
    hGQ

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
