import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoderComposition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.Opening
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCodeReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaBinderCode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.ImplicationConstructionInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.UniversalConstructionInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.VariableSymbolInversion

/-!
# FormalSystem 公式码的 checked replay 反演

本模块把对象公式构造码与显式环境 token decoder 对齐。每个递归构造分支都应
给出二选一结果：外壳形状立即在对象层矛盾，或解码失败严格下降到更短的子式
token 串。
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
对象否定构造与整行标准 token 串相等但显式环境解码失败时，失败严格下降到正文。

若整串不是由其规范中段重建出的否定串，则对象构造等式本身已经推出矛盾；
否则正文码等于该中段的标准序列，且正文解码必定失败。
-/
theorem gq_negation_code_decode_failure_descends
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (body : SetTerm) (tokens : List Nat)
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check)
    (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          neg_codeₘ(body))
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    (Γ ⊢ₘ[godel_quotation_theory]
        Formula.falsum) ∨
      ∃ bodyTokens,
        bodyTokens.length < tokens.length ∧
          fs_named_hilbert_tokens_decode_with_env
              freeBase boundNames bodyTokens =
            none ∧
          Γ ⊢ₘ[godel_quotation_theory]
            body ≐ₘ
              standard_token_sequence bodyTokens := by
  let bodyTokens : List Nat :=
    (tokens.drop 2).take (tokens.length - 3)
  have hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body :=
    gq_formula_code_member_implies_finite_sequence
      body hBody.admissible hBodyMember
  by_cases hShape :
      tokens =
        Numbered.negation_tokens bodyTokens
  · right
    refine ⟨bodyTokens, ?_, ?_, ?_⟩
    · rw [hShape]
      simp [Numbered.negation_tokens]
      omega
    · rw [hShape] at hDecode
      exact
        fs_named_hilbert_tokens_decode_with_env_negation_none
          freeBase boundNames bodyTokens hDecode
    · simpa [bodyTokens] using
        gq_negation_body_eq_standard_token_slice
          body tokens hBodyFinite hEquality
          (hBody := hBody)
  · left
    exact
      gq_negation_standard_code_falsum_of_not_slice_shape
        body tokens hBodyFinite hEquality
        (by simpa [bodyTokens] using hShape)
        (hBody := hBody)

/-- 否定反演同时保留正文 token 的有限签名 payload。 -/
theorem gq_negation_code_decode_failure_descends_with_signature
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (body : SetTerm) (tokens : List Nat)
    (hTokens : FSFormulaTokens tokens)
    (hBinders : FSFormulaBinderTokens tokens)
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check)
    (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          neg_codeₘ(body))
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    (Γ ⊢ₘ[godel_quotation_theory]
        Formula.falsum) ∨
      ∃ bodyTokens,
        bodyTokens.length < tokens.length ∧
          fs_named_hilbert_tokens_decode_with_env
              freeBase boundNames bodyTokens =
            none ∧
          FSFormulaTokens bodyTokens ∧
          FSFormulaBinderTokens bodyTokens ∧
          Γ ⊢ₘ[godel_quotation_theory]
            body ≐ₘ
              standard_token_sequence bodyTokens := by
  let bodyTokens : List Nat :=
    (tokens.drop 2).take (tokens.length - 3)
  have hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body :=
    gq_formula_code_member_implies_finite_sequence
      body hBody.admissible hBodyMember
  by_cases hShape :
      tokens =
        Numbered.negation_tokens bodyTokens
  · right
    refine ⟨bodyTokens, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hShape]
      simp [Numbered.negation_tokens]
      omega
    · rw [hShape] at hDecode
      exact
        fs_named_hilbert_tokens_decode_with_env_negation_none
          freeBase boundNames bodyTokens hDecode
    · rw [hShape] at hTokens
      intro token hToken
      apply hTokens token
      simp [Numbered.negation_tokens, hToken]
    · rw [hShape] at hBinders
      exact
        fs_formula_binder_tokens_negation_body
          bodyTokens hBinders
    · simpa [bodyTokens] using
        gq_negation_body_eq_standard_token_slice
          body tokens hBodyFinite hEquality
          (hBody := hBody)
  · left
    exact
      gq_negation_standard_code_falsum_of_not_slice_shape
        body tokens hBodyFinite hEquality
        (by simpa [bodyTokens] using hShape)
        (hBody := hBody)

/--
蕴含构造的左正文定义域已由 numeral 固定时，规范整串解码失败严格下降到某一正文。

对象层先从整串构造等式恢复左右正文的标准序列等式；宿主层随后只用 checked
decoder 的构造闭包判定究竟是哪一侧失败。
-/
theorem gq_implication_code_decode_failure_descends_of_left_domain
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (left right : SetTerm)
    (leftTokens rightTokens : List Nat)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check)
    (hLeftMember :
      Γ ⊢ₘ[godel_quotation_theory]
        left ∈ₘ FormulaCodeₘ)
    (hRightMember :
      Γ ⊢ₘ[godel_quotation_theory]
        right ∈ₘ FormulaCodeₘ)
    (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftTokens.length))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (Numbered.implication_tokens
              leftTokens rightTokens) ≐ₘ
          imp_codeₘ(left, right))
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames
          (Numbered.implication_tokens
            leftTokens rightTokens) =
        none) :
    (fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames leftTokens =
        none ∧
      Γ ⊢ₘ[godel_quotation_theory]
        left ≐ₘ standard_token_sequence leftTokens) ∨
    (fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames rightTokens =
        none ∧
      Γ ⊢ₘ[godel_quotation_theory]
        right ≐ₘ standard_token_sequence rightTokens) := by
  have hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left :=
    gq_formula_code_member_implies_finite_sequence
      left hLeft.admissible hLeftMember
  have hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right :=
    gq_formula_code_member_implies_finite_sequence
      right hRight.admissible hRightMember
  have hCodeString :
      Γ ⊢ₘ[godel_quotation_theory]
        imp_codeₘ(left, right) ≐ₘ
          implication_formula_string_term left right :=
    gq_implication_formula_code_eq_string_of_context
      left right (hLeft := hLeft) (hRight := hRight)
  have hStringEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (Numbered.implication_tokens
              leftTokens rightTokens) ≐ₘ
          implication_formula_string_term left right :=
    Metatheory.Derives.equality_trans
      hEquality hCodeString
  have hBodies :=
    gq_implication_bodies_eq_standard_token_sequences_of_left_domain
      left right leftTokens rightTokens
      hLeftFinite hRightFinite
      hLeftDomain hStringEquality
      (hLeft := hLeft) (hRight := hRight)
  rcases
      fs_named_hilbert_tokens_decode_with_env_implication_none
        freeBase boundNames leftTokens rightTokens hDecode with
    hLeftDecode | hRightDecode
  · exact Or.inl
      ⟨hLeftDecode,
        FirstOrder.Derives.conjElimLeft hBodies⟩
  · exact Or.inr
      ⟨hRightDecode,
        FirstOrder.Derives.conjElimRight hBodies⟩

/-- 蕴含反演同时保留左右正文 token 的有限签名 payload。 -/
theorem gq_implication_code_decode_failure_descends_of_left_domain_with_signature
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (left right : SetTerm)
    (leftTokens rightTokens : List Nat)
    (hLeftTokens : FSFormulaTokens leftTokens)
    (hRightTokens : FSFormulaTokens rightTokens)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check)
    (hLeftMember :
      Γ ⊢ₘ[godel_quotation_theory]
        left ∈ₘ FormulaCodeₘ)
    (hRightMember :
      Γ ⊢ₘ[godel_quotation_theory]
        right ∈ₘ FormulaCodeₘ)
    (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftTokens.length))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (Numbered.implication_tokens
              leftTokens rightTokens) ≐ₘ
          imp_codeₘ(left, right))
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames
          (Numbered.implication_tokens
            leftTokens rightTokens) =
        none) :
    (fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames leftTokens =
        none ∧
      FSFormulaTokens leftTokens ∧
      Γ ⊢ₘ[godel_quotation_theory]
        left ≐ₘ standard_token_sequence leftTokens) ∨
    (fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames rightTokens =
        none ∧
      FSFormulaTokens rightTokens ∧
      Γ ⊢ₘ[godel_quotation_theory]
        right ≐ₘ standard_token_sequence rightTokens) := by
  rcases
      gq_implication_code_decode_failure_descends_of_left_domain
        freeBase boundNames left right
        leftTokens rightTokens
        (hLeft := hLeft) (hRight := hRight)
        hLeftMember hRightMember
        hLeftDomain hEquality hDecode with
    hLeftFailure | hRightFailure
  · exact Or.inl
      ⟨hLeftFailure.1, hLeftTokens, hLeftFailure.2⟩
  · exact Or.inr
      ⟨hRightFailure.1, hRightTokens, hRightFailure.2⟩

/--
蕴含构造与任意标准整行相等时，已知两个正文定义域长度即可把 checked 解码失败
严格下降到某一正文；若整行不能由这两个切片重建，则对象层直接推出矛盾。

该接口是公式码强归纳的蕴含分支：返回的子行、有限签名和对象码等式均可直接
交给归纳假设。
-/
theorem
    gq_implication_code_decode_failure_descends_of_domains_arbitrary_with_signature
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (left right : SetTerm) (tokens : List Nat)
    (leftLength rightLength : Nat)
    (hTokens : FSFormulaTokens tokens)
    (hBinders : FSFormulaBinderTokens tokens)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check)
    (hLeftMember :
      Γ ⊢ₘ[godel_quotation_theory]
        left ∈ₘ FormulaCodeₘ)
    (hRightMember :
      Γ ⊢ₘ[godel_quotation_theory]
        right ∈ₘ FormulaCodeₘ)
    (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftLength))
    (hRightDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ≐ₘ numₘ(rightLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          imp_codeₘ(left, right))
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    (Γ ⊢ₘ[godel_quotation_theory]
        Formula.falsum) ∨
      (∃ leftTokens,
        leftTokens.length < tokens.length ∧
          fs_named_hilbert_tokens_decode_with_env
              freeBase boundNames leftTokens =
            none ∧
          FSFormulaTokens leftTokens ∧
          FSFormulaBinderTokens leftTokens ∧
          Γ ⊢ₘ[godel_quotation_theory]
            left ≐ₘ
              standard_token_sequence leftTokens) ∨
      ∃ rightTokens,
        rightTokens.length < tokens.length ∧
          fs_named_hilbert_tokens_decode_with_env
              freeBase boundNames rightTokens =
            none ∧
          FSFormulaTokens rightTokens ∧
          FSFormulaBinderTokens rightTokens ∧
          Γ ⊢ₘ[godel_quotation_theory]
            right ≐ₘ
              standard_token_sequence rightTokens := by
  let leftTokens : List Nat :=
    (tokens.drop 1).take leftLength
  let rightTokens : List Nat :=
    (tokens.drop (leftLength + 2)).take rightLength
  have hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left :=
    gq_formula_code_member_implies_finite_sequence
      left hLeft.admissible hLeftMember
  have hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right :=
    gq_formula_code_member_implies_finite_sequence
      right hRight.admissible hRightMember
  by_cases hShape :
      tokens =
        Numbered.implication_tokens
          leftTokens rightTokens
  · have hBodies :
        Γ ⊢ₘ[godel_quotation_theory]
          (left ≐ₘ
              standard_token_sequence leftTokens) ∧ₘ
            (right ≐ₘ
              standard_token_sequence rightTokens) := by
      simpa [leftTokens, rightTokens] using
        gq_implication_bodies_eq_standard_token_slices_of_domains
          left right tokens leftLength rightLength
          hLeftFinite hRightFinite
          hLeftDomain hRightDomain hEquality
          (hLeft := hLeft) (hRight := hRight)
    have hLeftTokens :
        FSFormulaTokens leftTokens := by
      rw [hShape] at hTokens
      intro token hToken
      apply hTokens token
      simp [Numbered.implication_tokens, hToken]
    have hRightTokens :
        FSFormulaTokens rightTokens := by
      rw [hShape] at hTokens
      intro token hToken
      apply hTokens token
      simp [Numbered.implication_tokens, hToken]
    have hLeftBinders :
        FSFormulaBinderTokens leftTokens := by
      rw [hShape] at hBinders
      exact
        fs_formula_binder_tokens_implication_left
          leftTokens rightTokens hBinders
    have hRightBinders :
        FSFormulaBinderTokens rightTokens := by
      rw [hShape] at hBinders
      exact
        fs_formula_binder_tokens_implication_right
          leftTokens rightTokens hBinders
    have hLeftLength :
        leftTokens.length < tokens.length := by
      rw [hShape]
      simp [Numbered.implication_tokens]
      omega
    have hRightLength :
        rightTokens.length < tokens.length := by
      rw [hShape]
      simp [Numbered.implication_tokens]
      omega
    rw [hShape] at hDecode
    rcases
        fs_named_hilbert_tokens_decode_with_env_implication_none
          freeBase boundNames leftTokens rightTokens hDecode with
      hLeftDecode | hRightDecode
    · exact Or.inr <| Or.inl
        ⟨leftTokens, hLeftLength, hLeftDecode,
          hLeftTokens, hLeftBinders,
          FirstOrder.Derives.conjElimLeft hBodies⟩
    · exact Or.inr <| Or.inr
        ⟨rightTokens, hRightLength, hRightDecode,
          hRightTokens, hRightBinders,
          FirstOrder.Derives.conjElimRight hBodies⟩
  · exact Or.inl <|
      gq_implication_standard_code_falsum_of_not_slice_shape
        left right tokens leftLength rightLength
        hLeftFinite hRightFinite
        hLeftDomain hRightDomain hEquality
        (by simpa [leftTokens, rightTokens] using hShape)
        (hLeft := hLeft) (hRight := hRight)

/--
任意全称构造与标准输入行相等时，第 `2` 个 token 唯一决定对象 binder 的
singleton 编码。这里只恢复输入中已经出现的具体 token，不反演对象自然数为
Lean 自然数。
-/
theorem gq_universal_bound_variable_eq_standard_token_singleton
    {Γ : Context signature}
    (boundVariable body : SetTerm)
    (tokens : List Nat) (token : Nat)
    (hBoundVariable :
      Term.CheckCertificate boundVariable SetSort.set := by
        prove_term_check)
    (hBody :
      Term.CheckCertificate body SetSort.set := by
        prove_term_check)
    (hGet :
      tokens[2]? = some token)
    (hBoundVariableMember :
      Γ ⊢ₘ[godel_quotation_theory]
        boundVariable ∈ₘ VarSymₘ)
    (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          forall_codeₘ(boundVariable, body)) :
    Γ ⊢ₘ[godel_quotation_theory]
      boundVariable ≐ₘ
        standard_token_sequence [token] := by
  have hBodyCodeString :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ CodeStrₘ :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (gq_formula_code_member_implies_code_string
          body hBody.admissible))
      hBodyMember
  have hOpening :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (gq_universal_formula_opening_inversion
          boundVariable body
          (hBoundVariable := hBoundVariable)
          (hBody := hBody)))
      (FirstOrder.Derives.conjIntro
        hBoundVariableMember hBodyCodeString)
  have hConstructorValue :
      Γ ⊢ₘ[godel_quotation_theory]
        (forall_codeₘ(boundVariable, body) ·ₘ
            numₘ(2)) ≐ₘ
          (boundVariable ·ₘ numₘ(0)) :=
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight hOpening
  have hWholeToken :=
    gq_standard_token_sequence_point_inversion
      (forall_codeₘ(boundVariable, body))
      tokens
      (Metatheory.Derives.equality_symm hEquality)
      hGet
  have hBoundValue :
      Γ ⊢ₘ[godel_quotation_theory]
        (boundVariable ·ₘ numₘ(0)) ≐ₘ
          numₘ(token) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm
        hConstructorValue)
      (FirstOrder.Derives.conjElimRight
        hWholeToken)
  have hStructure :
      Γ ⊢ₘ[godel_quotation_theory]
        (finite_sequence_condition boundVariable ∧ₘ
          (domₘ(boundVariable) ≐ₘ numₘ(1))) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (gq_variable_symbol_member_implies_finite_domain_one
          boundVariable hBoundVariable.admissible))
      hBoundVariableMember
  apply
    gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
      (T := godel_quotation_theory)
      (Γ := Γ)
      (fun _ hAxiom => Or.inl hAxiom)
      (fun _ hFormula =>
        godel_quotation_theory_sentence hFormula)
      boundVariable [token]
      (FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimLeft hStructure)
      (by
        simpa using
          FirstOrder.Derives.conjElimRight hStructure)
  intro index actual hSingletonGet
  have hIndexZero : index = 0 := by
    have hIndex :
        index < [token].length :=
      (List.getElem?_eq_some_iff.mp
        hSingletonGet).1
    simp only [List.length_cons,
      List.length_nil] at hIndex
    omega
  subst index
  simp only [List.getElem?_cons_zero,
    Option.some.injEq] at hSingletonGet
  subst actual
  exact hBoundValue

/--
若第 `2` 个 token 的有限 decoder 成功，则上一条对象 singleton 反演立即把
binder 识别为相应的规范具名变量码。
-/
theorem gq_universal_bound_variable_eq_named_of_decode
    {Γ : Context signature}
    (boundVariable body : SetTerm)
    (tokens : List Nat) (token name : Nat)
    (hBoundVariable :
      Term.CheckCertificate boundVariable SetSort.set := by
        prove_term_check)
    (hBody :
      Term.CheckCertificate body SetSort.set := by
        prove_term_check)
    (hGet :
      tokens[2]? = some token)
    (hDecode :
      fs_variable_name_decode token = some name)
    (hBoundVariableMember :
      Γ ⊢ₘ[godel_quotation_theory]
        boundVariable ∈ₘ VarSymₘ)
    (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          forall_codeₘ(boundVariable, body)) :
    Γ ⊢ₘ[godel_quotation_theory]
      boundVariable ≐ₘ
        Numbered.named_variable_code name := by
  have hSingleton :=
    gq_universal_bound_variable_eq_standard_token_singleton
      boundVariable body tokens token
      (hBoundVariable := hBoundVariable)
      (hBody := hBody)
      hGet
      hBoundVariableMember hBodyMember hEquality
  have hToken :
      Numbered.variable_token name = token :=
    fs_variable_name_decode_value_of_some hDecode
  have hNamed :
      Γ ⊢ₘ[godel_quotation_theory]
        Numbered.named_variable_code name ≐ₘ
          standard_token_sequence [token] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [hToken] using
          named_variable_code_eq_standard_token_sequence
            name
  exact Metatheory.Derives.equality_trans
    hSingleton
    (Metatheory.Derives.equality_symm hNamed)

/--
规范全称构造的正文定义域已由 numeral 固定时，整串解码失败严格下降到扩展
binder 环境后的正文；对象层同时恢复正文的标准 token 序列等式。
-/
theorem gq_universal_code_decode_failure_descends_of_domain
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (name : Nat) (body : SetTerm) (bodyTokens : List Nat)
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check)
    (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (Numbered.universal_tokens name bodyTokens) ≐ₘ
          forall_codeₘ(
            Numbered.named_variable_code name, body))
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames
          (Numbered.universal_tokens name bodyTokens) =
        none) :
    bodyTokens.length <
          (Numbered.universal_tokens name bodyTokens).length ∧
      fs_named_hilbert_tokens_decode_with_env
          freeBase (name :: boundNames) bodyTokens =
        none ∧
      Γ ⊢ₘ[godel_quotation_theory]
        body ≐ₘ standard_token_sequence bodyTokens := by
  have hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body :=
    gq_formula_code_member_implies_finite_sequence
      body hBody.admissible hBodyMember
  refine ⟨?_, ?_, ?_⟩
  · simp [Numbered.universal_tokens]
    omega
  · exact
      fs_named_hilbert_tokens_decode_with_env_universal_none
        freeBase boundNames name bodyTokens hDecode
  · exact
      gq_universal_body_eq_standard_token_sequence_of_standard_equality
        name body bodyTokens hBodyFinite hEquality
        (hBody := hBody)

/-- 全称反演同时保留正文 token 的有限签名 payload。 -/
theorem gq_universal_code_decode_failure_descends_of_domain_with_signature
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (name : Nat) (body : SetTerm) (bodyTokens : List Nat)
    (hBodyTokens : FSFormulaTokens bodyTokens)
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check)
    (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (Numbered.universal_tokens name bodyTokens) ≐ₘ
          forall_codeₘ(
            Numbered.named_variable_code name, body))
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames
          (Numbered.universal_tokens name bodyTokens) =
        none) :
    bodyTokens.length <
          (Numbered.universal_tokens name bodyTokens).length ∧
      fs_named_hilbert_tokens_decode_with_env
          freeBase (name :: boundNames) bodyTokens =
        none ∧
      FSFormulaTokens bodyTokens ∧
      Γ ⊢ₘ[godel_quotation_theory]
        body ≐ₘ standard_token_sequence bodyTokens := by
  rcases
      gq_universal_code_decode_failure_descends_of_domain
        freeBase boundNames name body bodyTokens
        (hBody := hBody) hBodyMember
        hEquality hDecode with
    ⟨hLength, hBodyDecode, hBodyEquality⟩
  exact ⟨hLength, hBodyDecode, hBodyTokens, hBodyEquality⟩

/--
全称构造与任意标准整行相等时，已知正文定义域长度即可把 checked 解码失败
严格下降到扩展 binder 环境后的正文；若整行不能由该切片重建，则对象层
直接推出矛盾。
-/
theorem
    gq_universal_code_decode_failure_descends_of_domain_arbitrary_with_signature
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (name : Nat) (body : SetTerm)
    (tokens : List Nat) (bodyLength : Nat)
    (hTokens : FSFormulaTokens tokens)
    (hBinders : FSFormulaBinderTokens tokens)
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check)
    (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ FormulaCodeₘ)
    (hBodyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          forall_codeₘ(
            Numbered.named_variable_code name, body))
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    (Γ ⊢ₘ[godel_quotation_theory]
        Formula.falsum) ∨
      ∃ bodyTokens,
        bodyTokens.length < tokens.length ∧
          fs_named_hilbert_tokens_decode_with_env
              freeBase (name :: boundNames) bodyTokens =
            none ∧
          FSFormulaTokens bodyTokens ∧
          FSFormulaBinderTokens bodyTokens ∧
          Γ ⊢ₘ[godel_quotation_theory]
            body ≐ₘ
              standard_token_sequence bodyTokens := by
  let bodyTokens :=
    (tokens.drop 3).take bodyLength
  have hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body :=
    gq_formula_code_member_implies_finite_sequence
      body hBody.admissible hBodyMember
  by_cases hShape :
      tokens =
        Numbered.universal_tokens name bodyTokens
  · have hBodyEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          body ≐ₘ
            standard_token_sequence bodyTokens := by
      simpa [bodyTokens] using
        gq_universal_body_eq_standard_token_slice_of_domain
          name body tokens bodyLength
          hBodyFinite hBodyDomain hEquality
          (hBody := hBody)
    have hBodyTokens :
        FSFormulaTokens bodyTokens := by
      rw [hShape] at hTokens
      intro token hToken
      apply hTokens token
      simp [Numbered.universal_tokens, hToken]
    have hBodyBinders :
        FSFormulaBinderTokens bodyTokens := by
      rw [hShape] at hBinders
      exact
        fs_formula_binder_tokens_universal_body
          name bodyTokens hBinders
    have hBodyLength :
        bodyTokens.length < tokens.length := by
      rw [hShape]
      simp [Numbered.universal_tokens]
      omega
    rw [hShape] at hDecode
    exact Or.inr
      ⟨bodyTokens, hBodyLength,
        fs_named_hilbert_tokens_decode_with_env_universal_none
          freeBase boundNames name bodyTokens hDecode,
        hBodyTokens, hBodyBinders, hBodyEquality⟩
  · exact Or.inl <|
      gq_universal_standard_code_falsum_of_not_slice_shape
        name body tokens bodyLength
        hBodyFinite hBodyDomain hEquality
        (by simpa [bodyTokens] using hShape)
        (hBody := hBody)

/--
全称构造的 binder 可以是生成反演给出的任意对象项。只要输入行第 `2` 位的
有限名字 decoder 成功，就先把该 binder 对齐到规范具名变量码，再复用现有
全称切片下降接口。
-/
theorem
    gq_universal_code_decode_failure_descends_of_domain_arbitrary_binder_with_signature
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (boundVariable body : SetTerm)
    (tokens : List Nat) (bodyLength : Nat)
    (token name : Nat)
    (hTokens : FSFormulaTokens tokens)
    (hBinders : FSFormulaBinderTokens tokens)
    (hBoundVariable :
      Term.CheckCertificate boundVariable SetSort.set := by
        prove_term_check)
    (hBody :
      Term.CheckCertificate body SetSort.set := by
        prove_term_check)
    (hGet :
      tokens[2]? = some token)
    (hVariableDecode :
      fs_variable_name_decode token = some name)
    (hBoundVariableMember :
      Γ ⊢ₘ[godel_quotation_theory]
        boundVariable ∈ₘ VarSymₘ)
    (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        body ∈ₘ FormulaCodeₘ)
    (hBodyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          forall_codeₘ(boundVariable, body))
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    (Γ ⊢ₘ[godel_quotation_theory]
        Formula.falsum) ∨
      ∃ bodyTokens,
        bodyTokens.length < tokens.length ∧
          fs_named_hilbert_tokens_decode_with_env
              freeBase (name :: boundNames) bodyTokens =
            none ∧
          FSFormulaTokens bodyTokens ∧
          FSFormulaBinderTokens bodyTokens ∧
          Γ ⊢ₘ[godel_quotation_theory]
            body ≐ₘ
              standard_token_sequence bodyTokens := by
  let namedVariable : SetTerm :=
    Numbered.named_variable_code name
  have hNamedVariable :
      Term.Admissible namedVariable SetSort.set := by
    simpa [namedVariable] using
      variable_code_term_admissible
        (numₘ(name))
        (finite_numeral_term_admissible name)
  have hBoundVariableEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        boundVariable ≐ₘ namedVariable := by
    simpa [namedVariable] using
      gq_universal_bound_variable_eq_named_of_decode
        boundVariable body tokens token name
        (hBoundVariable := hBoundVariable)
        (hBody := hBody)
        hGet hVariableDecode
        hBoundVariableMember hBodyMember hEquality
  have hConstructorEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        forall_codeₘ(boundVariable, body) ≐ₘ
          forall_codeₘ(namedVariable, body) :=
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      (fun binder formula =>
        forall_codeₘ(binder, formula))
      (fun binder formula hBinder hFormula =>
        universal_formula_code_term_admissible
          binder formula hBinder hFormula)
      (by
        intros
        simp [Term.substituteFree])
      boundVariable namedVariable body body
      hBoundVariable.admissible hNamedVariable
      hBody.admissible hBody.admissible
      hBoundVariableEquality
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) body)
  have hNamedEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          forall_codeₘ(namedVariable, body) :=
    Metatheory.Derives.equality_trans
      hEquality hConstructorEquality
  simpa [namedVariable] using
    gq_universal_code_decode_failure_descends_of_domain_arbitrary_with_signature
      freeBase boundNames name body tokens bodyLength
      hTokens hBinders (hBody := hBody)
      hBodyMember hBodyDomain
      (by simpa [namedVariable] using hNamedEquality)
      hDecode

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
