import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.Symbol
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.StandardTokenSequenceAdditionBound
/-!
# Gödel quotation 的序列值语义
本模块组织代码/token 对齐、标准序列、拼接及逐点反演。
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
universe u v w
/-! ## 参数代码列与标准 token 族 -/
/-- 一个对象代码与一段外部 token 串的值对齐证书。 -/
def gq_code_token_aligned (code : SetTerm) (tokens : List Nat) : Prop :=
  Numbered.CodeBoundary code ∧
    ⊢ₘ[godel_quotation_theory]
      code ≐ₘ standard_token_sequence tokens
/-- 两列等长，且对应对象代码与 token 分片逐项值对齐。 -/
inductive gq_code_token_aligned_list :
    List SetTerm → List (List Nat) → Prop where
  | nil : gq_code_token_aligned_list [] []
  | cons {code tokens codes pieces} (head : gq_code_token_aligned code tokens) (tail : gq_code_token_aligned_list codes pieces) :
      gq_code_token_aligned_list (code :: codes) (tokens :: pieces)
/-- 对齐代码列中的每个对象代码都携带完整代码边界。 -/
theorem gq_aligned_codes_boundary
    {codes : List SetTerm} {pieces : List (List Nat)} (hAligned : gq_code_token_aligned_list codes pieces) :
    ∀ code, code ∈ codes → Numbered.CodeBoundary code := by
  induction hAligned with
  | nil =>
      simp
  | cons hHead hTail ih =>
      intro code hCode
      simp only [List.mem_cons] at hCode
      rcases hCode with rfl | hCode
      · exact hHead.1
      · exact ih code hCode
/--
逐项对齐的对象代码列，其标准有限序列等于对应标准 token 序列组成的对象族。
-/
private theorem gq_standard_sequence_from_eq_token_family (start : Nat)
    {codes : List SetTerm} {pieces : List (List Nat)} (hAligned : gq_code_token_aligned_list codes pieces) :
    ⊢ₘ[godel_quotation_theory]
      standard_sequence_from start codes ≐ₘ
        standard_sequence_from start (pieces.map standard_token_sequence) := by
  induction hAligned generalizing start with
  | nil =>
      exact FirstOrder.Derives.eq_refl_m ∅ₘ
  | @cons code tokens codes pieces hHead hTail ih =>
      let standardCode := standard_token_sequence tokens
      let leftHead := {⟨numₘ(start), code⟩ₘ}ₘ
      let rightHead := {⟨numₘ(start), standardCode⟩ₘ}ₘ
      let leftTail := standard_sequence_from (start + 1) codes
      let rightTail :=
        standard_sequence_from (start + 1) (pieces.map standard_token_sequence)
      let parameter : FreeVarId := 398
      let headContext : SetTerm :=
        {⟨numₘ(start), x#parameter⟩ₘ}ₘ
      have hCode :
          Term.CheckCertificate code SetSort.set := by
        exact hHead.1.check_certificate
      have hStandardCode :
          Term.CheckCertificate standardCode SetSort.set := by
        prove_term_check
      have hHeadContext :
          Term.CheckCertificate headContext SetSort.set := by
        prove_term_check
      have hNumeralFixed (replacement : SetTerm) :
          Term.substituteFree SetSort.set parameter replacement (numₘ(start)) =
            numₘ(start) := by
        apply Term.substituteFree_eq_self_of_not_mem
        rw [finite_numeral_term_freeSupport]
        simp
      have hHeadRaw :=
        gq_term_context_congr_of_equality
          parameter code standardCode headContext
          hCode hStandardCode hHeadContext (by
            rw [hHead.1.2]
            exact List.not_mem_nil)
          hHead.2
      have hHeadEquality :
          ⊢ₘ[godel_quotation_theory]
            leftHead ≐ₘ rightHead := by
        simpa [leftHead, rightHead, standardCode,
          headContext, parameter, Formula.substituteFree,
          Term.substituteFree, set_variable, hNumeralFixed] using
          hHeadRaw
      have hLeftHead :
          Term.CheckCertificate leftHead SetSort.set := by
        prove_term_check
      have hRightHead :
          Term.CheckCertificate rightHead SetSort.set := by
        prove_term_check
      have hLeftTail :
          Term.CheckCertificate leftTail SetSort.set := by
        apply standard_sequence_from_check
        intro element hElement
        exact
          (gq_aligned_codes_boundary
            hTail element hElement).check_certificate
      have hRightTail :
          Term.CheckCertificate rightTail SetSort.set := by
        apply standard_sequence_from_check
        intro element hElement
        simp only [List.mem_map] at hElement
        rcases hElement with ⟨piece, hPiece, rfl⟩
        prove_term_check
      have hTailClosed :
          Term.freeSupport leftTail = [] := by
        apply seq_support_nil_m
        intro element hElement
        exact
          (gq_aligned_codes_boundary
            hTail element hElement).2
      have hTailEquality :
          ⊢ₘ[godel_quotation_theory]
            leftTail ≐ₘ rightTail := by
        simpa [leftTail, rightTail] using ih (start + 1)
      let firstParameter : FreeVarId := 400
      let firstContext := (x#firstParameter) ∪ₘ leftTail
      have hFirstContext :
          Term.CheckCertificate firstContext SetSort.set := by
        prove_term_check
      have hLeftTailFixed (replacement : SetTerm) :
          Term.substituteFree SetSort.set firstParameter replacement
              leftTail =
            leftTail := by
        apply Term.substituteFree_eq_self_of_not_mem
        rw [hTailClosed]
        exact List.not_mem_nil
      have hFirstRaw :=
        gq_term_context_congr_of_equality
          firstParameter leftHead rightHead firstContext
          hLeftHead hRightHead hFirstContext (by
            rw [show Term.freeSupport leftHead = [] by
              simp [leftHead, Term.freeSupport, Term.freeSupportList,
                hHead.1.2, finite_numeral_term_freeSupport]]
            exact List.not_mem_nil)
          hHeadEquality
      have hFirst :
          ⊢ₘ[godel_quotation_theory]
            (leftHead ∪ₘ leftTail) ≐ₘ
              (rightHead ∪ₘ leftTail) := by
        simpa [firstContext, firstParameter,
          binary_union_term, Term.substituteFree,
          set_variable, hLeftTailFixed] using hFirstRaw
      let secondParameter : FreeVarId := 401
      let secondContext := rightHead ∪ₘ (x#secondParameter)
      have hSecondContext :
          Term.CheckCertificate secondContext SetSort.set := by
        prove_term_check
      have hRightHeadFixed (replacement : SetTerm) :
          Term.substituteFree SetSort.set secondParameter replacement
              rightHead =
            rightHead := by
        apply Term.substituteFree_eq_self_of_not_mem
        simp [rightHead, standardCode, Term.freeSupport,
          Term.freeSupportList, standard_token_sequence_freeSupport_nil,
          finite_numeral_term_freeSupport]
      have hSecondRaw :=
        gq_term_context_congr_of_equality
          secondParameter leftTail rightTail secondContext
          hLeftTail hRightTail hSecondContext (by
            rw [hTailClosed]
            exact List.not_mem_nil)
          hTailEquality
      have hSecond :
          ⊢ₘ[godel_quotation_theory]
            (rightHead ∪ₘ leftTail) ≐ₘ
              (rightHead ∪ₘ rightTail) := by
        simpa [secondContext, secondParameter,
          binary_union_term, Term.substituteFree,
          set_variable, hRightHeadFixed] using hSecondRaw
      simpa [standard_sequence_from, leftHead, rightHead,
        leftTail, rightTail] using
        Metatheory.Derives.equality_trans
          hFirst hSecond
/-- 标准起点 `0` 上的参数代码列对齐。 -/
theorem gq_standard_sequence_eq_token_family
    {codes : List SetTerm} {pieces : List (List Nat)} (hAligned : gq_code_token_aligned_list codes pieces) :
    ⊢ₘ[godel_quotation_theory]
      standard_sequence codes ≐ₘ
        standard_sequence (pieces.map standard_token_sequence) := by
  exact gq_standard_sequence_from_eq_token_family 0 hAligned
/-- 逐项对齐的参数代码族折叠后等于全部 token 分片的外部 flatten。 -/
theorem gq_argument_family_flatten_eq_standard_token_sequence
    {codes : List SetTerm} {pieces : List (List Nat)} (hAligned : gq_code_token_aligned_list codes pieces) :
    ⊢ₘ[godel_quotation_theory]
      flattenₘ(standard_sequence codes) ≐ₘ
        standard_token_sequence pieces.flatten := by
  let leftFamily := standard_sequence codes
  let rightFamily :=
    standard_sequence (pieces.map standard_token_sequence)
  let parameter : FreeVarId := 399
  let flattenContext := flattenₘ(x#parameter)
  have hLeftFamily :
      Term.CheckCertificate leftFamily SetSort.set := by
    apply standard_sequence_from_check
    intro code hCode
    exact
      (gq_aligned_codes_boundary
        hAligned code hCode).check_certificate
  have hRightFamily :
      Term.CheckCertificate rightFamily SetSort.set := by
    apply standard_sequence_from_check
    intro code hCode
    simp only [List.mem_map] at hCode
    rcases hCode with ⟨tokens, hTokens, rfl⟩
    prove_term_check
  have hFlattenContext :
      Term.CheckCertificate flattenContext SetSort.set := by
    prove_term_check
  have hFamilyEquality :
      ⊢ₘ[godel_quotation_theory]
        leftFamily ≐ₘ rightFamily := by
    simpa [leftFamily, rightFamily] using
      gq_standard_sequence_eq_token_family hAligned
  have hFlattenRaw :=
    gq_term_context_congr_of_equality
      parameter leftFamily rightFamily flattenContext
      hLeftFamily hRightFamily hFlattenContext (by
        rw [show Term.freeSupport leftFamily = [] by
          apply seq_support_nil_m
          intro code hCode
          exact (gq_aligned_codes_boundary hAligned code hCode).2]
        exact List.not_mem_nil)
      hFamilyEquality
  have hFlattenFamilies :
      ⊢ₘ[godel_quotation_theory]
        flattenₘ(leftFamily) ≐ₘ flattenₘ(rightFamily) := by
    simpa [flattenContext, parameter, leftFamily, rightFamily,
      finite_sequence_flatten_term, Term.substituteFree,
      set_variable] using hFlattenRaw
  have hStandardFlatten :
      ⊢ₘ[godel_quotation_theory]
        standard_token_sequence pieces.flatten ≐ₘ
          flattenₘ(rightFamily) := by
    simpa [rightFamily] using
      gq_weaken_standard_sequence (standard_token_sequence_family_flatten pieces)
  have hStandardFlattenBack :
      ⊢ₘ[godel_quotation_theory]
        flattenₘ(rightFamily) ≐ₘ
          standard_token_sequence pieces.flatten :=
    Metatheory.Derives.equality_symm hStandardFlatten
  exact Metatheory.Derives.equality_trans
    hFlattenFamilies hStandardFlattenBack
/-- 两段已对齐的对象字符串拼接后仍与外部 token 拼接对齐。 -/
theorem gq_concatenation_eq_standard_token_sequence
    {Γ : Context signature} (leftTokens rightTokens : List Nat)
    (leftCode rightCode : SetTerm) (hLeft :
      Γ ⊢ₘ[godel_quotation_theory]
        leftCode ≐ₘ standard_token_sequence leftTokens) (hRight :
      Γ ⊢ₘ[godel_quotation_theory]
        rightCode ≐ₘ standard_token_sequence rightTokens)
    (hLeftCode : Term.CheckCertificate leftCode SetSort.set := by
      prove_term_check)
    (hRightCode : Term.CheckCertificate rightCode SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory] (leftCode ⌢ₘ rightCode) ≐ₘ
        standard_token_sequence (leftTokens ++ rightTokens) := by
  have hCongruence :=
    finite_sequence_concatenation_term_congr_of_equalities
      leftCode (standard_token_sequence leftTokens)
      rightCode (standard_token_sequence rightTokens)
      hLeftCode.admissible (standard_token_sequence_admissible leftTokens)
      hRightCode.admissible (standard_token_sequence_admissible rightTokens)
      hLeft hRight
  have hStandard :=
    gq_weaken_standard_sequence <|
      standard_token_sequence_append leftTokens rightTokens
  have hStandardBack :
      Γ ⊢ₘ[godel_quotation_theory] (standard_token_sequence leftTokens ⌢ₘ
            standard_token_sequence rightTokens) ≐ₘ
          standard_token_sequence (leftTokens ++ rightTokens) := by
    exact FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
        Metatheory.Derives.equality_symm hStandard
  exact Metatheory.Derives.equality_trans
    hCongruence hStandardBack
/--
与标准 token 序列相等的对象代码，可在每个合法外部下标上同时反演定义域成员和
逐点 token 值。
这是 quotation 值等式的基础消去接口；量词前缀、变量出现和替换反演均只需消费
这一结论，不再各自展开标准序列图。
-/
theorem gq_standard_token_sequence_point_inversion
    {Γ : Context signature} (code : SetTerm) (tokens : List Nat)
    {index token : Nat} (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ standard_token_sequence tokens)
    (hGet : tokens[index]? = some token)
    (hCode : Term.CheckCertificate code SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory] ((numₘ(index) ∈ₘ domₘ(code)) ∧ₘ ((code ·ₘ numₘ(index)) ≐ₘ numₘ(token))) := by
  let standardCode := standard_token_sequence tokens
  have hStandardCode :
      Term.CheckCertificate standardCode SetSort.set := by
    prove_term_check
  have hIndex : index < tokens.length := (List.getElem?_eq_some_iff.mp hGet).1
  have hStandardDomainEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(standardCode) ≐ₘ numₘ(tokens.length) := by
    exact FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [standardCode] using
          gq_weaken_standard_sequence (standard_token_sequence_domain_eq_length tokens)
  have hStandardDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(standardCode) := by
    have hTransport := membership_right_iff_of_equality (numₘ(index)) (domₘ(standardCode)) (numₘ(tokens.length)) (finite_numeral_term_admissible index)
      (domain_term_admissible standardCode hStandardCode.admissible)
      (finite_numeral_term_admissible tokens.length)
      hStandardDomainEquality
    exact FirstOrder.Derives.iffElimLeft hTransport <|
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <|
            standard_sequence_finite_numeral_mem_of_lt
              index tokens.length hIndex
  have hDomainEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ domₘ(standardCode) :=
    domain_term_congr_of_equality
      code standardCode hCode.admissible hStandardCode.admissible <| by
        simpa [standardCode] using hEquality
  have hCodeDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(code) := by
    exact FirstOrder.Derives.iffElimLeft (membership_right_iff_of_equality (numₘ(index)) (domₘ(code)) (domₘ(standardCode))
        (finite_numeral_term_admissible index)
        (domain_term_admissible code hCode.admissible)
        (domain_term_admissible standardCode hStandardCode.admissible)
        hDomainEquality)
      hStandardDomain
  have hApplicationEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        (code ·ₘ numₘ(index)) ≐ₘ
          (standardCode ·ₘ numₘ(index)) :=
    function_application_term_congr_function_of_equality
      code standardCode (numₘ(index))
      hCode.admissible hStandardCode.admissible
      (finite_numeral_term_admissible index) <| by
        simpa [standardCode] using hEquality
  have hStandardValue :
      Γ ⊢ₘ[godel_quotation_theory]
        (standardCode ·ₘ numₘ(index)) ≐ₘ
          numₘ(token) := by
    exact FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [standardCode] using
          gq_weaken_standard_sequence
            (standard_token_sequence_apply_getElem? tokens hGet)
  have hCodeValue :
      Γ ⊢ₘ[godel_quotation_theory]
        (code ·ₘ numₘ(index)) ≐ₘ numₘ(token) :=
    Metatheory.Derives.equality_trans
      hApplicationEquality hStandardValue
  exact FirstOrder.Derives.conjIntro hCodeDomain hCodeValue
/-- 与标准 token 序列相等的对象代码自动满足有限序列条件。 -/
theorem gq_finite_sequence_of_eq_standard_token_sequence
    {Γ : Context signature} (code : SetTerm) (tokens : List Nat)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ standard_token_sequence tokens)
    (hCode : Term.CheckCertificate code SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      finite_sequence_condition code := by
  have hStandard :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition (standard_token_sequence tokens) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_token_sequence_finite_sequence_condition tokens
  exact FirstOrder.Derives.iffElimLeft (finite_sequence_condition_iff_of_equality
      code (standard_token_sequence tokens)
      hCode.admissible (standard_token_sequence_admissible tokens)
      hEquality)
    hStandard
/--
在 Gödel 引号理论的任意扩张中，标准 token 序列等式同时确定源代码的定义域长度。
-/
theorem gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
    {T : SetTheory} {Γ : Context signature} (hTheory :
      ∀ formula, godel_quotation_theory formula → T formula)
    (code : SetTerm) (tokens : List Nat) (hEquality :
      Γ ⊢ₘ[T]
        code ≐ₘ standard_token_sequence tokens)
    (hCode : Term.CheckCertificate code SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[T]
      domₘ(code) ≐ₘ numₘ(tokens.length) := by
  let standardCode := standard_token_sequence tokens
  have hStandardCode :
      Term.CheckCertificate standardCode SetSort.set := by
    prove_term_check
  have hDomainCongruence :
      Γ ⊢ₘ[T]
        domₘ(code) ≐ₘ domₘ(standardCode) :=
    domain_term_congr_of_equality
      code standardCode hCode.admissible
        hStandardCode.admissible <| by
        simpa [standardCode] using hEquality
  have hStandardDomain :
      Γ ⊢ₘ[T]
        domₘ(standardCode) ≐ₘ numₘ(tokens.length) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <| by
          simpa [standardCode] using
            gq_weaken_standard_sequence (standard_token_sequence_domain_eq_length tokens)
  exact Metatheory.Derives.equality_trans
    hDomainCongruence hStandardDomain
/-- 任意逻辑符号代码都是有限 singleton 序列。 -/
theorem gq_logical_symbol_code_finite_sequence
    {Γ : Context signature} (symbol : LogicalSymbolKind) :
    Γ ⊢ₘ[godel_quotation_theory]
      finite_sequence_condition (logical_symbol_code_term symbol) :=
  gq_finite_sequence_of_eq_standard_token_sequence (logical_symbol_code_term symbol)
    [logical_token symbol]
    (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
        logical_symbol_code_eq_standard_token_sequence symbol)
/-- 任意逻辑符号 singleton 代码的定义域长度为 `1`。 -/
theorem gq_logical_symbol_code_domain_eq_one
    {Γ : Context signature} (symbol : LogicalSymbolKind) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(logical_symbol_code_term symbol) ≐ₘ numₘ(1) := by
  simpa using
    gq_domain_eq_length_of_eq_standard_token_sequence_of_theory (fun _ hAxiom => hAxiom) (logical_symbol_code_term symbol)
      [logical_token symbol]
      (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
          logical_symbol_code_eq_standard_token_sequence symbol)
/--
函数、标准 numeral 长度定义域和逐 token 值，在任意标准序列语义扩张中唯一决定
一个标准 token 序列。
-/
theorem gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
    {T : SetTheory} {Γ : Context signature} (hTheory :
      ∀ formula,
        standard_sequence_semantics_theory formula → T formula) (hTheorySentence :
      ∀ formula, T formula → Formula.Sentence formula)
    (source : SetTerm) (tokens : List Nat) (hFunction :
      Γ ⊢ₘ[T] is_function_formula source) (hDomain :
      Γ ⊢ₘ[T]
        domₘ(source) ≐ₘ numₘ(tokens.length)) (hPoint :
      ∀ {index token : Nat},
        tokens[index]? = some token →
          Γ ⊢ₘ[T] (source ·ₘ numₘ(index)) ≐ₘ numₘ(token))
    (hSource : Term.CheckCertificate source SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[T]
      source ≐ₘ standard_token_sequence tokens := by
  let elements := tokens.map finite_numeral_term
  have hElements :
      ∀ element, element ∈ elements →
        Term.CheckCertificate element SetSort.set := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨token, hToken, rfl⟩
    prove_term_check
  have hElementsClosed :
      ∀ element, element ∈ elements →
        Term.freeSupport element = [] := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨token, hToken, rfl⟩
    exact finite_numeral_term_freeSupport token
  have hMappedPoint :
      ∀ {index : Nat} {element : SetTerm},
        elements[index]? = some element →
          Γ ⊢ₘ[T] (source ·ₘ numₘ(index)) ≐ₘ element := by
    intro index element hGet
    cases hToken : tokens[index]? with
    | none =>
        simp [elements, List.getElem?_map, hToken] at hGet
    | some token =>
        have hElement : element = numₘ(token) := by
          simpa [elements, List.getElem?_map, hToken] using
            hGet.symm
        subst element
        exact hPoint hToken
  simpa [standard_token_sequence, elements] using
    standard_sequence_eq_of_function_domain_pointwise
      hTheory hTheorySentence source elements
      hSource.admissible
      (fun element hElement =>
        (hElements element hElement).admissible)
      hElementsClosed
      hFunction (by simpa [elements] using hDomain)
      hMappedPoint
/--
有限序列拼接保留左段一个已知点的定义域成员关系与逐点值。
-/
theorem gq_concatenation_left_point_of_theory
    {T : SetTheory} {Γ : Context signature} (hTheory :
      ∀ formula, godel_quotation_theory formula → T formula)
    (left right index value : SetTerm) (hLeftFinite :
      Γ ⊢ₘ[T]
        finite_sequence_condition left) (hRightFinite :
      Γ ⊢ₘ[T]
        finite_sequence_condition right) (hIndexMember :
      Γ ⊢ₘ[T]
        index ∈ₘ domₘ(left)) (hPointValue :
      Γ ⊢ₘ[T] (left ·ₘ index) ≐ₘ value)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check)
    (hIndex : Term.CheckCertificate index SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[T] ((index ∈ₘ domₘ(left ⌢ₘ right)) ∧ₘ (((left ⌢ₘ right) ·ₘ index) ≐ₘ value)) := by
  have hPointContract :
      Γ ⊢ₘ[T] (finite_sequence_condition left ∧ₘ
            finite_sequence_condition right) ⟶ₘ (index ∈ₘ domₘ(left)) ⟶ₘ ((index ∈ₘ domₘ(left ⌢ₘ right)) ∧ₘ (((left ⌢ₘ right) ·ₘ index) ≐ₘ (left ·ₘ index))) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <|
          gq_weaken_standard_sequence <|
            standard_sequence_weaken_concatenation <|
              finite_sequence_concatenation_left_point_derives
                left right index
                hLeft.admissible hRight.admissible
                hIndex.admissible
  have hPoint :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.impElim hPointContract <|
        FirstOrder.Derives.conjIntro
          hLeftFinite hRightFinite)
      hIndexMember
  have hResultValue :
      Γ ⊢ₘ[T] ((left ⌢ₘ right) ·ₘ index) ≐ₘ value :=
    Metatheory.Derives.equality_trans
      (FirstOrder.Derives.conjElimRight hPoint)
      hPointValue
  exact FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjElimLeft hPoint)
    hResultValue
/--
有限序列左段的定义域成员仍属于拼接后的定义域。该结论是拼接逐点规格的
定义域投影，不要求调用方额外提供点值。
-/
theorem gq_concatenation_left_domain_member_of_theory
    {T : SetTheory} {Γ : Context signature} (hTheory :
      ∀ formula, godel_quotation_theory formula → T formula)
    (left right index : SetTerm) (hLeftFinite :
      Γ ⊢ₘ[T] finite_sequence_condition left) (hRightFinite :
      Γ ⊢ₘ[T] finite_sequence_condition right) (hIndexMember :
      Γ ⊢ₘ[T] index ∈ₘ domₘ(left))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check)
    (hIndex : Term.CheckCertificate index SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[T] index ∈ₘ domₘ(left ⌢ₘ right) :=
  FirstOrder.Derives.conjElimLeft <|
    gq_concatenation_left_point_of_theory
      hTheory left right index (left ·ₘ index)
      hLeftFinite hRightFinite hIndexMember
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (left ·ₘ index))
      (hLeft := hLeft) (hRight := hRight)
      (hIndex := hIndex)
/-- 有限序列拼接在 Gödel quotation 基础理论中保留左段的已知点。 -/
theorem gq_concatenation_left_point
    {Γ : Context signature} (left right index value : SetTerm)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left) (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right) (hIndexMember :
      Γ ⊢ₘ[godel_quotation_theory]
        index ∈ₘ domₘ(left)) (hPointValue :
      Γ ⊢ₘ[godel_quotation_theory] (left ·ₘ index) ≐ₘ value)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check)
    (hIndex : Term.CheckCertificate index SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory] ((index ∈ₘ domₘ(left ⌢ₘ right)) ∧ₘ (((left ⌢ₘ right) ·ₘ index) ≐ₘ value)) :=
  gq_concatenation_left_point_of_theory (fun _ hAxiom => hAxiom)
    left right index value
    hLeftFinite hRightFinite
    hIndexMember hPointValue
/-- 有限序列左段的定义域成员可直接提升到 Gödel quotation 拼接结果。 -/
theorem gq_concatenation_left_domain_member
    {Γ : Context signature} (left right index : SetTerm)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left) (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right) (hIndexMember :
      Γ ⊢ₘ[godel_quotation_theory]
        index ∈ₘ domₘ(left))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check)
    (hIndex : Term.CheckCertificate index SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      index ∈ₘ domₘ(left ⌢ₘ right) :=
  gq_concatenation_left_domain_member_of_theory
    (fun _ hAxiom => hAxiom)
    left right index hLeftFinite hRightFinite hIndexMember
/-- 两个已知有限的对象序列拼接后仍是有限序列。 -/
theorem gq_concatenation_finite
    {Γ : Context signature} (left right : SetTerm) (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left) (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      finite_sequence_condition (left ⌢ₘ right) := by
  have hContract :
      Γ ⊢ₘ[godel_quotation_theory] (finite_sequence_condition left ∧ₘ
            finite_sequence_condition right) ⟶ₘ
          finite_sequence_condition (left ⌢ₘ right) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_weaken_concatenation <|
            finite_sequence_concatenation_finite_derives
              left right hLeft.admissible hRight.admissible
  exact FirstOrder.Derives.impElim hContract <|
    FirstOrder.Derives.conjIntro
      hLeftFinite hRightFinite
/-- 有限序列拼接的有限性可沿 Gödel 引号理论的任意扩张直接提升。 -/
theorem gq_concatenation_finite_of_theory
    {T : SetTheory} {Γ : Context signature} (hTheory :
      ∀ formula, godel_quotation_theory formula → T formula)
    (left right : SetTerm) (hLeftFinite :
      Γ ⊢ₘ[T] finite_sequence_condition left) (hRightFinite :
      Γ ⊢ₘ[T] finite_sequence_condition right)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[T]
      finite_sequence_condition (left ⌢ₘ right) := by
  have hContract :
      Γ ⊢ₘ[T] (finite_sequence_condition left ∧ₘ
            finite_sequence_condition right) ⟶ₘ
          finite_sequence_condition (left ⌢ₘ right) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <|
          gq_weaken_standard_sequence <|
            standard_sequence_weaken_concatenation <|
              finite_sequence_concatenation_finite_derives
                left right hLeft.admissible hRight.admissible
  exact FirstOrder.Derives.impElim hContract <|
    FirstOrder.Derives.conjIntro
      hLeftFinite hRightFinite
/--
在 Gödel 引号理论的任意扩张中，有限序列拼接的定义域就是两个分段定义域的
对象自然数加法。该接口保留开放的分段长度，供构造代码反演时先建立有限上界，
再在具体 numeral 中进行有界分类。
-/
theorem gq_concatenation_domain_eq_sum_of_theory
    {T : SetTheory} {Γ : Context signature} (hTheory :
      ∀ formula, godel_quotation_theory formula → T formula)
    (left right : SetTerm) (hLeftFinite :
      Γ ⊢ₘ[T] finite_sequence_condition left) (hRightFinite :
      Γ ⊢ₘ[T] finite_sequence_condition right)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[T]
      domₘ(left ⌢ₘ right) ≐ₘ
        (domₘ(left) +ₘ domₘ(right)) := by
  have hSpecContract :
      Γ ⊢ₘ[T] (finite_sequence_condition left ∧ₘ
            finite_sequence_condition right) ⟶ₘ
          finite_sequence_concatenation_spec
            left right (left ⌢ₘ right) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
      FirstOrder.Derives.theory_weaken hTheory <|
        gq_weaken_standard_sequence <|
          standard_sequence_weaken_concatenation <|
            finite_sequence_concatenation_self_spec_derives
              left right hLeft.admissible hRight.admissible
  have hSpec :
      Γ ⊢ₘ[T]
        finite_sequence_concatenation_spec
          left right (left ⌢ₘ right) :=
    FirstOrder.Derives.impElim hSpecContract <|
      FirstOrder.Derives.conjIntro
        hLeftFinite hRightFinite
  simpa [finite_sequence_concatenation_spec] using
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight hSpec

/--
左段定义域是一个正 numeral 时，右段定义域严格属于拼接后的定义域。

该接口只固定左段长度，不要求调用方先恢复右段的外部长度；这是公式构造反演中
对递归右子式执行有界长度消去的统一入口。
-/
theorem gq_concatenation_right_domain_member_of_positive_left_length_of_theory
    {T : SetTheory} {Γ : Context signature}
    (hTheory :
      ∀ formula, godel_quotation_theory formula → T formula)
    (left right : SetTerm)
    (leftLength : Nat)
    (hLeftFinite :
      Γ ⊢ₘ[T] finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[T] finite_sequence_condition right)
    (hLeftDomain :
      Γ ⊢ₘ[T]
        domₘ(left) ≐ₘ numₘ(leftLength + 1))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[T]
      domₘ(right) ∈ₘ
        domₘ(left ⌢ₘ right) := by
  let rightDomain := domₘ(right)
  let numeralSum :=
    numₘ(leftLength + 1) +ₘ rightDomain
  let domainSum :=
    domₘ(left) +ₘ rightDomain
  have hRightDomain :
      Term.Admissible rightDomain SetSort.set := by
    simpa [rightDomain] using
      domain_term_admissible right hRight.admissible
  have hRightOmega :
      Γ ⊢ₘ[T] rightDomain ∈ₘ ωₘ := by
    simpa [rightDomain, finite_sequence_condition] using
      FirstOrder.Derives.conjElimRight hRightFinite
  have hRightInNumeralSum :
      Γ ⊢ₘ[T]
        rightDomain ∈ₘ numeralSum := by
    have hBound :
        ⊢ₘ[T]
          (rightDomain ∈ₘ ωₘ) ⟶ₘ
            (rightDomain ∈ₘ numeralSum) := by
      apply FirstOrder.Derives.theory_weaken hTheory
      simpa [rightDomain, numeralSum] using
        gq_weaken_standard_sequence <|
          standard_sequence_right_mem_positive_numeral_addition
            leftLength rightDomain hRightDomain
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) hBound)
      hRightOmega
  have hSumEquality :
      Γ ⊢ₘ[T]
        numeralSum ≐ₘ domainSum := by
    simpa [numeralSum, domainSum, rightDomain] using
      natural_addition_term_congr_of_equalities
        (numₘ(leftLength + 1)) (domₘ(left))
        (domₘ(right)) (domₘ(right))
        (finite_numeral_term_admissible
          (leftLength + 1))
        (domain_term_admissible
          left hLeft.admissible)
        (domain_term_admissible
          right hRight.admissible)
        (domain_term_admissible
          right hRight.admissible)
        (Metatheory.Derives.equality_symm
          hLeftDomain)
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) (domₘ(right)))
  have hRightInDomainSum :
      Γ ⊢ₘ[T]
        rightDomain ∈ₘ domainSum :=
    FirstOrder.Derives.iffElimRight
      (membership_right_iff_of_equality
        rightDomain numeralSum domainSum
        hRightDomain
        (natural_addition_term_admissible
          (numₘ(leftLength + 1)) rightDomain
          (finite_numeral_term_admissible
            (leftLength + 1))
          hRightDomain)
        (natural_addition_term_admissible
          (domₘ(left)) rightDomain
          (domain_term_admissible
            left hLeft.admissible)
          hRightDomain)
        hSumEquality)
      hRightInNumeralSum
  have hConcatenationDomain :
      Γ ⊢ₘ[T]
        domₘ(left ⌢ₘ right) ≐ₘ domainSum := by
    simpa [domainSum, rightDomain] using
      gq_concatenation_domain_eq_sum_of_theory
        hTheory left right
        hLeftFinite hRightFinite
        (hLeft := hLeft) (hRight := hRight)
  exact FirstOrder.Derives.iffElimLeft
    (membership_right_iff_of_equality
      rightDomain
      (domₘ(left ⌢ₘ right)) domainSum
      hRightDomain
      (domain_term_admissible
        (left ⌢ₘ right)
        (finite_sequence_concatenation_term_admissible
          left right hLeft.admissible hRight.admissible))
      (natural_addition_term_admissible
        (domₘ(left)) rightDomain
        (domain_term_admissible
          left hLeft.admissible)
        hRightDomain)
      hConcatenationDomain)
    hRightInDomainSum

/--
Gödel quotation 理论中的右段定义域下降。
-/
theorem gq_concatenation_right_domain_member_of_positive_left_length
    {Γ : Context signature}
    (left right : SetTerm)
    (leftLength : Nat)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftLength + 1))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(right) ∈ₘ
        domₘ(left ⌢ₘ right) :=
  gq_concatenation_right_domain_member_of_positive_left_length_of_theory
    (fun _ hAxiom => hAxiom)
    left right leftLength
    hLeftFinite hRightFinite hLeftDomain
    (hLeft := hLeft) (hRight := hRight)

/--
在 Gödel 引号理论的任意扩张中，两个已知 numeral 长度的有限序列拼接后，
定义域长度等于两个外部长度之和。
-/
theorem gq_concatenation_domain_eq_numeral_lengths_of_theory
    {T : SetTheory} {Γ : Context signature} (hTheory :
      ∀ formula, godel_quotation_theory formula → T formula)
    (left right : SetTerm) (leftLength rightLength : Nat)
    (hLeftFinite :
      Γ ⊢ₘ[T] finite_sequence_condition left) (hRightFinite :
      Γ ⊢ₘ[T] finite_sequence_condition right) (hLeftDomain :
      Γ ⊢ₘ[T] domₘ(left) ≐ₘ numₘ(leftLength)) (hRightDomain :
      Γ ⊢ₘ[T] domₘ(right) ≐ₘ numₘ(rightLength))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[T]
      domₘ(left ⌢ₘ right) ≐ₘ
        numₘ(leftLength + rightLength) := by
  let domainSum := domₘ(left) +ₘ domₘ(right)
  let numeralSum := numₘ(leftLength) +ₘ numₘ(rightLength)
  have hRawDomain :
      Γ ⊢ₘ[T]
        domₘ(left ⌢ₘ right) ≐ₘ domainSum := by
    simpa [domainSum] using
      gq_concatenation_domain_eq_sum_of_theory
        hTheory left right hLeftFinite hRightFinite
  have hDomainCongruence :
      Γ ⊢ₘ[T]
        domainSum ≐ₘ numeralSum := by
    simpa [domainSum, numeralSum] using
      natural_addition_term_congr_of_equalities (domₘ(left)) (numₘ(leftLength)) (domₘ(right)) (numₘ(rightLength)) (domain_term_admissible left hLeft.admissible)
        (finite_numeral_term_admissible leftLength)
        (domain_term_admissible right hRight.admissible)
        (finite_numeral_term_admissible rightLength)
        hLeftDomain hRightDomain
  have hNumeralValue :
      Γ ⊢ₘ[T]
        numeralSum ≐ₘ numₘ(leftLength + rightLength) := by
    exact FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <|
          Metatheory.Derives.equality_symm <| by
              simpa [numeralSum] using
                gq_weaken_standard_sequence (standard_token_sequence_finite_numeral_addition
                    leftLength rightLength)
  have hDomainToNumeralSum :
      Γ ⊢ₘ[T]
        domₘ(left ⌢ₘ right) ≐ₘ numeralSum :=
    Metatheory.Derives.equality_trans hRawDomain hDomainCongruence
  exact Metatheory.Derives.equality_trans
    hDomainToNumeralSum hNumeralValue
/--
三段拼接代码在三个分段定义域均为标准 numeral 时，其整体定义域为三者长度之和。
`code` 可以是任意通过对象等式定义为 `(prefix ⌢ body) ⌢ suffix` 的构造代码；该接口
用于从公式构造子的原始字符串定义递归计算长度，而不要求正文已经等于标准序列。
-/
theorem gq_three_part_domain_eq_numeral_lengths_of_theory
    {T : SetTheory} {Γ : Context signature} (hTheory :
      ∀ formula, godel_quotation_theory formula → T formula) (code prefixCode body suffix : SetTerm) (prefixLength bodyLength suffixLength : Nat)
    (hCodeRaw :
      Γ ⊢ₘ[T]
        code ≐ₘ ((prefixCode ⌢ₘ body) ⌢ₘ suffix)) (hPrefixFinite :
      Γ ⊢ₘ[T] finite_sequence_condition prefixCode) (hBodyFinite :
      Γ ⊢ₘ[T] finite_sequence_condition body) (hSuffixFinite :
      Γ ⊢ₘ[T] finite_sequence_condition suffix) (hPrefixDomain :
      Γ ⊢ₘ[T] domₘ(prefixCode) ≐ₘ numₘ(prefixLength)) (hBodyDomain :
      Γ ⊢ₘ[T] domₘ(body) ≐ₘ numₘ(bodyLength)) (hSuffixDomain :
      Γ ⊢ₘ[T] domₘ(suffix) ≐ₘ numₘ(suffixLength))
    (hCode : Term.CheckCertificate code SetSort.set := by
      prove_term_check)
    (hPrefix : Term.CheckCertificate prefixCode SetSort.set := by
      prove_term_check)
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check)
    (hSuffix : Term.CheckCertificate suffix SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[T]
      domₘ(code) ≐ₘ
        numₘ(prefixLength + bodyLength + suffixLength) := by
  let stage := prefixCode ⌢ₘ body
  let rawCode := stage ⌢ₘ suffix
  have hStage :
      Term.CheckCertificate stage SetSort.set := by
    prove_term_check
  have hRawCode :
      Term.CheckCertificate rawCode SetSort.set := by
    prove_term_check
  have hStageFinite :
      Γ ⊢ₘ[T] finite_sequence_condition stage := by
    simpa [stage] using
      gq_concatenation_finite_of_theory
        hTheory prefixCode body hPrefixFinite hBodyFinite
  have hStageDomain :
      Γ ⊢ₘ[T]
        domₘ(stage) ≐ₘ
          numₘ(prefixLength + bodyLength) := by
    simpa [stage] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        hTheory prefixCode body prefixLength bodyLength
        hPrefixFinite hBodyFinite
        hPrefixDomain hBodyDomain
  have hRawDomain :
      Γ ⊢ₘ[T]
        domₘ(rawCode) ≐ₘ
          numₘ(prefixLength + bodyLength + suffixLength) := by
    simpa [rawCode, stage, Nat.add_assoc] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        hTheory stage suffix (prefixLength + bodyLength) suffixLength
        hStageFinite hSuffixFinite
        hStageDomain hSuffixDomain
  have hDomainCongruence :
      Γ ⊢ₘ[T]
        domₘ(code) ≐ₘ domₘ(rawCode) :=
    domain_term_congr_of_equality
      code rawCode hCode.admissible hRawCode.admissible <| by
        simpa [rawCode, stage] using hCodeRaw
  exact Metatheory.Derives.equality_trans
    hDomainCongruence hRawDomain
/-- 对象代码等式可把右端的定义域成员与逐点值反演回左端。 -/
theorem gq_point_inversion_of_equality_of_theory
    {T : SetTheory} {Γ : Context signature}
    (left right index value : SetTerm) (hEquality :
      Γ ⊢ₘ[T] left ≐ₘ right) (hRightPoint :
      Γ ⊢ₘ[T] ((index ∈ₘ domₘ(right)) ∧ₘ ((right ·ₘ index) ≐ₘ value)))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check)
    (hIndex : Term.CheckCertificate index SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[T] ((index ∈ₘ domₘ(left)) ∧ₘ ((left ·ₘ index) ≐ₘ value)) := by
  have hDomainEquality :
      Γ ⊢ₘ[T]
        domₘ(left) ≐ₘ domₘ(right) :=
    domain_term_congr_of_equality
      left right hLeft.admissible hRight.admissible hEquality
  have hLeftMember :
      Γ ⊢ₘ[T]
        index ∈ₘ domₘ(left) :=
    FirstOrder.Derives.iffElimLeft (membership_right_iff_of_equality
        index (domₘ(left)) (domₘ(right))
        hIndex.admissible
        (domain_term_admissible left hLeft.admissible)
        (domain_term_admissible right hRight.admissible)
        hDomainEquality) (FirstOrder.Derives.conjElimLeft hRightPoint)
  have hApplicationEquality :
      Γ ⊢ₘ[T] (left ·ₘ index) ≐ₘ (right ·ₘ index) :=
    function_application_term_congr_function_of_equality
      left right index
      hLeft.admissible hRight.admissible hIndex.admissible
      hEquality
  have hLeftValue :
      Γ ⊢ₘ[T] (left ·ₘ index) ≐ₘ value :=
    Metatheory.Derives.equality_trans
      hApplicationEquality (FirstOrder.Derives.conjElimRight hRightPoint)
  exact FirstOrder.Derives.conjIntro
    hLeftMember hLeftValue
/-- 对象代码等式在 Gödel quotation 基础理论中反演定义域成员与逐点值。 -/
theorem gq_point_inversion_of_equality
    {Γ : Context signature} (left right index value : SetTerm) (hEquality :
      Γ ⊢ₘ[godel_quotation_theory] left ≐ₘ right) (hRightPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((index ∈ₘ domₘ(right)) ∧ₘ ((right ·ₘ index) ≐ₘ value)))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check)
    (hIndex : Term.CheckCertificate index SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory] ((index ∈ₘ domₘ(left)) ∧ₘ ((left ·ₘ index) ≐ₘ value)) :=
  gq_point_inversion_of_equality_of_theory
    left right index value
    hEquality hRightPoint
/--
若左段定义域等于固定 numeral `leftLength`，则右段任意标准位置 `index` 在拼接
结果中精确平移到 `leftLength + index`。
该定理只依赖左段的对象长度证书，不要求左段本身已有标准 token 展开；因此也适合
构造子末尾 token 的反演。
-/
theorem gq_concatenation_right_point_at_numeral_offset_of_theory
    {T : SetTheory} {Γ : Context signature} (hTheory :
      ∀ formula, godel_quotation_theory formula → T formula)
    (left right : SetTerm) (leftLength index : Nat) (hLeftFinite :
      Γ ⊢ₘ[T]
        finite_sequence_condition left) (hRightFinite :
      Γ ⊢ₘ[T]
        finite_sequence_condition right) (hLeftDomain :
      Γ ⊢ₘ[T]
        domₘ(left) ≐ₘ numₘ(leftLength)) (hRightIndex :
      Γ ⊢ₘ[T]
        numₘ(index) ∈ₘ domₘ(right))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[T] ((numₘ(leftLength + index) ∈ₘ
          domₘ(left ⌢ₘ right)) ∧ₘ (((left ⌢ₘ right) ·ₘ
            numₘ(leftLength + index)) ≐ₘ (right ·ₘ numₘ(index)))) := by
  let shifted := domₘ(left) +ₘ numₘ(index)
  let result := left ⌢ₘ right
  have hResult :
      Term.CheckCertificate result SetSort.set := by
    prove_term_check
  have hShifted :
      Term.CheckCertificate shifted SetSort.set := by
    prove_term_check
  have hPointContract :
      Γ ⊢ₘ[T] (finite_sequence_condition left ∧ₘ
            finite_sequence_condition right) ⟶ₘ (numₘ(index) ∈ₘ domₘ(right)) ⟶ₘ ((shifted ∈ₘ domₘ(result)) ∧ₘ ((result ·ₘ shifted) ≐ₘ
                (right ·ₘ numₘ(index)))) := by
    simpa [shifted, result] using
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
          FirstOrder.Derives.theory_weaken hTheory <|
            gq_weaken_standard_sequence <|
              standard_sequence_weaken_concatenation <|
                finite_sequence_concatenation_right_point_derives
                  left right (numₘ(index))
                  hLeft.admissible hRight.admissible
                  (finite_numeral_term_admissible index)
  have hPoint :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.impElim hPointContract <|
        FirstOrder.Derives.conjIntro
          hLeftFinite hRightFinite)
      hRightIndex
  have hIndexReflexive :
      Γ ⊢ₘ[T]
        numₘ(index) ≐ₘ numₘ(index) :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (numₘ(index))
  have hAdditionCongruence :
      Γ ⊢ₘ[T]
        shifted ≐ₘ (numₘ(leftLength) +ₘ numₘ(index)) := by
    simpa [shifted] using
      natural_addition_term_congr_of_equalities (domₘ(left)) (numₘ(leftLength)) (numₘ(index)) (numₘ(index)) (domain_term_admissible left hLeft.admissible)
        (finite_numeral_term_admissible leftLength) (finite_numeral_term_admissible index) (finite_numeral_term_admissible index)
        hLeftDomain hIndexReflexive
  have hAdditionValue :
      Γ ⊢ₘ[T] (numₘ(leftLength) +ₘ numₘ(index)) ≐ₘ
          numₘ(leftLength + index) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hTheory <|
          Metatheory.Derives.equality_symm <| by
                simpa using
                  gq_weaken_standard_sequence (standard_token_sequence_finite_numeral_addition
                      leftLength index)
  have hShiftEquality :
      Γ ⊢ₘ[T]
        shifted ≐ₘ numₘ(leftLength + index) :=
    Metatheory.Derives.equality_trans
      hAdditionCongruence hAdditionValue
  have hShiftedMember :
      Γ ⊢ₘ[T]
        numₘ(leftLength + index) ∈ₘ domₘ(result) :=
    FirstOrder.Derives.iffElimRight (membership_left_iff_of_equality
        shifted (numₘ(leftLength + index)) (domₘ(result))
        hShifted.admissible
        (finite_numeral_term_admissible (leftLength + index))
        (domain_term_admissible result hResult.admissible)
        hShiftEquality) (FirstOrder.Derives.conjElimLeft hPoint)
  have hApplicationCongruence :
      Γ ⊢ₘ[T] (result ·ₘ shifted) ≐ₘ (result ·ₘ numₘ(leftLength + index)) :=
    function_application_term_congr_argument_of_equality
      result shifted (numₘ(leftLength + index))
      hResult.admissible hShifted.admissible
      (finite_numeral_term_admissible (leftLength + index))
      hShiftEquality
  have hApplicationBack :
      Γ ⊢ₘ[T] (result ·ₘ numₘ(leftLength + index)) ≐ₘ (result ·ₘ shifted) :=
    Metatheory.Derives.equality_symm hApplicationCongruence
  have hShiftedValue :
      Γ ⊢ₘ[T] (result ·ₘ numₘ(leftLength + index)) ≐ₘ (right ·ₘ numₘ(index)) :=
    Metatheory.Derives.equality_trans
      hApplicationBack (FirstOrder.Derives.conjElimRight hPoint)
  simpa [result] using
    FirstOrder.Derives.conjIntro
      hShiftedMember hShiftedValue
/--
若左段定义域等于固定 numeral，则右段标准位置在 Gödel quotation 基础理论中的平移。
-/
theorem gq_concatenation_right_point_at_numeral_offset
    {Γ : Context signature} (left right : SetTerm)
    (leftLength index : Nat) (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left) (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right) (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftLength)) (hRightIndex :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(right))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory] ((numₘ(leftLength + index) ∈ₘ
          domₘ(left ⌢ₘ right)) ∧ₘ (((left ⌢ₘ right) ·ₘ
            numₘ(leftLength + index)) ≐ₘ (right ·ₘ numₘ(index)))) :=
  gq_concatenation_right_point_at_numeral_offset_of_theory (fun _ hAxiom => hAxiom)
    left right leftLength index
    hLeftFinite hRightFinite
    hLeftDomain hRightIndex
    (hLeft := hLeft) (hRight := hRight)
/--
若左段与一个标准 token 序列相等，则右段任意标准位置 `index` 在拼接结果中精确
平移到 `leftTokens.length + index`。
-/
theorem gq_concatenation_right_point_at_standard_offset
    {Γ : Context signature} (left right : SetTerm)
    (leftTokens : List Nat) (index : Nat) (hLeftEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        left ≐ₘ standard_token_sequence leftTokens) (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right) (hRightIndex :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(right))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory] ((numₘ(leftTokens.length + index) ∈ₘ
          domₘ(left ⌢ₘ right)) ∧ₘ (((left ⌢ₘ right) ·ₘ
            numₘ(leftTokens.length + index)) ≐ₘ (right ·ₘ numₘ(index)))) := by
  have hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left :=
    gq_finite_sequence_of_eq_standard_token_sequence
      left leftTokens hLeftEquality (hCode := hLeft)
  have hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftTokens.length) :=
    gq_domain_eq_length_of_eq_standard_token_sequence_of_theory (fun _ hAxiom => hAxiom)
      left leftTokens hLeftEquality (hCode := hLeft)
  exact
    gq_concatenation_right_point_at_numeral_offset
      left right leftTokens.length index
      hLeftFinite hRightFinite
      hLeftDomain hRightIndex
      (hLeft := hLeft) (hRight := hRight)
/--
若左段与一个标准 token 序列相等，则拼接右段的零号位置精确落在左段长度处。
-/
theorem gq_concatenation_right_zero_at_standard_length
    {Γ : Context signature} (left right : SetTerm)
    (leftTokens : List Nat) (hLeftEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        left ≐ₘ standard_token_sequence leftTokens) (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right) (hRightZero :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(0) ∈ₘ domₘ(right))
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory] ((numₘ(leftTokens.length) ∈ₘ
          domₘ(left ⌢ₘ right)) ∧ₘ (((left ⌢ₘ right) ·ₘ
            numₘ(leftTokens.length)) ≐ₘ (right ·ₘ numₘ(0)))) := by
  simpa using
    gq_concatenation_right_point_at_standard_offset
      left right leftTokens 0
      hLeftEquality hRightFinite hRightZero
      (hLeft := hLeft) (hRight := hRight)
/--
三段拼接中，中段任意标准位置 `index` 平移到整体的
`prefixTokens.length + index`，并保持逐点值。
-/
theorem gq_concatenation_middle_point_at_standard_offset
    {Γ : Context signature} (prefixCode body suffix : SetTerm)
    (prefixTokens : List Nat) (index : Nat) (hPrefixEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ standard_token_sequence prefixTokens) (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body) (hSuffixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition suffix) (hBodyIndex :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(body))
    (hPrefix : Term.CheckCertificate prefixCode SetSort.set := by
      prove_term_check)
    (hBody : Term.CheckCertificate body SetSort.set := by
      prove_term_check)
    (hSuffix : Term.CheckCertificate suffix SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory] ((numₘ(prefixTokens.length + index) ∈ₘ
          domₘ((prefixCode ⌢ₘ body) ⌢ₘ suffix)) ∧ₘ ((((prefixCode ⌢ₘ body) ⌢ₘ suffix) ·ₘ
            numₘ(prefixTokens.length + index)) ≐ₘ (body ·ₘ numₘ(index)))) := by
  let stage := prefixCode ⌢ₘ body
  let whole := stage ⌢ₘ suffix
  have hStage :
      Term.CheckCertificate stage SetSort.set := by
    prove_term_check
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode :=
    gq_finite_sequence_of_eq_standard_token_sequence
      prefixCode prefixTokens hPrefixEquality
      (hCode := hPrefix)
  have hStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition stage := by
    simpa [stage] using
      gq_concatenation_finite
        prefixCode body hPrefixFinite hBodyFinite
        (hLeft := hPrefix) (hRight := hBody)
  have hStagePoint :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(prefixTokens.length + index) ∈ₘ
            domₘ(stage)) ∧ₘ ((stage ·ₘ
              numₘ(prefixTokens.length + index)) ≐ₘ (body ·ₘ numₘ(index)))) := by
    simpa [stage] using
      gq_concatenation_right_point_at_standard_offset
        prefixCode body prefixTokens index
        hPrefixEquality hBodyFinite hBodyIndex
        (hLeft := hPrefix) (hRight := hBody)
  have hWholePointFromBody :
      Γ ⊢ₘ[godel_quotation_theory] ((numₘ(prefixTokens.length + index) ∈ₘ
            domₘ(whole)) ∧ₘ ((whole ·ₘ
              numₘ(prefixTokens.length + index)) ≐ₘ (body ·ₘ numₘ(index)))) := by
    simpa [whole] using
      gq_concatenation_left_point
        stage suffix (numₘ(prefixTokens.length + index)) (body ·ₘ numₘ(index))
        hStageFinite hSuffixFinite
        (FirstOrder.Derives.conjElimLeft hStagePoint)
        (FirstOrder.Derives.conjElimRight hStagePoint)
        (hLeft := hStage) (hRight := hSuffix)
  simpa [whole, stage] using hWholePointFromBody
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
