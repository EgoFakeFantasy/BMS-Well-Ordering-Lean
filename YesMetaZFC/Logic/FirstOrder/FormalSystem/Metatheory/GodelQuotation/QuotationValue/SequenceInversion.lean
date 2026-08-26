import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.Sequence

/-!
# Gödel quotation 的序列拼接反演

本模块把标准 token 串与对象有限序列拼接的等式反向消去到左右分段。证明只使用
有限序列的函数性、定义域长度和拼接的逐点规格，不引入语义解释。
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
标准列表拼接等于对象序列拼接时，已知长度的左段就是对应的标准前缀。
-/
theorem
    gq_concatenation_left_inversion_of_standard_equality
    {Γ : Context signature}
    (left right : SetTerm)
    (leftTokens rightTokens : List Nat)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftTokens.length))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (leftTokens ++ rightTokens) ≐ₘ
          (left ⌢ₘ right))
    (hLeft :
      Term.CheckCertificate left SetSort.set := by
        prove_term_check)
    (hRight :
      Term.CheckCertificate right SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      left ≐ₘ standard_token_sequence leftTokens := by
  have hLeftFunction :
      Γ ⊢ₘ[godel_quotation_theory]
        is_function_formula left := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimLeft hLeftFinite
  apply
    gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
      (T := godel_quotation_theory)
      (Γ := Γ)
      (fun _ hAxiom => Or.inl hAxiom)
      (fun _ hFormula =>
        godel_quotation_theory_sentence hFormula)
      left leftTokens hLeftFunction hLeftDomain
  intro index token hGet
  have hIndex :
      index < leftTokens.length :=
    (List.getElem?_eq_some_iff.mp hGet).1
  have hIndexInNumeral :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ numₘ(leftTokens.length) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_mem_of_lt
            index leftTokens.length hIndex
  have hIndexInLeft :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(left) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(index))
        (domₘ(left))
        (numₘ(leftTokens.length))
        (finite_numeral_term_admissible index)
        (domain_term_admissible left hLeft.admissible)
        (finite_numeral_term_admissible
          leftTokens.length)
        hLeftDomain)
      hIndexInNumeral
  have hWholeFromLeft :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(index) ∈ₘ domₘ(left ⌢ₘ right)) ∧ₘ
          (((left ⌢ₘ right) ·ₘ numₘ(index)) ≐ₘ
            (left ·ₘ numₘ(index)))) :=
    gq_concatenation_left_point
      left right (numₘ(index))
      (left ·ₘ numₘ(index))
      hLeftFinite hRightFinite hIndexInLeft
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set)
        (left ·ₘ numₘ(index)))
      (hLeft := hLeft) (hRight := hRight)
  have hAppendGet :
      (leftTokens ++ rightTokens)[index]? =
        some token := by
    rw [List.getElem?_append_left hIndex]
    exact hGet
  have hWholeToken :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(index) ∈ₘ domₘ(left ⌢ₘ right)) ∧ₘ
          (((left ⌢ₘ right) ·ₘ numₘ(index)) ≐ₘ
            numₘ(token))) :=
    gq_standard_token_sequence_point_inversion
      (left ⌢ₘ right)
      (leftTokens ++ rightTokens)
      (Metatheory.Derives.equality_symm hEquality)
      hAppendGet
  exact Metatheory.Derives.equality_trans
    (Metatheory.Derives.equality_symm <|
      FirstOrder.Derives.conjElimRight
        hWholeFromLeft)
    (FirstOrder.Derives.conjElimRight
      hWholeToken)

/--
标准列表拼接等于对象序列拼接时，已知左右长度的右段就是对应的标准后缀。
-/
theorem
    gq_concatenation_right_inversion_of_standard_equality
    {Γ : Context signature}
    (left right : SetTerm)
    (leftTokens rightTokens : List Nat)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftTokens.length))
    (hRightDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ≐ₘ numₘ(rightTokens.length))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (leftTokens ++ rightTokens) ≐ₘ
          (left ⌢ₘ right))
    (hLeft :
      Term.CheckCertificate left SetSort.set := by
        prove_term_check)
    (hRight :
      Term.CheckCertificate right SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      right ≐ₘ standard_token_sequence rightTokens := by
  have hRightFunction :
      Γ ⊢ₘ[godel_quotation_theory]
        is_function_formula right := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimLeft hRightFinite
  apply
    gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
      (T := godel_quotation_theory)
      (Γ := Γ)
      (fun _ hAxiom => Or.inl hAxiom)
      (fun _ hFormula =>
        godel_quotation_theory_sentence hFormula)
      right rightTokens hRightFunction hRightDomain
  intro index token hGet
  have hIndex :
      index < rightTokens.length :=
    (List.getElem?_eq_some_iff.mp hGet).1
  have hIndexInNumeral :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ numₘ(rightTokens.length) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_mem_of_lt
            index rightTokens.length hIndex
  have hIndexInRight :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(right) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(index))
        (domₘ(right))
        (numₘ(rightTokens.length))
        (finite_numeral_term_admissible index)
        (domain_term_admissible right hRight.admissible)
        (finite_numeral_term_admissible
          rightTokens.length)
        hRightDomain)
      hIndexInNumeral
  have hWholeFromRight :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(leftTokens.length + index) ∈ₘ
            domₘ(left ⌢ₘ right)) ∧ₘ
          (((left ⌢ₘ right) ·ₘ
              numₘ(leftTokens.length + index)) ≐ₘ
            (right ·ₘ numₘ(index)))) :=
    gq_concatenation_right_point_at_numeral_offset
      left right leftTokens.length index
      hLeftFinite hRightFinite
      hLeftDomain hIndexInRight
      (hLeft := hLeft) (hRight := hRight)
  have hAppendGet :
      (leftTokens ++ rightTokens)[leftTokens.length + index]? =
        some token := by
    rw [List.getElem?_append_right]
    · simpa using hGet
    · omega
  have hWholeToken :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(leftTokens.length + index) ∈ₘ
            domₘ(left ⌢ₘ right)) ∧ₘ
          (((left ⌢ₘ right) ·ₘ
              numₘ(leftTokens.length + index)) ≐ₘ
            numₘ(token))) :=
    gq_standard_token_sequence_point_inversion
      (left ⌢ₘ right)
      (leftTokens ++ rightTokens)
      (Metatheory.Derives.equality_symm hEquality)
      hAppendGet
  exact Metatheory.Derives.equality_trans
    (Metatheory.Derives.equality_symm <|
      FirstOrder.Derives.conjElimRight
        hWholeFromRight)
    (FirstOrder.Derives.conjElimRight
      hWholeToken)

/--
标准整串等于三段对象拼接时，已知标准前缀与中段长度即可恢复中段切片。

该接口只使用有限序列函数性、定义域 numeral 证书和三段拼接逐点规格；末段内容
保持完全开放。
-/
theorem
    gq_concatenation_middle_eq_standard_slice_of_domain
    {Γ : Context signature}
    (prefixCode body suffix : SetTerm)
    (prefixTokens tokens : List Nat)
    (bodyLength : Nat)
    (hPrefixEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ
          standard_token_sequence prefixTokens)
    (hBodyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition body)
    (hSuffixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition suffix)
    (hBodyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ numₘ(bodyLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          ((prefixCode ⌢ₘ body) ⌢ₘ suffix))
    (hSliceBound :
      prefixTokens.length + bodyLength ≤
        tokens.length)
    (hPrefix :
      Term.CheckCertificate prefixCode SetSort.set := by
        prove_term_check)
    (hBody :
      Term.CheckCertificate body SetSort.set := by
        prove_term_check)
    (hSuffix :
      Term.CheckCertificate suffix SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      body ≐ₘ
        standard_token_sequence
          ((tokens.drop prefixTokens.length).take
            bodyLength) := by
  let bodyTokens : List Nat :=
    (tokens.drop prefixTokens.length).take
      bodyLength
  have hBodyTokensLength :
      bodyTokens.length = bodyLength := by
    simp only [bodyTokens, List.length_take,
      List.length_drop]
    omega
  have hBodyFunction :
      Γ ⊢ₘ[godel_quotation_theory]
        is_function_formula body := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimLeft
        hBodyFinite
  have hBodyDomain' :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(body) ≐ₘ
          numₘ(bodyTokens.length) := by
    simpa [hBodyTokensLength] using hBodyDomain
  apply
    gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
      (T := godel_quotation_theory)
      (Γ := Γ)
      (fun _ hAxiom => Or.inl hAxiom)
      (fun _ hFormula =>
        godel_quotation_theory_sentence hFormula)
      body bodyTokens hBodyFunction hBodyDomain'
      (hSource := hBody)
  intro index token hGet
  have hIndex :
      index < bodyTokens.length :=
    (List.getElem?_eq_some_iff.mp hGet).1
  have hIndexNumeral :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ
          numₘ(bodyTokens.length) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_mem_of_lt
            index bodyTokens.length hIndex
  have hIndexBody :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(body) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(index))
        (domₘ(body))
        (numₘ(bodyTokens.length))
        (finite_numeral_term_admissible index)
        (domain_term_admissible
          body hBody.admissible)
        (finite_numeral_term_admissible
          bodyTokens.length)
        hBodyDomain')
      hIndexNumeral
  have hBodyPoint :=
    gq_concatenation_middle_point_at_standard_offset
      prefixCode body suffix prefixTokens index
      hPrefixEquality hBodyFinite hSuffixFinite
      hIndexBody
      (hPrefix := hPrefix)
      (hBody := hBody)
      (hSuffix := hSuffix)
  have hSliceIndex :
      index < bodyLength := by
    simpa [hBodyTokensLength] using hIndex
  have hDropGet :
      (tokens.drop prefixTokens.length)[index]? =
        some token := by
    rw [List.getElem?_take_of_lt hSliceIndex] at hGet
    simpa [bodyTokens] using hGet
  have hTokenGet :
      tokens[prefixTokens.length + index]? =
        some token := by
    simpa using hDropGet
  have hWholePoint :=
    gq_standard_token_sequence_point_inversion
      ((prefixCode ⌢ₘ body) ⌢ₘ suffix)
      tokens
      (Metatheory.Derives.equality_symm hEquality)
      hTokenGet
  exact Metatheory.Derives.equality_trans
    (Metatheory.Derives.equality_symm <|
      FirstOrder.Derives.conjElimRight
        hBodyPoint)
    (FirstOrder.Derives.conjElimRight
      hWholePoint)

/--
父码等于一条标准 token 序列，且子码定义域属于父码定义域时，子码长度可在
`0, ..., tokens.length - 1` 上做有限对象层消去。

这是 checked replay 强归纳的统一入口：各公式构造只需证明严格子域成员，调用方
随后在每个具体 numeral 长度分支恢复对应的外部 token 切片。
-/
theorem
    gq_domain_length_elim_of_member_of_standard_equality
    {Γ : Context signature}
    (child parent : SetTerm)
    (tokens : List Nat)
    (conclusion : SetFormula)
    (hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(child) ∈ₘ domₘ(parent))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ parent)
    (hBranch :
      ∀ length, length < tokens.length →
        (domₘ(child) ≐ₘ numₘ(length)) :: Γ
          ⊢ₘ[godel_quotation_theory] conclusion)
    (hChild :
      Term.CheckCertificate child SetSort.set := by
        prove_term_check)
    (hParent :
      Term.CheckCertificate parent SetSort.set := by
        prove_term_check)
    (hConclusion :
      Formula.CheckCertificate conclusion := by
        prove_nd_formula_check) :
    Γ ⊢ₘ[godel_quotation_theory] conclusion := by
  have hParentDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(parent) ≐ₘ numₘ(tokens.length) :=
    gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
      (fun _ hAxiom => hAxiom)
      parent tokens
      (Metatheory.Derives.equality_symm hEquality)
      (hCode := hParent)
  have hLengthMember :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(child) ∈ₘ numₘ(tokens.length) :=
    FirstOrder.Derives.iffElimRight
      (membership_right_iff_of_equality
        (domₘ(child))
        (domₘ(parent))
        (numₘ(tokens.length))
        (domain_term_admissible
          child hChild.admissible)
        (domain_term_admissible
          parent hParent.admissible)
        (finite_numeral_term_admissible
          tokens.length)
        hParentDomain)
      hMember
  have hLengthCases :
      Γ ⊢ₘ[godel_quotation_theory]
        stdseq_numeral_member_condition
          tokens.length (domₘ(child)) :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <|
            stdseq_numeral_member_iff
              tokens.length (domₘ(child))
              (domain_term_admissible
                child hChild.admissible))
      hLengthMember
  exact FirstOrder.Derives.cut
    hLengthCases <|
      stdseq_numeral_member_condition_elim_context
        tokens.length (domₘ(child)) conclusion
        hBranch
        (hPointCheck := by
          exact Term.check_admissible_complete <|
            domain_term_admissible
              child hChild.admissible)
        (hConclusionCheck := hConclusion)

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
