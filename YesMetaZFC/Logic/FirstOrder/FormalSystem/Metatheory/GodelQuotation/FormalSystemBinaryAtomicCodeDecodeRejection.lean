import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemTermCodeDecodeClosure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoderComposition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.BracketedThreePartInversion

/-!
# FormalSystem 二元原子公式码的 checked 解码拒绝

本模块把括号三段对象反演与两棵项树的宿主 checked decoder 组合起来。公共核心
不绑定等式或隶属，只消费 singleton 中缀码及对应的成功组合器；两个实际关系符号
由薄封装给出。
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
括号三段二元原子码的两个分量长度已固定时，公式 decoder 失败必然下降到某一项
切片；若宿主整串形状与对象构造不一致，则对象层直接推出矛盾。
-/
theorem gq_binary_atomic_code_decode_failure_descends_of_domains
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (first middle last : SetTerm)
    (tokens : List Nat)
    (middleToken firstLength lastLength : Nat)
    (hCompose :
      ∀ {firstTerm lastTerm : SetTerm},
        fs_named_term_tokens_decode_with_env
            freeBase boundNames
              ((tokens.drop 1).take firstLength) =
          some firstTerm →
        fs_named_term_tokens_decode_with_env
            freeBase boundNames
              ((tokens.drop (firstLength + 2)).take
                lastLength) =
          some lastTerm →
        ∃ formula,
          fs_named_hilbert_tokens_decode_with_env
              freeBase boundNames
              ([Numbered.logical_token .leftParenthesis] ++
                (tokens.drop 1).take firstLength ++
                [middleToken] ++
                (tokens.drop (firstLength + 2)).take
                  lastLength ++
                [Numbered.logical_token
                  .rightParenthesis]) =
            some formula)
    (hTokens : FSFormulaTokens tokens)
    (hFirstFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition first)
    (hMiddleEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        middle ≐ₘ
          standard_token_sequence [middleToken])
    (hLastFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition last)
    (hFirstDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(first) ≐ₘ numₘ(firstLength))
    (hLastDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(last) ≐ₘ numₘ(lastLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          binary_atomic_formula_code_term
            middle first last)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none)
    (hFirst :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddle :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLast :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    (Γ ⊢ₘ[godel_quotation_theory]
        Formula.falsum) ∨
      (fs_named_term_tokens_decode_with_env
            freeBase boundNames
              ((tokens.drop 1).take firstLength) =
          none ∧
        FSFormulaTokens
          ((tokens.drop 1).take firstLength) ∧
        ((tokens.drop 1).take firstLength).length <
          tokens.length ∧
        Γ ⊢ₘ[godel_quotation_theory]
          first ≐ₘ
            standard_token_sequence
              ((tokens.drop 1).take firstLength)) ∨
      (fs_named_term_tokens_decode_with_env
            freeBase boundNames
              ((tokens.drop (firstLength + 2)).take
                lastLength) =
          none ∧
        FSFormulaTokens
          ((tokens.drop (firstLength + 2)).take
            lastLength) ∧
        ((tokens.drop (firstLength + 2)).take
            lastLength).length <
          tokens.length ∧
        Γ ⊢ₘ[godel_quotation_theory]
          last ≐ₘ
            standard_token_sequence
              ((tokens.drop (firstLength + 2)).take
                lastLength)) := by
  let firstTokens : List Nat :=
    (tokens.drop 1).take firstLength
  let lastTokens : List Nat :=
    (tokens.drop (firstLength + 2)).take
      lastLength
  let expected : List Nat :=
    [Numbered.logical_token .leftParenthesis] ++
      firstTokens ++ [middleToken] ++ lastTokens ++
        [Numbered.logical_token .rightParenthesis]
  by_cases hShape : tokens = expected
  · have hParts :
        Γ ⊢ₘ[godel_quotation_theory]
          (first ≐ₘ
              standard_token_sequence firstTokens) ∧ₘ
            (last ≐ₘ
              standard_token_sequence lastTokens) := by
      simpa [firstTokens, lastTokens] using
        gq_bracketed_three_part_parts_eq_standard_slices_of_domains
          first middle last tokens
          middleToken firstLength lastLength
          hFirstFinite hMiddleEquality hLastFinite
          hFirstDomain hLastDomain hEquality
          (hFirstCheck := hFirst)
          (hMiddleCheck := hMiddle)
          (hLastCheck := hLast)
    have hFirstTokens :
        FSFormulaTokens firstTokens := by
      rw [hShape] at hTokens
      intro token hToken
      apply hTokens token
      simp [expected, hToken]
    have hLastTokens :
        FSFormulaTokens lastTokens := by
      rw [hShape] at hTokens
      intro token hToken
      apply hTokens token
      simp [expected, hToken]
    have hFirstLength :
        firstTokens.length < tokens.length := by
      rw [hShape]
      simp [expected]
      omega
    have hLastLength :
        lastTokens.length < tokens.length := by
      rw [hShape]
      simp [expected]
      omega
    have hDecodeExpected :
        fs_named_hilbert_tokens_decode_with_env
            freeBase boundNames expected =
          none := by
      simpa [hShape] using hDecode
    cases hFirstDecode :
        fs_named_term_tokens_decode_with_env
          freeBase boundNames firstTokens with
    | none =>
        exact Or.inr <| Or.inl
          ⟨by rfl,
            by simpa [firstTokens] using hFirstTokens,
            by simpa [firstTokens] using hFirstLength,
            by simpa [firstTokens] using
              FirstOrder.Derives.conjElimLeft hParts⟩
    | some firstTerm =>
        cases hLastDecode :
            fs_named_term_tokens_decode_with_env
              freeBase boundNames lastTokens with
        | none =>
            exact Or.inr <| Or.inr
              ⟨by rfl,
                by simpa [lastTokens] using hLastTokens,
                by simpa [lastTokens] using hLastLength,
                by simpa [lastTokens] using
                  FirstOrder.Derives.conjElimRight hParts⟩
        | some lastTerm =>
            have hFirstDecode' :
                fs_named_term_tokens_decode_with_env
                    freeBase boundNames
                      ((tokens.drop 1).take firstLength) =
                  some firstTerm := by
              simpa [firstTokens] using hFirstDecode
            have hLastDecode' :
                fs_named_term_tokens_decode_with_env
                    freeBase boundNames
                      ((tokens.drop
                          (firstLength + 2)).take
                        lastLength) =
                  some lastTerm := by
              simpa [lastTokens] using hLastDecode
            rcases hCompose hFirstDecode' hLastDecode' with
              ⟨formula, hWhole⟩
            have hWhole' :
                fs_named_hilbert_tokens_decode_with_env
                    freeBase boundNames expected =
                  some formula := by
              simpa [expected, firstTokens, lastTokens] using
                hWhole
            simp [hDecodeExpected] at hWhole'
  · exact Or.inl <|
      gq_bracketed_three_part_standard_falsum_of_not_slice_shape
        first middle last tokens
        middleToken firstLength lastLength
        hFirstFinite hMiddleEquality hLastFinite
        hFirstDomain hLastDomain hEquality
        (by
          simpa [expected, firstTokens, lastTokens] using
            hShape)
        (hFirstCheck := hFirst)
        (hMiddleCheck := hMiddle)
        (hLastCheck := hLast)

/--
等式原子码的 checked 解码失败在已知左右项长度后下降到某一项切片。
-/
theorem gq_equality_atomic_code_decode_failure_descends_of_domains
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (left right : SetTerm) (tokens : List Nat)
    (leftLength rightLength : Nat)
    (hTokens : FSFormulaTokens tokens)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftLength))
    (hRightDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ≐ₘ numₘ(rightLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          equality_atomic_formula_code_term left right)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none)
    (hLeft :
      Term.CheckCertificate left SetSort.set := by
        prove_term_check)
    (hRight :
      Term.CheckCertificate right SetSort.set := by
        prove_term_check) :
    (Γ ⊢ₘ[godel_quotation_theory]
        Formula.falsum) ∨
      (fs_named_term_tokens_decode_with_env
            freeBase boundNames
              ((tokens.drop 1).take leftLength) =
          none ∧
        FSFormulaTokens
          ((tokens.drop 1).take leftLength) ∧
        ((tokens.drop 1).take leftLength).length <
          tokens.length ∧
        Γ ⊢ₘ[godel_quotation_theory]
          left ≐ₘ
            standard_token_sequence
              ((tokens.drop 1).take leftLength)) ∨
      (fs_named_term_tokens_decode_with_env
            freeBase boundNames
              ((tokens.drop (leftLength + 2)).take
                rightLength) =
          none ∧
        FSFormulaTokens
          ((tokens.drop (leftLength + 2)).take
            rightLength) ∧
        ((tokens.drop (leftLength + 2)).take
            rightLength).length <
          tokens.length ∧
        Γ ⊢ₘ[godel_quotation_theory]
          right ≐ₘ
            standard_token_sequence
              ((tokens.drop (leftLength + 2)).take
                rightLength)) := by
  apply
    gq_binary_atomic_code_decode_failure_descends_of_domains
      freeBase boundNames
      left equality_symbol_code_term right tokens
      (Numbered.logical_token .equality)
      leftLength rightLength
  · intro leftTerm rightTerm hLeftDecode hRightDecode
    refine ⟨.equal leftTerm rightTerm, ?_⟩
    simpa [Numbered.equality_tokens] using
      fs_named_hilbert_tokens_decode_with_env_equality_of_term_tokens
        freeBase boundNames hLeftDecode hRightDecode
  · exact hTokens
  · exact hLeftFinite
  · exact FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        logical_symbol_code_eq_standard_token_sequence
          .equality
  · exact hRightFinite
  · exact hLeftDomain
  · exact hRightDomain
  · simpa [equality_atomic_formula_code_term] using
      hEquality
  · exact hDecode

/--
隶属原子码的 checked 解码失败在已知左右项长度后下降到某一项切片。
-/
theorem gq_membership_atomic_code_decode_failure_descends_of_domains
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (left right : SetTerm) (tokens : List Nat)
    (leftLength rightLength : Nat)
    (hTokens : FSFormulaTokens tokens)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftLength))
    (hRightDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ≐ₘ numₘ(rightLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          membership_atomic_formula_code_term left right)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none)
    (hLeft :
      Term.CheckCertificate left SetSort.set := by
        prove_term_check)
    (hRight :
      Term.CheckCertificate right SetSort.set := by
        prove_term_check) :
    (Γ ⊢ₘ[godel_quotation_theory]
        Formula.falsum) ∨
      (fs_named_term_tokens_decode_with_env
            freeBase boundNames
              ((tokens.drop 1).take leftLength) =
          none ∧
        FSFormulaTokens
          ((tokens.drop 1).take leftLength) ∧
        ((tokens.drop 1).take leftLength).length <
          tokens.length ∧
        Γ ⊢ₘ[godel_quotation_theory]
          left ≐ₘ
            standard_token_sequence
              ((tokens.drop 1).take leftLength)) ∨
      (fs_named_term_tokens_decode_with_env
            freeBase boundNames
              ((tokens.drop (leftLength + 2)).take
                rightLength) =
          none ∧
        FSFormulaTokens
          ((tokens.drop (leftLength + 2)).take
            rightLength) ∧
        ((tokens.drop (leftLength + 2)).take
            rightLength).length <
          tokens.length ∧
        Γ ⊢ₘ[godel_quotation_theory]
          right ≐ₘ
            standard_token_sequence
              ((tokens.drop (leftLength + 2)).take
                rightLength)) := by
  apply
    gq_binary_atomic_code_decode_failure_descends_of_domains
      freeBase boundNames
      left membership_symbol_code_term right tokens
      Numbered.membership_token leftLength rightLength
  · intro leftTerm rightTerm hLeftDecode hRightDecode
    let formula : SetFormula :=
      Formula.rel RelationSymbol.membership
        [leftTerm, rightTerm]
    refine ⟨formula, ?_⟩
    simpa [Numbered.membership_tokens] using
      fs_named_hilbert_tokens_decode_with_env_membership_of_term_tokens
        freeBase boundNames hLeftDecode hRightDecode
  · exact hTokens
  · exact hLeftFinite
  · exact FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        membership_symbol_code_eq_standard_token_sequence
  · exact hRightFinite
  · exact hLeftDomain
  · exact hRightDomain
  · simpa [membership_atomic_formula_code_term] using
      hEquality
  · exact hDecode

/--
任意 singleton 中缀的二元原子对象码若由两个项码组成，则整串 checked decoder
失败在对象层推出矛盾。左右项长度仅在父标准码的有限定义域内消去。
-/
theorem gq_binary_atomic_code_decode_falsum
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (first middle last : SetTerm)
    (tokens : List Nat) (middleToken : Nat)
    (hCompose :
      ∀ (firstLength lastLength : Nat)
          {firstTerm lastTerm : SetTerm},
        fs_named_term_tokens_decode_with_env
            freeBase boundNames
              ((tokens.drop 1).take firstLength) =
          some firstTerm →
        fs_named_term_tokens_decode_with_env
            freeBase boundNames
              ((tokens.drop (firstLength + 2)).take
                lastLength) =
          some lastTerm →
        ∃ formula,
          fs_named_hilbert_tokens_decode_with_env
              freeBase boundNames
              ([Numbered.logical_token .leftParenthesis] ++
                (tokens.drop 1).take firstLength ++
                [middleToken] ++
                (tokens.drop (firstLength + 2)).take
                  lastLength ++
                [Numbered.logical_token
                  .rightParenthesis]) =
            some formula)
    (hTokens : FSFormulaTokens tokens)
    (hFirstMember :
      Γ ⊢ₘ[godel_quotation_theory]
        first ∈ₘ TermCodeₘ)
    (hLastMember :
      Γ ⊢ₘ[godel_quotation_theory]
        last ∈ₘ TermCodeₘ)
    (hMiddleEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        middle ≐ₘ
          standard_token_sequence [middleToken])
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          binary_atomic_formula_code_term
            middle first last)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none)
    (hFirst :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddle :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLast :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  let code : SetTerm :=
    binary_atomic_formula_code_term middle first last
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hFirstPredicate :
      Γ ⊢ₘ[godel_quotation_theory]
        term_codeₘ(first) :=
    FirstOrder.Derives.iffElimLeft
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_term_code_definition_instance
            first hFirst.admissible)
      hFirstMember
  have hLastPredicate :
      Γ ⊢ₘ[godel_quotation_theory]
        term_codeₘ(last) :=
    FirstOrder.Derives.iffElimLeft
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_term_code_definition_instance
            last hLast.admissible)
      hLastMember
  have hFirstFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition first :=
    gq_term_code_implies_finite_sequence
      first hFirst.admissible hFirstPredicate
  have hMiddleFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middle :=
    gq_finite_sequence_of_eq_standard_token_sequence
      middle [middleToken] hMiddleEquality
      (hCode := hMiddle)
  have hLastFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition last :=
    gq_term_code_implies_finite_sequence
      last hLast.admissible hLastPredicate
  have hFirstDomainMember :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(first) ∈ₘ domₘ(code) := by
    simpa [code] using
      gq_bracketed_three_part_first_domain_mem_code_domain
        first middle last
        hFirstFinite hMiddleFinite hLastFinite
        (hFirstCheck := hFirst)
        (hMiddleCheck := hMiddle)
        (hLastCheck := hLast)
  apply
    gq_domain_length_elim_of_member_of_standard_equality
      (child := first) (parent := code)
      tokens Formula.falsum
      hFirstDomainMember
      (by simpa [code] using hEquality)
  intro firstLength hFirstLength
  let firstDomainCondition : SetFormula :=
    domₘ(first) ≐ₘ numₘ(firstLength)
  let Δ : Context signature :=
    firstDomainCondition :: Γ
  have hWeakenΓΔ :
      ∀ formula, formula ∈ Γ → formula ∈ Δ := by
    intro formula hFormula
    exact List.mem_cons_of_mem
      firstDomainCondition hFormula
  have hFirstDomain :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(first) ≐ₘ numₘ(firstLength) :=
    FirstOrder.Derives.assumption
      (by simp [Δ, firstDomainCondition])
  have hFirstMember' :
      Δ ⊢ₘ[godel_quotation_theory]
        first ∈ₘ TermCodeₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ) hWeakenΓΔ hFirstMember
  have hLastMember' :
      Δ ⊢ₘ[godel_quotation_theory]
        last ∈ₘ TermCodeₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ) hWeakenΓΔ hLastMember
  have hFirstFinite' :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition first :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ) hWeakenΓΔ hFirstFinite
  have hMiddleEquality' :
      Δ ⊢ₘ[godel_quotation_theory]
        middle ≐ₘ
          standard_token_sequence [middleToken] :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ) hWeakenΓΔ
      hMiddleEquality
  have hLastFinite' :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition last :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ) hWeakenΓΔ hLastFinite
  have hEquality' :
      Δ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ code :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ) hWeakenΓΔ <| by
        simpa [code] using hEquality
  have hLastDomainMember :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(last) ∈ₘ domₘ(code) := by
    simpa [code] using
      gq_bracketed_three_part_last_domain_mem_code_domain
        first middle last middleToken firstLength
        hFirstFinite' hMiddleEquality' hLastFinite'
        hFirstDomain
        (hFirstCheck := hFirst)
        (hMiddleCheck := hMiddle)
        (hLastCheck := hLast)
  apply
    gq_domain_length_elim_of_member_of_standard_equality
      (child := last) (parent := code)
      tokens Formula.falsum
      hLastDomainMember hEquality'
  intro lastLength hLastLength
  let lastDomainCondition : SetFormula :=
    domₘ(last) ≐ₘ numₘ(lastLength)
  let Ε : Context signature :=
    lastDomainCondition :: Δ
  have hWeakenΔΕ :
      ∀ formula, formula ∈ Δ → formula ∈ Ε := by
    intro formula hFormula
    exact List.mem_cons_of_mem
      lastDomainCondition hFormula
  have hFirstMember'' :
      Ε ⊢ₘ[godel_quotation_theory]
        first ∈ₘ TermCodeₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := Δ) (Δ := Ε) hWeakenΔΕ hFirstMember'
  have hLastMember'' :
      Ε ⊢ₘ[godel_quotation_theory]
        last ∈ₘ TermCodeₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := Δ) (Δ := Ε) hWeakenΔΕ hLastMember'
  have hFirstFinite'' :
      Ε ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition first :=
    FirstOrder.Derives.context_weaken
      (Γ := Δ) (Δ := Ε) hWeakenΔΕ hFirstFinite'
  have hMiddleEquality'' :
      Ε ⊢ₘ[godel_quotation_theory]
        middle ≐ₘ
          standard_token_sequence [middleToken] :=
    FirstOrder.Derives.context_weaken
      (Γ := Δ) (Δ := Ε) hWeakenΔΕ
      hMiddleEquality'
  have hLastFinite'' :
      Ε ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition last :=
    FirstOrder.Derives.context_weaken
      (Γ := Δ) (Δ := Ε) hWeakenΔΕ hLastFinite'
  have hFirstDomain' :
      Ε ⊢ₘ[godel_quotation_theory]
        domₘ(first) ≐ₘ numₘ(firstLength) :=
    FirstOrder.Derives.context_weaken
      (Γ := Δ) (Δ := Ε) hWeakenΔΕ hFirstDomain
  have hLastDomain :
      Ε ⊢ₘ[godel_quotation_theory]
        domₘ(last) ≐ₘ numₘ(lastLength) :=
    FirstOrder.Derives.assumption
      (by simp [Ε, lastDomainCondition])
  have hEquality'' :
      Ε ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          binary_atomic_formula_code_term
            middle first last := by
    simpa [code] using
      FirstOrder.Derives.context_weaken
        (Γ := Δ) (Δ := Ε) hWeakenΔΕ hEquality'
  rcases
      gq_binary_atomic_code_decode_failure_descends_of_domains
        freeBase boundNames
        first middle last tokens
        middleToken firstLength lastLength
        (hCompose firstLength lastLength)
        hTokens hFirstFinite'' hMiddleEquality''
        hLastFinite'' hFirstDomain' hLastDomain
        hEquality'' hDecode
        (hFirst := hFirst)
        (hMiddle := hMiddle)
        (hLast := hLast) with
    hFalsum |
      (⟨hFirstDecode, hFirstTokens, _,
          hFirstEquality⟩ |
        ⟨hLastDecode, hLastTokens, _,
          hLastEquality⟩)
  · exact hFalsum
  · exact
      gq_term_child_falsum_of_standard_rejection
        first ((tokens.drop 1).take firstLength)
        hFirst.admissible hFirstMember''
        hFirstEquality
        (gq_standard_term_code_not_of_decode_none
          freeBase boundNames
          ((tokens.drop 1).take firstLength)
          hFirstTokens hFirstDecode)
  · exact
      gq_term_child_falsum_of_standard_rejection
        last
        ((tokens.drop (firstLength + 2)).take
          lastLength)
        hLast.admissible hLastMember''
        hLastEquality
        (gq_standard_term_code_not_of_decode_none
          freeBase boundNames
          ((tokens.drop (firstLength + 2)).take
            lastLength)
          hLastTokens hLastDecode)

/-- 两个项码构成的等式原子不可能由 checked 公式 decoder 拒绝。 -/
theorem gq_equality_atomic_code_decode_falsum
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (left right : SetTerm) (tokens : List Nat)
    (hTokens : FSFormulaTokens tokens)
    (hLeftMember :
      Γ ⊢ₘ[godel_quotation_theory]
        left ∈ₘ TermCodeₘ)
    (hRightMember :
      Γ ⊢ₘ[godel_quotation_theory]
        right ∈ₘ TermCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          equality_atomic_formula_code_term left right)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none)
    (hLeft :
      Term.CheckCertificate left SetSort.set := by
        prove_term_check)
    (hRight :
      Term.CheckCertificate right SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  apply
    gq_binary_atomic_code_decode_falsum
      freeBase boundNames
      left equality_symbol_code_term right tokens
      (Numbered.logical_token .equality)
  · intro leftLength rightLength leftTerm rightTerm
      hLeftDecode hRightDecode
    refine ⟨.equal leftTerm rightTerm, ?_⟩
    simpa [Numbered.equality_tokens] using
      fs_named_hilbert_tokens_decode_with_env_equality_of_term_tokens
        freeBase boundNames hLeftDecode hRightDecode
  · exact hTokens
  · exact hLeftMember
  · exact hRightMember
  · exact FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        logical_symbol_code_eq_standard_token_sequence
          .equality
  · simpa [equality_atomic_formula_code_term] using
      hEquality
  · exact hDecode

/-- 两个项码构成的隶属原子不可能由 checked 公式 decoder 拒绝。 -/
theorem gq_membership_atomic_code_decode_falsum
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (left right : SetTerm) (tokens : List Nat)
    (hTokens : FSFormulaTokens tokens)
    (hLeftMember :
      Γ ⊢ₘ[godel_quotation_theory]
        left ∈ₘ TermCodeₘ)
    (hRightMember :
      Γ ⊢ₘ[godel_quotation_theory]
        right ∈ₘ TermCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          membership_atomic_formula_code_term left right)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none)
    (hLeft :
      Term.CheckCertificate left SetSort.set := by
        prove_term_check)
    (hRight :
      Term.CheckCertificate right SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  apply
    gq_binary_atomic_code_decode_falsum
      freeBase boundNames
      left membership_symbol_code_term right tokens
      Numbered.membership_token
  · intro leftLength rightLength leftTerm rightTerm
      hLeftDecode hRightDecode
    let formula : SetFormula :=
      Formula.rel RelationSymbol.membership
        [leftTerm, rightTerm]
    refine ⟨formula, ?_⟩
    simpa [Numbered.membership_tokens] using
      fs_named_hilbert_tokens_decode_with_env_membership_of_term_tokens
        freeBase boundNames hLeftDecode hRightDecode
  · exact hTokens
  · exact hLeftMember
  · exact hRightMember
  · exact FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        membership_symbol_code_eq_standard_token_sequence
  · simpa [membership_atomic_formula_code_term] using
      hEquality
  · exact hDecode

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
