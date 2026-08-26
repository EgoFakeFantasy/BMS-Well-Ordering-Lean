import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.SequenceInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.FormulaConstruction

/-!
# 括号三段构造的通用反演

本模块处理
`左括号 ⌢ first ⌢ middle ⌢ last ⌢ 右括号`
这一公共对象字符串。二元原子与蕴含只需分别提供 singleton 中缀码；左右递归
分量的切片和总长度反演不再绑定具体逻辑符号。
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
三个分量均为有限序列时，括号三段构造的零位固定为左括号 token。
-/
theorem gq_bracketed_three_part_left_parenthesis_point
    {Γ : Context signature}
    (first middle last : SetTerm)
    (hFirstFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition first)
    (hMiddleFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middle)
    (hLastFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition last)
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
      ((numₘ(0) ∈ₘ
          domₘ(binary_atomic_formula_code_term
            middle first last)) ∧ₘ
        ((binary_atomic_formula_code_term
              middle first last ·ₘ numₘ(0)) ≐ₘ
          numₘ(Numbered.logical_token .leftParenthesis))) := by
  let leftParenthesis : SetTerm :=
    left_parenthesis_symbol_code_term
  let rightParenthesis : SetTerm :=
    right_parenthesis_symbol_code_term
  let prefixCode : SetTerm :=
    ((leftParenthesis ⌢ₘ first) ⌢ₘ middle) ⌢ₘ last
  have hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hLeftPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(leftParenthesis)) ∧ₘ
          ((leftParenthesis ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token .leftParenthesis))) := by
    simpa [leftParenthesis] using
      gq_standard_token_sequence_point_inversion
        leftParenthesis
        [Numbered.logical_token .leftParenthesis]
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            logical_symbol_code_eq_standard_token_sequence
              .leftParenthesis)
        (by simp)
  have hFirstStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition
          (leftParenthesis ⌢ₘ first) :=
    gq_concatenation_finite
      leftParenthesis first hLeftFinite hFirstFinite
  have hFirstStagePoint :=
    gq_concatenation_left_point
      leftParenthesis first
      (numₘ(0))
      (numₘ(Numbered.logical_token .leftParenthesis))
      hLeftFinite hFirstFinite
      (FirstOrder.Derives.conjElimLeft hLeftPoint)
      (FirstOrder.Derives.conjElimRight hLeftPoint)
  have hMiddleStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition
          ((leftParenthesis ⌢ₘ first) ⌢ₘ middle) :=
    gq_concatenation_finite
      (leftParenthesis ⌢ₘ first) middle
      hFirstStageFinite hMiddleFinite
  have hMiddleStagePoint :=
    gq_concatenation_left_point
      (leftParenthesis ⌢ₘ first) middle
      (numₘ(0))
      (numₘ(Numbered.logical_token .leftParenthesis))
      hFirstStageFinite hMiddleFinite
      (FirstOrder.Derives.conjElimLeft hFirstStagePoint)
      (FirstOrder.Derives.conjElimRight hFirstStagePoint)
  have hPrefixPoint :=
    gq_concatenation_left_point
      ((leftParenthesis ⌢ₘ first) ⌢ₘ middle) last
      (numₘ(0))
      (numₘ(Numbered.logical_token .leftParenthesis))
      hMiddleStageFinite hLastFinite
      (FirstOrder.Derives.conjElimLeft hMiddleStagePoint)
      (FirstOrder.Derives.conjElimRight hMiddleStagePoint)
  have hPrefixFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode := by
    exact gq_concatenation_finite
      ((leftParenthesis ⌢ₘ first) ⌢ₘ middle) last
      hMiddleStageFinite hLastFinite
  simpa [binary_atomic_formula_code_term,
    leftParenthesis, rightParenthesis, prefixCode] using
      gq_concatenation_left_point
        prefixCode rightParenthesis
        (numₘ(0))
        (numₘ(Numbered.logical_token .leftParenthesis))
        hPrefixFinite hRightFinite
        (FirstOrder.Derives.conjElimLeft hPrefixPoint)
        (FirstOrder.Derives.conjElimRight hPrefixPoint)

/--
任意 Gödel quotation 理论扩张中的括号三段左括号 fixed-point checked replay。
-/
theorem gq_bracketed_three_part_left_parenthesis_point_of_theory
    {T : SetTheory} {Γ : Context signature}
    (hTheory :
      ∀ formula, godel_quotation_theory formula → T formula)
    (first middle last : SetTerm)
    (hFirstFinite :
      Γ ⊢ₘ[T] finite_sequence_condition first)
    (hMiddleFinite :
      Γ ⊢ₘ[T] finite_sequence_condition middle)
    (hLastFinite :
      Γ ⊢ₘ[T] finite_sequence_condition last)
    (hFirst :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddle :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLast :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[T]
      ((numₘ(0) ∈ₘ
          domₘ(binary_atomic_formula_code_term
            middle first last)) ∧ₘ
        ((binary_atomic_formula_code_term
              middle first last ·ₘ numₘ(0)) ≐ₘ
          numₘ(Numbered.logical_token .leftParenthesis))) := by
  let Δ : Context signature :=
    finite_sequence_condition first ::
      finite_sequence_condition middle ::
      finite_sequence_condition last :: []
  have hPoint :=
    gq_bracketed_three_part_left_parenthesis_point
      (Γ := Δ) first middle last
      (FirstOrder.Derives.assumption (by simp [Δ]))
      (FirstOrder.Derives.assumption (by simp [Δ]))
      (FirstOrder.Derives.assumption (by simp [Δ]))
      (hFirst := hFirst) (hMiddle := hMiddle) (hLast := hLast)
  apply FirstOrder.Derives.multi_cut
    (T := T) (Γ := Γ) (premises := Δ)
  · intro formula hFormula
    simp [Δ] at hFormula
    rcases hFormula with rfl | rfl | rfl
    · exact hFirstFinite
    · exact hMiddleFinite
    · exact hLastFinite
  · exact
      (FirstOrder.Derives.theory_weaken
        hTheory hPoint).context_weaken_append

/--
局部上下文中，括号三段对象字符串可由三个标准分量逐层重建为标准 token 串。
-/
theorem gq_bracketed_three_part_eq_standard_token_sequence_of_context
    {Γ : Context signature}
    (firstTokens middleTokens lastTokens : List Nat)
    (first middle last : SetTerm)
    (hFirst :
      Γ ⊢ₘ[godel_quotation_theory]
        first ≐ₘ standard_token_sequence firstTokens)
    (hMiddle :
      Γ ⊢ₘ[godel_quotation_theory]
        middle ≐ₘ standard_token_sequence middleTokens)
    (hLast :
      Γ ⊢ₘ[godel_quotation_theory]
        last ≐ₘ standard_token_sequence lastTokens)
    (hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddleCheck :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLastCheck :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      binary_atomic_formula_code_term middle first last ≐ₘ
        standard_token_sequence
          ([Numbered.logical_token .leftParenthesis] ++
            firstTokens ++ middleTokens ++ lastTokens ++
              [Numbered.logical_token
                .rightParenthesis]) := by
  let leftParenthesis : SetTerm :=
    left_parenthesis_symbol_code_term
  let rightParenthesis : SetTerm :=
    right_parenthesis_symbol_code_term
  let firstStage : SetTerm :=
    leftParenthesis ⌢ₘ first
  let middleStage : SetTerm :=
    firstStage ⌢ₘ middle
  let lastStage : SetTerm :=
    middleStage ⌢ₘ last
  have hLeftParenthesis :
      Γ ⊢ₘ[godel_quotation_theory]
        leftParenthesis ≐ₘ
          standard_token_sequence
            [Numbered.logical_token
              .leftParenthesis] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [leftParenthesis] using
          logical_symbol_code_eq_standard_token_sequence
            .leftParenthesis
  have hRightParenthesis :
      Γ ⊢ₘ[godel_quotation_theory]
        rightParenthesis ≐ₘ
          standard_token_sequence
            [Numbered.logical_token
              .rightParenthesis] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [rightParenthesis] using
          logical_symbol_code_eq_standard_token_sequence
            .rightParenthesis
  have hFirstStage :
      Γ ⊢ₘ[godel_quotation_theory]
        firstStage ≐ₘ
          standard_token_sequence
            ([Numbered.logical_token
              .leftParenthesis] ++ firstTokens) := by
    simpa [firstStage] using
      gq_concatenation_eq_standard_token_sequence
        [Numbered.logical_token .leftParenthesis]
        firstTokens leftParenthesis first
        hLeftParenthesis hFirst
  have hMiddleStage :
      Γ ⊢ₘ[godel_quotation_theory]
        middleStage ≐ₘ
          standard_token_sequence
            (([Numbered.logical_token
                .leftParenthesis] ++ firstTokens) ++
              middleTokens) := by
    simpa [middleStage] using
      gq_concatenation_eq_standard_token_sequence
        ([Numbered.logical_token .leftParenthesis] ++
          firstTokens)
        middleTokens firstStage middle
        hFirstStage hMiddle
  have hLastStage :
      Γ ⊢ₘ[godel_quotation_theory]
        lastStage ≐ₘ
          standard_token_sequence
            ((([Numbered.logical_token
                  .leftParenthesis] ++ firstTokens) ++
                middleTokens) ++ lastTokens) := by
    simpa [lastStage] using
      gq_concatenation_eq_standard_token_sequence
        (([Numbered.logical_token .leftParenthesis] ++
          firstTokens) ++ middleTokens)
        lastTokens middleStage last
        hMiddleStage hLast
  have hComplete :=
    gq_concatenation_eq_standard_token_sequence
      ((([Numbered.logical_token .leftParenthesis] ++
          firstTokens) ++ middleTokens) ++ lastTokens)
      [Numbered.logical_token .rightParenthesis]
      lastStage rightParenthesis
      hLastStage hRightParenthesis
  simpa [binary_atomic_formula_code_term,
    leftParenthesis, rightParenthesis,
    firstStage, middleStage, lastStage,
    List.append_assoc] using hComplete

/--
左右分量长度固定且中缀为 singleton 标准码时，括号三段构造的定义域长度精确为
`firstLength + lastLength + 3`。
-/
theorem gq_bracketed_three_part_domain_eq_lengths
    {Γ : Context signature}
    (first middle last : SetTerm)
    (middleToken firstLength lastLength : Nat)
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
    (hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddleCheck :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLastCheck :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(binary_atomic_formula_code_term
          middle first last) ≐ₘ
        numₘ(firstLength + lastLength + 3) := by
  let leftParenthesis : SetTerm :=
    left_parenthesis_symbol_code_term
  let rightParenthesis : SetTerm :=
    right_parenthesis_symbol_code_term
  let firstStage : SetTerm :=
    leftParenthesis ⌢ₘ first
  let middleStage : SetTerm :=
    firstStage ⌢ₘ middle
  let lastStage : SetTerm :=
    middleStage ⌢ₘ last
  have hLeftParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hLeftParenthesisDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftParenthesis) ≐ₘ numₘ(1) := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .leftParenthesis
  have hMiddleFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middle :=
    gq_finite_sequence_of_eq_standard_token_sequence
      middle [middleToken] hMiddleEquality
      (hCode := hMiddleCheck)
  have hMiddleDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(middle) ≐ₘ numₘ(1) := by
    simpa using
      gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
        (fun _ hAxiom => hAxiom)
        middle [middleToken] hMiddleEquality
        (hCode := hMiddleCheck)
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hRightParenthesisDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(rightParenthesis) ≐ₘ numₘ(1) := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .rightParenthesis
  have hFirstStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition firstStage := by
    simpa [firstStage] using
      gq_concatenation_finite
        leftParenthesis first
        hLeftParenthesisFinite hFirstFinite
  have hFirstStageDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(firstStage) ≐ₘ
          numₘ(firstLength + 1) := by
    simpa [firstStage, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        leftParenthesis first 1 firstLength
        hLeftParenthesisFinite hFirstFinite
        hLeftParenthesisDomain hFirstDomain
  have hMiddleStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middleStage := by
    simpa [middleStage] using
      gq_concatenation_finite
        firstStage middle
        hFirstStageFinite hMiddleFinite
  have hMiddleStageDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(middleStage) ≐ₘ
          numₘ(firstLength + 2) := by
    simpa [middleStage, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        firstStage middle (firstLength + 1) 1
        hFirstStageFinite hMiddleFinite
        hFirstStageDomain hMiddleDomain
  have hLastStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition lastStage := by
    simpa [lastStage] using
      gq_concatenation_finite
        middleStage last
        hMiddleStageFinite hLastFinite
  have hLastStageDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(lastStage) ≐ₘ
          numₘ(firstLength + lastLength + 2) := by
    simpa [lastStage, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        middleStage last (firstLength + 2)
        lastLength
        hMiddleStageFinite hLastFinite
        hMiddleStageDomain hLastDomain
  simpa [binary_atomic_formula_code_term,
    leftParenthesis, rightParenthesis,
    firstStage, middleStage, lastStage,
    Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        lastStage rightParenthesis
        (firstLength + lastLength + 2) 1
        hLastStageFinite hRightParenthesisFinite
        hLastStageDomain hRightParenthesisDomain

/--
第一分量的定义域严格属于整个括号三段代码的定义域。这里只使用固定左括号的
正长度，不要求预先确定任一递归分量的外部长度。
-/
theorem gq_bracketed_three_part_first_domain_mem_code_domain
    {Γ : Context signature}
    (first middle last : SetTerm)
    (hFirstFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition first)
    (hMiddleFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middle)
    (hLastFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition last)
    (hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddleCheck :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLastCheck :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(first) ∈ₘ
        domₘ(binary_atomic_formula_code_term
          middle first last) := by
  let leftParenthesis : SetTerm :=
    left_parenthesis_symbol_code_term
  let rightParenthesis : SetTerm :=
    right_parenthesis_symbol_code_term
  let firstStage : SetTerm :=
    leftParenthesis ⌢ₘ first
  let middleStage : SetTerm :=
    firstStage ⌢ₘ middle
  let lastStage : SetTerm :=
    middleStage ⌢ₘ last
  have hLeftParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hLeftParenthesisDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftParenthesis) ≐ₘ numₘ(0 + 1) := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .leftParenthesis
  have hFirstInFirstStage :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(first) ∈ₘ domₘ(firstStage) := by
    simpa [firstStage] using
      gq_concatenation_right_domain_member_of_positive_left_length
        leftParenthesis first 0
        hLeftParenthesisFinite hFirstFinite
        hLeftParenthesisDomain
  have hFirstStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition firstStage := by
    simpa [firstStage] using
      gq_concatenation_finite
        leftParenthesis first
        hLeftParenthesisFinite hFirstFinite
  have hFirstInMiddleStage :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(first) ∈ₘ domₘ(middleStage) := by
    simpa [middleStage] using
      gq_concatenation_left_domain_member
        firstStage middle (domₘ(first))
        hFirstStageFinite hMiddleFinite
        hFirstInFirstStage
  have hMiddleStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middleStage := by
    simpa [middleStage] using
      gq_concatenation_finite
        firstStage middle
        hFirstStageFinite hMiddleFinite
  have hFirstInLastStage :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(first) ∈ₘ domₘ(lastStage) := by
    simpa [lastStage] using
      gq_concatenation_left_domain_member
        middleStage last (domₘ(first))
        hMiddleStageFinite hLastFinite
        hFirstInMiddleStage
  have hLastStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition lastStage := by
    simpa [lastStage] using
      gq_concatenation_finite
        middleStage last
        hMiddleStageFinite hLastFinite
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  simpa [binary_atomic_formula_code_term,
    leftParenthesis, rightParenthesis,
    firstStage, middleStage, lastStage] using
      gq_concatenation_left_domain_member
        lastStage rightParenthesis (domₘ(first))
        hLastStageFinite hRightParenthesisFinite
        hFirstInLastStage

/--
第一分量长度固定且中缀为 singleton 标准码时，第三分量定义域严格属于整个
括号三段代码的定义域。
-/
theorem gq_bracketed_three_part_last_domain_mem_code_domain
    {Γ : Context signature}
    (first middle last : SetTerm)
    (middleToken firstLength : Nat)
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
    (hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddleCheck :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLastCheck :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(last) ∈ₘ
        domₘ(binary_atomic_formula_code_term
          middle first last) := by
  let leftParenthesis : SetTerm :=
    left_parenthesis_symbol_code_term
  let rightParenthesis : SetTerm :=
    right_parenthesis_symbol_code_term
  let firstStage : SetTerm :=
    leftParenthesis ⌢ₘ first
  let middleStage : SetTerm :=
    firstStage ⌢ₘ middle
  let lastStage : SetTerm :=
    middleStage ⌢ₘ last
  have hLeftParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hLeftParenthesisDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftParenthesis) ≐ₘ numₘ(1) := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .leftParenthesis
  have hMiddleFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middle :=
    gq_finite_sequence_of_eq_standard_token_sequence
      middle [middleToken] hMiddleEquality
      (hCode := hMiddleCheck)
  have hMiddleDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(middle) ≐ₘ numₘ(1) := by
    simpa using
      gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
        (fun _ hAxiom => hAxiom)
        middle [middleToken] hMiddleEquality
        (hCode := hMiddleCheck)
  have hFirstStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition firstStage := by
    simpa [firstStage] using
      gq_concatenation_finite
        leftParenthesis first
        hLeftParenthesisFinite hFirstFinite
  have hFirstStageDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(firstStage) ≐ₘ
          numₘ(firstLength + 1) := by
    simpa [firstStage, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        leftParenthesis first 1 firstLength
        hLeftParenthesisFinite hFirstFinite
        hLeftParenthesisDomain hFirstDomain
  have hMiddleStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middleStage := by
    simpa [middleStage] using
      gq_concatenation_finite
        firstStage middle
        hFirstStageFinite hMiddleFinite
  have hMiddleStageDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(middleStage) ≐ₘ
          numₘ((firstLength + 1) + 1) := by
    simpa [middleStage] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        firstStage middle (firstLength + 1) 1
        hFirstStageFinite hMiddleFinite
        hFirstStageDomain hMiddleDomain
  have hLastInLastStage :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(last) ∈ₘ domₘ(lastStage) := by
    simpa [lastStage] using
      gq_concatenation_right_domain_member_of_positive_left_length
        middleStage last (firstLength + 1)
        hMiddleStageFinite hLastFinite
        hMiddleStageDomain
  have hLastStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition lastStage := by
    simpa [lastStage] using
      gq_concatenation_finite
        middleStage last
        hMiddleStageFinite hLastFinite
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  simpa [binary_atomic_formula_code_term,
    leftParenthesis, rightParenthesis,
    firstStage, middleStage, lastStage] using
      gq_concatenation_left_domain_member
        lastStage rightParenthesis (domₘ(last))
        hLastStageFinite hRightParenthesisFinite
        hLastInLastStage

/--
括号三段构造在偏移 `1 + index` 处保留第一分量的第 `index` 个值。
-/
theorem gq_bracketed_three_part_first_point_at_standard_offset
    {Γ : Context signature}
    (first middle last : SetTerm) (index : Nat)
    (hFirstFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition first)
    (hMiddleFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middle)
    (hLastFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition last)
    (hIndex :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(first))
    (hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddleCheck :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLastCheck :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      ((numₘ(1 + index) ∈ₘ
          domₘ(binary_atomic_formula_code_term
            middle first last)) ∧ₘ
        ((binary_atomic_formula_code_term
              middle first last ·ₘ
            numₘ(1 + index)) ≐ₘ
          (first ·ₘ numₘ(index)))) := by
  let leftParenthesis : SetTerm :=
    left_parenthesis_symbol_code_term
  let rightParenthesis : SetTerm :=
    right_parenthesis_symbol_code_term
  let middleStage : SetTerm :=
    (leftParenthesis ⌢ₘ first) ⌢ₘ middle
  let lastStage : SetTerm :=
    middleStage ⌢ₘ last
  let rawCode : SetTerm :=
    lastStage ⌢ₘ rightParenthesis
  have hLeftParenthesisEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftParenthesis ≐ₘ
          standard_token_sequence
            [Numbered.logical_token
              .leftParenthesis] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [leftParenthesis] using
          logical_symbol_code_eq_standard_token_sequence
            .leftParenthesis
  have hMiddleStagePoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1 + index) ∈ₘ
            domₘ(middleStage)) ∧ₘ
          ((middleStage ·ₘ numₘ(1 + index)) ≐ₘ
            (first ·ₘ numₘ(index)))) := by
    simpa [middleStage] using
      gq_concatenation_middle_point_at_standard_offset
        leftParenthesis first middle
        [Numbered.logical_token .leftParenthesis]
        index hLeftParenthesisEquality
        hFirstFinite hMiddleFinite hIndex
  have hLeftParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hMiddleStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middleStage := by
    simpa [middleStage] using
      gq_concatenation_finite
        (leftParenthesis ⌢ₘ first) middle
        (gq_concatenation_finite
          leftParenthesis first
          hLeftParenthesisFinite hFirstFinite)
        hMiddleFinite
  have hLastStagePoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1 + index) ∈ₘ
            domₘ(lastStage)) ∧ₘ
          ((lastStage ·ₘ numₘ(1 + index)) ≐ₘ
            (first ·ₘ numₘ(index)))) := by
    simpa [lastStage] using
      gq_concatenation_left_point
        middleStage last
        (numₘ(1 + index))
        (first ·ₘ numₘ(index))
        hMiddleStageFinite hLastFinite
        (FirstOrder.Derives.conjElimLeft
          hMiddleStagePoint)
        (FirstOrder.Derives.conjElimRight
          hMiddleStagePoint)
  have hLastStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition lastStage := by
    simpa [lastStage] using
      gq_concatenation_finite
        middleStage last
        hMiddleStageFinite hLastFinite
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hRawPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1 + index) ∈ₘ
            domₘ(rawCode)) ∧ₘ
          ((rawCode ·ₘ numₘ(1 + index)) ≐ₘ
            (first ·ₘ numₘ(index)))) := by
    simpa [rawCode] using
      gq_concatenation_left_point
        lastStage rightParenthesis
        (numₘ(1 + index))
        (first ·ₘ numₘ(index))
        hLastStageFinite hRightParenthesisFinite
        (FirstOrder.Derives.conjElimLeft
          hLastStagePoint)
        (FirstOrder.Derives.conjElimRight
          hLastStagePoint)
  simpa [rawCode, lastStage, middleStage,
    leftParenthesis, rightParenthesis,
    binary_atomic_formula_code_term] using hRawPoint

/--
第一分量长度为 `firstLength` 时，括号三段构造在偏移 `firstLength + 1`
处保留 singleton 中缀的固定 token。
-/
theorem gq_bracketed_three_part_middle_point_of_first_domain
    {Γ : Context signature}
    (first middle last : SetTerm)
    (middleToken firstLength : Nat)
    (hFirstFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition first)
    (hFirstDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(first) ≐ₘ numₘ(firstLength))
    (hMiddleEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        middle ≐ₘ standard_token_sequence [middleToken])
    (hLastFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition last)
    (hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddleCheck :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLastCheck :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      ((numₘ(firstLength + 1) ∈ₘ
          domₘ(binary_atomic_formula_code_term
            middle first last)) ∧ₘ
        ((binary_atomic_formula_code_term
              middle first last ·ₘ
            numₘ(firstLength + 1)) ≐ₘ
          numₘ(middleToken))) := by
  let leftParenthesis : SetTerm :=
    left_parenthesis_symbol_code_term
  let rightParenthesis : SetTerm :=
    right_parenthesis_symbol_code_term
  let firstStage : SetTerm :=
    leftParenthesis ⌢ₘ first
  let middleStage : SetTerm :=
    firstStage ⌢ₘ middle
  let lastStage : SetTerm :=
    middleStage ⌢ₘ last
  have hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .leftParenthesis
  have hLeftDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(leftParenthesis) ≐ₘ numₘ(1) := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_domain_eq_one
        (Γ := Γ) .leftParenthesis
  have hMiddleFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middle :=
    gq_finite_sequence_of_eq_standard_token_sequence
      middle [middleToken] hMiddleEquality
  have hMiddlePoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(middle)) ∧ₘ
          ((middle ·ₘ numₘ(0)) ≐ₘ numₘ(middleToken))) :=
    gq_standard_token_sequence_point_inversion
      middle [middleToken] hMiddleEquality (by simp)
  have hFirstStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition firstStage := by
    simpa [firstStage] using
      gq_concatenation_finite
        leftParenthesis first hLeftFinite hFirstFinite
  have hFirstStageDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(firstStage) ≐ₘ numₘ(1 + firstLength) := by
    simpa [firstStage] using
      gq_concatenation_domain_eq_numeral_lengths_of_theory
        (fun _ hAxiom => hAxiom)
        leftParenthesis first 1 firstLength
        hLeftFinite hFirstFinite hLeftDomain hFirstDomain
  have hMiddleStagePoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1 + firstLength) ∈ₘ
            domₘ(middleStage)) ∧ₘ
          ((middleStage ·ₘ numₘ(1 + firstLength)) ≐ₘ
            numₘ(middleToken))) := by
    have hPoint :=
      gq_concatenation_right_point_at_numeral_offset
        firstStage middle (1 + firstLength) 0
        hFirstStageFinite hMiddleFinite hFirstStageDomain
        (FirstOrder.Derives.conjElimLeft hMiddlePoint)
    exact FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjElimLeft hPoint)
      (Metatheory.Derives.equality_trans
        (FirstOrder.Derives.conjElimRight hPoint)
        (FirstOrder.Derives.conjElimRight hMiddlePoint))
  have hMiddleStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middleStage := by
    simpa [middleStage] using
      gq_concatenation_finite
        firstStage middle hFirstStageFinite hMiddleFinite
  have hLastStagePoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1 + firstLength) ∈ₘ
            domₘ(lastStage)) ∧ₘ
          ((lastStage ·ₘ numₘ(1 + firstLength)) ≐ₘ
            numₘ(middleToken))) := by
    simpa [lastStage] using
      gq_concatenation_left_point
        middleStage last
        (numₘ(1 + firstLength)) (numₘ(middleToken))
        hMiddleStageFinite hLastFinite
        (FirstOrder.Derives.conjElimLeft hMiddleStagePoint)
        (FirstOrder.Derives.conjElimRight hMiddleStagePoint)
  have hLastStageFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition lastStage := by
    simpa [lastStage] using
      gq_concatenation_finite
        middleStage last hMiddleStageFinite hLastFinite
  have hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hRawPoint :=
    gq_concatenation_left_point
      lastStage rightParenthesis
      (numₘ(1 + firstLength)) (numₘ(middleToken))
      hLastStageFinite hRightFinite
      (FirstOrder.Derives.conjElimLeft hLastStagePoint)
      (FirstOrder.Derives.conjElimRight hLastStagePoint)
  simpa [binary_atomic_formula_code_term,
    leftParenthesis, rightParenthesis,
    firstStage, middleStage, lastStage,
    Nat.add_comm] using hRawPoint

/--
任意 Gödel quotation 理论扩张中的括号三段中缀固定点 checked replay。
-/
theorem gq_bracketed_three_part_middle_point_of_first_domain_of_theory
    {T : SetTheory} {Γ : Context signature}
    (hTheory :
      ∀ formula, godel_quotation_theory formula → T formula)
    (first middle last : SetTerm)
    (middleToken firstLength : Nat)
    (hFirstFinite :
      Γ ⊢ₘ[T]
        finite_sequence_condition first)
    (hFirstDomain :
      Γ ⊢ₘ[T]
        domₘ(first) ≐ₘ numₘ(firstLength))
    (hMiddleEquality :
      Γ ⊢ₘ[T]
        middle ≐ₘ standard_token_sequence [middleToken])
    (hLastFinite :
      Γ ⊢ₘ[T]
        finite_sequence_condition last)
    (hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddleCheck :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLastCheck :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[T]
      ((numₘ(firstLength + 1) ∈ₘ
          domₘ(binary_atomic_formula_code_term
            middle first last)) ∧ₘ
        ((binary_atomic_formula_code_term
              middle first last ·ₘ
            numₘ(firstLength + 1)) ≐ₘ
          numₘ(middleToken))) := by
  let Δ : Context signature :=
    finite_sequence_condition first ::
      (domₘ(first) ≐ₘ numₘ(firstLength)) ::
      (middle ≐ₘ standard_token_sequence [middleToken]) ::
      finite_sequence_condition last :: []
  have hFirstFiniteAt :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition first :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hFirstDomainAt :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(first) ≐ₘ numₘ(firstLength) :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hMiddleEqualityAt :
      Δ ⊢ₘ[godel_quotation_theory]
        middle ≐ₘ standard_token_sequence [middleToken] :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hLastFiniteAt :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition last :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hPoint :=
    gq_bracketed_three_part_middle_point_of_first_domain
      first middle last middleToken firstLength
      hFirstFiniteAt hFirstDomainAt
      hMiddleEqualityAt hLastFiniteAt
      (hFirstCheck := hFirstCheck)
      (hMiddleCheck := hMiddleCheck)
      (hLastCheck := hLastCheck)
  apply FirstOrder.Derives.multi_cut
    (T := T) (Γ := Γ) (premises := Δ)
  · intro formula hFormula
    simp [Δ] at hFormula
    rcases hFormula with rfl | rfl | rfl | rfl
    · exact hFirstFinite
    · exact hFirstDomain
    · exact hMiddleEquality
    · exact hLastFinite
  · exact
      (FirstOrder.Derives.theory_weaken
        hTheory hPoint).context_weaken_append

/--
标准整串等于括号三段构造时，已知第一分量长度即可恢复紧随左括号的标准切片。
-/
theorem gq_bracketed_three_part_first_eq_standard_slice_of_domain
    {Γ : Context signature}
    (first middle last : SetTerm)
    (tokens : List Nat) (firstLength : Nat)
    (hFirstLength : firstLength < tokens.length)
    (hFirstFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition first)
    (hMiddleFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition middle)
    (hLastFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition last)
    (hFirstDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(first) ≐ₘ numₘ(firstLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          binary_atomic_formula_code_term
            middle first last)
    (hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddleCheck :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLastCheck :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      first ≐ₘ
        standard_token_sequence
          ((tokens.drop 1).take firstLength) := by
  let firstTokens : List Nat :=
    (tokens.drop 1).take firstLength
  have hFirstTokensLength :
      firstTokens.length = firstLength := by
    simp only [firstTokens, List.length_take,
      List.length_drop]
    omega
  have hFirstFunction :
      Γ ⊢ₘ[godel_quotation_theory]
        is_function_formula first := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimLeft hFirstFinite
  have hFirstDomain' :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(first) ≐ₘ
          numₘ(firstTokens.length) := by
    simpa [hFirstTokensLength] using hFirstDomain
  apply
    gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
      (T := godel_quotation_theory)
      (Γ := Γ)
      (fun _ hAxiom => Or.inl hAxiom)
      (fun _ hFormula =>
        godel_quotation_theory_sentence hFormula)
      first firstTokens hFirstFunction hFirstDomain'
      (hSource := hFirstCheck)
  intro index token hGet
  have hIndex :
      index < firstTokens.length :=
    (List.getElem?_eq_some_iff.mp hGet).1
  have hIndexNumeral :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ
          numₘ(firstTokens.length) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_mem_of_lt
            index firstTokens.length hIndex
  have hIndexFirst :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(first) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(index))
        (domₘ(first))
        (numₘ(firstTokens.length))
        (finite_numeral_term_admissible index)
        (domain_term_admissible
          first hFirstCheck.admissible)
        (finite_numeral_term_admissible
          firstTokens.length)
        hFirstDomain')
      hIndexNumeral
  have hSliceIndex :
      index < firstLength := by
    simpa [hFirstTokensLength] using hIndex
  have hDropGet :
      (tokens.drop 1)[index]? = some token := by
    rw [List.getElem?_take_of_lt hSliceIndex] at hGet
    simpa [firstTokens] using hGet
  have hTokenGet :
      tokens[1 + index]? = some token := by
    simpa [Nat.add_comm] using hDropGet
  have hBodyPoint :=
    gq_bracketed_three_part_first_point_at_standard_offset
      first middle last index
      hFirstFinite hMiddleFinite hLastFinite
      hIndexFirst
      (hFirstCheck := hFirstCheck)
      (hMiddleCheck := hMiddleCheck)
      (hLastCheck := hLastCheck)
  have hCodePoint :=
    gq_standard_token_sequence_point_inversion
      (binary_atomic_formula_code_term
        middle first last)
      tokens
      (Metatheory.Derives.equality_symm hEquality)
      hTokenGet
  exact Metatheory.Derives.equality_trans
    (Metatheory.Derives.equality_symm <|
      FirstOrder.Derives.conjElimRight
        hBodyPoint)
    (FirstOrder.Derives.conjElimRight
      hCodePoint)

/--
第一分量与 singleton 中缀已规范化时，第三分量的第 `index` 个值出现在偏移
`firstTokens.length + 2 + index`。
-/
theorem gq_bracketed_three_part_last_point_at_standard_offset
    {Γ : Context signature}
    (first middle last : SetTerm)
    (firstTokens : List Nat)
    (middleToken index : Nat)
    (hFirstEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        first ≐ₘ
          standard_token_sequence firstTokens)
    (hMiddleEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        middle ≐ₘ
          standard_token_sequence [middleToken])
    (hLastFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition last)
    (hIndex :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(last))
    (hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddleCheck :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLastCheck :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      ((numₘ(firstTokens.length + 2 + index) ∈ₘ
          domₘ(binary_atomic_formula_code_term
            middle first last)) ∧ₘ
        ((binary_atomic_formula_code_term
              middle first last ·ₘ
            numₘ(firstTokens.length + 2 + index)) ≐ₘ
          (last ·ₘ numₘ(index)))) := by
  let leftParenthesis : SetTerm :=
    left_parenthesis_symbol_code_term
  let rightParenthesis : SetTerm :=
    right_parenthesis_symbol_code_term
  let firstStage : SetTerm :=
    leftParenthesis ⌢ₘ first
  let prefixCode : SetTerm :=
    firstStage ⌢ₘ middle
  let rawCode : SetTerm :=
    (prefixCode ⌢ₘ last) ⌢ₘ rightParenthesis
  let prefixTokens : List Nat :=
    [Numbered.logical_token .leftParenthesis] ++
      firstTokens ++ [middleToken]
  have hLeftParenthesisEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftParenthesis ≐ₘ
          standard_token_sequence
            [Numbered.logical_token
              .leftParenthesis] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        simpa [leftParenthesis] using
          logical_symbol_code_eq_standard_token_sequence
            .leftParenthesis
  have hFirstStageEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        firstStage ≐ₘ
          standard_token_sequence
            ([Numbered.logical_token
                .leftParenthesis] ++ firstTokens) := by
    simpa [firstStage] using
      gq_concatenation_eq_standard_token_sequence
        [Numbered.logical_token .leftParenthesis]
        firstTokens leftParenthesis first
        hLeftParenthesisEquality hFirstEquality
  have hPrefixEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        prefixCode ≐ₘ
          standard_token_sequence prefixTokens := by
    simpa [prefixCode, prefixTokens,
      List.append_assoc] using
      gq_concatenation_eq_standard_token_sequence
        ([Numbered.logical_token .leftParenthesis] ++
          firstTokens)
        [middleToken] firstStage middle
        hFirstStageEquality hMiddleEquality
  have hRightParenthesisFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Γ) .rightParenthesis
  have hRawPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(prefixTokens.length + index) ∈ₘ
            domₘ(rawCode)) ∧ₘ
          ((rawCode ·ₘ
              numₘ(prefixTokens.length + index)) ≐ₘ
            (last ·ₘ numₘ(index)))) := by
    simpa [rawCode] using
      gq_concatenation_middle_point_at_standard_offset
        prefixCode last rightParenthesis
        prefixTokens index hPrefixEquality
        hLastFinite hRightParenthesisFinite hIndex
  simpa [rawCode, prefixCode, firstStage,
    prefixTokens, leftParenthesis,
    rightParenthesis,
    binary_atomic_formula_code_term,
    Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hRawPoint

/--
标准整串等于括号三段构造，且第一分量已恢复为标准串时，按其后固定两位偏移恢复
第三分量切片。
-/
theorem gq_bracketed_three_part_last_eq_standard_slice_of_domains
    {Γ : Context signature}
    (first middle last : SetTerm)
    (tokens firstTokens : List Nat)
    (middleToken lastLength : Nat)
    (hSliceBound :
      firstTokens.length + 2 + lastLength ≤
        tokens.length)
    (hFirstEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        first ≐ₘ
          standard_token_sequence firstTokens)
    (hMiddleEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        middle ≐ₘ
          standard_token_sequence [middleToken])
    (hLastFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition last)
    (hLastDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(last) ≐ₘ numₘ(lastLength))
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          binary_atomic_formula_code_term
            middle first last)
    (hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddleCheck :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLastCheck :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      last ≐ₘ
        standard_token_sequence
          ((tokens.drop (firstTokens.length + 2)).take
            lastLength) := by
  let lastTokens : List Nat :=
    (tokens.drop (firstTokens.length + 2)).take
      lastLength
  have hLastTokensLength :
      lastTokens.length = lastLength := by
    simp only [lastTokens, List.length_take,
      List.length_drop]
    omega
  have hLastFunction :
      Γ ⊢ₘ[godel_quotation_theory]
        is_function_formula last := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimLeft hLastFinite
  have hLastDomain' :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(last) ≐ₘ
          numₘ(lastTokens.length) := by
    simpa [hLastTokensLength] using hLastDomain
  apply
    gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
      (T := godel_quotation_theory)
      (Γ := Γ)
      (fun _ hAxiom => Or.inl hAxiom)
      (fun _ hFormula =>
        godel_quotation_theory_sentence hFormula)
      last lastTokens hLastFunction hLastDomain'
      (hSource := hLastCheck)
  intro index token hGet
  have hIndex :
      index < lastTokens.length :=
    (List.getElem?_eq_some_iff.mp hGet).1
  have hIndexNumeral :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ
          numₘ(lastTokens.length) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_mem_of_lt
            index lastTokens.length hIndex
  have hIndexLast :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(last) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(index))
        (domₘ(last))
        (numₘ(lastTokens.length))
        (finite_numeral_term_admissible index)
        (domain_term_admissible
          last hLastCheck.admissible)
        (finite_numeral_term_admissible
          lastTokens.length)
        hLastDomain')
      hIndexNumeral
  have hSliceIndex :
      index < lastLength := by
    simpa [hLastTokensLength] using hIndex
  have hDropGet :
      (tokens.drop (firstTokens.length + 2))[index]? =
        some token := by
    rw [List.getElem?_take_of_lt hSliceIndex] at hGet
    simpa [lastTokens] using hGet
  have hTokenGet :
      tokens[firstTokens.length + 2 + index]? =
        some token := by
    simpa using hDropGet
  have hBodyPoint :=
    gq_bracketed_three_part_last_point_at_standard_offset
      first middle last firstTokens middleToken index
      hFirstEquality hMiddleEquality hLastFinite hIndexLast
      (hFirstCheck := hFirstCheck)
      (hMiddleCheck := hMiddleCheck)
      (hLastCheck := hLastCheck)
  have hCodePoint :=
    gq_standard_token_sequence_point_inversion
      (binary_atomic_formula_code_term
        middle first last)
      tokens
      (Metatheory.Derives.equality_symm hEquality)
      hTokenGet
  exact Metatheory.Derives.equality_trans
    (Metatheory.Derives.equality_symm <|
      FirstOrder.Derives.conjElimRight hBodyPoint)
    (FirstOrder.Derives.conjElimRight hCodePoint)

/--
标准输入长度与括号三段构造的两个分量长度不相容时，对象层 numeral 不等式
直接推出矛盾。
-/
theorem gq_bracketed_three_part_standard_falsum_of_length_ne
    {Γ : Context signature}
    (first middle last : SetTerm)
    (tokens : List Nat)
    (middleToken firstLength lastLength : Nat)
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
    (hLength :
      tokens.length ≠ firstLength + lastLength + 3)
    (hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddleCheck :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLastCheck :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  let code : SetTerm :=
    binary_atomic_formula_code_term middle first last
  have hCode :
      Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hCodeDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ numₘ(tokens.length) := by
    simpa [code] using
      gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
        (fun _ hAxiom => hAxiom)
        code tokens
        (Metatheory.Derives.equality_symm hEquality)
        (hCode := hCode)
  have hConstructorDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ
          numₘ(firstLength + lastLength + 3) := by
    simpa [code] using
      gq_bracketed_three_part_domain_eq_lengths
        first middle last
        middleToken firstLength lastLength
        hFirstFinite hMiddleEquality hLastFinite
        hFirstDomain hLastDomain
        (hFirstCheck := hFirstCheck)
        (hMiddleCheck := hMiddleCheck)
        (hLastCheck := hLastCheck)
  have hNumeralEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(tokens.length) ≐ₘ
          numₘ(firstLength + lastLength + 3) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hCodeDomain)
      hConstructorDomain
  have hNotEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        ¬ₘ (numₘ(tokens.length) ≐ₘ
          numₘ(firstLength + lastLength + 3)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_ne hLength
  exact FirstOrder.Derives.negElim
    hNumeralEquality hNotEquality

/--
已知两个分量定义域长度时，任意标准整串同时恢复左右两个规范切片。
总长度错误的分支由对象层矛盾闭合。
-/
theorem gq_bracketed_three_part_parts_eq_standard_slices_of_domains
    {Γ : Context signature}
    (first middle last : SetTerm)
    (tokens : List Nat)
    (middleToken firstLength lastLength : Nat)
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
    (hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddleCheck :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLastCheck :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      (first ≐ₘ
          standard_token_sequence
            ((tokens.drop 1).take firstLength)) ∧ₘ
        (last ≐ₘ
          standard_token_sequence
            ((tokens.drop (firstLength + 2)).take
              lastLength)) := by
  by_cases hLength :
      tokens.length = firstLength + lastLength + 3
  · let firstTokens : List Nat :=
      (tokens.drop 1).take firstLength
    have hFirstTokensLength :
        firstTokens.length = firstLength := by
      simp only [firstTokens, List.length_take,
        List.length_drop]
      omega
    have hFirstLength :
        firstLength < tokens.length := by
      omega
    have hSliceBound :
        firstTokens.length + 2 + lastLength ≤
          tokens.length := by
      omega
    have hFirstEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          first ≐ₘ standard_token_sequence firstTokens := by
      simpa [firstTokens] using
        gq_bracketed_three_part_first_eq_standard_slice_of_domain
          first middle last tokens firstLength
          hFirstLength hFirstFinite
          (gq_finite_sequence_of_eq_standard_token_sequence
            middle [middleToken] hMiddleEquality
            (hCode := hMiddleCheck))
          hLastFinite hFirstDomain hEquality
          (hFirstCheck := hFirstCheck)
          (hMiddleCheck := hMiddleCheck)
          (hLastCheck := hLastCheck)
    have hLastEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          last ≐ₘ
            standard_token_sequence
              ((tokens.drop
                  (firstTokens.length + 2)).take
                lastLength) :=
      gq_bracketed_three_part_last_eq_standard_slice_of_domains
        first middle last tokens firstTokens
        middleToken lastLength hSliceBound
        hFirstEquality hMiddleEquality hLastFinite
        hLastDomain hEquality
        (hFirstCheck := hFirstCheck)
        (hMiddleCheck := hMiddleCheck)
        (hLastCheck := hLastCheck)
    exact FirstOrder.Derives.conjIntro
      (by simpa [firstTokens] using hFirstEquality)
      (by simpa [hFirstTokensLength] using hLastEquality)
  · exact FirstOrder.Derives.falsumElim <|
      gq_bracketed_three_part_standard_falsum_of_length_ne
        first middle last tokens
        middleToken firstLength lastLength
        hFirstFinite hMiddleEquality hLastFinite
        hFirstDomain hLastDomain hEquality hLength
        (hFirstCheck := hFirstCheck)
        (hMiddleCheck := hMiddleCheck)
        (hLastCheck := hLastCheck)

/--
括号三段反演只依赖 GQ 理论；任意包含 GQ 理论的扩张均可直接复用该反演。
调用方只需在目标理论中证明六个对象前提，不需要重复内部序列证明。
-/
theorem gq_bracketed_three_part_parts_eq_standard_slices_of_theory
    {T : Theory signature}
    {Γ : Context signature}
    (hTheory :
      ∀ formula,
        godel_quotation_theory formula →
          T formula)
    (first middle last : SetTerm)
    (tokens : List Nat)
    (middleToken firstLength lastLength : Nat)
    (hFirstFinite :
      Γ ⊢ₘ[T] finite_sequence_condition first)
    (hMiddleEquality :
      Γ ⊢ₘ[T]
        middle ≐ₘ
          standard_token_sequence [middleToken])
    (hLastFinite :
      Γ ⊢ₘ[T] finite_sequence_condition last)
    (hFirstDomain :
      Γ ⊢ₘ[T]
        domₘ(first) ≐ₘ numₘ(firstLength))
    (hLastDomain :
      Γ ⊢ₘ[T]
        domₘ(last) ≐ₘ numₘ(lastLength))
    (hEquality :
      Γ ⊢ₘ[T]
        standard_token_sequence tokens ≐ₘ
          binary_atomic_formula_code_term
            middle first last)
    (hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddleCheck :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLastCheck :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[T]
      (first ≐ₘ
          standard_token_sequence
            ((tokens.drop 1).take firstLength)) ∧ₘ
        (last ≐ₘ
          standard_token_sequence
            ((tokens.drop (firstLength + 2)).take
              lastLength)) := by
  let Δ : Context signature := [
    (finite_sequence_condition first),
    (middle ≐ₘ standard_token_sequence [middleToken]),
    (finite_sequence_condition last),
    (domₘ(first) ≐ₘ numₘ(firstLength)),
    (domₘ(last) ≐ₘ numₘ(lastLength)),
    (standard_token_sequence tokens ≐ₘ
      binary_atomic_formula_code_term middle first last)]
  have hFirstFiniteAt :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition first :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (finite_sequence_condition_admissible
          first hFirstCheck.admissible))
  have hMiddleEqualityAt :
      Δ ⊢ₘ[godel_quotation_theory]
        middle ≐ₘ
          standard_token_sequence [middleToken] :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (Formula.Admissible.equal
          hMiddleCheck.admissible
          (standard_token_sequence_admissible
            [middleToken])))
  have hLastFiniteAt :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition last :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (finite_sequence_condition_admissible
          last hLastCheck.admissible))
  have hFirstDomainAt :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(first) ≐ₘ numₘ(firstLength) :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (Formula.Admissible.equal
          (domain_term_admissible
            first hFirstCheck.admissible)
          (finite_numeral_term_admissible
            firstLength)))
  have hLastDomainAt :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(last) ≐ₘ numₘ(lastLength) :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (Formula.Admissible.equal
          (domain_term_admissible
            last hLastCheck.admissible)
          (finite_numeral_term_admissible
            lastLength)))
  have hEqualityAt :
      Δ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          binary_atomic_formula_code_term
            middle first last :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (Formula.Admissible.equal
          (standard_token_sequence_admissible tokens)
          (binary_atomic_formula_code_term_admissible
            middle first last
            hMiddleCheck.admissible
            hFirstCheck.admissible
            hLastCheck.admissible)))
  have hParts :
      Δ ⊢ₘ[godel_quotation_theory]
        (first ≐ₘ
            standard_token_sequence
              ((tokens.drop 1).take firstLength)) ∧ₘ
          (last ≐ₘ
            standard_token_sequence
              ((tokens.drop (firstLength + 2)).take
                lastLength)) :=
    gq_bracketed_three_part_parts_eq_standard_slices_of_domains
      first middle last tokens
      middleToken firstLength lastLength
      hFirstFiniteAt hMiddleEqualityAt hLastFiniteAt
      hFirstDomainAt hLastDomainAt hEqualityAt
      (hFirstCheck := hFirstCheck)
      (hMiddleCheck := hMiddleCheck)
      (hLastCheck := hLastCheck)
  apply FirstOrder.Derives.multi_cut
    (T := T) (Γ := Γ) (premises := Δ)
  · intro formula hFormula
    simp [Δ] at hFormula
    rcases hFormula with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact hFirstFinite
    · exact hMiddleEquality
    · exact hLastFinite
    · exact hFirstDomain
    · exact hLastDomain
    · exact hEquality
  · exact
      (FirstOrder.Derives.theory_weaken
        hTheory hParts).context_weaken_append

/--
标准输入不等于由两个恢复切片重建出的括号三段串时，对象构造等式推出矛盾。
-/
theorem gq_bracketed_three_part_standard_falsum_of_not_slice_shape
    {Γ : Context signature}
    (first middle last : SetTerm)
    (tokens : List Nat)
    (middleToken firstLength lastLength : Nat)
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
    (hShape :
      tokens ≠
        [Numbered.logical_token .leftParenthesis] ++
          (tokens.drop 1).take firstLength ++
          [middleToken] ++
          (tokens.drop (firstLength + 2)).take
            lastLength ++
          [Numbered.logical_token .rightParenthesis])
    (hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
        prove_term_check)
    (hMiddleCheck :
      Term.CheckCertificate middle SetSort.set := by
        prove_term_check)
    (hLastCheck :
      Term.CheckCertificate last SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  let firstTokens : List Nat :=
    (tokens.drop 1).take firstLength
  let lastTokens : List Nat :=
    (tokens.drop (firstLength + 2)).take
      lastLength
  have hParts :=
    gq_bracketed_three_part_parts_eq_standard_slices_of_domains
      first middle last tokens
      middleToken firstLength lastLength
      hFirstFinite hMiddleEquality hLastFinite
      hFirstDomain hLastDomain hEquality
      (hFirstCheck := hFirstCheck)
      (hMiddleCheck := hMiddleCheck)
      (hLastCheck := hLastCheck)
  have hConstructorStandard :
      Γ ⊢ₘ[godel_quotation_theory]
        binary_atomic_formula_code_term middle first last ≐ₘ
          standard_token_sequence
            ([Numbered.logical_token .leftParenthesis] ++
              firstTokens ++ [middleToken] ++
                lastTokens ++
                  [Numbered.logical_token
                    .rightParenthesis]) :=
    gq_bracketed_three_part_eq_standard_token_sequence_of_context
      firstTokens [middleToken] lastTokens
      first middle last
      (FirstOrder.Derives.conjElimLeft hParts)
      hMiddleEquality
      (FirstOrder.Derives.conjElimRight hParts)
      (hFirstCheck := hFirstCheck)
      (hMiddleCheck := hMiddleCheck)
      (hLastCheck := hLastCheck)
  have hStandardEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          standard_token_sequence
            ([Numbered.logical_token .leftParenthesis] ++
              firstTokens ++ [middleToken] ++
                lastTokens ++
                  [Numbered.logical_token
                    .rightParenthesis]) :=
    Metatheory.Derives.equality_trans
      hEquality hConstructorStandard
  have hNotEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        ¬ₘ (standard_token_sequence tokens ≐ₘ
          standard_token_sequence
            ([Numbered.logical_token .leftParenthesis] ++
              firstTokens ++ [middleToken] ++
                lastTokens ++
                  [Numbered.logical_token
                    .rightParenthesis])) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_token_sequence_ne <| by
            simpa [firstTokens, lastTokens] using hShape
  exact FirstOrder.Derives.negElim
    hStandardEquality hNotEquality

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
