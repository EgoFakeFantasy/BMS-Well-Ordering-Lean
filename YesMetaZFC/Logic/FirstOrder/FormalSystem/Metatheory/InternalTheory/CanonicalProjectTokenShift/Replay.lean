import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalProjectTokenShift.Core
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.CanonicalBinderShift.Sequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemTokenDecoder
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTraceLegality.CodeTransport

/-!
# 二元 cutoff-shift 的正向回放

本模块只做两次编译：

1. 把已有 `CanonicalProjectFormulaShift` 翻译为 quotation token 的逐点关系；
2. 把逐点关系回放为对象层二元代码条件。

不构造或消费任何公式 shift trace。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-! ## 公式 shift 到 token shift -/

/--
同一公式级 cutoff-shift 的两份规范 quotation 逐 token 对应。

`cutoff ≤ entryDepth` 只用于当前层全称 binder；原子变量仍由各自的真实深度决定
保持不变或后移。
-/
theorem CanonicalProjectFormulaShift.quote_hilbert_tokens_relation
    {cutoff entryDepth : Nat}
    {sourceFormula targetFormula : SetFormula}
    (shift :
      CanonicalProjectFormulaShift cutoff entryDepth
        sourceFormula targetFormula)
    (hCutoff : cutoff ≤ entryDepth)
    {sourceTokens targetTokens : List Nat}
    (hSource :
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names entryDepth)
          entryDepth sourceFormula =
        some sourceTokens)
    (hTarget :
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names (entryDepth + 1))
          (entryDepth + 1) targetFormula =
        some targetTokens) :
    CanonicalProjectShiftTokens cutoff
      sourceTokens targetTokens := by
  induction shift generalizing sourceTokens targetTokens with
  | equality hSourceLeft hSourceRight
      hTargetLeft hTargetRight =>
      have hSourceLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceLeft
      have hSourceRightTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceRight
      have hTargetLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetLeft
      have hTargetRightTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetRight
      simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
        hSourceLeftTokens, hSourceRightTokens,
        hTargetLeftTokens, hTargetRightTokens] at hSource hTarget
      subst sourceTokens
      subst targetTokens
      exact CanonicalProjectShiftTokens.equality
        (CanonicalProjectShiftTokens.singleton
          (.bound _))
        (CanonicalProjectShiftTokens.singleton
          (.bound _))
  | membership hSourceLeft hSourceRight
      hTargetLeft hTargetRight =>
      have hSourceLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceLeft
      have hSourceRightTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceRight
      have hTargetLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetLeft
      have hTargetRightTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetRight
      simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
        GodelQuotation.Numbered.quote_relation_tokens_with?,
        hSourceLeftTokens, hSourceRightTokens,
        hTargetLeftTokens, hTargetRightTokens] at hSource hTarget
      subst sourceTokens
      subst targetTokens
      exact CanonicalProjectShiftTokens.membership
        (CanonicalProjectShiftTokens.singleton
          (.bound _))
        (CanonicalProjectShiftTokens.singleton
          (.bound _))
  | subset hSourceLeft hSourceRight
      hTargetLeft hTargetRight =>
      have hSourceLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceLeft
      have hSourceRightTokens :=
        canonical_project_variable_depth?_quote_tokens hSourceRight
      have hTargetLeftTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetLeft
      have hTargetRightTokens :=
        canonical_project_variable_depth?_quote_tokens hTargetRight
      simp [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
        GodelQuotation.Numbered.quote_relation_tokens_with?,
        hSourceLeftTokens, hSourceRightTokens,
        hTargetLeftTokens, hTargetRightTokens,
        GodelQuotation.fs_relation_kind_eq_predicate
          (relation := RelationSymbol.subset) (by decide)]
        at hSource hTarget
      subst sourceTokens
      subst targetTokens
      exact CanonicalProjectShiftTokens.subset
        (CanonicalProjectShiftTokens.singleton
          (.bound _))
        (CanonicalProjectShiftTokens.singleton
          (.bound _))
  | @negation entryDepth sourceBody targetBody body ih =>
      simp only [
        GodelQuotation.Numbered.quote_hilbert_tokens_with?]
        at hSource hTarget
      cases hSourceBody :
          GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name
            GodelQuotation.bound_name
            (GodelQuotation.canonical_bound_names entryDepth)
            entryDepth sourceBody with
      | none =>
          simp [hSourceBody] at hSource
      | some sourceBodyTokens =>
          cases hTargetBody :
              GodelQuotation.Numbered.quote_hilbert_tokens_with?
                GodelQuotation.free_name
                GodelQuotation.bound_name
                (GodelQuotation.canonical_bound_names
                  (entryDepth + 1))
                (entryDepth + 1) targetBody with
          | none =>
              simp [hTargetBody] at hTarget
          | some targetBodyTokens =>
              simp [hSourceBody] at hSource
              simp [hTargetBody] at hTarget
              subst sourceTokens
              subst targetTokens
              exact CanonicalProjectShiftTokens.negation
                (ih hCutoff hSourceBody hTargetBody)
  | @implication entryDepth sourceLeft sourceRight
      targetLeft targetRight left right ihLeft ihRight =>
      simp only [
        GodelQuotation.Numbered.quote_hilbert_tokens_with?]
        at hSource hTarget
      cases hSourceLeft :
          GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name
            GodelQuotation.bound_name
            (GodelQuotation.canonical_bound_names entryDepth)
            entryDepth sourceLeft with
      | none =>
          simp [hSourceLeft] at hSource
      | some sourceLeftTokens =>
          cases hSourceRight :
              GodelQuotation.Numbered.quote_hilbert_tokens_with?
                GodelQuotation.free_name
                GodelQuotation.bound_name
                (GodelQuotation.canonical_bound_names entryDepth)
                entryDepth sourceRight with
          | none =>
              simp [hSourceLeft, hSourceRight] at hSource
          | some sourceRightTokens =>
              cases hTargetLeft :
                  GodelQuotation.Numbered.quote_hilbert_tokens_with?
                    GodelQuotation.free_name
                    GodelQuotation.bound_name
                    (GodelQuotation.canonical_bound_names
                      (entryDepth + 1))
                    (entryDepth + 1) targetLeft with
              | none =>
                  simp [hTargetLeft] at hTarget
              | some targetLeftTokens =>
                  cases hTargetRight :
                      GodelQuotation.Numbered.quote_hilbert_tokens_with?
                        GodelQuotation.free_name
                        GodelQuotation.bound_name
                        (GodelQuotation.canonical_bound_names
                          (entryDepth + 1))
                        (entryDepth + 1) targetRight with
                  | none =>
                      simp [hTargetLeft, hTargetRight] at hTarget
                  | some targetRightTokens =>
                      simp [hSourceLeft, hSourceRight] at hSource
                      simp [hTargetLeft, hTargetRight] at hTarget
                      subst sourceTokens
                      subst targetTokens
                      exact CanonicalProjectShiftTokens.implication
                        (ihLeft hCutoff hSourceLeft hTargetLeft)
                        (ihRight hCutoff hSourceRight hTargetRight)
  | @universal entryDepth sourceBody targetBody body ih =>
      simp only [
        GodelQuotation.Numbered.quote_hilbert_tokens_with?]
        at hSource hTarget
      cases hSourceBody :
          GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name
            GodelQuotation.bound_name
            (GodelQuotation.bound_name entryDepth ::
              GodelQuotation.canonical_bound_names entryDepth)
            (entryDepth + 1) sourceBody with
      | none =>
          simp [hSourceBody] at hSource
      | some sourceBodyTokens =>
          cases hTargetBody :
              GodelQuotation.Numbered.quote_hilbert_tokens_with?
                GodelQuotation.free_name
                GodelQuotation.bound_name
                (GodelQuotation.bound_name (entryDepth + 1) ::
                  GodelQuotation.canonical_bound_names
                    (entryDepth + 1))
                (entryDepth + 2) targetBody with
          | none =>
              simp [hTargetBody] at hTarget
          | some targetBodyTokens =>
              simp [hSourceBody] at hSource
              simp [hTargetBody] at hTarget
              subst sourceTokens
              subst targetTokens
              exact CanonicalProjectShiftTokens.universal
                entryDepth hCutoff <| by
                  simpa [GodelQuotation.canonical_bound_names,
                    Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using
                    ih (Nat.le.step hCutoff)
                      hSourceBody hTargetBody

/-! ## 单 token 的对象回放 -/

/-- 规范 bound token 的外部数值等于对象层 `2d+1` 变量符号项。 -/
theorem canonical_project_bound_token_value
    (depth : Nat) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      numₘ(GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name depth)) ≐ₘ
        variable_symbol_number_term
          (Sₘ(numₘ(2) *ₘ numₘ(depth))) := by
  let indexProduct : SetTerm :=
    numₘ(2) *ₘ numₘ(depth)
  let sourceIndex := Nat.succ (2 * depth)
  have hIndexProduct :
      Term.Admissible indexProduct SetSort.set :=
    natural_multiplication_term_admissible
      (numₘ(2)) (numₘ(depth))
      (finite_numeral_term_admissible 2)
      (finite_numeral_term_admissible depth)
  have hProductValue :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(2 * depth) ≐ₘ indexProduct := by
    simpa [indexProduct] using
      (GodelQuotation.gq_weaken_standard_sequence <|
        GodelQuotation.standard_token_sequence_finite_numeral_multiplication
          2 depth)
  have hIndexValueRaw :=
    successor_term_congr_of_equality
      (numₘ(2 * depth)) indexProduct
      (finite_numeral_term_admissible (2 * depth))
      hIndexProduct hProductValue
  have hIndexValue :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(sourceIndex) ≐ₘ Sₘ(indexProduct) := by
    simpa [sourceIndex, finite_numeral_term] using
      hIndexValueRaw
  have hName :
      GodelQuotation.bound_name depth = sourceIndex := by
    simp [GodelQuotation.bound_name, sourceIndex]
  rw [hName]
  simpa [GodelQuotation.Numbered.variable_token,
    variable_symbol_number_term, indexProduct] using
    GodelQuotation.gq_binder_shift_indexed_prime_power_value
      3 sourceIndex (Sₘ(indexProduct))
      (successor_term_admissible indexProduct hIndexProduct)
      hIndexValue

/-- 外部单 token cutoff-shift 满足对象层二元条件。 -/
theorem canonical_project_shift_token_condition_with_ids_of_relation
    {cutoff sourceToken targetToken : Nat}
    (relation :
      CanonicalProjectShiftToken cutoff
        sourceToken targetToken)
    (freshBase : FreeVarId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_shift_token_condition_with_ids
        (numₘ(cutoff))
        (numₘ(sourceToken))
        (numₘ(targetToken))
        freshBase (freshBase + 1) := by
  have hConditionCheck :=
    canonical_project_shift_token_condition_with_ids_check
      (numₘ(cutoff))
      (numₘ(sourceToken))
      (numₘ(targetToken))
      freshBase (freshBase + 1)
      (finite_numeral_term_check cutoff)
      (finite_numeral_term_check sourceToken)
      (finite_numeral_term_check targetToken)
  rw [canonical_project_shift_token_condition_with_ids]
    at hConditionCheck
  rcases Formula.CheckCertificate.disj_iff.mp hConditionCheck with
    ⟨hFixedCaseCheck, hVariableCaseCheck⟩
  have hFixedConditionCheck :
      Formula.CheckCertificate
        (canonical_project_shift_fixed_token_condition
          (numₘ(sourceToken))) :=
    Formula.check_certificate_of_admissible
      (canonical_project_shift_fixed_token_condition_admissible
        (numₘ(sourceToken))
        (finite_numeral_term_admissible sourceToken))
  rw [canonical_project_shift_fixed_token_condition]
    at hFixedConditionCheck
  rcases Formula.CheckCertificate.disj_iff.mp
      hFixedConditionCheck with
    ⟨hBinderFixedCheck, hSubsetCheck⟩
  cases relation with
  | logical symbol =>
      have hFixed :
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            canonical_project_shift_fixed_token_condition
              (numₘ(GodelQuotation.Numbered.logical_token symbol)) := by
        rw [canonical_project_shift_fixed_token_condition]
        exact FirstOrder.Derives.disjIntroLeft
          (hRightCheck := hSubsetCheck)
          (GodelQuotation.gq_binder_shift_fixed_logical_condition
            symbol)
      exact FirstOrder.Derives.disjIntroLeft
        (hRightCheck := hVariableCaseCheck) <|
          FirstOrder.Derives.conjIntro hFixed
            (FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set)
              (numₘ(GodelQuotation.Numbered.logical_token symbol))
              (hTermCheck :=
                finite_numeral_term_check
                  (GodelQuotation.Numbered.logical_token symbol)))
  | membership =>
      have hFixed :
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            canonical_project_shift_fixed_token_condition
              (numₘ(GodelQuotation.Numbered.membership_token)) := by
        rw [canonical_project_shift_fixed_token_condition]
        exact FirstOrder.Derives.disjIntroLeft
          (hRightCheck := hSubsetCheck)
          GodelQuotation.gq_binder_shift_fixed_membership_condition
      exact FirstOrder.Derives.disjIntroLeft
        (hRightCheck := hVariableCaseCheck) <|
          FirstOrder.Derives.conjIntro hFixed
            (FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set)
              (numₘ(GodelQuotation.Numbered.membership_token))
              (hTermCheck :=
                finite_numeral_term_check
                  GodelQuotation.Numbered.membership_token))
  | subset =>
      have hValue :
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            numₘ(GodelQuotation.Numbered.predicate_token
                1 RelationSymbol.subset.ctorIdx) ≐ₘ
              coded_predicate_symbol_number_term
                (numₘ(1))
                (numₘ(RelationSymbol.subset.ctorIdx)) := by
        simpa [GodelQuotation.Numbered.predicate_token,
          coded_predicate_symbol_number_term] using
          GodelQuotation.gq_binder_shift_binary_symbol_value
            7 1 RelationSymbol.subset.ctorIdx
      have hFixed :
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            canonical_project_shift_fixed_token_condition
              (numₘ(GodelQuotation.Numbered.predicate_token
                1 RelationSymbol.subset.ctorIdx)) := by
        rw [canonical_project_shift_fixed_token_condition]
        exact FirstOrder.Derives.disjIntroRight
          (hLeftCheck := hBinderFixedCheck) hValue
      exact FirstOrder.Derives.disjIntroLeft
        (hRightCheck := hVariableCaseCheck) <|
          FirstOrder.Derives.conjIntro hFixed
            (FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set)
              (numₘ(GodelQuotation.Numbered.predicate_token
                1 RelationSymbol.subset.ctorIdx))
              (hTermCheck :=
                finite_numeral_term_check
                  (GodelQuotation.Numbered.predicate_token
                    1 RelationSymbol.subset.ctorIdx)))
  | bound depth =>
      let targetDepth :=
        canonical_project_shift_depth cutoff depth
      have hBase :
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            (((numₘ(depth) ∈ₘ
                  Sₘ(numₘ(GodelQuotation.Numbered.variable_token
                    (GodelQuotation.bound_name depth)))) ∧ₘ
                (numₘ(GodelQuotation.Numbered.variable_token
                    (GodelQuotation.bound_name depth)) ≐ₘ
                  variable_symbol_number_term
                    (Sₘ(numₘ(2) *ₘ numₘ(depth))))) ∧ₘ
              (canonical_shifted_depth_condition
                  (numₘ(cutoff))
                  (numₘ(depth))
                  (numₘ(targetDepth)) ∧ₘ
                (numₘ(GodelQuotation.Numbered.variable_token
                    (GodelQuotation.bound_name targetDepth)) ≐ₘ
                  variable_symbol_number_term
                    (Sₘ(numₘ(2) *ₘ numₘ(targetDepth)))))) :=
        FirstOrder.Derives.conjIntro
          (FirstOrder.Derives.conjIntro
            (GodelQuotation.gq_weaken_standard_sequence <| by
              have hDepthName :
                  depth <
                    GodelQuotation.bound_name depth := by
                simp [GodelQuotation.bound_name]
                omega
              have hDepthToken :
                  depth <
                    GodelQuotation.Numbered.variable_token
                        (GodelQuotation.bound_name depth) + 1 :=
                Nat.lt_trans hDepthName
                  (GodelQuotation.fs_name_lt_variable_token_succ
                    (GodelQuotation.bound_name depth))
              simpa [finite_numeral_term] using
                GodelQuotation.standard_sequence_finite_numeral_mem_of_lt
                  depth
                  (GodelQuotation.Numbered.variable_token
                    (GodelQuotation.bound_name depth) + 1)
                  hDepthToken)
            (canonical_project_bound_token_value depth))
          (FirstOrder.Derives.conjIntro
            (by
              simpa [targetDepth] using
                canonical_shifted_depth_condition_numeral_derives
                  cutoff depth)
            (canonical_project_bound_token_value targetDepth))
      exact FirstOrder.Derives.disjIntroRight
        (hLeftCheck := hFixedCaseCheck) <| by
          nd_apply FirstOrder.Derives.exists_intro
            (sort := SetSort.set)
            (term := numₘ(depth))
          apply FirstOrder.Derives.conjIntro
          · simpa [
              Formula.openAt_closeFreeAt_eq_substituteFree,
              canonical_shifted_depth_condition,
              Formula.openAt, Formula.closeFreeAt,
              Formula.next_depth, Formula.substituteFree,
              Term.openAt, Term.closeFreeAt,
              Term.substituteFree, set_variable,
              set_bound_variable, targetDepth,
              GodelQuotation.gq_binder_shift_numeral_open,
              GodelQuotation.gq_binder_shift_numeral_close,
              GodelQuotation.gq_binder_shift_numeral_substitute] using
              FirstOrder.Derives.conjElimLeft
                (FirstOrder.Derives.conjElimLeft hBase)
          · nd_apply FirstOrder.Derives.exists_intro
              (sort := SetSort.set)
              (term := numₘ(targetDepth))
            apply FirstOrder.Derives.conjIntro
            · simpa [
                Formula.openAt_closeFreeAt_eq_substituteFree,
                Formula.openAt, Formula.closeFreeAt,
                Formula.next_depth,
                Formula.substituteFree, Term.openAt,
                Term.closeFreeAt, Term.substituteFree,
                targetDepth] using
                GodelQuotation.gq_weaken_standard_sequence
                  (GodelQuotation.standard_sequence_finite_numeral_mem_omega
                    targetDepth)
            · apply FirstOrder.Derives.conjIntro
              · simpa [
                  Formula.openAt_closeFreeAt_eq_substituteFree,
                  Formula.openAt, Formula.closeFreeAt,
                  Formula.next_depth, Formula.substituteFree,
                  Term.openAt, Term.closeFreeAt,
                  Term.substituteFree, set_variable,
                  set_bound_variable, targetDepth,
                  GodelQuotation.gq_binder_shift_numeral_open,
                  GodelQuotation.gq_binder_shift_numeral_close,
                  GodelQuotation.gq_binder_shift_numeral_substitute] using
                  FirstOrder.Derives.conjElimRight
                    (FirstOrder.Derives.conjElimLeft hBase)
              · simpa [
                  Formula.openAt_closeFreeAt_eq_substituteFree,
                  canonical_shifted_depth_condition,
                  Formula.openAt, Formula.closeFreeAt,
                  Formula.next_depth, Formula.substituteFree,
                  Term.openAt, Term.closeFreeAt,
                  Term.substituteFree, set_variable,
                  set_bound_variable, targetDepth,
                  GodelQuotation.gq_binder_shift_numeral_open,
                  GodelQuotation.gq_binder_shift_numeral_close,
                  GodelQuotation.gq_binder_shift_numeral_substitute] using
                  FirstOrder.Derives.conjElimRight hBase

/--
把标准 numeral 上的单 token 关系运输到任意两个已对齐的对象值。

两个内部深度见证占用 `freshBase` 与 `freshBase + 1`；运输孔使用后续两个编号。
-/
theorem canonical_project_shift_token_condition_with_ids_of_values
    {cutoff sourceToken targetToken : Nat}
    {Γ : Context signature}
    (relation :
      CanonicalProjectShiftToken cutoff
        sourceToken targetToken)
    (freshBase : FreeVarId)
    (sourceValue targetValue : SetTerm)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceFreshFrom :
      ∀ id, freshBase ≤ id →
        (SetSort.set, id) ∉ Term.freeSupport sourceValue)
    (hTargetFreshFrom :
      ∀ id, freshBase ≤ id →
        (SetSort.set, id) ∉ Term.freeSupport targetValue)
    (hSourceEquality :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hTargetEquality :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        targetValue ≐ₘ numₘ(targetToken)) :
    Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_shift_token_condition_with_ids
        (numₘ(cutoff)) sourceValue targetValue
        freshBase (freshBase + 1) := by
  let sourceParameter := freshBase + 2
  let targetParameter := freshBase + 3
  let numeralTarget := numₘ(targetToken)
  have hSourceHoleFresh :
      (SetSort.set, sourceParameter) ∉
        Term.freeSupport sourceValue :=
    hSourceFreshFrom sourceParameter (by
      simp [sourceParameter])
  have hTargetHoleFresh :
      (SetSort.set, targetParameter) ∉
        Term.freeSupport sourceValue :=
    hSourceFreshFrom targetParameter (by
      simp [targetParameter])
  have hFreshBaseLeAdd (offset : Nat) :
      freshBase ≤ freshBase + offset :=
    Nat.le_add_right freshBase offset
  have hSourceFixedByTarget :
      Term.substituteFree SetSort.set targetParameter
          targetValue sourceValue =
        sourceValue :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set targetParameter targetValue
      sourceValue hTargetHoleFresh
  have hSourceFixedByTargetNumeral :
      Term.substituteFree SetSort.set targetParameter
          (numₘ(targetToken)) sourceValue =
        sourceValue :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set targetParameter (numₘ(targetToken))
      sourceValue hTargetHoleFresh
  have hSourceCloseCommute
      (closedId : FreeVarId) (depth : Nat)
      (formula : SetFormula)
      (hLower : freshBase ≤ closedId)
      (hDistinct : sourceParameter ≠ closedId) :
      Formula.substituteFree SetSort.set sourceParameter
          sourceValue
          (Formula.closeFreeAt SetSort.set
            closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set
            sourceParameter sourceValue formula) := by
    exact (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceParameter closedId depth
      sourceValue formula hDistinct hSourceValue.2
      (hSourceFreshFrom closedId hLower)).symm
  have hTargetCloseCommute
      (closedId : FreeVarId) (depth : Nat)
      (formula : SetFormula)
      (hLower : freshBase ≤ closedId)
      (hDistinct : targetParameter ≠ closedId) :
      Formula.substituteFree SetSort.set targetParameter
          targetValue
          (Formula.closeFreeAt SetSort.set
            closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set
            targetParameter targetValue formula) := by
    exact (Formula.closeFreeAt_substituteFree_comm
      SetSort.set targetParameter closedId depth
      targetValue formula hDistinct hTargetValue.2
      (hTargetFreshFrom closedId hLower)).symm
  have hNumeralCloseCommute
      (parameter closedId : FreeVarId)
      (depth value : Nat) (formula : SetFormula)
      (hDistinct : parameter ≠ closedId) :
      Formula.substituteFree SetSort.set parameter
          (numₘ(value))
          (Formula.closeFreeAt SetSort.set
            closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set parameter
            (numₘ(value)) formula) := by
    exact (Formula.closeFreeAt_substituteFree_comm
      SetSort.set parameter closedId depth
      (numₘ(value)) formula hDistinct
      (finite_numeral_term_admissible value).2
      (by simp [finite_numeral_term_freeSupport])).symm
  let sourceBody : SetFormula :=
    canonical_project_shift_token_condition_with_ids
      (numₘ(cutoff)) (x#sourceParameter) numeralTarget
      freshBase (freshBase + 1)
  have hNumeralCondition :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_shift_token_condition_with_ids
          (numₘ(cutoff))
          (numₘ(sourceToken))
          (numₘ(targetToken))
          freshBase (freshBase + 1) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      (canonical_project_shift_token_condition_with_ids_of_relation
        relation freshBase)
  have hSourceIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := GodelQuotation.godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := sourceParameter)
      (left := sourceValue)
      (right := numₘ(sourceToken))
      (body := sourceBody)
      hSourceEquality
  have hSourceIff :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_shift_token_condition_with_ids
            (numₘ(cutoff)) sourceValue numeralTarget
            freshBase (freshBase + 1) ↔ₘ
          canonical_project_shift_token_condition_with_ids
            (numₘ(cutoff))
            (numₘ(sourceToken)) numeralTarget
            freshBase (freshBase + 1) := by
    simpa [sourceBody, sourceParameter, numeralTarget,
      canonical_project_shift_token_condition_with_ids,
      canonical_project_shift_fixed_token_condition,
      canonical_shifted_depth_condition,
      Formula.substituteFree, Term.substituteFree,
      set_variable, hSourceHoleFresh,
      hSourceCloseCommute, hFreshBaseLeAdd,
      hNumeralCloseCommute,
      GodelQuotation.gq_binder_shift_numeral_substitute] using
      hSourceIffRaw
  have hAtSource :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_shift_token_condition_with_ids
          (numₘ(cutoff)) sourceValue numeralTarget
          freshBase (freshBase + 1) :=
    FirstOrder.Derives.iffElimLeft hSourceIff <| by
      simpa [numeralTarget] using hNumeralCondition
  let targetBody : SetFormula :=
    canonical_project_shift_token_condition_with_ids
      (numₘ(cutoff)) sourceValue (x#targetParameter)
      freshBase (freshBase + 1)
  have hTargetIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := GodelQuotation.godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := targetParameter)
      (left := targetValue)
      (right := numₘ(targetToken))
      (body := targetBody)
      hTargetEquality
  have hTargetIff :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_shift_token_condition_with_ids
            (numₘ(cutoff)) sourceValue targetValue
            freshBase (freshBase + 1) ↔ₘ
          canonical_project_shift_token_condition_with_ids
            (numₘ(cutoff)) sourceValue numeralTarget
            freshBase (freshBase + 1) := by
    simpa [targetBody, targetParameter, numeralTarget,
      canonical_project_shift_token_condition_with_ids,
      canonical_project_shift_fixed_token_condition,
      canonical_shifted_depth_condition,
      Formula.substituteFree, Term.substituteFree,
      set_variable, hTargetHoleFresh,
      hSourceFixedByTarget, hSourceFixedByTargetNumeral,
      hTargetCloseCommute, hFreshBaseLeAdd,
      hNumeralCloseCommute,
      GodelQuotation.gq_binder_shift_numeral_substitute] using
      hTargetIffRaw
  exact FirstOrder.Derives.iffElimLeft
    hTargetIff hAtSource

/-! ## 标准序列与完整代码关系 -/

/-- 一个具体下标等式分支上的逐 token 回放。 -/
private theorem canonical_project_shift_at_index_equality
    {cutoff : Nat}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalProjectShiftTokens cutoff
        sourceTokens targetTokens)
    (indexId : FreeVarId)
    (index : Nat)
    (hIndex : index < sourceTokens.length) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      ((x#indexId) ≐ₘ numₘ(index)) ⟶ₘ
        canonical_project_shift_token_condition_with_ids
          (numₘ(cutoff))
          (GodelQuotation.standard_token_sequence sourceTokens ·ₘ
            x#indexId)
          (GodelQuotation.standard_token_sequence targetTokens ·ₘ
            x#indexId)
          (indexId + 1) (indexId + 2) := by
  let sourceSequence :=
    GodelQuotation.standard_token_sequence sourceTokens
  let targetSequence :=
    GodelQuotation.standard_token_sequence targetTokens
  let point : SetTerm := x#indexId
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  let sourceToken := sourceTokens[index]
  have hSourceGet :
      sourceTokens[index]? = some sourceToken := by
    simp [sourceToken, List.getElem?_eq_getElem hIndex]
  rcases relation.getElem?_relation hSourceGet with
    ⟨targetToken, hTargetGet, tokenRelation⟩
  have hSource :
      Term.Admissible sourceSequence SetSort.set :=
    GodelQuotation.standard_token_sequence_admissible sourceTokens
  have hTarget :
      Term.Admissible targetSequence SetSort.set :=
    GodelQuotation.standard_token_sequence_admissible targetTokens
  have hPoint :
      Term.Admissible point SetSort.set := by
    simpa [point] using set_variable_admissible indexId
  have hNumeral :
      Term.Admissible (numₘ(index)) SetSort.set :=
    finite_numeral_term_admissible index
  have hSourcePoint :
      Term.Admissible
        (sourceSequence ·ₘ point) SetSort.set :=
    function_application_term_admissible
      sourceSequence point hSource hPoint
  have hTargetPoint :
      Term.Admissible
        (targetSequence ·ₘ point) SetSort.set :=
    function_application_term_admissible
      targetSequence point hTarget hPoint
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        point ≐ₘ numₘ(index) := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := GodelQuotation.godel_quotation_theory)
        (Γ := Γ) (φ := equality)
        (by simp [Γ]))
  have hSourceArgument :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        (sourceSequence ·ₘ point) ≐ₘ
          (sourceSequence ·ₘ numₘ(index)) :=
    function_application_term_congr_argument_of_equality
      sourceSequence point (numₘ(index))
      hSource hPoint hNumeral hEquality
  have hTargetArgument :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        (targetSequence ·ₘ point) ≐ₘ
          (targetSequence ·ₘ numₘ(index)) :=
    function_application_term_congr_argument_of_equality
      targetSequence point (numₘ(index))
      hTarget hPoint hNumeral hEquality
  have hSourceAtNumeral :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        (sourceSequence ·ₘ numₘ(index)) ≐ₘ
          numₘ(sourceToken) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
        simpa [sourceSequence] using
          GodelQuotation.gq_weaken_standard_sequence
            (GodelQuotation.standard_token_sequence_apply_getElem?
              sourceTokens hSourceGet)
  have hTargetAtNumeral :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        (targetSequence ·ₘ numₘ(index)) ≐ₘ
          numₘ(targetToken) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
        simpa [targetSequence] using
          GodelQuotation.gq_weaken_standard_sequence
            (GodelQuotation.standard_token_sequence_apply_getElem?
              targetTokens hTargetGet)
  have hSourceEquality :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        (sourceSequence ·ₘ point) ≐ₘ
          numₘ(sourceToken) :=
    Metatheory.Derives.equality_trans
      hSourceArgument hSourceAtNumeral
  have hTargetEquality :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        (targetSequence ·ₘ point) ≐ₘ
          numₘ(targetToken) :=
    Metatheory.Derives.equality_trans
      hTargetArgument hTargetAtNumeral
  have hSourcePointSupport :
      Term.freeSupport (sourceSequence ·ₘ point) =
        [(SetSort.set, indexId)] := by
    simp [sourceSequence, point,
      Term.freeSupport, Term.freeSupportList,
      GodelQuotation.standard_token_sequence_freeSupport_nil] <;>
      rfl
  have hTargetPointSupport :
      Term.freeSupport (targetSequence ·ₘ point) =
        [(SetSort.set, indexId)] := by
    simp [targetSequence, point,
      Term.freeSupport, Term.freeSupportList,
      GodelQuotation.standard_token_sequence_freeSupport_nil] <;>
      rfl
  have hSourceFreshFrom :
      ∀ id, indexId + 1 ≤ id →
        (SetSort.set, id) ∉
          Term.freeSupport (sourceSequence ·ₘ point) := by
    intro id hLower hMember
    rw [hSourcePointSupport] at hMember
    have hId : id = indexId :=
      congrArg Prod.snd (List.mem_singleton.mp hMember)
    have hStrict : indexId < id :=
      Nat.lt_of_succ_le hLower
    rw [hId] at hStrict
    exact (Nat.lt_irrefl indexId) hStrict
  have hTargetFreshFrom :
      ∀ id, indexId + 1 ≤ id →
        (SetSort.set, id) ∉
          Term.freeSupport (targetSequence ·ₘ point) := by
    intro id hLower hMember
    rw [hTargetPointSupport] at hMember
    have hId : id = indexId :=
      congrArg Prod.snd (List.mem_singleton.mp hMember)
    have hStrict : indexId < id :=
      Nat.lt_of_succ_le hLower
    rw [hId] at hStrict
    exact (Nat.lt_irrefl indexId) hStrict
  have hCondition :=
    canonical_project_shift_token_condition_with_ids_of_values
      tokenRelation (indexId + 1)
      (sourceSequence ·ₘ point)
      (targetSequence ·ₘ point)
      hSourcePoint hTargetPoint
      hSourceFreshFrom hTargetFreshFrom
      hSourceEquality hTargetEquality
  simpa [Γ, equality, sourceSequence,
    targetSequence, point, Nat.add_assoc] using
    hCondition

/-- 同步 token 串在标准定义域的每个位置满足对象层二元关系。 -/
theorem canonical_project_shift_standard_sequences_pointwise
    {cutoff : Nat}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalProjectShiftTokens cutoff
        sourceTokens targetTokens)
    (indexId : FreeVarId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      ∀ₘ[SetSort.set, indexId],
        (x#indexId ∈ₘ
          domₘ(GodelQuotation.standard_token_sequence sourceTokens)) ⟶ₘ
        canonical_project_shift_token_condition_with_ids
          (numₘ(cutoff))
          (GodelQuotation.standard_token_sequence sourceTokens ·ₘ
            x#indexId)
          (GodelQuotation.standard_token_sequence targetTokens ·ₘ
            x#indexId)
          (indexId + 1) (indexId + 2) := by
  let sourceSequence :=
    GodelQuotation.standard_token_sequence sourceTokens
  let targetSequence :=
    GodelQuotation.standard_token_sequence targetTokens
  let point : SetTerm := x#indexId
  let conclusion : SetFormula :=
    canonical_project_shift_token_condition_with_ids
      (numₘ(cutoff))
      (sourceSequence ·ₘ point)
      (targetSequence ·ₘ point)
      (indexId + 1) (indexId + 2)
  have hPoint :
      Term.Admissible point SetSort.set := by
    simpa [point] using set_variable_admissible indexId
  have hSource :
      Term.Admissible sourceSequence SetSort.set :=
    GodelQuotation.standard_token_sequence_admissible sourceTokens
  have hTarget :
      Term.Admissible targetSequence SetSort.set :=
    GodelQuotation.standard_token_sequence_admissible targetTokens
  have hConclusion :
      Formula.Admissible conclusion := by
    simpa [conclusion] using
      canonical_project_shift_token_condition_with_ids_admissible
        (numₘ(cutoff))
        (sourceSequence ·ₘ point)
        (targetSequence ·ₘ point)
        (indexId + 1) (indexId + 2)
        (finite_numeral_term_admissible cutoff)
        (function_application_term_admissible
          sourceSequence point hSource hPoint)
        (function_application_term_admissible
          targetSequence point hTarget hPoint)
  have hCases :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        GodelQuotation.stdseq_numeral_member_condition
            sourceTokens.length point ⟶ₘ
          conclusion :=
    GodelQuotation.stdseq_numeral_member_condition_elim_of_theory
      sourceTokens.length point conclusion
      (fun index hIndex => by
        simpa [conclusion, sourceSequence,
          targetSequence, point] using
          canonical_project_shift_at_index_equality
            relation indexId index hIndex)
  have hDomain :
      Term.Admissible (domₘ(sourceSequence)) SetSort.set :=
    domain_term_admissible sourceSequence hSource
  have hDomainEq :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        domₘ(sourceSequence) ≐ₘ
          numₘ(sourceTokens.length) := by
    simpa [sourceSequence] using
      GodelQuotation.gq_weaken_standard_sequence
        (GodelQuotation.standard_token_sequence_domain_eq_length
          sourceTokens)
  have hDomainIff :=
    membership_right_iff_of_equality
      point (domₘ(sourceSequence))
      (numₘ(sourceTokens.length))
      hPoint hDomain
      (finite_numeral_term_admissible sourceTokens.length)
      hDomainEq
  have hNumeralIff :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        (point ∈ₘ numₘ(sourceTokens.length)) ↔ₘ
          GodelQuotation.stdseq_numeral_member_condition
            sourceTokens.length point :=
    GodelQuotation.gq_weaken_standard_sequence
      (GodelQuotation.stdseq_numeral_member_iff
        sourceTokens.length point hPoint)
  have hOpen :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        (point ∈ₘ domₘ(sourceSequence)) ⟶ₘ
          conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    have hMembership :
        [point ∈ₘ domₘ(sourceSequence)]
          ⊢ₘ[GodelQuotation.godel_quotation_theory]
            point ∈ₘ domₘ(sourceSequence) :=
      FirstOrder.Derives.assumption (by simp)
    have hNumeralMembership :=
      FirstOrder.Derives.iffElimRight
        (FirstOrder.Derives.context_weaken_cons hDomainIff)
        hMembership
    have hCondition :=
      FirstOrder.Derives.iffElimRight
        (FirstOrder.Derives.context_weaken_cons hNumeralIff)
        hNumeralMembership
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken_cons hCases)
      hCondition
  have hTheoryFresh :
      ∀ formula,
        GodelQuotation.godel_quotation_theory formula →
          (SetSort.set, indexId) ∉
            Formula.freeSupport formula := by
    intro formula hFormula
    rw [(GodelQuotation.godel_quotation_theory_sentence
      hFormula).2]
    exact List.not_mem_nil
  have hGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := GodelQuotation.godel_quotation_theory)
      (Γ := []) (sort := SetSort.set)
      (eigen := indexId)
      hTheoryFresh (by simp) hOpen
  simpa [sourceSequence, targetSequence,
    point, conclusion] using hGeneralized

/-- 两条标准 token 序列满足完整二元 cutoff-shift 代码条件。 -/
theorem canonical_project_shift_standard_sequences_code_condition_with_ids
    {cutoff : Nat}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalProjectShiftTokens cutoff
        sourceTokens targetTokens)
    (indexId : FreeVarId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_shift_code_condition_with_ids
        (numₘ(cutoff))
        (GodelQuotation.standard_token_sequence sourceTokens)
        (GodelQuotation.standard_token_sequence targetTokens)
        indexId (indexId + 1) (indexId + 2) := by
  let sourceSequence :=
    GodelQuotation.standard_token_sequence sourceTokens
  let targetSequence :=
    GodelQuotation.standard_token_sequence targetTokens
  have hSourceDomain :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        domₘ(sourceSequence) ≐ₘ
          numₘ(sourceTokens.length) := by
    simpa [sourceSequence] using
      GodelQuotation.gq_weaken_standard_sequence
        (GodelQuotation.standard_token_sequence_domain_eq_length
          sourceTokens)
  have hTargetDomain :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        domₘ(targetSequence) ≐ₘ
          numₘ(sourceTokens.length) := by
    simpa [targetSequence, relation.length_eq] using
      GodelQuotation.gq_weaken_standard_sequence
        (GodelQuotation.standard_token_sequence_domain_eq_length
          targetTokens)
  have hDomainEquality :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        domₘ(sourceSequence) ≐ₘ domₘ(targetSequence) :=
    Metatheory.Derives.equality_trans hSourceDomain
      (Metatheory.Derives.equality_symm hTargetDomain)
  have hCutoff :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(cutoff) ∈ₘ ωₘ :=
    GodelQuotation.gq_weaken_standard_sequence
      (GodelQuotation.standard_sequence_finite_numeral_mem_omega
        cutoff)
  have hSourceFinite :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        finite_sequence_condition sourceSequence := by
    simpa [sourceSequence] using
      GodelQuotation.gq_weaken_standard_sequence
        (GodelQuotation.standard_token_sequence_finite_sequence_condition
          sourceTokens)
  have hTargetFinite :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        finite_sequence_condition targetSequence := by
    simpa [targetSequence] using
      GodelQuotation.gq_weaken_standard_sequence
        (GodelQuotation.standard_token_sequence_finite_sequence_condition
          targetTokens)
  have hPointwise :=
    canonical_project_shift_standard_sequences_pointwise
      relation indexId
  rw [canonical_project_shift_code_condition_with_ids]
  exact FirstOrder.Derives.conjIntro
    (FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjIntro hCutoff hSourceFinite)
        hTargetFinite)
      (by
        simpa [sourceSequence, targetSequence] using
          hDomainEquality))
    hPointwise

/-- 两组闭代码等式把二元 cutoff-shift 从标准参考码运输回实际码。 -/
theorem canonical_project_shift_code_condition_with_ids_of_equalities
    {cutoff : Nat}
    {Γ : Context signature}
    (indexId : FreeVarId)
    (sourceCode targetCode sourceReference targetReference : SetTerm)
    (hSourceCode :
      GodelQuotation.Numbered.CodeBoundary sourceCode)
    (hTargetCode :
      GodelQuotation.Numbered.CodeBoundary targetCode)
    (hSourceReference :
      GodelQuotation.Numbered.CodeBoundary sourceReference)
    (hTargetReference :
      GodelQuotation.Numbered.CodeBoundary targetReference)
    (hSourceEquality :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        sourceCode ≐ₘ sourceReference)
    (hTargetEquality :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        targetCode ≐ₘ targetReference)
    (hReferenceCondition :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_shift_code_condition_with_ids
          (numₘ(cutoff))
          sourceReference targetReference
          indexId (indexId + 1) (indexId + 2)) :
    Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_shift_code_condition_with_ids
        (numₘ(cutoff))
        sourceCode targetCode
        indexId (indexId + 1) (indexId + 2) := by
  let sourceParameter := indexId + 3
  let targetParameter := indexId + 4
  have hFixed
      (parameter : FreeVarId)
      (replacement fixed : SetTerm)
      (hFixed :
        GodelQuotation.Numbered.CodeBoundary fixed) :
      Term.substituteFree SetSort.set parameter
          replacement fixed =
        fixed :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter replacement fixed (by
        rw [hFixed.2]
        exact List.not_mem_nil)
  have hCloseCommute
      (parameter closedId : FreeVarId)
      (depth : Nat) (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement)
      (formula : SetFormula)
      (hDistinct : parameter ≠ closedId) :
      Formula.substituteFree SetSort.set parameter
          replacement
          (Formula.closeFreeAt SetSort.set
            closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set parameter
            replacement formula) := by
    exact (Formula.closeFreeAt_substituteFree_comm
      SetSort.set parameter closedId depth replacement formula
      hDistinct hReplacement.1.2 (by
        rw [hReplacement.2]
        exact List.not_mem_nil)).symm
  have hSourceCodeClose
      (closedId : FreeVarId) (depth : Nat)
      (formula : SetFormula)
      (hDistinct : sourceParameter ≠ closedId) :
      Formula.substituteFree SetSort.set sourceParameter
          sourceCode
          (Formula.closeFreeAt SetSort.set
            closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set sourceParameter
            sourceCode formula) :=
    hCloseCommute sourceParameter closedId depth
      sourceCode hSourceCode formula hDistinct
  have hSourceReferenceClose
      (closedId : FreeVarId) (depth : Nat)
      (formula : SetFormula)
      (hDistinct : sourceParameter ≠ closedId) :
      Formula.substituteFree SetSort.set sourceParameter
          sourceReference
          (Formula.closeFreeAt SetSort.set
            closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set sourceParameter
            sourceReference formula) :=
    hCloseCommute sourceParameter closedId depth
      sourceReference hSourceReference formula hDistinct
  have hTargetCodeClose
      (closedId : FreeVarId) (depth : Nat)
      (formula : SetFormula)
      (hDistinct : targetParameter ≠ closedId) :
      Formula.substituteFree SetSort.set targetParameter
          targetCode
          (Formula.closeFreeAt SetSort.set
            closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set targetParameter
            targetCode formula) :=
    hCloseCommute targetParameter closedId depth
      targetCode hTargetCode formula hDistinct
  have hTargetReferenceClose
      (closedId : FreeVarId) (depth : Nat)
      (formula : SetFormula)
      (hDistinct : targetParameter ≠ closedId) :
      Formula.substituteFree SetSort.set targetParameter
          targetReference
          (Formula.closeFreeAt SetSort.set
            closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set targetParameter
            targetReference formula) :=
    hCloseCommute targetParameter closedId depth
      targetReference hTargetReference formula hDistinct
  have hTargetReferenceFixedBySourceCode :
      Term.substituteFree SetSort.set sourceParameter
          sourceCode targetReference =
        targetReference :=
    hFixed sourceParameter sourceCode targetReference
      hTargetReference
  have hTargetReferenceFixedBySourceReference :
      Term.substituteFree SetSort.set sourceParameter
          sourceReference targetReference =
        targetReference :=
    hFixed sourceParameter sourceReference targetReference
      hTargetReference
  have hSourceCodeFixedByTargetCode :
      Term.substituteFree SetSort.set targetParameter
          targetCode sourceCode =
        sourceCode :=
    hFixed targetParameter targetCode sourceCode hSourceCode
  have hSourceCodeFixedByTargetReference :
      Term.substituteFree SetSort.set targetParameter
          targetReference sourceCode =
        sourceCode :=
    hFixed targetParameter targetReference sourceCode hSourceCode
  let sourceBody : SetFormula :=
    canonical_project_shift_code_condition_with_ids
      (numₘ(cutoff)) (x#sourceParameter) targetReference
      indexId (indexId + 1) (indexId + 2)
  have hSourceIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := GodelQuotation.godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := sourceParameter)
      (left := sourceCode) (right := sourceReference)
      (body := sourceBody) hSourceEquality
  have hSourceIff :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_shift_code_condition_with_ids
            (numₘ(cutoff))
            sourceCode targetReference
            indexId (indexId + 1) (indexId + 2) ↔ₘ
          canonical_project_shift_code_condition_with_ids
            (numₘ(cutoff))
            sourceReference targetReference
            indexId (indexId + 1) (indexId + 2) := by
    simpa [sourceBody, sourceParameter,
      canonical_project_shift_code_condition_with_ids,
      canonical_project_shift_token_condition_with_ids,
      canonical_project_shift_fixed_token_condition,
      canonical_shifted_depth_condition,
      finite_sequence_condition,
      Formula.substituteFree, Formula.next_depth,
      Term.substituteFree, set_variable,
      hTargetReferenceFixedBySourceCode,
      hTargetReferenceFixedBySourceReference,
      hSourceCodeClose, hSourceReferenceClose,
      GodelQuotation.gq_binder_shift_numeral_substitute] using
      hSourceIffRaw
  have hAtSource :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_shift_code_condition_with_ids
          (numₘ(cutoff))
          sourceCode targetReference
          indexId (indexId + 1) (indexId + 2) :=
    FirstOrder.Derives.iffElimLeft
      hSourceIff hReferenceCondition
  let targetBody : SetFormula :=
    canonical_project_shift_code_condition_with_ids
      (numₘ(cutoff)) sourceCode (x#targetParameter)
      indexId (indexId + 1) (indexId + 2)
  have hTargetIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := GodelQuotation.godel_quotation_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := targetParameter)
      (left := targetCode) (right := targetReference)
      (body := targetBody) hTargetEquality
  have hTargetIff :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_shift_code_condition_with_ids
            (numₘ(cutoff))
            sourceCode targetCode
            indexId (indexId + 1) (indexId + 2) ↔ₘ
          canonical_project_shift_code_condition_with_ids
            (numₘ(cutoff))
            sourceCode targetReference
            indexId (indexId + 1) (indexId + 2) := by
    simpa [targetBody, targetParameter,
      canonical_project_shift_code_condition_with_ids,
      canonical_project_shift_token_condition_with_ids,
      canonical_project_shift_fixed_token_condition,
      canonical_shifted_depth_condition,
      finite_sequence_condition,
      Formula.substituteFree, Formula.next_depth,
      Term.substituteFree, set_variable,
      hSourceCodeFixedByTargetCode,
      hSourceCodeFixedByTargetReference,
      hTargetCodeClose, hTargetReferenceClose,
      GodelQuotation.gq_binder_shift_numeral_substitute] using
      hTargetIffRaw
  exact FirstOrder.Derives.iffElimLeft
    hTargetIff hAtSource

/--
公式级 cutoff-shift 的两侧 quotation 直接满足对象层二元代码关系。

该定理是 schema replay 的公开入口；调用方不再构造公式 shift trace。
-/
theorem CanonicalProjectFormulaShift.quote_hilbert_with?_code_condition_with_ids
    {cutoff entryDepth : Nat}
    {sourceFormula targetFormula : SetFormula}
    (shift :
      CanonicalProjectFormulaShift cutoff entryDepth
        sourceFormula targetFormula)
    (hCutoff : cutoff ≤ entryDepth)
    {sourceTokens targetTokens : List Nat}
    {sourceCode targetCode : SetTerm}
    (hSourceTokens :
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names entryDepth)
          entryDepth sourceFormula =
        some sourceTokens)
    (hTargetTokens :
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names (entryDepth + 1))
          (entryDepth + 1) targetFormula =
        some targetTokens)
    (hSourceCode :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names entryDepth)
          entryDepth sourceFormula =
        some sourceCode)
    (hTargetCode :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names (entryDepth + 1))
          (entryDepth + 1) targetFormula =
        some targetCode)
    (indexId : FreeVarId) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_shift_code_condition_with_ids
        (numₘ(cutoff)) sourceCode targetCode
        indexId (indexId + 1) (indexId + 2) := by
  have hRelation :
      CanonicalProjectShiftTokens cutoff
        sourceTokens targetTokens :=
    shift.quote_hilbert_tokens_relation
      hCutoff hSourceTokens hTargetTokens
  have hSourceBoundary :
      GodelQuotation.Numbered.CodeBoundary sourceCode :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name
      GodelQuotation.bound_name hSourceCode
  have hTargetBoundary :
      GodelQuotation.Numbered.CodeBoundary targetCode :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name
      GodelQuotation.bound_name hTargetCode
  have hSourceReferenceBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (GodelQuotation.standard_token_sequence sourceTokens) :=
    ⟨GodelQuotation.standard_token_sequence_admissible sourceTokens,
      GodelQuotation.standard_token_sequence_freeSupport_nil
        sourceTokens⟩
  have hTargetReferenceBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (GodelQuotation.standard_token_sequence targetTokens) :=
    ⟨GodelQuotation.standard_token_sequence_admissible targetTokens,
      GodelQuotation.standard_token_sequence_freeSupport_nil
        targetTokens⟩
  have hSourceEquality :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        sourceCode ≐ₘ
          GodelQuotation.standard_token_sequence sourceTokens :=
    GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
      GodelQuotation.free_name
      GodelQuotation.bound_name hSourceTokens hSourceCode
  have hTargetEquality :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        targetCode ≐ₘ
          GodelQuotation.standard_token_sequence targetTokens :=
    GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
      GodelQuotation.free_name
      GodelQuotation.bound_name hTargetTokens hTargetCode
  have hReferenceCondition :=
    canonical_project_shift_standard_sequences_code_condition_with_ids
      hRelation indexId
  exact
    canonical_project_shift_code_condition_with_ids_of_equalities
      indexId sourceCode targetCode
      (GodelQuotation.standard_token_sequence sourceTokens)
      (GodelQuotation.standard_token_sequence targetTokens)
      hSourceBoundary hTargetBoundary
      hSourceReferenceBoundary hTargetReferenceBoundary
      hSourceEquality hTargetEquality hReferenceCondition

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
