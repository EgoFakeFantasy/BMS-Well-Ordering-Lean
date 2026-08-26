import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalProjectTokenShift.Replay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaConditionInversion

/-!
# 规范项目 token 平移的对象层反演

本模块证明二元 cutoff-shift 图的函数性。反演只使用源 token 数值给出的有限上界：

* 固定 token 分支由九个闭符号值逐项排除；
* bound token 分支把源深度限制在 `sourceToken + 1` 内；
* 唯一正确的源深度交给公共 `canonical_shifted_depth_condition` 函数性处理。

证明只读取二元 shift 条件和标准 token 位置，并在对象层恢复所需分量。
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

/-! ## bound token 数值项的等词性 -/

/-- 对象深度对应的原始变量 token 数值项。 -/
abbrev canonical_project_bound_token_term
    (depth : SetTerm) : SetTerm :=
  variable_symbol_number_term
    (canonical_binder_name_term depth)

/-- 原始变量 token 数值项保持 admissibility。 -/
theorem canonical_project_bound_token_term_admissible
    (depth : SetTerm)
    (hDepth : Term.Admissible depth SetSort.set) :
    Term.Admissible
      (canonical_project_bound_token_term depth)
      SetSort.set := by
  exact variable_symbol_number_term_admissible _
    (successor_term_admissible _
      (natural_multiplication_term_admissible
        (numₘ(2)) depth
        (finite_numeral_term_admissible 2)
        hDepth))

/-- 深度等式逐层提升为原始变量 token 数值项等式。 -/
theorem canonical_project_bound_token_term_congr_of_equality
    {T : SetTheory}
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEquality :
      Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      canonical_project_bound_token_term left ≐ₘ
        canonical_project_bound_token_term right := by
  exact Metatheory.Derives.unary_term_constructor_congr_of_equality
    canonical_project_bound_token_term
    canonical_project_bound_token_term_admissible
    (by
      intro parameter replacement term
      simp [canonical_project_bound_token_term,
        canonical_binder_name_term,
        variable_symbol_number_term,
        indexed_prime_power_code_term,
        prime_power_code_term,
        natural_exponentiation_term,
        Term.substituteFree,
        GodelQuotation.gq_binder_shift_numeral_substitute])
    left right hLeft hRight hEquality

/-! ## 闭符号值排除 -/

/-- 一个已知 numeral 不可能等于另一个 numeral 所表示的闭符号值。 -/
private theorem fs_zfc_support_raw_falsum_of_symbol_value
    {Γ : Context signature}
    (sourceToken fixedToken : Nat)
    (fixedValue : SetTerm)
    (hNe : sourceToken ≠ fixedToken)
    (hFixedValue :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(fixedToken) ≐ₘ fixedValue)
    (hSourceValue :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(sourceToken) ≐ₘ fixedValue) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hFixedValueAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(fixedToken) ≐ₘ fixedValue :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation
          hFixedValue
  exact fs_zfc_support_raw_falsum_of_numeral_equality
    hNe <|
      Metatheory.Derives.equality_trans hSourceValue
        (Metatheory.Derives.equality_symm hFixedValueAt)

/-- 已知 bound token 不满足固定 token 枚举。 -/
private theorem fs_zfc_support_raw_bound_token_fixed_falsum
    {Γ : Context signature}
    (depth : Nat)
    (hFixed :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_project_shift_fixed_token_condition
          (numₘ(GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name depth)))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  let sourceToken :=
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name depth)
  change Γ ⊢ₘ[fs_zfc_support_raw_theory]
    canonical_project_shift_fixed_token_condition
      (numₘ(sourceToken)) at hFixed
  have hBinderFixed :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_shift_fixed_token_condition
          (numₘ(sourceToken)) := by
    rw [canonical_project_shift_fixed_token_condition]
      at hFixed
    apply FirstOrder.Derives.disjElim hFixed
    · exact FirstOrder.Derives.assumption (by simp)
    · let Δ : Context signature :=
        (numₘ(sourceToken) ≐ₘ
          coded_predicate_symbol_number_term
            (numₘ(1))
            (numₘ(RelationSymbol.subset.ctorIdx))) :: Γ
      exact FirstOrder.Derives.falsumElim
        (φ :=
          canonical_binder_shift_fixed_token_condition
            (numₘ(sourceToken)))
        (fs_zfc_support_raw_falsum_of_symbol_value
          sourceToken
          (GodelQuotation.Numbered.predicate_token
            1 RelationSymbol.subset.ctorIdx)
          (coded_predicate_symbol_number_term
            (numₘ(1))
            (numₘ(RelationSymbol.subset.ctorIdx)))
          (GodelQuotation.predicate_token_ne_variable_token
            1 RelationSymbol.subset.ctorIdx
            (GodelQuotation.bound_name depth)).symm
          (by
            simpa [GodelQuotation.Numbered.predicate_token,
              coded_predicate_symbol_number_term] using
              GodelQuotation.gq_binder_shift_binary_symbol_value
                7 1 RelationSymbol.subset.ctorIdx)
          (FirstOrder.Derives.assumption (by simp)))
  change Γ ⊢ₘ[fs_zfc_support_raw_theory]
    ((numₘ(sourceToken) ≐ₘ
          logical_symbol_number_term .equality) ∨ₘ
        ((numₘ(sourceToken) ≐ₘ
            logical_symbol_number_term .negation) ∨ₘ
          ((numₘ(sourceToken) ≐ₘ
              logical_symbol_number_term .implication) ∨ₘ
            ((numₘ(sourceToken) ≐ₘ
                logical_symbol_number_term .universal) ∨ₘ
              ((numₘ(sourceToken) ≐ₘ
                  logical_symbol_number_term .leftParenthesis) ∨ₘ
                ((numₘ(sourceToken) ≐ₘ
                    logical_symbol_number_term .rightParenthesis) ∨ₘ
                  ((numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .existential) ∨ₘ
                    ((numₘ(sourceToken) ≐ₘ
                        logical_symbol_number_term .conjunction) ∨ₘ
                      ((numₘ(sourceToken) ≐ₘ
                          membership_symbol_number_term) ∨ₘ
                        Formula.falsum))))))))) at hBinderFixed
  have hLogical
      (symbol : LogicalSymbolKind)
      {Θ : Context signature}
      (hValue :
        (numₘ(sourceToken) ≐ₘ
          logical_symbol_number_term symbol) :: Θ
          ⊢ₘ[fs_zfc_support_raw_theory]
            numₘ(sourceToken) ≐ₘ
              logical_symbol_number_term symbol) :
      (numₘ(sourceToken) ≐ₘ
          logical_symbol_number_term symbol) :: Θ
        ⊢ₘ[fs_zfc_support_raw_theory]
          Formula.falsum :=
    fs_zfc_support_raw_falsum_of_symbol_value
      sourceToken
      (GodelQuotation.Numbered.logical_token symbol)
      (logical_symbol_number_term symbol)
      (GodelQuotation.logical_token_ne_variable_token
        symbol (GodelQuotation.bound_name depth)).symm
      (GodelQuotation.gq_binder_shift_logical_symbol_value symbol)
      hValue
  have hMembership
      {Θ : Context signature}
      (hValue :
        (numₘ(sourceToken) ≐ₘ
          membership_symbol_number_term) :: Θ
          ⊢ₘ[fs_zfc_support_raw_theory]
            numₘ(sourceToken) ≐ₘ
              membership_symbol_number_term) :
      (numₘ(sourceToken) ≐ₘ
          membership_symbol_number_term) :: Θ
        ⊢ₘ[fs_zfc_support_raw_theory]
          Formula.falsum :=
    fs_zfc_support_raw_falsum_of_symbol_value
      sourceToken
      GodelQuotation.Numbered.membership_token
      membership_symbol_number_term
      (GodelQuotation.membership_token_ne_variable_token
        (GodelQuotation.bound_name depth)).symm
      GodelQuotation.gq_binder_shift_membership_symbol_value
      hValue
  apply FirstOrder.Derives.disjElim hBinderFixed
  · exact hLogical .equality
      (FirstOrder.Derives.assumption (by simp))
  · apply FirstOrder.Derives.disjElim
      (left :=
        numₘ(sourceToken) ≐ₘ
          logical_symbol_number_term .negation)
      (right :=
        (numₘ(sourceToken) ≐ₘ
            logical_symbol_number_term .implication) ∨ₘ
          ((numₘ(sourceToken) ≐ₘ
              logical_symbol_number_term .universal) ∨ₘ
            ((numₘ(sourceToken) ≐ₘ
                logical_symbol_number_term .leftParenthesis) ∨ₘ
              ((numₘ(sourceToken) ≐ₘ
                  logical_symbol_number_term .rightParenthesis) ∨ₘ
                ((numₘ(sourceToken) ≐ₘ
                    logical_symbol_number_term .existential) ∨ₘ
                  ((numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .conjunction) ∨ₘ
                    ((numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term) ∨ₘ
                      Formula.falsum)))))))
      (FirstOrder.Derives.assumption (by simp))
    · exact hLogical .negation
        (FirstOrder.Derives.assumption (by simp))
    · apply FirstOrder.Derives.disjElim
        (left :=
          numₘ(sourceToken) ≐ₘ
            logical_symbol_number_term .implication)
        (right :=
          (numₘ(sourceToken) ≐ₘ
              logical_symbol_number_term .universal) ∨ₘ
            ((numₘ(sourceToken) ≐ₘ
                logical_symbol_number_term .leftParenthesis) ∨ₘ
              ((numₘ(sourceToken) ≐ₘ
                  logical_symbol_number_term .rightParenthesis) ∨ₘ
                ((numₘ(sourceToken) ≐ₘ
                    logical_symbol_number_term .existential) ∨ₘ
                  ((numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .conjunction) ∨ₘ
                    ((numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term) ∨ₘ
                      Formula.falsum))))))
        (FirstOrder.Derives.assumption (by simp))
      · exact hLogical .implication
          (FirstOrder.Derives.assumption (by simp))
      · apply FirstOrder.Derives.disjElim
          (left :=
            numₘ(sourceToken) ≐ₘ
              logical_symbol_number_term .universal)
          (right :=
            (numₘ(sourceToken) ≐ₘ
                logical_symbol_number_term .leftParenthesis) ∨ₘ
              ((numₘ(sourceToken) ≐ₘ
                  logical_symbol_number_term .rightParenthesis) ∨ₘ
                ((numₘ(sourceToken) ≐ₘ
                    logical_symbol_number_term .existential) ∨ₘ
                  ((numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .conjunction) ∨ₘ
                    ((numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term) ∨ₘ
                      Formula.falsum)))))
          (FirstOrder.Derives.assumption (by simp))
        · exact hLogical .universal
            (FirstOrder.Derives.assumption (by simp))
        · apply FirstOrder.Derives.disjElim
            (left :=
              numₘ(sourceToken) ≐ₘ
                logical_symbol_number_term .leftParenthesis)
            (right :=
              (numₘ(sourceToken) ≐ₘ
                  logical_symbol_number_term .rightParenthesis) ∨ₘ
                ((numₘ(sourceToken) ≐ₘ
                    logical_symbol_number_term .existential) ∨ₘ
                  ((numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .conjunction) ∨ₘ
                    ((numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term) ∨ₘ
                      Formula.falsum))))
            (FirstOrder.Derives.assumption (by simp))
          · exact hLogical .leftParenthesis
              (FirstOrder.Derives.assumption (by simp))
          · apply FirstOrder.Derives.disjElim
              (left :=
                numₘ(sourceToken) ≐ₘ
                  logical_symbol_number_term .rightParenthesis)
              (right :=
                (numₘ(sourceToken) ≐ₘ
                    logical_symbol_number_term .existential) ∨ₘ
                  ((numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .conjunction) ∨ₘ
                    ((numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term) ∨ₘ
                      Formula.falsum)))
              (FirstOrder.Derives.assumption (by simp))
            · exact hLogical .rightParenthesis
                (FirstOrder.Derives.assumption (by simp))
            · apply FirstOrder.Derives.disjElim
                (left :=
                  numₘ(sourceToken) ≐ₘ
                    logical_symbol_number_term .existential)
                (right :=
                  (numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .conjunction) ∨ₘ
                    ((numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term) ∨ₘ
                      Formula.falsum))
                (FirstOrder.Derives.assumption (by simp))
              · exact hLogical .existential
                  (FirstOrder.Derives.assumption (by simp))
              · apply FirstOrder.Derives.disjElim
                  (left :=
                    numₘ(sourceToken) ≐ₘ
                      logical_symbol_number_term .conjunction)
                  (right :=
                    (numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term) ∨ₘ
                      Formula.falsum)
                  (FirstOrder.Derives.assumption (by simp))
                · exact hLogical .conjunction
                    (FirstOrder.Derives.assumption (by simp))
                · apply FirstOrder.Derives.disjElim
                    (left :=
                      numₘ(sourceToken) ≐ₘ
                        membership_symbol_number_term)
                    (right := Formula.falsum)
                    (FirstOrder.Derives.assumption (by simp))
                  · exact hMembership
                      (FirstOrder.Derives.assumption (by simp))
                  · exact FirstOrder.Derives.assumption
                      (by simp)

/-! ## 单 token 函数性 -/

/-- 沿源深度等式把 cutoff-shift 条件运输到标准 numeral。 -/
private theorem fs_zfc_support_raw_canonical_shifted_depth_of_source_equality
    {Γ : Context signature}
    (cutoff sourceDepth : Nat)
    (sourceDepthId : FreeVarId)
    (targetDepth : SetTerm)
    (hSourceFreshTarget :
      (SetSort.set, sourceDepthId) ∉
        Term.freeSupport targetDepth)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (x#sourceDepthId) ≐ₘ numₘ(sourceDepth))
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_shifted_depth_condition
          (numₘ(cutoff)) (x#sourceDepthId)
          targetDepth) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      canonical_shifted_depth_condition
        (numₘ(cutoff)) (numₘ(sourceDepth))
        targetDepth := by
  let body : SetFormula :=
    canonical_shifted_depth_condition
      (numₘ(cutoff)) (x#sourceDepthId)
      targetDepth
  have hTransport :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (sort := SetSort.set)
      (eigen := sourceDepthId)
      (left := x#sourceDepthId)
      (right := numₘ(sourceDepth))
      (body := body)
      hSourceEquality
  have hTargetFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceDepthId
          replacement targetDepth =
        targetDepth :=
    Term.substituteFree_eq_self_of_not_mem
      _ _ _ _ hSourceFreshTarget
  have hIff :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_shifted_depth_condition
            (numₘ(cutoff)) (x#sourceDepthId)
            targetDepth ↔ₘ
          canonical_shifted_depth_condition
            (numₘ(cutoff)) (numₘ(sourceDepth))
            targetDepth := by
    simpa [body, canonical_shifted_depth_condition,
      Formula.substituteFree, Term.substituteFree,
      set_variable, hTargetFixed,
      GodelQuotation.gq_binder_shift_numeral_substitute] using
      hTransport
  exact FirstOrder.Derives.iffElimRight
    hIff hCondition

/--
源值同时等于一个已知标准 token 和深度 `index` 的 bound token 时，若两个
外部 token 不同，则对象层导出矛盾。
-/
private theorem fs_zfc_support_raw_canonical_project_source_token_falsum
    {Γ : Context signature}
    (sourceToken index : Nat)
    (sourceValue sourceDepth : SetTerm)
    (hNe :
      sourceToken ≠
        GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name index))
    (hSourceDepth :
      Term.Admissible sourceDepth SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hTokenEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ
          canonical_project_bound_token_term sourceDepth)
    (hDepthEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceDepth ≐ₘ numₘ(index)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hTermEquality :=
    canonical_project_bound_token_term_congr_of_equality
      sourceDepth (numₘ(index))
      hSourceDepth
      (finite_numeral_term_admissible index)
      hDepthEquality
  have hValue :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name index)) ≐ₘ
          canonical_project_bound_token_term
            (numₘ(index)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <| by
          simpa [canonical_project_bound_token_term,
            canonical_binder_name_term] using
            canonical_project_bound_token_value index
  have hNumeralEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(sourceToken) ≐ₘ
          numₘ(GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name index)) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hSourceEquality) <|
        Metatheory.Derives.equality_trans hTokenEquality <|
          Metatheory.Derives.equality_trans hTermEquality
            (Metatheory.Derives.equality_symm hValue)
  exact fs_zfc_support_raw_falsum_of_numeral_equality
    hNe hNumeralEquality

/--
已知标准源 token 时，二元 cutoff-shift 条件唯一决定目标 token。

内部深度编号只要求避开左右值和当前上下文；不附加任何自然数标准性前提。
-/
theorem fs_zfc_support_raw_canonical_project_shift_token_unique
    {Γ : Context signature}
    {cutoff sourceToken targetToken : Nat}
    (relation :
      CanonicalProjectShiftToken cutoff
        sourceToken targetToken)
    (sourceValue targetValue : SetTerm)
    (freshBase : FreeVarId)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hTargetFresh :
      ∀ id, freshBase ≤ id →
        (SetSort.set, id) ∉
          Term.freeSupport targetValue)
    (hSourceFresh :
      ∀ id, freshBase ≤ id →
        (SetSort.set, id) ∉
          Term.freeSupport sourceValue)
    (hContextFresh :
      ∀ formula, formula ∈ Γ →
        ∀ id, freshBase ≤ id →
          (SetSort.set, id) ∉
            Formula.freeSupport formula)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_project_shift_token_condition_with_ids
          (numₘ(cutoff)) sourceValue targetValue
          freshBase (freshBase + 1)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ numₘ(targetToken) := by
  have hConclusion :
      Formula.Admissible
        (targetValue ≐ₘ numₘ(targetToken)) :=
    Formula.Admissible.equal hTargetValue
      (finite_numeral_term_admissible targetToken)
  rw [canonical_project_shift_token_condition_with_ids]
    at hCondition
  apply FirstOrder.Derives.disjElim hCondition
  · let Δ : Context signature :=
      (canonical_project_shift_fixed_token_condition sourceValue ∧ₘ
        (targetValue ≐ₘ sourceValue)) :: Γ
    have hFixedCase :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_fixed_token_condition sourceValue ∧ₘ
            (targetValue ≐ₘ sourceValue) :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hTargetSource :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          targetValue ≐ₘ sourceValue :=
      FirstOrder.Derives.conjElimRight hFixedCase
    cases relation with
    | logical symbol =>
        exact Metatheory.Derives.equality_trans hTargetSource
          (FirstOrder.Derives.context_weaken_cons hSourceEquality)
    | membership =>
        exact Metatheory.Derives.equality_trans hTargetSource
          (FirstOrder.Derives.context_weaken_cons hSourceEquality)
    | subset =>
        exact Metatheory.Derives.equality_trans hTargetSource
          (FirstOrder.Derives.context_weaken_cons hSourceEquality)
    | bound depth =>
        have hFixedAt :
            Δ ⊢ₘ[fs_zfc_support_raw_theory]
              canonical_project_shift_fixed_token_condition
                (numₘ(GodelQuotation.Numbered.variable_token
                  (GodelQuotation.bound_name depth))) := by
          let parameter :=
            FreshVariable.fresh_id SetSort.set
              [sourceValue ≐ₘ sourceValue]
          let body : SetFormula :=
            canonical_project_shift_fixed_token_condition
              (x#parameter)
          have hIffRaw :=
            Metatheory.Derives.equality_iff_of_equality
              (T := fs_zfc_support_raw_theory)
              (Γ := Δ) (sort := SetSort.set)
              (eigen := parameter)
              (left := sourceValue)
              (right :=
                numₘ(GodelQuotation.Numbered.variable_token
                  (GodelQuotation.bound_name depth)))
              (body := body)
              (FirstOrder.Derives.context_weaken_cons
                hSourceEquality)
          have hIff :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                canonical_project_shift_fixed_token_condition
                    sourceValue ↔ₘ
                  canonical_project_shift_fixed_token_condition
                    (numₘ(GodelQuotation.Numbered.variable_token
                      (GodelQuotation.bound_name depth))) := by
            simpa [body, parameter,
              canonical_project_shift_fixed_token_condition,
              Formula.substituteFree, Term.substituteFree,
              set_variable,
              GodelQuotation.gq_binder_shift_numeral_substitute] using
              hIffRaw
          exact FirstOrder.Derives.iffElimRight hIff
            (FirstOrder.Derives.conjElimLeft hFixedCase)
        exact FirstOrder.Derives.falsumElim
          (φ := targetValue ≐ₘ
            numₘ(GodelQuotation.Numbered.variable_token
              (GodelQuotation.bound_name
                (canonical_project_shift_depth cutoff depth))))
          (fs_zfc_support_raw_bound_token_fixed_falsum
            depth hFixedAt)
  · let sourceDepth : SetTerm := x#freshBase
    let targetDepth : SetTerm := x#(freshBase + 1)
    let rawBody : SetFormula :=
      (targetDepth ∈ₘ ωₘ) ∧ₘ
        ((sourceValue ≐ₘ
            canonical_project_bound_token_term sourceDepth) ∧ₘ
          (canonical_shifted_depth_condition
              (numₘ(cutoff)) sourceDepth targetDepth ∧ₘ
            (targetValue ≐ₘ
              canonical_project_bound_token_term targetDepth)))
    let outerBody : SetFormula :=
      (sourceDepth ∈ₘ Sₘ(sourceValue)) ∧ₘ
        (∃ₘ[SetSort.set, freshBase + 1], rawBody)
    let variableCase : SetFormula :=
      ∃ₘ[SetSort.set, freshBase], outerBody
    let Θ : Context signature :=
      variableCase :: Γ
    change Θ ⊢ₘ[fs_zfc_support_raw_theory]
      targetValue ≐ₘ numₘ(targetToken)
    have hSourceDepth :
        Term.Admissible sourceDepth SetSort.set :=
      set_variable_admissible freshBase
    have hTargetDepth :
        Term.Admissible targetDepth SetSort.set :=
      set_variable_admissible (freshBase + 1)
    have hRawBody :
        Formula.Admissible rawBody := by
      exact Formula.Admissible.conj
        (membership_formula_admissible
          hTargetDepth omega_term_admissible)
        (Formula.Admissible.conj
          (Formula.Admissible.equal hSourceValue
            (canonical_project_bound_token_term_admissible
              sourceDepth hSourceDepth))
          (Formula.Admissible.conj
            (canonical_shifted_depth_condition_admissible
              (numₘ(cutoff)) sourceDepth targetDepth
              (finite_numeral_term_admissible cutoff)
              hSourceDepth hTargetDepth)
            (Formula.Admissible.equal hTargetValue
              (canonical_project_bound_token_term_admissible
                targetDepth hTargetDepth))))
    have hOuterBody :
        Formula.Admissible outerBody :=
      Formula.Admissible.conj
        (membership_formula_admissible
          hSourceDepth
          (successor_term_admissible
            sourceValue hSourceValue))
        (Formula.Admissible.exists_closeFreeAt
          SetSort.set (freshBase + 1) hRawBody)
    have hVariable :
        Θ ⊢ₘ[fs_zfc_support_raw_theory]
          variableCase :=
      FirstOrder.Derives.assumption (by simp [Θ])
    have hExists :
        Θ ⊢ₘ[fs_zfc_support_raw_theory]
          ∃ₘ[SetSort.set, freshBase], outerBody := by
      simpa [variableCase] using hVariable
    nd_apply FirstOrder.Derives.exists_elim
      (T := fs_zfc_support_raw_theory)
      (Γ := Θ)
      (sort := SetSort.set)
      (eigen := freshBase)
      (body := outerBody)
      (conclusion :=
        targetValue ≐ₘ numₘ(targetToken))
      (hBodyCheck :=
        Formula.check_admissible_complete hOuterBody)
    · intro formula hFormula
      rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      simp only [Θ, List.mem_cons] at hFormula
      rcases hFormula with rfl | hFormula
      · simpa [variableCase] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set freshBase 0 outerBody
      · exact hContextFresh formula hFormula
          freshBase (Nat.le_refl freshBase)
    · simpa [Formula.freeSupport,
        finite_numeral_term_freeSupport] using
        hTargetFresh freshBase (Nat.le_refl freshBase)
    · exact hExists
    · let Δ : Context signature := outerBody :: Θ
      change Δ ⊢ₘ[fs_zfc_support_raw_theory]
        targetValue ≐ₘ numₘ(targetToken)
      have hOuterData :
          Δ ⊢ₘ[fs_zfc_support_raw_theory]
            outerBody :=
        FirstOrder.Derives.assumption (by simp [Δ, outerBody])
      have hSourceMember :
          Δ ⊢ₘ[fs_zfc_support_raw_theory]
            sourceDepth ∈ₘ Sₘ(sourceValue) :=
        FirstOrder.Derives.conjElimLeft hOuterData
      have hOuterExists :
          Δ ⊢ₘ[fs_zfc_support_raw_theory]
            ∃ₘ[SetSort.set, freshBase + 1], rawBody :=
        FirstOrder.Derives.conjElimRight hOuterData
      nd_apply FirstOrder.Derives.exists_elim
        (T := fs_zfc_support_raw_theory)
        (Γ := Δ)
        (sort := SetSort.set)
        (eigen := freshBase + 1)
        (body := rawBody)
        (conclusion :=
          targetValue ≐ₘ numₘ(targetToken))
        (hBodyCheck :=
          Formula.check_admissible_complete hRawBody)
      · intro formula hFormula
        rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
        exact List.not_mem_nil
      · intro formula hFormula
        simp only [Δ, List.mem_cons] at hFormula
        rcases hFormula with rfl | hFormula
        · have hTargetFreshOuter :
              (SetSort.set, freshBase + 1) ∉
                Formula.freeSupport outerBody := by
            have hRawFresh :
                (SetSort.set, freshBase + 1) ∉
                  Formula.freeSupport
                    (Formula.closeFreeAt
                      SetSort.set (freshBase + 1) 0 rawBody) :=
              Formula.not_mem_freeSupport_closeFreeAt
                SetSort.set (freshBase + 1) 0 rawBody
            have hSourceTermFresh :
                (SetSort.set, freshBase + 1) ∉
                  Term.freeSupport sourceValue :=
              hSourceFresh (freshBase + 1)
                (Nat.le_add_right freshBase 1)
            have hDepthFresh :
                (SetSort.set, freshBase + 1) ∉
                  Term.freeSupport sourceDepth := by
              simp only [sourceDepth, Term.freeSupport]
              intro hMember
              have hId : freshBase + 1 = freshBase := by
                exact congrArg Prod.snd
                  (List.mem_singleton.mp hMember)
              have hLt : freshBase < freshBase + 1 := by
                exact Nat.lt_succ_self freshBase
              exact (Nat.ne_of_lt hLt) hId.symm
            have hSuccessorFresh :
                (SetSort.set, freshBase + 1) ∉
                  Term.freeSupport (Sₘ(sourceValue)) := by
              simpa [Term.freeSupport, Term.freeSupportList] using
                hSourceTermFresh
            have hGuardFresh :
                (SetSort.set, freshBase + 1) ∉
                  Term.freeSupportList
                    [sourceDepth, Sₘ(sourceValue)] := by
              simp only [Term.freeSupportList]
              exact List.not_mem_append hDepthFresh <| by
                exact List.not_mem_append hSuccessorFresh
                  List.not_mem_nil
            simp only [outerBody, Formula.freeSupport]
            exact List.not_mem_append hGuardFresh hRawFresh
          exact hTargetFreshOuter
        · simp only [Θ, List.mem_cons] at hFormula
          rcases hFormula with rfl | hFormula
          · have hTargetFreshOuter :
                (SetSort.set, freshBase + 1) ∉
                  Formula.freeSupport outerBody := by
              have hRawFresh :
                  (SetSort.set, freshBase + 1) ∉
                    Formula.freeSupport
                      (Formula.closeFreeAt
                        SetSort.set (freshBase + 1) 0 rawBody) :=
                Formula.not_mem_freeSupport_closeFreeAt
                  SetSort.set (freshBase + 1) 0 rawBody
              have hSourceTermFresh :
                  (SetSort.set, freshBase + 1) ∉
                    Term.freeSupport sourceValue :=
                hSourceFresh (freshBase + 1)
                  (Nat.le_add_right freshBase 1)
              have hDepthFresh :
                  (SetSort.set, freshBase + 1) ∉
                    Term.freeSupport sourceDepth := by
                simp only [sourceDepth, Term.freeSupport]
                intro hMember
                have hId : freshBase + 1 = freshBase := by
                  exact congrArg Prod.snd
                    (List.mem_singleton.mp hMember)
                have hLt : freshBase < freshBase + 1 := by
                  exact Nat.lt_succ_self freshBase
                exact (Nat.ne_of_lt hLt) hId.symm
              have hSuccessorFresh :
                  (SetSort.set, freshBase + 1) ∉
                    Term.freeSupport (Sₘ(sourceValue)) := by
                simpa [Term.freeSupport, Term.freeSupportList] using
                  hSourceTermFresh
              have hGuardFresh :
                  (SetSort.set, freshBase + 1) ∉
                    Term.freeSupportList
                      [sourceDepth, Sₘ(sourceValue)] := by
                simp only [Term.freeSupportList]
                exact List.not_mem_append hDepthFresh <| by
                  exact List.not_mem_append hSuccessorFresh
                    List.not_mem_nil
              simp only [outerBody, Formula.freeSupport]
              exact List.not_mem_append hGuardFresh hRawFresh
            have hTargetFreshClosedSource :=
              Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
                (SetSort.set, freshBase + 1)
                SetSort.set freshBase 0 outerBody
                hTargetFreshOuter
            simpa [variableCase, Formula.freeSupport] using
              hTargetFreshClosedSource
          · exact hContextFresh formula hFormula
              (freshBase + 1)
              (Nat.le_add_right freshBase 1)
      · simpa [Formula.freeSupport,
          finite_numeral_term_freeSupport] using
          hTargetFresh (freshBase + 1)
            (Nat.le_add_right freshBase 1)
      · exact hOuterExists
      · let Ζ : Context signature := rawBody :: Δ
        change Ζ ⊢ₘ[fs_zfc_support_raw_theory]
          targetValue ≐ₘ numₘ(targetToken)
        have hRaw :
            Ζ ⊢ₘ[fs_zfc_support_raw_theory]
              rawBody :=
          FirstOrder.Derives.assumption (by simp [Ζ])
        have hTargetData :=
          FirstOrder.Derives.conjElimRight hRaw
        have hSourceData := hTargetData
        have hSourceMember :
            Ζ ⊢ₘ[fs_zfc_support_raw_theory]
              sourceDepth ∈ₘ Sₘ(sourceValue) := by
          exact FirstOrder.Derives.context_weaken_cons hSourceMember
        have hSourceToken :
            Ζ ⊢ₘ[fs_zfc_support_raw_theory]
              sourceValue ≐ₘ
                canonical_project_bound_token_term
                  sourceDepth := by
          simpa [rawBody] using
            FirstOrder.Derives.conjElimLeft hSourceData
        have hShift :
            Ζ ⊢ₘ[fs_zfc_support_raw_theory]
              canonical_shifted_depth_condition
                (numₘ(cutoff)) sourceDepth targetDepth := by
          simpa [rawBody] using
            FirstOrder.Derives.conjElimLeft
              (FirstOrder.Derives.conjElimRight hTargetData)
        have hTargetToken :
            Ζ ⊢ₘ[fs_zfc_support_raw_theory]
              targetValue ≐ₘ
                canonical_project_bound_token_term
                  targetDepth := by
          simpa [rawBody] using
            FirstOrder.Derives.conjElimRight
              (FirstOrder.Derives.conjElimRight hTargetData)
        have hSourceEqualityAt :
            Ζ ⊢ₘ[fs_zfc_support_raw_theory]
              sourceValue ≐ₘ numₘ(sourceToken) :=
          FirstOrder.Derives.context_weaken
            (Γ := Γ) (Δ := Ζ) (by
              intro formula hFormula
              simp [Ζ, Δ, Θ, hFormula])
            hSourceEquality
        have hSuccessorEquality :=
          successor_term_congr_of_equality
            sourceValue (numₘ(sourceToken))
            hSourceValue
            (finite_numeral_term_admissible sourceToken)
            hSourceEqualityAt
        have hMemberIff :=
          membership_right_iff_of_equality
            sourceDepth
            (Sₘ(sourceValue))
            (Sₘ(numₘ(sourceToken)))
            hSourceDepth
            (successor_term_admissible
              sourceValue hSourceValue)
            (successor_term_admissible
              (numₘ(sourceToken))
              (finite_numeral_term_admissible sourceToken))
            hSuccessorEquality
        have hBoundMember :
            Ζ ⊢ₘ[fs_zfc_support_raw_theory]
              sourceDepth ∈ₘ numₘ(sourceToken + 1) := by
          simpa [finite_numeral_term] using
            FirstOrder.Derives.iffElimRight
              hMemberIff hSourceMember
        apply
          fs_zfc_support_raw_finite_numeral_member_elim_context
            (sourceToken + 1) sourceDepth
            (targetValue ≐ₘ numₘ(targetToken))
            hSourceDepth hConclusion hBoundMember
        intro index hIndex
        let sourceDepthEquality : SetFormula :=
          sourceDepth ≐ₘ numₘ(index)
        let Ε : Context signature :=
          sourceDepthEquality :: Ζ
        change Ε ⊢ₘ[fs_zfc_support_raw_theory]
          targetValue ≐ₘ numₘ(targetToken)
        have hDepthEquality :
            Ε ⊢ₘ[fs_zfc_support_raw_theory]
              sourceDepth ≐ₘ numₘ(index) := by
          simpa [Ε, sourceDepthEquality] using
            (FirstOrder.Derives.assumption
              (T := fs_zfc_support_raw_theory)
              (Γ := Ε) (φ := sourceDepthEquality)
              (by simp [Ε]))
        have hSourceEqualityBranch :
            Ε ⊢ₘ[fs_zfc_support_raw_theory]
              sourceValue ≐ₘ numₘ(sourceToken) :=
          FirstOrder.Derives.context_weaken_cons
            hSourceEqualityAt
        have hSourceTokenBranch :
            Ε ⊢ₘ[fs_zfc_support_raw_theory]
              sourceValue ≐ₘ
                canonical_project_bound_token_term
                  sourceDepth :=
          FirstOrder.Derives.context_weaken_cons
            hSourceToken
        cases relation with
        | logical symbol =>
            exact FirstOrder.Derives.falsumElim
              (φ := targetValue ≐ₘ
                numₘ(GodelQuotation.Numbered.logical_token symbol))
              (fs_zfc_support_raw_canonical_project_source_token_falsum
                (GodelQuotation.Numbered.logical_token symbol)
                index sourceValue sourceDepth
                (GodelQuotation.logical_token_ne_variable_token
                  symbol (GodelQuotation.bound_name index))
                hSourceDepth hSourceEqualityBranch
                hSourceTokenBranch hDepthEquality)
        | membership =>
            exact FirstOrder.Derives.falsumElim
              (φ := targetValue ≐ₘ
                numₘ(GodelQuotation.Numbered.membership_token))
              (fs_zfc_support_raw_canonical_project_source_token_falsum
                GodelQuotation.Numbered.membership_token
                index sourceValue sourceDepth
                (GodelQuotation.membership_token_ne_variable_token
                  (GodelQuotation.bound_name index))
                hSourceDepth hSourceEqualityBranch
                hSourceTokenBranch hDepthEquality)
        | subset =>
            exact FirstOrder.Derives.falsumElim
              (φ := targetValue ≐ₘ
                numₘ(GodelQuotation.Numbered.predicate_token
                  1 RelationSymbol.subset.ctorIdx))
              (fs_zfc_support_raw_canonical_project_source_token_falsum
                (GodelQuotation.Numbered.predicate_token
                  1 RelationSymbol.subset.ctorIdx)
                index sourceValue sourceDepth
                (GodelQuotation.predicate_token_ne_variable_token
                  1 RelationSymbol.subset.ctorIdx
                  (GodelQuotation.bound_name index))
                hSourceDepth hSourceEqualityBranch
                hSourceTokenBranch hDepthEquality)
        | bound depth =>
            by_cases hDepth : index = depth
            · subst index
              have hShiftAt :
                  Ε ⊢ₘ[fs_zfc_support_raw_theory]
                    canonical_shifted_depth_condition
                      (numₘ(cutoff)) sourceDepth targetDepth :=
                FirstOrder.Derives.context_weaken_cons hShift
              have hSourceFreshTarget :
                  (SetSort.set, freshBase) ∉
                    Term.freeSupport targetDepth := by
                intro hMember
                change
                  (SetSort.set, freshBase) ∈
                    [(SetSort.set, freshBase + 1)]
                  at hMember
                have hPair :
                    (SetSort.set, freshBase) =
                      (SetSort.set, freshBase + 1) := by
                  exact List.mem_singleton.mp hMember
                have hId :
                    freshBase = freshBase + 1 :=
                  congrArg Prod.snd hPair
                exact (Nat.ne_of_lt
                  (Nat.lt_succ_self freshBase)) <| by
                    simp at hId
              have hShiftTransported :=
                fs_zfc_support_raw_canonical_shifted_depth_of_source_equality
                  cutoff depth freshBase targetDepth
                  hSourceFreshTarget
                  hDepthEquality hShiftAt
              have hTargetDepthEquality :=
                fs_zfc_support_raw_canonical_shifted_depth_condition_unique
                  cutoff depth targetDepth hTargetDepth
                  hShiftTransported
              have hTargetTermEquality :=
                canonical_project_bound_token_term_congr_of_equality
                  targetDepth
                  (numₘ(canonical_project_shift_depth
                    cutoff depth))
                  hTargetDepth
                  (finite_numeral_term_admissible
                    (canonical_project_shift_depth cutoff depth))
                  hTargetDepthEquality
              have hTargetTokenAt :
                  Ε ⊢ₘ[fs_zfc_support_raw_theory]
                    targetValue ≐ₘ
                      canonical_project_bound_token_term
                        targetDepth :=
                FirstOrder.Derives.context_weaken_cons
                  hTargetToken
              have hValue :
                  Ε ⊢ₘ[fs_zfc_support_raw_theory]
                    numₘ(GodelQuotation.Numbered.variable_token
                        (GodelQuotation.bound_name
                          (canonical_project_shift_depth
                            cutoff depth))) ≐ₘ
                      canonical_project_bound_token_term
                        (numₘ(canonical_project_shift_depth
                          cutoff depth)) :=
                FirstOrder.Derives.context_weaken
                  (Γ := []) (Δ := Ε) (by simp) <|
                    fs_zfc_support_raw_derives_of_godel_quotation <| by
                      simpa [canonical_project_bound_token_term,
                        canonical_binder_name_term] using
                        canonical_project_bound_token_value
                          (canonical_project_shift_depth
                            cutoff depth)
              exact Metatheory.Derives.equality_trans
                hTargetTokenAt <|
                  Metatheory.Derives.equality_trans
                    hTargetTermEquality
                    (Metatheory.Derives.equality_symm hValue)
            · have hTokenNe :
                  GodelQuotation.Numbered.variable_token
                      (GodelQuotation.bound_name depth) ≠
                    GodelQuotation.Numbered.variable_token
                      (GodelQuotation.bound_name index) :=
                GodelQuotation.variable_token_ne_variable_token <| by
                  intro hNames
                  exact hDepth <|
                    (GodelQuotation.bound_name_injective
                      hNames).symm
              exact FirstOrder.Derives.falsumElim
                (φ := targetValue ≐ₘ
                  numₘ(GodelQuotation.Numbered.variable_token
                    (GodelQuotation.bound_name
                      (canonical_project_shift_depth
                        cutoff depth))))
                (fs_zfc_support_raw_canonical_project_source_token_falsum
                  (GodelQuotation.Numbered.variable_token
                    (GodelQuotation.bound_name depth))
                  index sourceValue sourceDepth
                  hTokenNe hSourceDepth
                  hSourceEqualityBranch
                  hSourceTokenBranch hDepthEquality)

/-! ## 代码层函数性 -/

/-- 将代码条件的逐点全称式实例化到一个标准下标。 -/
private theorem fs_zfc_support_raw_canonical_project_shift_point_at
    {Γ : Context signature}
    (cutoff index : Nat)
    (sourceCode targetCode : SetTerm)
    (indexId : FreeVarId)
    (hSourceCode :
      Term.Admissible sourceCode SetSort.set)
    (hTargetCode :
      Term.Admissible targetCode SetSort.set)
    (hSourceFresh :
      ∀ id, indexId ≤ id →
        (SetSort.set, id) ∉
          Term.freeSupport sourceCode)
    (hTargetFresh :
      ∀ id, indexId ≤ id →
        (SetSort.set, id) ∉
          Term.freeSupport targetCode)
    (hPointwise :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[SetSort.set, indexId],
          (x#indexId ∈ₘ domₘ(sourceCode)) ⟶ₘ
            canonical_project_shift_token_condition_with_ids
              (numₘ(cutoff))
              (sourceCode ·ₘ x#indexId)
              (targetCode ·ₘ x#indexId)
              (indexId + 1) (indexId + 2)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (numₘ(index) ∈ₘ domₘ(sourceCode)) ⟶ₘ
        canonical_project_shift_token_condition_with_ids
          (numₘ(cutoff))
          (sourceCode ·ₘ numₘ(index))
          (targetCode ·ₘ numₘ(index))
          (indexId + 1) (indexId + 2) := by
  have hSourceClose :
      Term.closeFreeAt SetSort.set indexId 0 sourceCode =
        sourceCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 sourceCode
      hSourceCode.2
      (hSourceFresh indexId (Nat.le_refl indexId))
  have hTargetClose :
      Term.closeFreeAt SetSort.set indexId 0 targetCode =
        targetCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 targetCode
      hTargetCode.2
      (hTargetFresh indexId (Nat.le_refl indexId))
  have hSourceInnerClose :
      Term.closeFreeAt SetSort.set indexId 2 sourceCode =
        sourceCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 2 sourceCode
      hSourceCode.2
      (hSourceFresh indexId (Nat.le_refl indexId))
  have hTargetInnerClose :
      Term.closeFreeAt SetSort.set indexId 2 targetCode =
        targetCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 2 targetCode
      hTargetCode.2
      (hTargetFresh indexId (Nat.le_refl indexId))
  have hSourceDepthClose :
      Term.closeFreeAt SetSort.set (indexId + 1) 1
          sourceCode =
        sourceCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set (indexId + 1) 1 sourceCode
      hSourceCode.2
      (hSourceFresh (indexId + 1)
        (Nat.le_add_right indexId 1))
  have hSourceTargetDepthClose :
      Term.closeFreeAt SetSort.set (indexId + 2) 0
          sourceCode =
        sourceCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set (indexId + 2) 0 sourceCode
      hSourceCode.2
      (hSourceFresh (indexId + 2)
        (Nat.le_add_right indexId 2))
  have hTargetSourceDepthClose :
      Term.closeFreeAt SetSort.set (indexId + 1) 1
          targetCode =
        targetCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set (indexId + 1) 1 targetCode
      hTargetCode.2
      (hTargetFresh (indexId + 1)
        (Nat.le_add_right indexId 1))
  have hTargetDepthClose :
      Term.closeFreeAt SetSort.set (indexId + 2) 0
          targetCode =
        targetCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set (indexId + 2) 0 targetCode
      hTargetCode.2
      (hTargetFresh (indexId + 2)
        (Nat.le_add_right indexId 2))
  have hSourceOpen :
      Term.openAt SetSort.set 0 (numₘ(index)) sourceCode =
        sourceCode :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (numₘ(index)) sourceCode
      hSourceCode.2
  have hTargetOpen :
      Term.openAt SetSort.set 0 (numₘ(index)) targetCode =
        targetCode :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (numₘ(index)) targetCode
      hTargetCode.2
  have hSourceInnerOpen :
      Term.openAt SetSort.set 2 (numₘ(index)) sourceCode =
        sourceCode :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 (numₘ(index)) sourceCode
      hSourceCode.2
  have hTargetInnerOpen :
      Term.openAt SetSort.set 2 (numₘ(index)) targetCode =
        targetCode :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 (numₘ(index)) targetCode
      hTargetCode.2
  have hSourceDepthOpen :
      Term.openAt SetSort.set 1 (numₘ(index))
          (Term.closeFreeAt SetSort.set indexId 1
            (Term.closeFreeAt SetSort.set (indexId + 1) 0 sourceCode)) =
        Term.closeFreeAt SetSort.set (indexId + 1) 0 sourceCode := by
    rw [Term.openAt_closeFreeAt_eq_substituteFree]
    exact Term.substituteFree_eq_self_of_not_mem
      SetSort.set indexId (numₘ(index))
      (Term.closeFreeAt SetSort.set (indexId + 1) 0 sourceCode)
      (Term.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, indexId) SetSort.set (indexId + 1) 0 sourceCode
        (hSourceFresh indexId (Nat.le_refl indexId)))
  have hTargetDepthOpen :
      Term.openAt SetSort.set 1 (numₘ(index))
          (Term.closeFreeAt SetSort.set indexId 1
            (Term.closeFreeAt SetSort.set (indexId + 1) 0 targetCode)) =
        Term.closeFreeAt SetSort.set (indexId + 1) 0 targetCode := by
    rw [Term.openAt_closeFreeAt_eq_substituteFree]
    exact Term.substituteFree_eq_self_of_not_mem
      SetSort.set indexId (numₘ(index))
      (Term.closeFreeAt SetSort.set (indexId + 1) 0 targetCode)
      (Term.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, indexId) SetSort.set (indexId + 1) 0 targetCode
        (hTargetFresh indexId (Nat.le_refl indexId)))
  have hSourceTokenOpen :
      Term.openAt SetSort.set 2 (numₘ(index))
          (Term.closeFreeAt SetSort.set indexId 2
            (Term.closeFreeAt SetSort.set (indexId + 1) 1
              (Term.closeFreeAt SetSort.set (indexId + 2) 0 sourceCode))) =
        Term.closeFreeAt SetSort.set (indexId + 1) 1
          (Term.closeFreeAt SetSort.set (indexId + 2) 0 sourceCode) := by
    rw [Term.openAt_closeFreeAt_eq_substituteFree]
    exact Term.substituteFree_eq_self_of_not_mem
      SetSort.set indexId (numₘ(index))
      (Term.closeFreeAt SetSort.set (indexId + 1) 1
        (Term.closeFreeAt SetSort.set (indexId + 2) 0 sourceCode))
      (Term.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, indexId) SetSort.set (indexId + 1) 1
        (Term.closeFreeAt SetSort.set (indexId + 2) 0 sourceCode)
        (Term.not_mem_freeSupport_closeFreeAt_of_not_mem
          (SetSort.set, indexId) SetSort.set (indexId + 2) 0 sourceCode
          (hSourceFresh indexId (Nat.le_refl indexId))))
  have hTargetTokenOpen :
      Term.openAt SetSort.set 2 (numₘ(index))
          (Term.closeFreeAt SetSort.set indexId 2
            (Term.closeFreeAt SetSort.set (indexId + 1) 1
              (Term.closeFreeAt SetSort.set (indexId + 2) 0 targetCode))) =
        Term.closeFreeAt SetSort.set (indexId + 1) 1
          (Term.closeFreeAt SetSort.set (indexId + 2) 0 targetCode) := by
    rw [Term.openAt_closeFreeAt_eq_substituteFree]
    exact Term.substituteFree_eq_self_of_not_mem
      SetSort.set indexId (numₘ(index))
      (Term.closeFreeAt SetSort.set (indexId + 1) 1
        (Term.closeFreeAt SetSort.set (indexId + 2) 0 targetCode))
      (Term.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, indexId) SetSort.set (indexId + 1) 1
        (Term.closeFreeAt SetSort.set (indexId + 2) 0 targetCode)
        (Term.not_mem_freeSupport_closeFreeAt_of_not_mem
          (SetSort.set, indexId) SetSort.set (indexId + 2) 0 targetCode
          (hTargetFresh indexId (Nat.le_refl indexId))))
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := numₘ(index)) hPointwise
  simpa [canonical_project_shift_token_condition_with_ids,
    canonical_project_shift_fixed_token_condition,
    canonical_shifted_depth_condition,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Term.openAt, Term.closeFreeAt,
    set_variable, set_bound_variable,
    hSourceClose, hTargetClose,
    hSourceInnerClose, hTargetInnerClose,
    hSourceDepthClose,
    hTargetSourceDepthClose,
    hSourceOpen, hTargetOpen,
    hSourceInnerOpen, hTargetInnerOpen,
    hSourceDepthOpen, hTargetDepthOpen,
    hSourceTokenOpen, hTargetTokenOpen,
    GodelQuotation.gq_binder_shift_numeral_open,
    GodelQuotation.gq_binder_shift_numeral_close] using
    hAtRaw

/--
标准源 token 串和逐点 cutoff-shift 关系唯一决定任意满足代码条件的目标代码。

该结论只依赖有限序列函数外延和单 token 函数性；不要求两端属于 `FormulaCodeₘ`。
-/
theorem fs_zfc_support_raw_canonical_project_shift_code_unique
    {Γ : Context signature}
    {cutoff : Nat}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalProjectShiftTokens cutoff
        sourceTokens targetTokens)
    (sourceCode targetCode : SetTerm)
    (indexId : FreeVarId)
    (hSourceCode :
      Term.CheckCertificate sourceCode SetSort.set)
    (hTargetCode :
      Term.CheckCertificate targetCode SetSort.set)
    (hSourceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceCode ≐ₘ
          GodelQuotation.standard_token_sequence
            sourceTokens)
    (hSourceFresh :
      ∀ id, indexId ≤ id →
        (SetSort.set, id) ∉
          Term.freeSupport sourceCode)
    (hTargetFresh :
      ∀ id, indexId ≤ id →
        (SetSort.set, id) ∉
          Term.freeSupport targetCode)
    (hContextFresh :
      ∀ formula, formula ∈ Γ →
        ∀ id, indexId ≤ id →
          (SetSort.set, id) ∉
            Formula.freeSupport formula)
    (hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_project_shift_code_condition_with_ids
          (numₘ(cutoff)) sourceCode targetCode
          indexId (indexId + 1) (indexId + 2)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      targetCode ≐ₘ
        GodelQuotation.standard_token_sequence
          targetTokens := by
  rw [canonical_project_shift_code_condition_with_ids]
    at hCondition
  have hData :=
    FirstOrder.Derives.conjElimLeft hCondition
  have hPointwise :=
    FirstOrder.Derives.conjElimRight hCondition
  have hDomainEquality :=
    FirstOrder.Derives.conjElimRight hData
  have hFiniteData :=
    FirstOrder.Derives.conjElimLeft hData
  have hTargetFinite :=
    FirstOrder.Derives.conjElimRight hFiniteData
  have hTargetFunction :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        is_function_formula targetCode := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimLeft hTargetFinite
  have hSourceDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(sourceCode) ≐ₘ
          numₘ(sourceTokens.length) :=
    GodelQuotation.gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_quotation hFormula)
      sourceCode sourceTokens hSourceEquality
      hSourceCode
  have hTargetDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(targetCode) ≐ₘ
          numₘ(targetTokens.length) := by
    have hTargetSource :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          domₘ(targetCode) ≐ₘ domₘ(sourceCode) :=
      Metatheory.Derives.equality_symm hDomainEquality
    simpa [relation.length_eq] using
      Metatheory.Derives.equality_trans
        hTargetSource hSourceDomain
  apply
    GodelQuotation.gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_standard_sequence_semantics
          hFormula)
      (fun _ hFormula =>
        fs_zfc_support_raw_theory_sentence hFormula)
      targetCode targetTokens
      hTargetFunction hTargetDomain
      (hSource := hTargetCode)
  intro index targetToken hTargetGet
  rcases relation.getElem?_source_relation hTargetGet with
    ⟨sourceToken, hSourceGet, tokenRelation⟩
  have hReferencePointGq :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        ((numₘ(index) ∈ₘ
            domₘ(GodelQuotation.standard_token_sequence
              sourceTokens)) ∧ₘ
          ((GodelQuotation.standard_token_sequence
              sourceTokens ·ₘ numₘ(index)) ≐ₘ
            numₘ(sourceToken))) :=
    GodelQuotation.gq_standard_token_sequence_point_inversion
      (GodelQuotation.standard_token_sequence sourceTokens)
      sourceTokens
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set)
        (GodelQuotation.standard_token_sequence sourceTokens))
      hSourceGet
  have hReferencePoint :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ((numₘ(index) ∈ₘ
            domₘ(GodelQuotation.standard_token_sequence
              sourceTokens)) ∧ₘ
          ((GodelQuotation.standard_token_sequence
              sourceTokens ·ₘ numₘ(index)) ≐ₘ
            numₘ(sourceToken))) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation
              hFormula)
          hReferencePointGq
  have hSourcePoint :=
    GodelQuotation.gq_point_inversion_of_equality_of_theory
      sourceCode
      (GodelQuotation.standard_token_sequence sourceTokens)
      (numₘ(index)) (numₘ(sourceToken))
      hSourceEquality hReferencePoint
      (hLeft := hSourceCode)
  have hAt :=
    fs_zfc_support_raw_canonical_project_shift_point_at
      cutoff index sourceCode targetCode indexId
      hSourceCode.admissible hTargetCode.admissible
      hSourceFresh hTargetFresh
      hPointwise
  have hTokenCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_project_shift_token_condition_with_ids
          (numₘ(cutoff))
          (sourceCode ·ₘ numₘ(index))
          (targetCode ·ₘ numₘ(index))
          (indexId + 1) (indexId + 2) :=
    FirstOrder.Derives.impElim hAt
      (FirstOrder.Derives.conjElimLeft hSourcePoint)
  have hSourceAt :
      Term.Admissible
        (sourceCode ·ₘ numₘ(index)) SetSort.set :=
    function_application_term_admissible
      sourceCode (numₘ(index))
      hSourceCode.admissible
      (finite_numeral_term_admissible index)
  have hTargetAt :
      Term.Admissible
        (targetCode ·ₘ numₘ(index)) SetSort.set :=
    function_application_term_admissible
      targetCode (numₘ(index))
      hTargetCode.admissible
      (finite_numeral_term_admissible index)
  have hTargetAtFresh :
      ∀ id, indexId + 1 ≤ id →
        (SetSort.set, id) ∉
          Term.freeSupport
            (targetCode ·ₘ numₘ(index)) := by
    intro id hId
    simpa [Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport] using
      hTargetFresh id (Nat.le_trans
        (Nat.le_add_right indexId 1) hId)
  exact
    fs_zfc_support_raw_canonical_project_shift_token_unique
      (relation := tokenRelation)
      (sourceValue := sourceCode ·ₘ numₘ(index))
      (targetValue := targetCode ·ₘ numₘ(index))
      (freshBase := indexId + 1)
      (hSourceValue := hSourceAt)
      (hTargetValue := hTargetAt)
      (hSourceEquality := FirstOrder.Derives.conjElimRight hSourcePoint)
      (hTargetFresh := hTargetAtFresh)
      (hSourceFresh := by
        intro id hId
        simpa [Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport] using
          hSourceFresh id (Nat.le_trans
            (Nat.le_add_right indexId 1) hId))
      (hContextFresh := by
        intro formula hFormula id hId
        exact hContextFresh formula hFormula id
          (Nat.le_trans
            (Nat.le_add_right indexId 1) hId))
      (hCondition := hTokenCondition)

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
