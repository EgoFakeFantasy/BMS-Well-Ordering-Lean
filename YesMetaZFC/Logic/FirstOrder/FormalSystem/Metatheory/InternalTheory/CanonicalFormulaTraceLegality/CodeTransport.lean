import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTrace
/-!
# 规范公式轨迹的码运输与原子合法性
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false
/-! ## 公式码构造的对象等式运输 -/
/-- 已证明的名称码等式可穿过变量符号编码构造。 -/
theorem canonical_variable_code_term_congr_of_equality
    {T : SetTheory} {Γ : Context signature} (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] var_codeₘ(left) ≐ₘ var_codeₘ(right) := by
  exact Metatheory.Derives.unary_term_constructor_congr_of_equality
    (fun term => var_codeₘ(term))
    (fun term hTerm => variable_code_term_admissible term hTerm)
    (by intros; simp [Term.substituteFree])
    left right hLeft hRight hEquality
/-- 已证明的公式码等式可穿过否定码构造。 -/
theorem canonical_negation_code_term_congr_of_equality
    {T : SetTheory} {Γ : Context signature} (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] neg_codeₘ(left) ≐ₘ neg_codeₘ(right) := by
  exact Metatheory.Derives.unary_term_constructor_congr_of_equality
    (fun term => neg_codeₘ(term))
    (fun term hTerm => negation_formula_code_term_admissible term hTerm)
    (by intros; simp [Term.substituteFree])
    left right hLeft hRight hEquality
/-- 两组公式码等式可逐参数提升为蕴含码等式。 -/
theorem canonical_implication_code_term_congr_of_equalities
    {T : SetTheory} {Γ : Context signature} (left₁ left₂ right₁ right₂ : SetTerm) (hLeft₁ : Term.Admissible left₁ SetSort.set)
    (hLeft₂ : Term.Admissible left₂ SetSort.set) (hRight₁ : Term.Admissible right₁ SetSort.set) (hRight₂ : Term.Admissible right₂ SetSort.set)
    (hLeftEquality : Γ ⊢ₘ[T] left₁ ≐ₘ left₂) (hRightEquality : Γ ⊢ₘ[T] right₁ ≐ₘ right₂) :
    Γ ⊢ₘ[T]
      imp_codeₘ(left₁, right₁) ≐ₘ
        imp_codeₘ(left₂, right₂) := by
  exact Metatheory.Derives.binary_term_constructor_congr_of_equalities
    (fun left right => imp_codeₘ(left, right))
    (fun left right hLeft hRight =>
      implication_formula_code_term_admissible left right hLeft hRight)
    (by intros; simp [Term.substituteFree])
    left₁ left₂ right₁ right₂
    hLeft₁ hLeft₂ hRight₁ hRight₂
    hLeftEquality hRightEquality
/-- 两组参数等式可逐参数提升为全称量词码等式。 -/
theorem canonical_universal_code_term_congr_of_equalities
    {T : SetTheory} {Γ : Context signature} (variable₁ variable₂ body₁ body₂ : SetTerm) (hVariable₁ : Term.Admissible variable₁ SetSort.set)
    (hVariable₂ : Term.Admissible variable₂ SetSort.set) (hBody₁ : Term.Admissible body₁ SetSort.set) (hBody₂ : Term.Admissible body₂ SetSort.set)
    (hVariableEquality : Γ ⊢ₘ[T] variable₁ ≐ₘ variable₂) (hBodyEquality : Γ ⊢ₘ[T] body₁ ≐ₘ body₂) :
    Γ ⊢ₘ[T]
      forall_codeₘ(variable₁, body₁) ≐ₘ
        forall_codeₘ(variable₂, body₂) := by
  exact Metatheory.Derives.binary_term_constructor_congr_of_equalities
    (fun boundVariable body => forall_codeₘ(boundVariable, body))
    (fun boundVariable body hVariable hBody =>
      universal_formula_code_term_admissible
        boundVariable body hVariable hBody)
    (by intros; simp [Term.substituteFree])
    variable₁ variable₂ body₁ body₂
    hVariable₁ hVariable₂ hBody₁ hBody₂
    hVariableEquality hBodyEquality
/--
两组项码等式可逐参数提升为隶属原子码等式。
隶属原子是五段有限序列拼接；这里直接复用公共拼接合同，而不把具体关系符号的
替换上下文泄漏给上层 schema 分类器。
-/
theorem canonical_membership_atomic_code_term_congr_of_equalities
    {T : SetTheory} {Γ : Context signature} (left₁ left₂ right₁ right₂ : SetTerm) (hLeft₁ : Term.Admissible left₁ SetSort.set)
    (hLeft₂ : Term.Admissible left₂ SetSort.set) (hRight₁ : Term.Admissible right₁ SetSort.set) (hRight₂ : Term.Admissible right₂ SetSort.set)
    (hLeftEquality : Γ ⊢ₘ[T] left₁ ≐ₘ left₂) (hRightEquality : Γ ⊢ₘ[T] right₁ ≐ₘ right₂) :
    Γ ⊢ₘ[T]
      membership_atomic_formula_code_term left₁ right₁ ≐ₘ
        membership_atomic_formula_code_term left₂ right₂ := by
  exact Metatheory.Derives.binary_term_constructor_congr_of_equalities
    membership_atomic_formula_code_term
    (fun left right hLeft hRight =>
      binary_atomic_formula_code_term_admissible
        membership_symbol_code_term left right
        membership_symbol_code_term_admissible hLeft hRight)
    (by
      intro parameter replacement left right
      have hNumeralFixed (number : Nat) :
          Term.substituteFree SetSort.set parameter replacement
              (numₘ(number)) =
            numₘ(number) := by
        apply Term.substituteFree_eq_self_of_not_mem
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil
      simp [membership_atomic_formula_code_term,
        binary_atomic_formula_code_term, Term.substituteFree,
        hNumeralFixed])
    left₁ left₂ right₁ right₂
    hLeft₁ hLeft₂ hRight₁ hRight₂
    hLeftEquality hRightEquality

/-- 两组项码等式可逐参数提升为等式公式码运算的等式。 -/
theorem canonical_equality_code_term_congr_of_equalities
    {T : SetTheory} {Γ : Context signature}
    (left₁ left₂ right₁ right₂ : SetTerm)
    (hLeft₁ : Term.Admissible left₁ SetSort.set)
    (hLeft₂ : Term.Admissible left₂ SetSort.set)
    (hRight₁ : Term.Admissible right₁ SetSort.set)
    (hRight₂ : Term.Admissible right₂ SetSort.set)
    (hLeftEquality : Γ ⊢ₘ[T] left₁ ≐ₘ left₂)
    (hRightEquality : Γ ⊢ₘ[T] right₁ ≐ₘ right₂) :
    Γ ⊢ₘ[T]
      eq_codeₘ(left₁, right₁) ≐ₘ
        eq_codeₘ(left₂, right₂) := by
  exact
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      (fun left right => eq_codeₘ(left, right))
      (fun left right hLeft hRight =>
        equality_formula_code_term_admissible
          left right hLeft hRight)
      (by intros; simp [Term.substituteFree])
      left₁ left₂ right₁ right₂
      hLeft₁ hLeft₂ hRight₁ hRight₂
      hLeftEquality hRightEquality

/-- 两组项码等式可逐参数提升为项目子集原子码等式。 -/
theorem canonical_project_subset_atomic_code_term_congr_of_equalities
    {T : SetTheory} {Γ : Context signature}
    (left₁ left₂ right₁ right₂ : SetTerm)
    (hLeft₁ : Term.Admissible left₁ SetSort.set)
    (hLeft₂ : Term.Admissible left₂ SetSort.set)
    (hRight₁ : Term.Admissible right₁ SetSort.set)
    (hRight₂ : Term.Admissible right₂ SetSort.set)
    (hLeftEquality : Γ ⊢ₘ[T] left₁ ≐ₘ left₂)
    (hRightEquality : Γ ⊢ₘ[T] right₁ ≐ₘ right₂) :
    Γ ⊢ₘ[T]
      project_subset_atomic_code_term left₁ right₁ ≐ₘ
        project_subset_atomic_code_term left₂ right₂ := by
  exact
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      project_subset_atomic_code_term
      (fun left right hLeft hRight =>
        canonical_project_subset_atomic_code_term_admissible
          left right hLeft hRight)
      (by
        intro parameter replacement left right
        have hNumeralFixed (number : Nat) :
            Term.substituteFree SetSort.set parameter replacement
                (numₘ(number)) =
              numₘ(number) := by
          apply Term.substituteFree_eq_self_of_not_mem
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil
        simp [project_subset_atomic_code_term,
          GodelQuotation.Numbered.argument_sequence,
          GodelQuotation.standard_sequence_from,
          Term.substituteFree, hNumeralFixed])
      left₁ left₂ right₁ right₂
      hLeft₁ hLeft₂ hRight₁ hRight₂
      hLeftEquality hRightEquality

/-- 两组公式码等式可逐参数提升为合取缩写码等式。 -/
theorem canonical_conjunction_code_term_congr_of_equalities
    {T : SetTheory} {Γ : Context signature} (left₁ left₂ right₁ right₂ : SetTerm) (hLeft₁ : Term.Admissible left₁ SetSort.set)
    (hLeft₂ : Term.Admissible left₂ SetSort.set) (hRight₁ : Term.Admissible right₁ SetSort.set) (hRight₂ : Term.Admissible right₂ SetSort.set)
    (hLeftEquality : Γ ⊢ₘ[T] left₁ ≐ₘ left₂) (hRightEquality : Γ ⊢ₘ[T] right₁ ≐ₘ right₂) :
    Γ ⊢ₘ[T]
      conjunction_formula_code_term left₁ right₁ ≐ₘ
        conjunction_formula_code_term left₂ right₂ := by
  have hNegRight₁ :=
    negation_formula_code_term_admissible right₁ hRight₁
  have hNegRight₂ :=
    negation_formula_code_term_admissible right₂ hRight₂
  have hNegRightEquality :=
    canonical_negation_code_term_congr_of_equality
      right₁ right₂ hRight₁ hRight₂ hRightEquality
  have hImplicationEquality :=
    canonical_implication_code_term_congr_of_equalities
      left₁ left₂ (neg_codeₘ(right₁)) (neg_codeₘ(right₂))
      hLeft₁ hLeft₂ hNegRight₁ hNegRight₂
      hLeftEquality hNegRightEquality
  exact canonical_negation_code_term_congr_of_equality (imp_codeₘ(left₁, neg_codeₘ(right₁))) (imp_codeₘ(left₂, neg_codeₘ(right₂)))
    (implication_formula_code_term_admissible
      left₁ (neg_codeₘ(right₁)) hLeft₁ hNegRight₁) (implication_formula_code_term_admissible
      left₂ (neg_codeₘ(right₂)) hLeft₂ hNegRight₂)
    hImplicationEquality
/-- 两组参数等式可逐参数提升为存在量词缩写码等式。 -/
theorem canonical_existential_code_term_congr_of_equalities
    {T : SetTheory} {Γ : Context signature} (variable₁ variable₂ body₁ body₂ : SetTerm) (hVariable₁ : Term.Admissible variable₁ SetSort.set)
    (hVariable₂ : Term.Admissible variable₂ SetSort.set) (hBody₁ : Term.Admissible body₁ SetSort.set) (hBody₂ : Term.Admissible body₂ SetSort.set)
    (hVariableEquality : Γ ⊢ₘ[T] variable₁ ≐ₘ variable₂) (hBodyEquality : Γ ⊢ₘ[T] body₁ ≐ₘ body₂) :
    Γ ⊢ₘ[T]
      existential_formula_code_term variable₁ body₁ ≐ₘ
        existential_formula_code_term variable₂ body₂ := by
  have hNegBody₁ :=
    negation_formula_code_term_admissible body₁ hBody₁
  have hNegBody₂ :=
    negation_formula_code_term_admissible body₂ hBody₂
  have hNegBodyEquality :=
    canonical_negation_code_term_congr_of_equality
      body₁ body₂ hBody₁ hBody₂ hBodyEquality
  have hUniversalEquality :=
    canonical_universal_code_term_congr_of_equalities
      variable₁ variable₂ (neg_codeₘ(body₁)) (neg_codeₘ(body₂))
      hVariable₁ hVariable₂ hNegBody₁ hNegBody₂
      hVariableEquality hNegBodyEquality
  exact canonical_negation_code_term_congr_of_equality (forall_codeₘ(variable₁, neg_codeₘ(body₁))) (forall_codeₘ(variable₂, neg_codeₘ(body₂)))
    (universal_formula_code_term_admissible
      variable₁ (neg_codeₘ(body₁)) hVariable₁ hNegBody₁) (universal_formula_code_term_admissible
      variable₂ (neg_codeₘ(body₂)) hVariable₂ hNegBody₂)
    hUniversalEquality
/-- quotation 深度等式可提升为规范 binder 变量码等式。 -/
theorem canonical_binder_variable_code_term_congr_of_equality
    {T : SetTheory} {Γ : Context signature} (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      canonical_binder_variable_code_term left ≐ₘ
        canonical_binder_variable_code_term right := by
  let parameter := FreshVariable.fresh_id SetSort.set
    [left ≐ₘ left]
  let productContext : SetTerm :=
    numₘ(2) *ₘ x#parameter
  have hProductContext :
      Term.Admissible productContext SetSort.set := by
    dsimp [productContext]
    exact natural_multiplication_term_admissible _ _ (finite_numeral_term_admissible 2) (set_variable_admissible parameter)
  have hFresh : (SetSort.set, parameter) ∉ Term.freeSupport left := by
    dsimp [parameter]
    exact FreshVariable.fresh_term_not_mem_m SetSort.set left
  have hTwoFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter
          replacement (numₘ(2)) =
        numₘ(2) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hProductRaw :=
    Metatheory.Derives.term_substituteFree_congr_of_equality (T := T) (Γ := Γ)
      SetSort.set parameter left right productContext
      hLeft hRight hProductContext hFresh hEquality
  have hProduct :
      Γ ⊢ₘ[T] (numₘ(2) *ₘ left) ≐ₘ (numₘ(2) *ₘ right) := by
    simpa [productContext, Term.substituteFree,
      set_variable, hTwoFixed] using hProductRaw
  have hLeftProduct :
      Term.Admissible (numₘ(2) *ₘ left) SetSort.set :=
    natural_multiplication_term_admissible _ _ (finite_numeral_term_admissible 2) hLeft
  have hRightProduct :
      Term.Admissible (numₘ(2) *ₘ right) SetSort.set :=
    natural_multiplication_term_admissible _ _ (finite_numeral_term_admissible 2) hRight
  have hSuccessor :=
    successor_term_congr_of_equality (numₘ(2) *ₘ left) (numₘ(2) *ₘ right)
      hLeftProduct hRightProduct hProduct
  exact canonical_variable_code_term_congr_of_equality (canonical_binder_name_term left) (canonical_binder_name_term right)
    (successor_term_admissible _ hLeftProduct) (successor_term_admissible _ hRightProduct)
    hSuccessor
/--
外部深度 `depth` 的 named quotation 变量码等于分类器使用的对象规范 binder 变量码。
乘法不是 Lean 定义规约，而由标准 numeral 算术的对象证明给出，因此该引理是后续
原子和全称行共享的必要桥梁。
-/
theorem canonical_binder_variable_code_numeral_derives (depth : Nat) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name depth) ≐ₘ
        canonical_binder_variable_code_term (numₘ(depth)) := by
  have hMultiplication :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(2 * depth) ≐ₘ (numₘ(2) *ₘ numₘ(depth)) :=
    GodelQuotation.gq_weaken_standard_sequence (GodelQuotation.standard_token_sequence_finite_numeral_multiplication
        2 depth)
  have hProduct :
      Term.Admissible (numₘ(2) *ₘ numₘ(depth)) SetSort.set :=
    natural_multiplication_term_admissible (numₘ(2)) (numₘ(depth)) (finite_numeral_term_admissible 2) (finite_numeral_term_admissible depth)
  have hSuccessor :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        Sₘ(numₘ(2 * depth)) ≐ₘ
          Sₘ(numₘ(2) *ₘ numₘ(depth)) :=
    successor_term_congr_of_equality (numₘ(2 * depth)) (numₘ(2) *ₘ numₘ(depth)) (finite_numeral_term_admissible (2 * depth))
      hProduct hMultiplication
  have hName :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(GodelQuotation.bound_name depth) ≐ₘ
          canonical_binder_name_term (numₘ(depth)) := by
    simpa [GodelQuotation.bound_name, finite_numeral_term] using
      hSuccessor
  exact canonical_variable_code_term_congr_of_equality (numₘ(GodelQuotation.bound_name depth)) (canonical_binder_name_term (numₘ(depth)))
    (finite_numeral_term_admissible (GodelQuotation.bound_name depth)) (successor_term_admissible (numₘ(2) *ₘ numₘ(depth)) hProduct)
    hName
/-! ## 规范 cutoff-shift 的对象算术 -/
/--
对内部两个 binder 新鲜的 admissible 替换可穿过显式编号的变量 cutoff-shift 条件。
该条件内部连续占用 `variableDepthId` 与 `variableDepthId + 1` 两个 binder；调用方只需
保证外部替换参数与二者不同。此接口使外层原子见证代入保持定义级稳定。
-/
theorem canonical_shifted_variable_code_condition_with_id_substitute_of_fresh (cutoff entryDepth leftVariable rightVariable replacement :
      SetTerm) (parameter variableDepthId : FreeVarId) (hParameterNeDepth : parameter ≠ variableDepthId)
    (hParameterNeTargetDepth : parameter ≠ variableDepthId + 1) (hReplacement : Term.Admissible replacement SetSort.set) (hReplacementFreshDepth :
      (SetSort.set, variableDepthId) ∉
        Term.freeSupport replacement) (hReplacementFreshTargetDepth : (SetSort.set, variableDepthId + 1) ∉
        Term.freeSupport replacement) :
    Formula.substituteFree SetSort.set parameter replacement (canonical_shifted_variable_code_condition_with_id
          cutoff entryDepth leftVariable rightVariable
          variableDepthId) =
      canonical_shifted_variable_code_condition_with_id (Term.substituteFree SetSort.set parameter replacement cutoff)
        (Term.substituteFree SetSort.set parameter replacement entryDepth) (Term.substituteFree SetSort.set parameter replacement leftVariable)
        (Term.substituteFree SetSort.set parameter replacement rightVariable)
        variableDepthId := by
  have hDepthNeParameter : variableDepthId ≠ parameter :=
    Ne.symm hParameterNeDepth
  have hTargetDepthNeParameter :
      variableDepthId + 1 ≠ parameter :=
    Ne.symm hParameterNeTargetDepth
  have hTwoFixed :
      Term.substituteFree SetSort.set parameter replacement (numₘ(2)) =
        numₘ(2) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  unfold canonical_shifted_variable_code_condition_with_id
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set parameter variableDepthId 0 replacement _
    hParameterNeDepth hReplacement.2
    hReplacementFreshDepth]
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set parameter (variableDepthId + 1) 0 replacement _
    hParameterNeTargetDepth hReplacement.2
    hReplacementFreshTargetDepth]
  simp [
    canonical_shifted_variable_target_condition,
    canonical_shifted_depth_condition,
    canonical_binder_variable_code_term,
    canonical_binder_name_term,
    Formula.substituteFree,
    Term.substituteFree,
    set_variable,
    hDepthNeParameter,
    hTargetDepthNeParameter,
    hTwoFixed]
/--
闭项替换可穿过显式编号的变量 cutoff-shift 条件。
-/
theorem canonical_shifted_variable_code_condition_with_id_substitute_closed (cutoff entryDepth leftVariable rightVariable replacement :
      SetTerm) (parameter variableDepthId : FreeVarId) (hParameterNeDepth : parameter ≠ variableDepthId)
    (hParameterNeTargetDepth : parameter ≠ variableDepthId + 1) (hReplacement : Term.Admissible replacement SetSort.set)
    (hReplacementClosed : Term.freeSupport replacement = []) :
    Formula.substituteFree SetSort.set parameter replacement (canonical_shifted_variable_code_condition_with_id
          cutoff entryDepth leftVariable rightVariable
          variableDepthId) =
      canonical_shifted_variable_code_condition_with_id (Term.substituteFree SetSort.set parameter replacement cutoff)
        (Term.substituteFree SetSort.set parameter replacement entryDepth) (Term.substituteFree SetSort.set parameter replacement leftVariable)
        (Term.substituteFree SetSort.set parameter replacement rightVariable)
        variableDepthId := by
  apply canonical_shifted_variable_code_condition_with_id_substitute_of_fresh
    cutoff entryDepth leftVariable rightVariable replacement
    parameter variableDepthId
    hParameterNeDepth hParameterNeTargetDepth hReplacement
  · rw [hReplacementClosed]
    exact List.not_mem_nil
  · rw [hReplacementClosed]
    exact List.not_mem_nil
/--
对全部内部 binder 新鲜的 admissible 替换逐参数穿过原子 cutoff-shift 条件。
四个外层变量码 binder 与两组连续深度 binder 都保持固定；因此该定理正好提供
对象等式运输所需的定义级稳定性。
-/
theorem canonical_project_atomic_shift_condition_with_ids_substitute_of_fresh (cutoff entryDepth leftCode rightCode replacement : SetTerm)
    (sourceId leftFirstId rightFirstId leftSecondId rightSecondId
      firstDepthId secondDepthId : FreeVarId) (hSourceNeLeftFirst : sourceId ≠ leftFirstId) (hSourceNeRightFirst : sourceId ≠ rightFirstId)
    (hSourceNeLeftSecond : sourceId ≠ leftSecondId) (hSourceNeRightSecond : sourceId ≠ rightSecondId) (hSourceNeFirstDepth : sourceId ≠ firstDepthId)
    (hSourceNeFirstTargetDepth : sourceId ≠ firstDepthId + 1) (hSourceNeSecondDepth : sourceId ≠ secondDepthId)
    (hSourceNeSecondTargetDepth : sourceId ≠ secondDepthId + 1) (hReplacement : Term.Admissible replacement SetSort.set) (hReplacementFreshLeftFirst :
      (SetSort.set, leftFirstId) ∉ Term.freeSupport replacement) (hReplacementFreshRightFirst : (SetSort.set, rightFirstId) ∉ Term.freeSupport replacement)
    (hReplacementFreshLeftSecond : (SetSort.set, leftSecondId) ∉ Term.freeSupport replacement) (hReplacementFreshRightSecond :
      (SetSort.set, rightSecondId) ∉ Term.freeSupport replacement) (hReplacementFreshFirstDepth : (SetSort.set, firstDepthId) ∉ Term.freeSupport replacement)
    (hReplacementFreshFirstTargetDepth : (SetSort.set, firstDepthId + 1) ∉
        Term.freeSupport replacement) (hReplacementFreshSecondDepth : (SetSort.set, secondDepthId) ∉ Term.freeSupport replacement)
    (hReplacementFreshSecondTargetDepth : (SetSort.set, secondDepthId + 1) ∉
        Term.freeSupport replacement) :
    Formula.substituteFree SetSort.set sourceId replacement (canonical_project_atomic_shift_condition_with_ids
          cutoff entryDepth leftCode rightCode
          leftFirstId rightFirstId leftSecondId rightSecondId
          firstDepthId secondDepthId) =
      canonical_project_atomic_shift_condition_with_ids (Term.substituteFree SetSort.set sourceId replacement cutoff)
        (Term.substituteFree SetSort.set sourceId replacement entryDepth) (Term.substituteFree SetSort.set sourceId replacement leftCode)
        (Term.substituteFree SetSort.set sourceId replacement rightCode)
        leftFirstId rightFirstId leftSecondId rightSecondId
        firstDepthId secondDepthId := by
  have hLeftFirstFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#leftFirstId) =
        x#leftFirstId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hSourceNeLeftFirst]
  have hRightFirstFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#rightFirstId) =
        x#rightFirstId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hSourceNeRightFirst]
  have hLeftSecondFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#leftSecondId) =
        x#leftSecondId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hSourceNeLeftSecond]
  have hRightSecondFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#rightSecondId) =
        x#rightSecondId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hSourceNeRightSecond]
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hFirstShiftSubstitution :=
    canonical_shifted_variable_code_condition_with_id_substitute_of_fresh
      cutoff entryDepth (x#leftFirstId) (x#rightFirstId)
      replacement sourceId firstDepthId
      hSourceNeFirstDepth hSourceNeFirstTargetDepth
      hReplacement
      hReplacementFreshFirstDepth
      hReplacementFreshFirstTargetDepth
  have hSecondShiftSubstitution :=
    canonical_shifted_variable_code_condition_with_id_substitute_of_fresh
      cutoff entryDepth (x#leftSecondId) (x#rightSecondId)
      replacement sourceId secondDepthId
      hSourceNeSecondDepth hSourceNeSecondTargetDepth
      hReplacement
      hReplacementFreshSecondDepth
      hReplacementFreshSecondTargetDepth
  unfold canonical_project_atomic_shift_condition_with_ids
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set sourceId leftFirstId 0 replacement _
    hSourceNeLeftFirst hReplacement.2
    hReplacementFreshLeftFirst]
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set sourceId rightFirstId 0 replacement _
    hSourceNeRightFirst hReplacement.2
    hReplacementFreshRightFirst]
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set sourceId leftSecondId 0 replacement _
    hSourceNeLeftSecond hReplacement.2
    hReplacementFreshLeftSecond]
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set sourceId rightSecondId 0 replacement _
    hSourceNeRightSecond hReplacement.2
    hReplacementFreshRightSecond]
  simp [Formula.substituteFree, Term.substituteFree, set_variable,
    GodelQuotation.Numbered.argument_sequence,
    GodelQuotation.standard_sequence_from,
    hLeftFirstFixed, hRightFirstFixed,
    hLeftSecondFixed, hRightSecondFixed,
    hNumeralFixed,
    hFirstShiftSubstitution, hSecondShiftSubstitution]
  rfl
/--
闭项替换逐参数穿过显式编号的原子 cutoff-shift 条件。
-/
theorem canonical_project_atomic_shift_condition_with_ids_substitute_closed (cutoff entryDepth leftCode rightCode replacement : SetTerm)
    (sourceId leftFirstId rightFirstId leftSecondId rightSecondId
      firstDepthId secondDepthId : FreeVarId) (hSourceNeLeftFirst : sourceId ≠ leftFirstId) (hSourceNeRightFirst : sourceId ≠ rightFirstId)
    (hSourceNeLeftSecond : sourceId ≠ leftSecondId) (hSourceNeRightSecond : sourceId ≠ rightSecondId) (hSourceNeFirstDepth : sourceId ≠ firstDepthId)
    (hSourceNeFirstTargetDepth : sourceId ≠ firstDepthId + 1) (hSourceNeSecondDepth : sourceId ≠ secondDepthId)
    (hSourceNeSecondTargetDepth : sourceId ≠ secondDepthId + 1) (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement) :
    Formula.substituteFree SetSort.set sourceId replacement (canonical_project_atomic_shift_condition_with_ids
          cutoff entryDepth leftCode rightCode
          leftFirstId rightFirstId leftSecondId rightSecondId
          firstDepthId secondDepthId) =
      canonical_project_atomic_shift_condition_with_ids (Term.substituteFree SetSort.set sourceId replacement cutoff)
        (Term.substituteFree SetSort.set sourceId replacement entryDepth) (Term.substituteFree SetSort.set sourceId replacement leftCode)
        (Term.substituteFree SetSort.set sourceId replacement rightCode)
        leftFirstId rightFirstId leftSecondId rightSecondId
        firstDepthId secondDepthId := by
  apply canonical_project_atomic_shift_condition_with_ids_substitute_of_fresh
    cutoff entryDepth leftCode rightCode replacement
    sourceId leftFirstId rightFirstId leftSecondId rightSecondId
    firstDepthId secondDepthId
    hSourceNeLeftFirst hSourceNeRightFirst
    hSourceNeLeftSecond hSourceNeRightSecond
    hSourceNeFirstDepth hSourceNeFirstTargetDepth
    hSourceNeSecondDepth hSourceNeSecondTargetDepth
    hReplacement.1
  all_goals
    rw [hReplacement.2]
    exact List.not_mem_nil
/-- 标准 numeral 深度满足规范 cutoff-shift 的对象算术条件。 -/
theorem canonical_shifted_depth_condition_numeral_derives (cutoff sourceDepth : Nat) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_shifted_depth_condition (numₘ(cutoff)) (numₘ(sourceDepth)) (numₘ(canonical_project_shift_depth
          cutoff sourceDepth)) := by
  have hCutoff :=
    finite_numeral_term_admissible cutoff
  have hSource :=
    finite_numeral_term_admissible sourceDepth
  have hTarget :=
    finite_numeral_term_admissible (canonical_project_shift_depth cutoff sourceDepth)
  have hLeftAdmissible :
      Formula.Admissible (((numₘ(sourceDepth) ∈ₘ numₘ(cutoff)) ∧ₘ (numₘ(canonical_project_shift_depth
              cutoff sourceDepth) ≐ₘ
            numₘ(sourceDepth)))) :=
    Formula.Admissible.conj (membership_formula_admissible hSource hCutoff) (Formula.Admissible.equal hTarget hSource)
  have hRightAdmissible :
      Formula.Admissible (((numₘ(sourceDepth) ≐ₘ numₘ(cutoff)) ∨ₘ (numₘ(cutoff) ∈ₘ numₘ(sourceDepth))) ∧ₘ (numₘ(canonical_project_shift_depth
              cutoff sourceDepth) ≐ₘ
            Sₘ(numₘ(sourceDepth)))) :=
    Formula.Admissible.conj (Formula.Admissible.disj (Formula.Admissible.equal hSource hCutoff) (membership_formula_admissible hCutoff hSource))
      (Formula.Admissible.equal hTarget (successor_term_admissible (numₘ(sourceDepth)) hSource))
  unfold canonical_shifted_depth_condition
  by_cases hBelow : sourceDepth < cutoff
  · nd_apply FirstOrder.Derives.disjIntroLeft
    apply FirstOrder.Derives.conjIntro
    · exact GodelQuotation.gq_weaken_standard_sequence (GodelQuotation.standard_sequence_finite_numeral_mem_of_lt
          sourceDepth cutoff hBelow)
    · simpa [canonical_project_shift_depth_of_lt hBelow] using
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) (numₘ(sourceDepth)))
  · have hCutoffLe : cutoff ≤ sourceDepth :=
      Nat.le_of_not_gt hBelow
    nd_apply FirstOrder.Derives.disjIntroRight
    apply FirstOrder.Derives.conjIntro
    · by_cases hEqual : sourceDepth = cutoff
      · subst sourceDepth
        exact FirstOrder.Derives.disjIntroLeft
          (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set) (numₘ(cutoff)))
      · have hStrict : cutoff < sourceDepth := by
          omega
        exact FirstOrder.Derives.disjIntroRight
          (GodelQuotation.gq_weaken_standard_sequence
            (GodelQuotation.standard_sequence_finite_numeral_mem_of_lt
              cutoff sourceDepth hStrict))
    · simpa [
        canonical_project_shift_depth_of_le hCutoffLe,
        finite_numeral_term] using
          (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set) (Sₘ(numₘ(sourceDepth))))
/--
显式深度见证版本的规范变量 cutoff-shift，由两个标准 numeral 深度直接给出。
-/
theorem canonical_shifted_variable_code_condition_with_id_numeral_derives (cutoff entryDepth sourceDepth : Nat) (variableDepthId : FreeVarId)
    (hSourceDepth : sourceDepth < entryDepth) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_shifted_variable_code_condition_with_id (numₘ(cutoff)) (numₘ(entryDepth)) (GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.bound_name sourceDepth)) (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name (canonical_project_shift_depth
              cutoff sourceDepth)))
        variableDepthId := by
  let targetDepth :=
    canonical_project_shift_depth cutoff sourceDepth
  have hCutoff :=
    finite_numeral_term_admissible cutoff
  have hEntryDepth :=
    finite_numeral_term_admissible entryDepth
  have hSourceDepthTerm :=
    finite_numeral_term_admissible sourceDepth
  have hTargetDepthTerm :=
    finite_numeral_term_admissible targetDepth
  have hLeftVariable :=
    variable_code_term_admissible (numₘ(GodelQuotation.bound_name sourceDepth)) (finite_numeral_term_admissible (GodelQuotation.bound_name sourceDepth))
  have hRightVariable :=
    variable_code_term_admissible (numₘ(GodelQuotation.bound_name targetDepth)) (finite_numeral_term_admissible (GodelQuotation.bound_name targetDepth))
  have hNumeralOpen (number depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term (numₘ(number)) =
        numₘ(number) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term (numₘ(number)) (finite_numeral_term_admissible number).2
  have hNumeralClose (number : Nat) (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth (numₘ(number)) =
        numₘ(number) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth (numₘ(number)) (finite_numeral_term_admissible number).2 (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hLeftVariableOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name sourceDepth)) =
        GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name sourceDepth) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name sourceDepth))
      hLeftVariable.2
  have hLeftVariableClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name sourceDepth)) =
        GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name sourceDepth) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name sourceDepth))
      hLeftVariable.2 (by
        simp [Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport])
  have hRightVariableOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name targetDepth)) =
        GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name targetDepth) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name targetDepth))
      hRightVariable.2
  have hRightVariableClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name targetDepth)) =
        GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name targetDepth) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name targetDepth))
      hRightVariable.2 (by
        simp [Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport])
  have hNumeralSubstitute (id : FreeVarId) (replacement : SetTerm) (number : Nat) :
      Term.substituteFree SetSort.set id replacement (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hLeftVariableSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name sourceDepth)) =
        GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name sourceDepth) := by
    apply Term.substituteFree_eq_self_of_not_mem
    simp [Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport]
  have hRightVariableSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name targetDepth)) =
        GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name targetDepth) := by
    apply Term.substituteFree_eq_self_of_not_mem
    simp [Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport]
  have hTarget :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        ∃ₘ[SetSort.set, variableDepthId + 1],
          canonical_shifted_variable_target_condition (numₘ(cutoff)) (numₘ(sourceDepth)) (GodelQuotation.Numbered.named_variable_code
              (GodelQuotation.bound_name targetDepth)) (x#(variableDepthId + 1)) := by
    nd_apply FirstOrder.Derives.exists_intro
      (term := numₘ(targetDepth))
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    simpa [
      canonical_shifted_variable_target_condition,
      canonical_shifted_depth_condition,
      canonical_binder_variable_code_term,
      canonical_binder_name_term,
      Formula.substituteFree,
      Formula.next_depth,
      Term.substituteFree,
      set_variable,
      hNumeralSubstitute,
      hRightVariableSubstitute] using (FirstOrder.Derives.conjIntro (by
          simpa [targetDepth] using
            canonical_shifted_depth_condition_numeral_derives
              cutoff sourceDepth) (by
          simpa [targetDepth] using
            canonical_binder_variable_code_numeral_derives
              targetDepth))
  rw [canonical_shifted_variable_code_condition_with_id]
  nd_apply FirstOrder.Derives.exists_intro
    (term := numₘ(sourceDepth))
  rw [Formula.openAt_closeFreeAt_eq_substituteFree]
  simpa [
    canonical_shifted_variable_target_condition,
    canonical_shifted_depth_condition,
    canonical_binder_variable_code_term,
    canonical_binder_name_term,
    Formula.openAt,
    Formula.closeFreeAt,
    Formula.next_depth,
    Formula.substituteFree,
    Term.openAt,
    Term.closeFreeAt,
    Term.substituteFree,
    set_variable,
    set_bound_variable,
    hNumeralOpen,
    hNumeralClose,
    hLeftVariableOpen,
    hLeftVariableClose,
    hRightVariableOpen,
    hRightVariableClose,
    hNumeralSubstitute,
    hLeftVariableSubstitute,
    hRightVariableSubstitute] using (FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro (GodelQuotation.gq_weaken_standard_sequence
          (GodelQuotation.standard_sequence_finite_numeral_mem_of_lt
            sourceDepth entryDepth hSourceDepth)) (canonical_binder_variable_code_numeral_derives
          sourceDepth))
      hTarget)
/-! ## 规范 scope 变量的对象见证 -/
/--
把数码 scope 的规范变量见证沿对象深度等式运输到任意闭 quotation 项。
轨迹行读取出的深度是标准序列应用，而不是 Lean 定义上的数码；保留这一层运输可使
原子行直接使用实际的逐点读取项，而无需改变分类器中由该项决定的新鲜 binder 编号。
-/
theorem canonical_scoped_variable_code_condition_with_id_of_depth_equality
    {Γ : Context signature} (scopeDepth variableDepth : Nat) (scope : SetTerm) (variableDepthId : FreeVarId)
    (hScope : GodelQuotation.Numbered.CodeBoundary scope) (hScopeValue :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        scope ≐ₘ numₘ(scopeDepth)) (hVariableDepth : variableDepth < scopeDepth) :
    Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_scoped_variable_code_condition_with_id
        scope (GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name variableDepth))
        variableDepthId := by
  have hMembershipNumeral :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(variableDepth) ∈ₘ numₘ(scopeDepth) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) (GodelQuotation.gq_weaken_standard_sequence
        (GodelQuotation.standard_sequence_finite_numeral_mem_of_lt
          variableDepth scopeDepth hVariableDepth))
  have hMembershipIff :=
    membership_right_iff_of_equality (numₘ(variableDepth))
      scope (numₘ(scopeDepth)) (finite_numeral_term_admissible variableDepth)
      hScope.1 (finite_numeral_term_admissible scopeDepth)
      hScopeValue
  have hMembership :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        numₘ(variableDepth) ∈ₘ scope :=
    FirstOrder.Derives.iffElimLeft
      hMembershipIff hMembershipNumeral
  have hScopeOpen (witness : SetTerm) (depth : Nat) :
      Term.openAt SetSort.set depth witness scope = scope :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth witness scope hScope.1.2
  have hScopeClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth scope = scope :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth scope hScope.1.2 (by
        rw [hScope.2]
        exact List.not_mem_nil)
  have hNumeralOpen (number depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term (numₘ(number)) =
        numₘ(number) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term (numₘ(number)) (finite_numeral_term_admissible number).2
  have hNumeralClose (number : Nat) (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth (numₘ(number)) =
        numₘ(number) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth (numₘ(number)) (finite_numeral_term_admissible number).2 (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  rw [canonical_scoped_variable_code_condition_with_id]
  nd_apply FirstOrder.Derives.exists_intro
    (term := numₘ(variableDepth))
  simpa [
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt,
    Formula.closeFreeAt,
    Formula.next_depth,
    Formula.substituteFree,
    Term.openAt,
    Term.closeFreeAt,
    Term.substituteFree,
    set_variable,
    set_bound_variable,
    hScopeOpen,
    hScopeClose,
    hNumeralOpen,
    hNumeralClose] using (FirstOrder.Derives.conjIntro
      hMembership (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) (canonical_binder_variable_code_numeral_derives
          variableDepth)))
/-! ## 规范原子行 -/
/--
两个标准变量深度在任意连续内部编号块上给出三类规范原子的同步 cutoff-shift 证明。
显式暴露编号块起点，使逐行证明能够先按实际序列应用选择新鲜编号，再沿对象等式
运输 numeral 证书，而不会依赖自动 fresh base 在语法替换前后定义相等。
-/
theorem canonical_project_atomic_shift_condition_with_base_numeral_derives (cutoff entryDepth leftDepth rightDepth : Nat) (kind : CanonicalProjectAtomKind)
    (base : FreeVarId) (hLeftDepth : leftDepth < entryDepth) (hRightDepth : rightDepth < entryDepth) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_atomic_shift_condition_with_ids (numₘ(cutoff)) (numₘ(entryDepth)) (CanonicalProjectTrace.canonical_project_atom_code
          kind leftDepth rightDepth) (CanonicalProjectTrace.canonical_project_atom_code
          kind (canonical_project_shift_depth cutoff leftDepth) (canonical_project_shift_depth cutoff rightDepth))
        base (base + 1) (base + 2) (base + 3) (base + 4) (base + 6) := by
  let targetLeftDepth :=
    canonical_project_shift_depth cutoff leftDepth
  let targetRightDepth :=
    canonical_project_shift_depth cutoff rightDepth
  let sourceLeft :=
    GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name leftDepth)
  let targetLeft :=
    GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name targetLeftDepth)
  let sourceRight :=
    GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name rightDepth)
  let targetRight :=
    GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name targetRightDepth)
  let sourceCode :=
    CanonicalProjectTrace.canonical_project_atom_code
      kind leftDepth rightDepth
  let targetCode :=
    CanonicalProjectTrace.canonical_project_atom_code
      kind targetLeftDepth targetRightDepth
  let leftFirstId := base
  let rightFirstId := leftFirstId + 1
  let leftSecondId := leftFirstId + 2
  let rightSecondId := leftFirstId + 3
  let firstDepthId := leftFirstId + 4
  let secondDepthId := leftFirstId + 6
  have hSourceLeft :
      GodelQuotation.Numbered.CodeBoundary sourceLeft := by
    constructor
    · exact variable_code_term_admissible _ (finite_numeral_term_admissible (GodelQuotation.bound_name leftDepth))
    · simp [sourceLeft, Term.freeSupport,
        Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hTargetLeft :
      GodelQuotation.Numbered.CodeBoundary targetLeft := by
    constructor
    · exact variable_code_term_admissible _ (finite_numeral_term_admissible (GodelQuotation.bound_name targetLeftDepth))
    · simp [targetLeft, Term.freeSupport,
        Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hSourceRight :
      GodelQuotation.Numbered.CodeBoundary sourceRight := by
    constructor
    · exact variable_code_term_admissible _ (finite_numeral_term_admissible (GodelQuotation.bound_name rightDepth))
    · simp [sourceRight, Term.freeSupport,
        Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hTargetRight :
      GodelQuotation.Numbered.CodeBoundary targetRight := by
    constructor
    · exact variable_code_term_admissible _ (finite_numeral_term_admissible (GodelQuotation.bound_name targetRightDepth))
    · simp [targetRight, Term.freeSupport,
        Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hEqualitySource :=
    equality_formula_code_term_admissible
      sourceLeft sourceRight
      hSourceLeft.1 hSourceRight.1
  have hEqualityTarget :=
    equality_formula_code_term_admissible
      targetLeft targetRight
      hTargetLeft.1 hTargetRight.1
  have hMembershipSource :=
    binary_atomic_formula_code_term_admissible
      membership_symbol_code_term
      sourceLeft sourceRight
      membership_symbol_code_term_admissible
      hSourceLeft.1 hSourceRight.1
  have hMembershipTarget :=
    binary_atomic_formula_code_term_admissible
      membership_symbol_code_term
      targetLeft targetRight
      membership_symbol_code_term_admissible
      hTargetLeft.1 hTargetRight.1
  have hSubsetSource :=
    canonical_project_subset_atomic_code_term_admissible
      sourceLeft sourceRight
      hSourceLeft.1 hSourceRight.1
  have hSubsetTarget :=
    canonical_project_subset_atomic_code_term_admissible
      targetLeft targetRight
      hTargetLeft.1 hTargetRight.1
  have hSourceCode :
      GodelQuotation.Numbered.CodeBoundary sourceCode := by
    constructor
    · cases kind with
      | equality =>
          simpa [sourceCode,
            CanonicalProjectTrace.canonical_project_atom_code,
            sourceLeft, sourceRight] using hEqualitySource
      | membership =>
          simpa [sourceCode,
            CanonicalProjectTrace.canonical_project_atom_code,
            sourceLeft, sourceRight] using hMembershipSource
      | subset =>
          simpa [sourceCode,
            CanonicalProjectTrace.canonical_project_atom_code,
            sourceLeft, sourceRight] using hSubsetSource
    · cases kind <;>
        simp [sourceCode,
          CanonicalProjectTrace.canonical_project_atom_code,
          Term.freeSupport, Term.freeSupportList,
          GodelQuotation.Numbered.argument_sequence,
          GodelQuotation.standard_sequence_from,
          finite_numeral_term_freeSupport]
  have hTargetCode :
      GodelQuotation.Numbered.CodeBoundary targetCode := by
    constructor
    · cases kind with
      | equality =>
          simpa [targetCode,
            CanonicalProjectTrace.canonical_project_atom_code,
            targetLeft, targetRight] using hEqualityTarget
      | membership =>
          simpa [targetCode,
            CanonicalProjectTrace.canonical_project_atom_code,
            targetLeft, targetRight] using hMembershipTarget
      | subset =>
          simpa [targetCode,
            CanonicalProjectTrace.canonical_project_atom_code,
            targetLeft, targetRight] using hSubsetTarget
    · cases kind <;>
        simp [targetCode,
          CanonicalProjectTrace.canonical_project_atom_code,
          Term.freeSupport, Term.freeSupportList,
          GodelQuotation.Numbered.argument_sequence,
          GodelQuotation.standard_sequence_from,
          finite_numeral_term_freeSupport]
  have hFirstShift :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_shifted_variable_code_condition_with_id (numₘ(cutoff)) (numₘ(entryDepth))
          sourceLeft targetLeft firstDepthId := by
    simpa [sourceLeft, targetLeft, targetLeftDepth] using
      canonical_shifted_variable_code_condition_with_id_numeral_derives
        cutoff entryDepth leftDepth firstDepthId hLeftDepth
  have hSecondShift :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_shifted_variable_code_condition_with_id (numₘ(cutoff)) (numₘ(entryDepth))
          sourceRight targetRight secondDepthId := by
    simpa [sourceRight, targetRight, targetRightDepth] using
      canonical_shifted_variable_code_condition_with_id_numeral_derives
        cutoff entryDepth rightDepth secondDepthId hRightDepth
  have hEqualityPairAdmissible :
      Formula.Admissible ((sourceCode ≐ₘ
            eq_codeₘ(sourceLeft, sourceRight)) ∧ₘ (targetCode ≐ₘ
            eq_codeₘ(targetLeft, targetRight))) :=
    Formula.Admissible.conj (Formula.Admissible.equal
        hSourceCode.1 hEqualitySource) (Formula.Admissible.equal
        hTargetCode.1 hEqualityTarget)
  have hMembershipPairAdmissible :
      Formula.Admissible ((sourceCode ≐ₘ
            membership_atomic_formula_code_term
              sourceLeft sourceRight) ∧ₘ (targetCode ≐ₘ
            membership_atomic_formula_code_term
              targetLeft targetRight)) :=
    Formula.Admissible.conj (Formula.Admissible.equal
        hSourceCode.1 hMembershipSource) (Formula.Admissible.equal
        hTargetCode.1 hMembershipTarget)
  have hSubsetPairAdmissible :
      Formula.Admissible ((sourceCode ≐ₘ
            project_subset_atomic_code_term
              sourceLeft sourceRight) ∧ₘ (targetCode ≐ₘ
            project_subset_atomic_code_term
              targetLeft targetRight)) :=
    Formula.Admissible.conj (Formula.Admissible.equal
        hSourceCode.1 hSubsetSource) (Formula.Admissible.equal
        hTargetCode.1 hSubsetTarget)
  have hShapeCases :
      ⊢ₘ[GodelQuotation.godel_quotation_theory] (((sourceCode ≐ₘ
              eq_codeₘ(sourceLeft, sourceRight)) ∧ₘ (targetCode ≐ₘ
              eq_codeₘ(targetLeft, targetRight))) ∨ₘ (((sourceCode ≐ₘ
                membership_atomic_formula_code_term
                  sourceLeft sourceRight) ∧ₘ (targetCode ≐ₘ
                membership_atomic_formula_code_term
                  targetLeft targetRight)) ∨ₘ ((sourceCode ≐ₘ
                project_subset_atomic_code_term
                  sourceLeft sourceRight) ∧ₘ (targetCode ≐ₘ
                project_subset_atomic_code_term
                  targetLeft targetRight)))) := by
    cases kind with
    | equality =>
        nd_apply FirstOrder.Derives.disjIntroLeft
        exact FirstOrder.Derives.conjIntro (by
            simpa [sourceCode,
              CanonicalProjectTrace.canonical_project_atom_code,
              sourceLeft, sourceRight] using
                (FirstOrder.Derives.eq_refl_m
                  (sort := SetSort.set) sourceCode)) (by
            simpa [targetCode,
              CanonicalProjectTrace.canonical_project_atom_code,
              targetLeft, targetRight] using
                (FirstOrder.Derives.eq_refl_m
                  (sort := SetSort.set) targetCode))
    | membership =>
        nd_apply FirstOrder.Derives.disjIntroRight
        nd_apply FirstOrder.Derives.disjIntroLeft
        exact FirstOrder.Derives.conjIntro (by
            simpa [sourceCode,
              CanonicalProjectTrace.canonical_project_atom_code,
              sourceLeft, sourceRight] using
                (FirstOrder.Derives.eq_refl_m
                  (sort := SetSort.set) sourceCode)) (by
            simpa [targetCode,
              CanonicalProjectTrace.canonical_project_atom_code,
              targetLeft, targetRight] using
                (FirstOrder.Derives.eq_refl_m
                  (sort := SetSort.set) targetCode))
    | subset =>
        nd_apply FirstOrder.Derives.disjIntroRight
        nd_apply FirstOrder.Derives.disjIntroRight
        exact FirstOrder.Derives.conjIntro (by
            simpa [sourceCode,
              CanonicalProjectTrace.canonical_project_atom_code,
              sourceLeft, sourceRight] using
                (FirstOrder.Derives.eq_refl_m
                  (sort := SetSort.set) sourceCode)) (by
            simpa [targetCode,
              CanonicalProjectTrace.canonical_project_atom_code,
              targetLeft, targetRight] using
                (FirstOrder.Derives.eq_refl_m
                  (sort := SetSort.set) targetCode))
  have hFixed (id : FreeVarId) (replacement term : SetTerm) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set id replacement term =
        term := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hTerm.2]
    exact List.not_mem_nil
  have hNumeralFixed (id : FreeVarId) (replacement : SetTerm) (number : Nat) :
      Term.substituteFree SetSort.set id replacement (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hBoundaryFresh (term : SetTerm) (hTerm : GodelQuotation.Numbered.CodeBoundary term) (id : FreeVarId) : (SetSort.set, id) ∉ Term.freeSupport term := by
    rw [hTerm.2]
    exact List.not_mem_nil
  have hSourceLeftFixed (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement sourceLeft =
        sourceLeft :=
    hFixed id replacement sourceLeft hSourceLeft
  have hTargetLeftFixed (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement targetLeft =
        targetLeft :=
    hFixed id replacement targetLeft hTargetLeft
  have hSourceRightFixed (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement sourceRight =
        sourceRight :=
    hFixed id replacement sourceRight hSourceRight
  have hTargetRightFixed (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement targetRight =
        targetRight :=
    hFixed id replacement targetRight hTargetRight
  have hSourceCodeFixed (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement sourceCode =
        sourceCode :=
    hFixed id replacement sourceCode hSourceCode
  have hTargetCodeFixed (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement targetCode =
        targetCode :=
    hFixed id replacement targetCode hTargetCode
  have hShiftSubstitute (replacement : SetTerm) (hReplacement : GodelQuotation.Numbered.CodeBoundary replacement) (parameter depthId : FreeVarId)
      (hParameterNeDepth : parameter ≠ depthId) (hParameterNeTargetDepth : parameter ≠ depthId + 1) (cutoffTerm entryDepthTerm leftVariable rightVariable :
        SetTerm) :
      Formula.substituteFree SetSort.set parameter replacement (canonical_shifted_variable_code_condition_with_id
            cutoffTerm entryDepthTerm leftVariable rightVariable
            depthId) =
        canonical_shifted_variable_code_condition_with_id (Term.substituteFree SetSort.set parameter replacement
            cutoffTerm) (Term.substituteFree SetSort.set parameter replacement
            entryDepthTerm) (Term.substituteFree SetSort.set parameter replacement
            leftVariable) (Term.substituteFree SetSort.set parameter replacement
            rightVariable)
          depthId :=
    canonical_shifted_variable_code_condition_with_id_substitute_closed
      cutoffTerm entryDepthTerm leftVariable rightVariable
      replacement parameter depthId
      hParameterNeDepth hParameterNeTargetDepth
      hReplacement.1 hReplacement.2
  have hOffsetNe (leftOffset rightOffset : Nat) (hOffset : leftOffset < rightOffset) :
      leftFirstId + leftOffset ≠ leftFirstId + rightOffset :=
    Nat.ne_of_lt (Nat.add_lt_add_left hOffset leftFirstId)
  have hLeftFirstNeFirstDepth :
      leftFirstId ≠ firstDepthId := by
    simp [firstDepthId]
  have hLeftFirstNeFirstTargetDepth :
      leftFirstId ≠ firstDepthId + 1 := by
    simp [firstDepthId, Nat.add_assoc]
  have hRightFirstNeFirstDepth :
      rightFirstId ≠ firstDepthId := by
    simp [rightFirstId, firstDepthId]
  have hRightFirstNeFirstTargetDepth :
      rightFirstId ≠ firstDepthId + 1 := by
    simp [rightFirstId, firstDepthId, Nat.add_assoc]
  have hLeftSecondNeFirstDepth :
      leftSecondId ≠ firstDepthId := by
    simp [leftSecondId, firstDepthId]
  have hLeftSecondNeFirstTargetDepth :
      leftSecondId ≠ firstDepthId + 1 := by
    simp [leftSecondId, firstDepthId, Nat.add_assoc]
  have hRightSecondNeFirstDepth :
      rightSecondId ≠ firstDepthId := by
    simp [rightSecondId, firstDepthId]
  have hRightSecondNeFirstTargetDepth :
      rightSecondId ≠ firstDepthId + 1 := by
    simp [rightSecondId, firstDepthId, Nat.add_assoc]
  have hLeftFirstNeSecondDepth :
      leftFirstId ≠ secondDepthId := by
    simp [secondDepthId]
  have hLeftFirstNeSecondTargetDepth :
      leftFirstId ≠ secondDepthId + 1 := by
    simp [secondDepthId, Nat.add_assoc]
  have hRightFirstNeSecondDepth :
      rightFirstId ≠ secondDepthId := by
    simp [rightFirstId, secondDepthId]
  have hRightFirstNeSecondTargetDepth :
      rightFirstId ≠ secondDepthId + 1 := by
    simp [rightFirstId, secondDepthId, Nat.add_assoc]
  have hLeftSecondNeSecondDepth :
      leftSecondId ≠ secondDepthId := by
    simp [leftSecondId, secondDepthId]
  have hLeftSecondNeSecondTargetDepth :
      leftSecondId ≠ secondDepthId + 1 := by
    simp [leftSecondId, secondDepthId, Nat.add_assoc]
  have hRightSecondNeSecondDepth :
      rightSecondId ≠ secondDepthId := by
    simp [rightSecondId, secondDepthId]
  have hRightSecondNeSecondTargetDepth :
      rightSecondId ≠ secondDepthId + 1 := by
    simp [rightSecondId, secondDepthId, Nat.add_assoc]
  change
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      ∃ₘ[SetSort.set, leftFirstId],
        ∃ₘ[SetSort.set, rightFirstId],
          ∃ₘ[SetSort.set, leftSecondId],
            ∃ₘ[SetSort.set, rightSecondId], ((canonical_shifted_variable_code_condition_with_id (numₘ(cutoff)) (numₘ(entryDepth))
                  (x#leftFirstId) (x#rightFirstId)
                  firstDepthId ∧ₘ
                canonical_shifted_variable_code_condition_with_id (numₘ(cutoff)) (numₘ(entryDepth)) (x#leftSecondId) (x#rightSecondId)
                  secondDepthId) ∧ₘ (((sourceCode ≐ₘ
                      eq_codeₘ(
                        x#leftFirstId, x#leftSecondId)) ∧ₘ (targetCode ≐ₘ
                      eq_codeₘ(
                        x#rightFirstId, x#rightSecondId))) ∨ₘ ((((sourceCode ≐ₘ
                        membership_atomic_formula_code_term (x#leftFirstId) (x#leftSecondId)) ∧ₘ (targetCode ≐ₘ
                        membership_atomic_formula_code_term (x#rightFirstId) (x#rightSecondId)))) ∨ₘ ((sourceCode ≐ₘ
                        project_subset_atomic_code_term (x#leftFirstId) (x#leftSecondId)) ∧ₘ (targetCode ≐ₘ
                        project_subset_atomic_code_term (x#rightFirstId) (x#rightSecondId))))))
  nd_apply FirstOrder.Derives.exists_intro_substituted
    leftFirstId (witness := sourceLeft)
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set leftFirstId rightFirstId 0 sourceLeft _ (by
      change leftFirstId ≠ leftFirstId + 1
      exact Nat.ne_of_lt (Nat.lt_succ_self leftFirstId))
    hSourceLeft.1.2 (hBoundaryFresh sourceLeft hSourceLeft rightFirstId)]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    rightFirstId (witness := targetLeft)
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set leftFirstId leftSecondId 0 sourceLeft _ (by
      change leftFirstId ≠ leftFirstId + 2
      exact Nat.ne_of_lt <|
        Nat.lt_trans (Nat.lt_succ_self leftFirstId) (Nat.lt_succ_self (leftFirstId + 1)))
    hSourceLeft.1.2 (hBoundaryFresh sourceLeft hSourceLeft leftSecondId)]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set rightFirstId leftSecondId 0 targetLeft _ (by
      change leftFirstId + 1 ≠ leftFirstId + 2
      exact Nat.ne_of_lt (Nat.lt_succ_self (leftFirstId + 1)))
    hTargetLeft.1.2 (hBoundaryFresh targetLeft hTargetLeft leftSecondId)]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    leftSecondId (witness := sourceRight)
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set leftFirstId rightSecondId 0 sourceLeft _ (by
      change leftFirstId ≠ leftFirstId + 3
      exact Nat.ne_of_lt <|
        Nat.lt_trans (Nat.lt_succ_self leftFirstId) (Nat.lt_trans (Nat.lt_succ_self (leftFirstId + 1)) (Nat.lt_succ_self (leftFirstId + 2))))
    hSourceLeft.1.2 (hBoundaryFresh sourceLeft hSourceLeft rightSecondId)]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set rightFirstId rightSecondId 0 targetLeft _ (by
      change leftFirstId + 1 ≠ leftFirstId + 3
      exact Nat.ne_of_lt <|
        Nat.lt_trans (Nat.lt_succ_self (leftFirstId + 1)) (Nat.lt_succ_self (leftFirstId + 2)))
    hTargetLeft.1.2 (hBoundaryFresh targetLeft hTargetLeft rightSecondId)]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set leftSecondId rightSecondId 0 sourceRight _ (by
      change leftFirstId + 2 ≠ leftFirstId + 3
      exact Nat.ne_of_lt (Nat.lt_succ_self (leftFirstId + 2)))
    hSourceRight.1.2 (hBoundaryFresh sourceRight hSourceRight rightSecondId)]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    rightSecondId (witness := targetRight)
  simpa [
    Formula.substituteFree,
    Term.substituteFree,
    set_variable,
    GodelQuotation.Numbered.argument_sequence,
    GodelQuotation.standard_sequence_from,
    leftFirstId, rightFirstId,
    leftSecondId, rightSecondId,
    firstDepthId, secondDepthId,
    hNumeralFixed,
    hSourceLeftFixed, hTargetLeftFixed,
    hSourceRightFixed, hTargetRightFixed,
    hSourceCodeFixed, hTargetCodeFixed,
    hShiftSubstitute sourceLeft hSourceLeft
      leftFirstId firstDepthId
      hLeftFirstNeFirstDepth
      hLeftFirstNeFirstTargetDepth,
    hShiftSubstitute targetLeft hTargetLeft
      rightFirstId firstDepthId
      hRightFirstNeFirstDepth
      hRightFirstNeFirstTargetDepth,
    hShiftSubstitute sourceRight hSourceRight
      leftSecondId firstDepthId
      hLeftSecondNeFirstDepth
      hLeftSecondNeFirstTargetDepth,
    hShiftSubstitute targetRight hTargetRight
      rightSecondId firstDepthId
      hRightSecondNeFirstDepth
      hRightSecondNeFirstTargetDepth,
    hShiftSubstitute sourceLeft hSourceLeft
      leftFirstId secondDepthId
      hLeftFirstNeSecondDepth
      hLeftFirstNeSecondTargetDepth,
    hShiftSubstitute targetLeft hTargetLeft
      rightFirstId secondDepthId
      hRightFirstNeSecondDepth
      hRightFirstNeSecondTargetDepth,
    hShiftSubstitute sourceRight hSourceRight
      leftSecondId secondDepthId
      hLeftSecondNeSecondDepth
      hLeftSecondNeSecondTargetDepth,
    hShiftSubstitute targetRight hTargetRight
      rightSecondId secondDepthId
      hRightSecondNeSecondDepth
      hRightSecondNeSecondTargetDepth] using (FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro
        hFirstShift hSecondShift)
      hShapeCases)
/--
入口深度的对象等式可运输连续编号版原子 shift 条件。

`base + 8` 仅作为 Leibniz 模板孔；它必须对静态左右码新鲜。两侧深度必须对原子
条件内部的八个 binder 新鲜，防止替换穿过存在量词时发生捕获。该接口不要求任何
项闭合，也不依赖具体对象理论。
-/
theorem
    canonical_project_atomic_shift_condition_with_base_iff_of_entry_depth_equality_of_fresh
    {T : SetTheory} {Γ : Context signature}
    (cutoff : Nat)
    (left right leftCode rightCode : SetTerm)
    (base : FreeVarId)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hLeftCode : Term.Admissible leftCode SetSort.set)
    (hRightCode : Term.Admissible rightCode SetSort.set)
    (hDepthFresh :
      ReservedIdsFresh
        [base, base + 1, base + 2, base + 3,
          base + 4, base + 5, base + 6, base + 7]
        [left, right])
    (hStaticFresh :
      ReservedIdsFresh [base + 8]
        [leftCode, rightCode])
    (hEquality :
      Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      canonical_project_atomic_shift_condition_with_ids
          (numₘ(cutoff)) left leftCode rightCode
          base (base + 1) (base + 2) (base + 3)
          (base + 4) (base + 6) ↔ₘ
        canonical_project_atomic_shift_condition_with_ids
          (numₘ(cutoff)) right leftCode rightCode
          base (base + 1) (base + 2) (base + 3)
          (base + 4) (base + 6) := by
  let parameterId := base + 8
  let condition (depth : SetTerm) : SetFormula :=
    canonical_project_atomic_shift_condition_with_ids
      (numₘ(cutoff)) depth leftCode rightCode
      base (base + 1) (base + 2) (base + 3)
      (base + 4) (base + 6)
  have hParameterNe (offset : Nat) (hOffset : offset < 8) :
      parameterId ≠ base + offset := by
    dsimp [parameterId]
    exact Ne.symm <|
      Nat.ne_of_lt (Nat.add_lt_add_left hOffset base)
  have hFixed
      (replacement term : SetTerm)
      (hFresh :
        (SetSort.set, parameterId) ∉
          Term.freeSupport term) :
      Term.substituteFree SetSort.set parameterId
          replacement term =
        term := by
    apply Term.substituteFree_eq_self_of_not_mem
    exact hFresh
  have hNumeralFresh :
      (SetSort.set, parameterId) ∉
        Term.freeSupport (numₘ(cutoff)) := by
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hLeftCodeFresh :
      (SetSort.set, parameterId) ∉
        Term.freeSupport leftCode :=
    hStaticFresh leftCode (by simp)
      parameterId (by simp [parameterId])
  have hRightCodeFresh :
      (SetSort.set, parameterId) ∉
        Term.freeSupport rightCode :=
    hStaticFresh rightCode (by simp)
      parameterId (by simp [parameterId])
  have hNormalize
      (replacement : SetTerm)
      (hReplacement :
        Term.Admissible replacement SetSort.set)
      (hReplacementFresh :
        ∀ id,
          id ∈
            [base, base + 1, base + 2, base + 3,
              base + 4, base + 5, base + 6, base + 7] →
          (SetSort.set, id) ∉
            Term.freeSupport replacement) :
      Formula.substituteFree SetSort.set parameterId replacement
          (condition (x#parameterId)) =
        condition replacement := by
    dsimp [condition]
    rw [
      canonical_project_atomic_shift_condition_with_ids_substitute_of_fresh
        (numₘ(cutoff)) (x#parameterId)
        leftCode rightCode replacement
        parameterId
        base (base + 1) (base + 2) (base + 3)
        (base + 4) (base + 6)
        (hParameterNe 0 (by omega))
        (hParameterNe 1 (by omega))
        (hParameterNe 2 (by omega))
        (hParameterNe 3 (by omega))
        (hParameterNe 4 (by omega))
        (by
          simpa [Nat.add_assoc] using
            hParameterNe 5 (by omega))
        (hParameterNe 6 (by omega))
        (by
          simpa [Nat.add_assoc] using
            hParameterNe 7 (by omega))
        hReplacement
        (hReplacementFresh base (by simp))
        (hReplacementFresh (base + 1) (by simp))
        (hReplacementFresh (base + 2) (by simp))
        (hReplacementFresh (base + 3) (by simp))
        (hReplacementFresh (base + 4) (by simp))
        (hReplacementFresh (base + 5) (by simp))
        (hReplacementFresh (base + 6) (by simp))
        (hReplacementFresh (base + 7) (by simp))]
    simp [Term.substituteFree, set_variable,
      hFixed replacement (numₘ(cutoff)) hNumeralFresh,
      hFixed replacement leftCode hLeftCodeFresh,
      hFixed replacement rightCode hRightCodeFresh]
  have hBodyAdmissible :
      Formula.Admissible
        (condition (x#parameterId)) := by
    dsimp [condition]
    exact
      canonical_project_atomic_shift_condition_with_ids_admissible
        (numₘ(cutoff)) (x#parameterId)
        leftCode rightCode
        base (base + 1) (base + 2) (base + 3)
        (base + 4) (base + 6)
        (finite_numeral_term_admissible cutoff)
        (set_variable_admissible parameterId)
        hLeftCode hRightCode
  have hTransport :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ)
      (sort := SetSort.set) (eigen := parameterId)
      (left := left) (right := right)
      (body := condition (x#parameterId))
      hEquality
  change
    Γ ⊢ₘ[T]
      Formula.substituteFree SetSort.set parameterId left
          (condition (x#parameterId)) ↔ₘ
        Formula.substituteFree SetSort.set parameterId right
          (condition (x#parameterId))
    at hTransport
  simpa only [
    hNormalize left hLeft
      (fun id hId =>
        hDepthFresh left (by simp) id hId),
    hNormalize right hRight
      (fun id hId =>
        hDepthFresh right (by simp) id hId)] using
    hTransport

/--
把显式编号块上的 numeral 原子 shift 证书沿入口深度及左右公式码等式运输到实际闭项。
这是双轨标准序列逐点读取与原子分类器之间的稳定接口：内部编号块保持不变，三次
Leibniz 替换分别处理深度、左码和右码。
-/
theorem canonical_project_atomic_shift_condition_with_base_of_equalities_derives
    {Γ : Context signature} (cutoff entryDepth : Nat) (sourceCode targetCode entryDepthTerm
      leftCodeTerm rightCodeTerm : SetTerm) (base : FreeVarId) (hSourceCode :
      GodelQuotation.Numbered.CodeBoundary sourceCode) (hTargetCode :
      GodelQuotation.Numbered.CodeBoundary targetCode) (hEntryDepthTerm :
      GodelQuotation.Numbered.CodeBoundary entryDepthTerm) (hLeftCodeTerm :
      GodelQuotation.Numbered.CodeBoundary leftCodeTerm) (hRightCodeTerm :
      GodelQuotation.Numbered.CodeBoundary rightCodeTerm) (hEntryDepthValue :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        entryDepthTerm ≐ₘ numₘ(entryDepth)) (hLeftCodeValue :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        leftCodeTerm ≐ₘ sourceCode) (hRightCodeValue :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        rightCodeTerm ≐ₘ targetCode) (hNumeral :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        canonical_project_atomic_shift_condition_with_ids (numₘ(cutoff)) (numₘ(entryDepth))
          sourceCode targetCode
          base (base + 1) (base + 2) (base + 3) (base + 4) (base + 6)) :
    Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_atomic_shift_condition_with_ids (numₘ(cutoff)) entryDepthTerm
        leftCodeTerm rightCodeTerm
        base (base + 1) (base + 2) (base + 3) (base + 4) (base + 6) := by
  let parameterId := base + 8
  let condition (depth leftCode rightCode : SetTerm) : SetFormula :=
    canonical_project_atomic_shift_condition_with_ids (numₘ(cutoff)) depth leftCode rightCode
      base (base + 1) (base + 2) (base + 3) (base + 4) (base + 6)
  have hParameterNe (offset : Nat) (hOffset : offset < 8) :
      parameterId ≠ base + offset := by
    dsimp [parameterId]
    exact Ne.symm <|
      Nat.ne_of_lt (Nat.add_lt_add_left hOffset base)
  have hFixed (replacement term : SetTerm) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set parameterId
          replacement term =
        term := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hTerm.2]
    exact List.not_mem_nil
  have hNormalizeEntry (replacement : SetTerm) (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement) :
      Formula.substituteFree SetSort.set parameterId replacement (condition (x#parameterId) sourceCode targetCode) =
        condition replacement sourceCode targetCode := by
    dsimp [condition]
    rw [
      canonical_project_atomic_shift_condition_with_ids_substitute_closed (numₘ(cutoff)) (x#parameterId)
        sourceCode targetCode replacement
        parameterId
        base (base + 1) (base + 2) (base + 3) (base + 4) (base + 6) (hParameterNe 0 (by omega)) (hParameterNe 1 (by omega)) (hParameterNe 2 (by omega))
        (hParameterNe 3 (by omega)) (hParameterNe 4 (by omega)) (by
          simpa [Nat.add_assoc] using
            hParameterNe 5 (by omega)) (hParameterNe 6 (by omega)) (by
          simpa [Nat.add_assoc] using
            hParameterNe 7 (by omega))
        hReplacement]
    simp [Term.substituteFree, set_variable,
      hFixed replacement (numₘ(cutoff))
        ⟨finite_numeral_term_admissible cutoff,
          finite_numeral_term_freeSupport cutoff⟩,
      hFixed replacement sourceCode hSourceCode,
      hFixed replacement targetCode hTargetCode]
  have hNormalizeLeft (replacement : SetTerm) (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement) :
      Formula.substituteFree SetSort.set parameterId replacement (condition entryDepthTerm (x#parameterId) targetCode) =
        condition entryDepthTerm replacement targetCode := by
    dsimp [condition]
    rw [
      canonical_project_atomic_shift_condition_with_ids_substitute_closed (numₘ(cutoff)) entryDepthTerm (x#parameterId) targetCode replacement
        parameterId
        base (base + 1) (base + 2) (base + 3) (base + 4) (base + 6) (hParameterNe 0 (by omega)) (hParameterNe 1 (by omega)) (hParameterNe 2 (by omega))
        (hParameterNe 3 (by omega)) (hParameterNe 4 (by omega)) (by
          simpa [Nat.add_assoc] using
            hParameterNe 5 (by omega)) (hParameterNe 6 (by omega)) (by
          simpa [Nat.add_assoc] using
            hParameterNe 7 (by omega))
        hReplacement]
    simp [Term.substituteFree, set_variable,
      hFixed replacement (numₘ(cutoff))
        ⟨finite_numeral_term_admissible cutoff,
          finite_numeral_term_freeSupport cutoff⟩,
      hFixed replacement entryDepthTerm hEntryDepthTerm,
      hFixed replacement targetCode hTargetCode]
  have hNormalizeRight (replacement : SetTerm) (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement) :
      Formula.substituteFree SetSort.set parameterId replacement (condition entryDepthTerm leftCodeTerm (x#parameterId)) =
        condition entryDepthTerm leftCodeTerm replacement := by
    dsimp [condition]
    rw [
      canonical_project_atomic_shift_condition_with_ids_substitute_closed (numₘ(cutoff)) entryDepthTerm
        leftCodeTerm (x#parameterId) replacement
        parameterId
        base (base + 1) (base + 2) (base + 3) (base + 4) (base + 6) (hParameterNe 0 (by omega)) (hParameterNe 1 (by omega)) (hParameterNe 2 (by omega))
        (hParameterNe 3 (by omega)) (hParameterNe 4 (by omega)) (by
          simpa [Nat.add_assoc] using
            hParameterNe 5 (by omega)) (hParameterNe 6 (by omega)) (by
          simpa [Nat.add_assoc] using
            hParameterNe 7 (by omega))
        hReplacement]
    simp [Term.substituteFree, set_variable,
      hFixed replacement (numₘ(cutoff))
        ⟨finite_numeral_term_admissible cutoff,
          finite_numeral_term_freeSupport cutoff⟩,
      hFixed replacement entryDepthTerm hEntryDepthTerm,
      hFixed replacement leftCodeTerm hLeftCodeTerm]
  have hNumeralInContext :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        condition (numₘ(entryDepth))
          sourceCode targetCode := by
    simpa [condition] using (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) hNumeral)
  have hEntryBodyAdmissible :
      Formula.Admissible (condition (x#parameterId)
          sourceCode targetCode) := by
    dsimp [condition]
    exact
      canonical_project_atomic_shift_condition_with_ids_admissible (numₘ(cutoff)) (x#parameterId)
        sourceCode targetCode
        base (base + 1) (base + 2) (base + 3) (base + 4) (base + 6) (finite_numeral_term_admissible cutoff) (set_variable_admissible parameterId)
        hSourceCode.1 hTargetCode.1
  have hEntryIffRaw :=
    Metatheory.Derives.equality_iff_of_equality (T := GodelQuotation.godel_quotation_theory) (Γ := Γ) (sort := SetSort.set) (eigen := parameterId)
      (left := entryDepthTerm) (right := numₘ(entryDepth)) (body := condition (x#parameterId)
        sourceCode targetCode)
      hEntryDepthValue
  have hEntryIff :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        condition entryDepthTerm sourceCode targetCode ↔ₘ
          condition (numₘ(entryDepth))
            sourceCode targetCode := by
    simpa only [
      hNormalizeEntry entryDepthTerm hEntryDepthTerm,
      hNormalizeEntry (numₘ(entryDepth))
        ⟨finite_numeral_term_admissible entryDepth,
          finite_numeral_term_freeSupport entryDepth⟩] using
      hEntryIffRaw
  have hAtEntry :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        condition entryDepthTerm sourceCode targetCode :=
    FirstOrder.Derives.iffElimLeft
      hEntryIff hNumeralInContext
  have hLeftBodyAdmissible :
      Formula.Admissible (condition entryDepthTerm (x#parameterId) targetCode) := by
    dsimp [condition]
    exact
      canonical_project_atomic_shift_condition_with_ids_admissible (numₘ(cutoff)) entryDepthTerm (x#parameterId) targetCode
        base (base + 1) (base + 2) (base + 3) (base + 4) (base + 6) (finite_numeral_term_admissible cutoff)
        hEntryDepthTerm.1 (set_variable_admissible parameterId)
        hTargetCode.1
  have hLeftIffRaw :=
    Metatheory.Derives.equality_iff_of_equality (T := GodelQuotation.godel_quotation_theory) (Γ := Γ) (sort := SetSort.set) (eigen := parameterId)
      (left := leftCodeTerm) (right := sourceCode) (body := condition entryDepthTerm (x#parameterId) targetCode)
      hLeftCodeValue
  have hLeftIff :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        condition entryDepthTerm leftCodeTerm targetCode ↔ₘ
          condition entryDepthTerm sourceCode targetCode := by
    simpa only [
      hNormalizeLeft leftCodeTerm hLeftCodeTerm,
      hNormalizeLeft sourceCode hSourceCode] using
      hLeftIffRaw
  have hAtLeft :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        condition entryDepthTerm leftCodeTerm targetCode :=
    FirstOrder.Derives.iffElimLeft hLeftIff hAtEntry
  have hRightBodyAdmissible :
      Formula.Admissible (condition entryDepthTerm leftCodeTerm (x#parameterId)) := by
    dsimp [condition]
    exact
      canonical_project_atomic_shift_condition_with_ids_admissible (numₘ(cutoff)) entryDepthTerm
        leftCodeTerm (x#parameterId)
        base (base + 1) (base + 2) (base + 3) (base + 4) (base + 6) (finite_numeral_term_admissible cutoff)
        hEntryDepthTerm.1 hLeftCodeTerm.1 (set_variable_admissible parameterId)
  have hRightIffRaw :=
    Metatheory.Derives.equality_iff_of_equality (T := GodelQuotation.godel_quotation_theory) (Γ := Γ) (sort := SetSort.set) (eigen := parameterId)
      (left := rightCodeTerm) (right := targetCode) (body := condition entryDepthTerm leftCodeTerm (x#parameterId))
      hRightCodeValue
  have hRightIff :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        condition entryDepthTerm leftCodeTerm rightCodeTerm ↔ₘ
          condition entryDepthTerm leftCodeTerm targetCode := by
    simpa only [
      hNormalizeRight rightCodeTerm hRightCodeTerm,
      hNormalizeRight targetCode hTargetCode] using
      hRightIffRaw
  simpa [condition] using (FirstOrder.Derives.iffElimLeft hRightIff hAtLeft)
/--
两个合法 scope 变量及候选码的对象等式共同给出三类规范项目原子的内部分类证明。
`candidate` 可以是标准序列的逐点应用，而不要求它在 Lean 中定义等于原子码；对象
等式 `hShape` 正是逐行轨迹到分类器之间的接口。
-/
theorem canonical_project_atomic_code_condition_with_ids_derives
    {Γ : Context signature} (scopeDepth leftDepth rightDepth : Nat) (kind : CanonicalProjectAtomKind) (scope : SetTerm) (candidate : SetTerm)
    (leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) (hLeftCodeNeRightCode :
      leftVariableCodeId ≠ rightVariableCodeId) (hLeftCodeNeLeftDepth :
      leftVariableCodeId ≠ leftVariableDepthId) (hRightCodeNeRightDepth :
      rightVariableCodeId ≠ rightVariableDepthId) (hScope :
      GodelQuotation.Numbered.CodeBoundary scope) (hScopeValue :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        scope ≐ₘ numₘ(scopeDepth)) (hLeftDepth : leftDepth < scopeDepth) (hRightDepth : rightDepth < scopeDepth) (hCandidate :
      GodelQuotation.Numbered.CodeBoundary candidate) (hShape :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
        candidate ≐ₘ
          CanonicalProjectTrace.canonical_project_atom_code
            kind leftDepth rightDepth) :
    Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_atomic_code_condition_with_ids
        scope candidate
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId := by
  let leftCode :=
    GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name leftDepth)
  let rightCode :=
    GodelQuotation.Numbered.named_variable_code (GodelQuotation.bound_name rightDepth)
  have hLeftCode :
      GodelQuotation.Numbered.CodeBoundary leftCode := by
    constructor
    · exact variable_code_term_admissible _ (finite_numeral_term_admissible (GodelQuotation.bound_name leftDepth))
    · simp [leftCode,
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hRightCode :
      GodelQuotation.Numbered.CodeBoundary rightCode := by
    constructor
    · exact variable_code_term_admissible _ (finite_numeral_term_admissible (GodelQuotation.bound_name rightDepth))
    · simp [rightCode,
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hLeftCodeMember :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        leftCode ∈ₘ TermCodeₘ := by
    have hVariableMember :
        ⊢ₘ[GodelQuotation.godel_quotation_theory]
          leftCode ∈ₘ VarSymₘ := by
      simpa [leftCode] using
        GodelQuotation.named_variable_code_mem_variable_symbols
          (GodelQuotation.bound_name leftDepth)
    exact GodelQuotation.gq_subset_member
      VarSymₘ TermCodeₘ leftCode
      variable_symbol_set_term_admissible
      term_code_set_term_admissible
      hLeftCode.1
      (GodelQuotation.gq_variable_symbols_subset_term_codes)
      hVariableMember
  have hRightCodeMember :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        rightCode ∈ₘ TermCodeₘ := by
    have hVariableMember :
        ⊢ₘ[GodelQuotation.godel_quotation_theory]
          rightCode ∈ₘ VarSymₘ := by
      simpa [rightCode] using
        GodelQuotation.named_variable_code_mem_variable_symbols
          (GodelQuotation.bound_name rightDepth)
    exact GodelQuotation.gq_subset_member
      VarSymₘ TermCodeₘ rightCode
      variable_symbol_set_term_admissible
      term_code_set_term_admissible
      hRightCode.1
      (GodelQuotation.gq_variable_symbols_subset_term_codes)
      hVariableMember
  have hLeftScope :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_scoped_variable_code_condition_with_id
          scope leftCode
          leftVariableDepthId := by
    simpa [leftCode] using
      canonical_scoped_variable_code_condition_with_id_of_depth_equality
        scopeDepth leftDepth scope leftVariableDepthId
        hScope hScopeValue hLeftDepth
  have hRightScope :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_scoped_variable_code_condition_with_id
          scope rightCode
          rightVariableDepthId := by
    simpa [rightCode] using
      canonical_scoped_variable_code_condition_with_id_of_depth_equality
        scopeDepth rightDepth scope rightVariableDepthId
        hScope hScopeValue hRightDepth
  have hEqualityShapeAdmissible :
      Formula.Admissible (candidate ≐ₘ eq_codeₘ(leftCode, rightCode)) :=
    Formula.Admissible.equal hCandidate.1 (equality_formula_code_term_admissible
        leftCode rightCode hLeftCode.1 hRightCode.1)
  have hMembershipShapeAdmissible :
      Formula.Admissible (candidate ≐ₘ
          membership_atomic_formula_code_term
            leftCode rightCode) :=
    Formula.Admissible.equal hCandidate.1 (binary_atomic_formula_code_term_admissible
        membership_symbol_code_term leftCode rightCode
        membership_symbol_code_term_admissible
        hLeftCode.1 hRightCode.1)
  have hArgumentSequenceAdmissible :
      Term.Admissible (GodelQuotation.Numbered.argument_sequence
          [leftCode, rightCode]) SetSort.set :=
    GodelQuotation.seq_admissible_m 0 <| by
      intro term hTerm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
      rcases hTerm with rfl | rfl
      · exact hLeftCode.1
      · exact hRightCode.1
  have hSubsetShapeAdmissible :
      Formula.Admissible (candidate ≐ₘ
          project_subset_atomic_code_term
            leftCode rightCode) :=
    Formula.Admissible.equal hCandidate.1 (predicate_application_code_term_admissible (numₘ(1)) (numₘ(RelationSymbol.subset.ctorIdx))
        (GodelQuotation.Numbered.argument_sequence
          [leftCode, rightCode]) (finite_numeral_term_admissible 1) (finite_numeral_term_admissible
          RelationSymbol.subset.ctorIdx)
        hArgumentSequenceAdmissible)
  have hShapeCases :
      Γ ⊢ₘ[GodelQuotation.godel_quotation_theory] ((candidate ≐ₘ eq_codeₘ(leftCode, rightCode)) ∨ₘ ((candidate ≐ₘ
              membership_atomic_formula_code_term
                leftCode rightCode) ∨ₘ (candidate ≐ₘ
              project_subset_atomic_code_term
                leftCode rightCode))) := by
    cases kind with
    | equality =>
        nd_apply FirstOrder.Derives.disjIntroLeft
        simpa [CanonicalProjectTrace.canonical_project_atom_code,
          leftCode, rightCode] using hShape
    | membership =>
        nd_apply FirstOrder.Derives.disjIntroRight
        nd_apply FirstOrder.Derives.disjIntroLeft
        simpa [CanonicalProjectTrace.canonical_project_atom_code,
          leftCode, rightCode] using hShape
    | subset =>
        nd_apply FirstOrder.Derives.disjIntroRight
        nd_apply FirstOrder.Derives.disjIntroRight
        simpa [CanonicalProjectTrace.canonical_project_atom_code,
          leftCode, rightCode] using hShape
  have hOpen (term witness : SetTerm) (depth : Nat) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.openAt SetSort.set depth witness term = term :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth witness term hTerm.1.2
  have hClose (term : SetTerm) (id : FreeVarId) (depth : Nat) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.closeFreeAt SetSort.set id depth term = term :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth term hTerm.1.2 (by
        rw [hTerm.2]
        exact List.not_mem_nil)
  have hCandidateOpen (witness : SetTerm) (depth : Nat) :
      Term.openAt SetSort.set depth witness candidate = candidate :=
    hOpen candidate witness depth hCandidate
  have hCandidateClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth candidate = candidate :=
    hClose candidate id depth hCandidate
  have hScopeOpen (witness : SetTerm) (depth : Nat) :
      Term.openAt SetSort.set depth witness scope = scope :=
    hOpen scope witness depth hScope
  have hScopeClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth scope = scope :=
    hClose scope id depth hScope
  have hLeftCodeOpen (witness : SetTerm) (depth : Nat) :
      Term.openAt SetSort.set depth witness leftCode = leftCode :=
    hOpen leftCode witness depth hLeftCode
  have hLeftCodeClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth leftCode = leftCode :=
    hClose leftCode id depth hLeftCode
  have hRightCodeOpen (witness : SetTerm) (depth : Nat) :
      Term.openAt SetSort.set depth witness rightCode = rightCode :=
    hOpen rightCode witness depth hRightCode
  have hRightCodeClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth rightCode = rightCode :=
    hClose rightCode id depth hRightCode
  have hNumeralOpen (number depth : Nat) (witness : SetTerm) :
      Term.openAt SetSort.set depth witness (numₘ(number)) =
        numₘ(number) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth witness (numₘ(number)) (finite_numeral_term_admissible number).2
  have hNumeralClose (number : Nat) (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth (numₘ(number)) =
        numₘ(number) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth (numₘ(number)) (finite_numeral_term_admissible number).2 (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hSubstituteFixed (variableId : FreeVarId) (replacement term : SetTerm) (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set variableId replacement term =
        term := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hTerm.2]
    exact List.not_mem_nil
  have hCandidateLeftFixed :=
    hSubstituteFixed leftVariableCodeId leftCode
      candidate hCandidate
  have hCandidateRightFixed :=
    hSubstituteFixed rightVariableCodeId rightCode
      candidate hCandidate
  have hScopeLeftFixed :=
    hSubstituteFixed leftVariableCodeId leftCode scope hScope
  have hScopeRightFixed :=
    hSubstituteFixed rightVariableCodeId rightCode scope hScope
  have hLeftCodeRightFixed :=
    hSubstituteFixed rightVariableCodeId rightCode
      leftCode hLeftCode
  have hNumeralLeftFixed (number : Nat) :
      Term.substituteFree SetSort.set leftVariableCodeId
          leftCode (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hNumeralRightFixed (number : Nat) :
      Term.substituteFree SetSort.set rightVariableCodeId
          rightCode (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  rw [canonical_project_atomic_code_condition_with_ids]
  nd_apply FirstOrder.Derives.exists_intro
    (term := leftCode)
  rw [Formula.openAt_closeFreeAt_eq_substituteFree]
  apply FirstOrder.Derives.conjIntro
  · simpa [leftCode, Formula.substituteFree, Term.substituteFree,
      set_variable] using
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        hLeftCodeMember
  ·
    nd_apply FirstOrder.Derives.exists_intro
      (term := rightCode)
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set leftVariableCodeId rightVariableCodeId 0
      leftCode _ hLeftCodeNeRightCode hLeftCode.1.2 (by
        rw [hLeftCode.2]
        exact List.not_mem_nil)]
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    apply FirstOrder.Derives.conjIntro
    · simpa [rightCode, Formula.substituteFree, Term.substituteFree,
        set_variable, hLeftCodeNeRightCode,
        Ne.symm hLeftCodeNeRightCode] using
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp)
          hRightCodeMember
    ·
      simpa [
        canonical_scoped_variable_code_condition_with_id,
        Formula.openAt_closeFreeAt_eq_substituteFree,
        Formula.openAt,
        Formula.closeFreeAt,
        Formula.next_depth,
        Formula.substituteFree,
        Term.openAt,
        Term.openAt_closeFreeAt_eq_substituteFree,
        Term.closeFreeAt,
        Term.substituteFree,
        GodelQuotation.Numbered.argument_sequence,
        GodelQuotation.standard_sequence_from,
        set_variable,
        set_bound_variable,
        hLeftCodeNeRightCode,
        hLeftCodeNeLeftDepth,
        hRightCodeNeRightDepth,
        hCandidateOpen,
        hCandidateClose,
        hScopeOpen,
        hScopeClose,
        hLeftCodeOpen,
        hLeftCodeClose,
        hRightCodeOpen,
        hRightCodeClose,
        hCandidateLeftFixed,
        hCandidateRightFixed,
        hScopeLeftFixed,
        hScopeRightFixed,
        hLeftCodeRightFixed,
        hNumeralLeftFixed,
        hNumeralRightFixed,
        hLeftCodeNeRightCode,
        Ne.symm hLeftCodeNeRightCode,
        hNumeralOpen,
        hNumeralClose] using
        (FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro
            hLeftScope hRightScope)
          hShapeCases)
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
