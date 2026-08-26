import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTrace.Compiler
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta0Support

/-!
# 规范项目公式的二元 token 平移

本模块把 schema 所需的 cutoff-shift 收紧为一个直接的二元关系：

* 逻辑符号、隶属符号和项目子集谓词保持不变；
* 规范 bound 变量 `2d+1` 变为 `2 shift(d)+1`；
* 公式码层只要求两端是同定义域的有限序列，并逐点满足上述关系。

该接口不记录公式树、入口深度或构造 trace。公式分类由调用方已有的 canonical
classifier 负责；这里仅表达 Rosser 终局真正需要的原始递归二元图。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-! ## 外部逐 token 关系 -/

/-- cutoff-shift 在单个 canonical project token 上的图。 -/
inductive CanonicalProjectShiftToken (cutoff : Nat) : Nat → Nat → Prop where
  | logical (symbol : LogicalSymbolKind) :
      CanonicalProjectShiftToken cutoff
        (GodelQuotation.Numbered.logical_token symbol)
        (GodelQuotation.Numbered.logical_token symbol)
  | membership :
      CanonicalProjectShiftToken cutoff
        GodelQuotation.Numbered.membership_token
        GodelQuotation.Numbered.membership_token
  | subset :
      CanonicalProjectShiftToken cutoff
        (GodelQuotation.Numbered.predicate_token
          1 RelationSymbol.subset.ctorIdx)
        (GodelQuotation.Numbered.predicate_token
          1 RelationSymbol.subset.ctorIdx)
  | bound (depth : Nat) :
      CanonicalProjectShiftToken cutoff
        (GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name depth))
        (GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name
            (canonical_project_shift_depth cutoff depth)))

/-- 两条 token 串逐点满足同一个 cutoff-shift。 -/
inductive CanonicalProjectShiftTokens (cutoff : Nat) :
    List Nat → List Nat → Prop where
  | nil :
      CanonicalProjectShiftTokens cutoff [] []
  | cons
      {sourceToken targetToken : Nat}
      {sourceTokens targetTokens : List Nat}
      (head :
        CanonicalProjectShiftToken cutoff
          sourceToken targetToken)
      (tail :
        CanonicalProjectShiftTokens cutoff
          sourceTokens targetTokens) :
      CanonicalProjectShiftTokens cutoff
        (sourceToken :: sourceTokens)
        (targetToken :: targetTokens)

namespace CanonicalProjectShiftTokens

/-- 单 token 关系提升为 singleton 串关系。 -/
theorem singleton
    {cutoff sourceToken targetToken : Nat}
    (token :
      CanonicalProjectShiftToken cutoff
        sourceToken targetToken) :
    CanonicalProjectShiftTokens cutoff
      [sourceToken] [targetToken] :=
  .cons token .nil

/-- 逐点关系对列表拼接封闭。 -/
theorem append
    {cutoff : Nat}
    {sourceLeft sourceRight targetLeft targetRight : List Nat}
    (left :
      CanonicalProjectShiftTokens cutoff
        sourceLeft targetLeft)
    (right :
      CanonicalProjectShiftTokens cutoff
        sourceRight targetRight) :
    CanonicalProjectShiftTokens cutoff
      (sourceLeft ++ sourceRight)
      (targetLeft ++ targetRight) := by
  induction left with
  | nil =>
      simpa using right
  | cons head tail ih =>
      exact .cons head ih

/-- cutoff-shift 保持 token 串长度。 -/
theorem length_eq
    {cutoff : Nat}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalProjectShiftTokens cutoff
        sourceTokens targetTokens) :
    sourceTokens.length = targetTokens.length := by
  induction relation with
  | nil =>
      rfl
  | cons _ _ ih =>
      simp [ih]

/-- 成功读取源 token 时，目标同一位置存在对应 token。 -/
theorem getElem?_relation
    {cutoff : Nat}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalProjectShiftTokens cutoff
        sourceTokens targetTokens)
    {index sourceToken : Nat}
    (sourceGet :
      sourceTokens[index]? = some sourceToken) :
    ∃ targetToken,
      targetTokens[index]? = some targetToken ∧
        CanonicalProjectShiftToken cutoff
          sourceToken targetToken := by
  induction relation generalizing index sourceToken with
  | nil =>
      simp at sourceGet
  | @cons sourceHead targetHead sourceTail targetTail
      head tail ih =>
      cases index with
      | zero =>
          simp at sourceGet
          subst sourceToken
          exact ⟨targetHead, by simp, head⟩
      | succ index =>
          simp at sourceGet
          exact ih sourceGet

/-- 成功读取目标 token 时，源端同一位置存在唯一配对的关系见证。 -/
theorem getElem?_source_relation
    {cutoff : Nat}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalProjectShiftTokens cutoff
        sourceTokens targetTokens)
    {index targetToken : Nat}
    (targetGet :
      targetTokens[index]? = some targetToken) :
    ∃ sourceToken,
      sourceTokens[index]? = some sourceToken ∧
        CanonicalProjectShiftToken cutoff
          sourceToken targetToken := by
  induction relation generalizing index targetToken with
  | nil =>
      simp at targetGet
  | @cons sourceHead targetHead sourceTail targetTail
      head tail ih =>
      cases index with
      | zero =>
          simp at targetGet
          subst targetToken
          exact ⟨sourceHead, by simp, head⟩
      | succ index =>
          simp at targetGet
          exact ih targetGet

/-- 等式构造逐片段保持 cutoff-shift。 -/
theorem equality
    {cutoff : Nat}
    {sourceLeft sourceRight targetLeft targetRight : List Nat}
    (left :
      CanonicalProjectShiftTokens cutoff
        sourceLeft targetLeft)
    (right :
      CanonicalProjectShiftTokens cutoff
        sourceRight targetRight) :
    CanonicalProjectShiftTokens cutoff
      (GodelQuotation.Numbered.equality_tokens
        sourceLeft sourceRight)
      (GodelQuotation.Numbered.equality_tokens
        targetLeft targetRight) := by
  simpa [GodelQuotation.Numbered.equality_tokens,
    List.append_assoc] using
    (singleton (.logical .leftParenthesis)).append <|
      left.append <|
        (singleton (.logical .equality)).append <|
          right.append <|
            singleton (.logical .rightParenthesis)

/-- 隶属构造逐片段保持 cutoff-shift。 -/
theorem membership
    {cutoff : Nat}
    {sourceLeft sourceRight targetLeft targetRight : List Nat}
    (left :
      CanonicalProjectShiftTokens cutoff
        sourceLeft targetLeft)
    (right :
      CanonicalProjectShiftTokens cutoff
        sourceRight targetRight) :
    CanonicalProjectShiftTokens cutoff
      (GodelQuotation.Numbered.membership_tokens
        sourceLeft sourceRight)
      (GodelQuotation.Numbered.membership_tokens
        targetLeft targetRight) := by
  simpa [GodelQuotation.Numbered.membership_tokens,
    List.append_assoc] using
    (singleton (.logical .leftParenthesis)).append <|
      left.append <|
        (singleton .membership).append <|
          right.append <|
            singleton (.logical .rightParenthesis)

/-- 项目子集谓词应用保持 cutoff-shift。 -/
theorem subset
    {cutoff : Nat}
    {sourceLeft sourceRight targetLeft targetRight : List Nat}
    (left :
      CanonicalProjectShiftTokens cutoff
        sourceLeft targetLeft)
    (right :
      CanonicalProjectShiftTokens cutoff
        sourceRight targetRight) :
    CanonicalProjectShiftTokens cutoff
      (GodelQuotation.Numbered.predicate_application_tokens
        1 RelationSymbol.subset.ctorIdx
        [sourceLeft, sourceRight])
      (GodelQuotation.Numbered.predicate_application_tokens
        1 RelationSymbol.subset.ctorIdx
        [targetLeft, targetRight]) := by
  simpa [GodelQuotation.Numbered.predicate_application_tokens,
    List.append_assoc] using
    (singleton .subset).append <|
      (singleton (.logical .leftParenthesis)).append <|
        left.append <|
          right.append <|
            singleton (.logical .rightParenthesis)

/-- 否定构造保持 cutoff-shift。 -/
theorem negation
    {cutoff : Nat}
    {sourceBody targetBody : List Nat}
    (body :
      CanonicalProjectShiftTokens cutoff
        sourceBody targetBody) :
    CanonicalProjectShiftTokens cutoff
      (GodelQuotation.Numbered.negation_tokens sourceBody)
      (GodelQuotation.Numbered.negation_tokens targetBody) := by
  simpa [GodelQuotation.Numbered.negation_tokens,
    List.append_assoc] using
    (singleton (.logical .leftParenthesis)).append <|
      (singleton (.logical .negation)).append <|
        body.append <|
          singleton (.logical .rightParenthesis)

/-- 蕴含构造逐分量保持 cutoff-shift。 -/
theorem implication
    {cutoff : Nat}
    {sourceLeft sourceRight targetLeft targetRight : List Nat}
    (left :
      CanonicalProjectShiftTokens cutoff
        sourceLeft targetLeft)
    (right :
      CanonicalProjectShiftTokens cutoff
        sourceRight targetRight) :
    CanonicalProjectShiftTokens cutoff
      (GodelQuotation.Numbered.implication_tokens
        sourceLeft sourceRight)
      (GodelQuotation.Numbered.implication_tokens
        targetLeft targetRight) := by
  simpa [GodelQuotation.Numbered.implication_tokens,
    List.append_assoc] using
    (singleton (.logical .leftParenthesis)).append <|
      left.append <|
        (singleton (.logical .implication)).append <|
          right.append <|
            singleton (.logical .rightParenthesis)

/-- cutoff 不高于当前入口时，全称 binder 与其 body 同步平移。 -/
theorem universal
    {cutoff : Nat}
    (depth : Nat)
    (hCutoff : cutoff ≤ depth)
    {sourceBody targetBody : List Nat}
    (body :
      CanonicalProjectShiftTokens cutoff
        sourceBody targetBody) :
    CanonicalProjectShiftTokens cutoff
      (GodelQuotation.Numbered.universal_tokens
        (GodelQuotation.bound_name depth) sourceBody)
      (GodelQuotation.Numbered.universal_tokens
        (GodelQuotation.bound_name (depth + 1)) targetBody) := by
  simpa [GodelQuotation.Numbered.universal_tokens,
    canonical_project_shift_depth_of_le hCutoff,
    List.append_assoc] using
    (singleton (.logical .leftParenthesis)).append <|
      (singleton (.logical .universal)).append <|
        (singleton (.bound depth)).append <|
          body.append <|
            singleton (.logical .rightParenthesis)

end CanonicalProjectShiftTokens

/-! ## 对象层二元关系 -/

/-- canonical project 公式中允许保持不变的固定 token。 -/
def canonical_project_shift_fixed_token_condition
    (sourceValue : SetTerm) : SetFormula :=
  canonical_binder_shift_fixed_token_condition sourceValue ∨ₘ
    (sourceValue ≐ₘ
      coded_predicate_symbol_number_term
        (numₘ(1))
        (numₘ(RelationSymbol.subset.ctorIdx)))

/--
单 token 的 cutoff-shift 图。

固定 token 直接保持不变；变量分支显式给出源、目标深度，并复用公共的
`canonical_shifted_depth_condition`。
-/
def canonical_project_shift_token_condition_with_ids
    (cutoff sourceValue targetValue : SetTerm)
    (sourceDepthId targetDepthId : FreeVarId) :
    SetFormula :=
  let fixedCase :=
    canonical_project_shift_fixed_token_condition
        sourceValue ∧ₘ
      (targetValue ≐ₘ sourceValue)
  let variableCase :=
    ∃ₘ[SetSort.set, sourceDepthId],
      (x#sourceDepthId ∈ₘ Sₘ(sourceValue)) ∧ₘ
        (∃ₘ[SetSort.set, targetDepthId],
          (x#targetDepthId ∈ₘ ωₘ) ∧ₘ
            ((sourceValue ≐ₘ
                variable_symbol_number_term
                  (Sₘ(numₘ(2) *ₘ x#sourceDepthId))) ∧ₘ
              (canonical_shifted_depth_condition
                  cutoff (x#sourceDepthId) (x#targetDepthId) ∧ₘ
                  (targetValue ≐ₘ
                    variable_symbol_number_term
                      (Sₘ(numₘ(2) *ₘ x#targetDepthId))))))
  fixedCase ∨ₘ variableCase

/--
两个有限序列逐点实现 canonical project cutoff-shift。

这里刻意不要求 `FormulaCodeₘ`，因为公式合法性已由 schema classifier 单独检查；
二元关系本身只承担可计算的 token 映射和输出唯一性。
-/
def canonical_project_shift_code_condition_with_ids
    (cutoff sourceCode targetCode : SetTerm)
    (indexId sourceDepthId targetDepthId : FreeVarId) :
    SetFormula :=
  ((((cutoff ∈ₘ ωₘ) ∧ₘ
        finite_sequence_condition sourceCode) ∧ₘ
      finite_sequence_condition targetCode) ∧ₘ
    (domₘ(sourceCode) ≐ₘ domₘ(targetCode))) ∧ₘ
  (∀ₘ[SetSort.set, indexId],
    (x#indexId ∈ₘ domₘ(sourceCode)) ⟶ₘ
      canonical_project_shift_token_condition_with_ids
        cutoff
        (sourceCode ·ₘ x#indexId)
        (targetCode ·ₘ x#indexId)
        sourceDepthId targetDepthId)

/-- 自动分配三个内部见证编号的二元 cutoff-shift。 -/
def canonical_project_shift_code_condition
    (cutoff sourceCode targetCode : SetTerm) :
    SetFormula :=
  let base :=
    canonical_formula_classifier_fresh_base
      [cutoff, sourceCode, targetCode]
  canonical_project_shift_code_condition_with_ids
    cutoff sourceCode targetCode
    base (base + 1) (base + 2)

/-! ## 句法边界 -/

theorem canonical_project_shift_fixed_token_condition_admissible
    (sourceValue : SetTerm)
    (hSource : Term.Admissible sourceValue SetSort.set) :
    Formula.Admissible
      (canonical_project_shift_fixed_token_condition sourceValue) := by
  unfold canonical_project_shift_fixed_token_condition
  exact Formula.Admissible.disj
    (canonical_binder_shift_fixed_token_condition_admissible
      sourceValue hSource)
    (Formula.Admissible.equal hSource
      (coded_predicate_symbol_number_term_admissible
        (numₘ(1))
        (numₘ(RelationSymbol.subset.ctorIdx))
        (finite_numeral_term_admissible 1)
        (finite_numeral_term_admissible
          RelationSymbol.subset.ctorIdx)))

theorem canonical_project_shift_token_condition_with_ids_admissible
    (cutoff sourceValue targetValue : SetTerm)
    (sourceDepthId targetDepthId : FreeVarId)
    (hCutoff : Term.Admissible cutoff SetSort.set)
    (hSource : Term.Admissible sourceValue SetSort.set)
    (hTarget : Term.Admissible targetValue SetSort.set) :
    Formula.Admissible
      (canonical_project_shift_token_condition_with_ids
        cutoff sourceValue targetValue
        sourceDepthId targetDepthId) := by
  let sourceDepth : SetTerm := x#sourceDepthId
  let targetDepth : SetTerm := x#targetDepthId
  have hSourceDepth :
      Term.Admissible sourceDepth SetSort.set :=
    set_variable_admissible sourceDepthId
  have hTargetDepth :
      Term.Admissible targetDepth SetSort.set :=
    set_variable_admissible targetDepthId
  have hTwo :
      Term.Admissible (numₘ(2)) SetSort.set :=
    finite_numeral_term_admissible 2
  have hSourceIndex :
      Term.Admissible
        (Sₘ(numₘ(2) *ₘ sourceDepth)) SetSort.set :=
    successor_term_admissible _
      (natural_multiplication_term_admissible
        (numₘ(2)) sourceDepth hTwo hSourceDepth)
  have hTargetIndex :
      Term.Admissible
        (Sₘ(numₘ(2) *ₘ targetDepth)) SetSort.set :=
    successor_term_admissible _
      (natural_multiplication_term_admissible
        (numₘ(2)) targetDepth hTwo hTargetDepth)
  have hTargetBody :
      Formula.Admissible
        ((targetDepth ∈ₘ ωₘ) ∧ₘ
          ((sourceValue ≐ₘ
              variable_symbol_number_term
                (Sₘ(numₘ(2) *ₘ sourceDepth))) ∧ₘ
            (canonical_shifted_depth_condition
                cutoff sourceDepth targetDepth ∧ₘ
                (targetValue ≐ₘ
                  variable_symbol_number_term
                    (Sₘ(numₘ(2) *ₘ targetDepth)))))) :=
    Formula.Admissible.conj
      (membership_formula_admissible
        hTargetDepth omega_term_admissible)
      (Formula.Admissible.conj
        (Formula.Admissible.equal hSource
          (variable_symbol_number_term_admissible
            _ hSourceIndex))
        (Formula.Admissible.conj
          (canonical_shifted_depth_condition_admissible
            cutoff sourceDepth targetDepth
            hCutoff hSourceDepth hTargetDepth)
          (Formula.Admissible.equal hTarget
            (variable_symbol_number_term_admissible
              _ hTargetIndex))))
  have hVariableBody :
      Formula.Admissible
        ((sourceDepth ∈ₘ Sₘ(sourceValue)) ∧ₘ
          (∃ₘ[SetSort.set, targetDepthId],
            (x#targetDepthId ∈ₘ ωₘ) ∧ₘ
              ((sourceValue ≐ₘ
                  variable_symbol_number_term
                    (Sₘ(numₘ(2) *ₘ sourceDepth))) ∧ₘ
                (canonical_shifted_depth_condition
                    cutoff sourceDepth (x#targetDepthId) ∧ₘ
                 (targetValue ≐ₘ
                    variable_symbol_number_term
                      (Sₘ(numₘ(2) *ₘ x#targetDepthId))))))) :=
    Formula.Admissible.conj
      (membership_formula_admissible
        hSourceDepth
        (successor_term_admissible sourceValue hSource))
      (Formula.Admissible.exists_closeFreeAt
        SetSort.set targetDepthId hTargetBody)
  unfold canonical_project_shift_token_condition_with_ids
  exact Formula.Admissible.disj
    (Formula.Admissible.conj
      (canonical_project_shift_fixed_token_condition_admissible
        sourceValue hSource)
      (Formula.Admissible.equal hTarget hSource))
    (Formula.Admissible.exists_closeFreeAt
      SetSort.set sourceDepthId <|
        hVariableBody)

@[formula_check]
theorem canonical_project_shift_token_condition_with_ids_check
    (cutoff sourceValue targetValue : SetTerm)
    (sourceDepthId targetDepthId : FreeVarId)
    (hCutoff : Term.CheckCertificate cutoff SetSort.set)
    (hSource : Term.CheckCertificate sourceValue SetSort.set)
    (hTarget : Term.CheckCertificate targetValue SetSort.set) :
    Formula.CheckCertificate
      (canonical_project_shift_token_condition_with_ids
        cutoff sourceValue targetValue
        sourceDepthId targetDepthId) :=
  Formula.check_certificate_of_admissible
    (canonical_project_shift_token_condition_with_ids_admissible
      cutoff sourceValue targetValue
      sourceDepthId targetDepthId
      hCutoff.admissible hSource.admissible hTarget.admissible)

theorem canonical_project_shift_code_condition_with_ids_admissible
    (cutoff sourceCode targetCode : SetTerm)
    (indexId sourceDepthId targetDepthId : FreeVarId)
    (hCutoff : Term.Admissible cutoff SetSort.set)
    (hSource : Term.Admissible sourceCode SetSort.set)
    (hTarget : Term.Admissible targetCode SetSort.set) :
    Formula.Admissible
      (canonical_project_shift_code_condition_with_ids
        cutoff sourceCode targetCode
        indexId sourceDepthId targetDepthId) := by
  let index : SetTerm := x#indexId
  have hIndex :
      Term.Admissible index SetSort.set :=
    set_variable_admissible indexId
  have hSourceDomain :=
    domain_term_admissible sourceCode hSource
  have hTargetDomain :=
    domain_term_admissible targetCode hTarget
  have hSourceAt :=
    function_application_term_admissible
      sourceCode index hSource hIndex
  have hTargetAt :=
    function_application_term_admissible
      targetCode index hTarget hIndex
  unfold canonical_project_shift_code_condition_with_ids
  exact Formula.Admissible.conj
    (Formula.Admissible.conj
      (Formula.Admissible.conj
        (Formula.Admissible.conj
          (membership_formula_admissible
            hCutoff omega_term_admissible)
          (finite_sequence_condition_admissible
            sourceCode hSource))
        (finite_sequence_condition_admissible
          targetCode hTarget))
      (Formula.Admissible.equal
        hSourceDomain hTargetDomain))
    (Formula.Admissible.forall_closeFreeAt
      SetSort.set indexId <|
        Formula.Admissible.imp
          (membership_formula_admissible
            hIndex hSourceDomain)
          (canonical_project_shift_token_condition_with_ids_admissible
            cutoff
            (sourceCode ·ₘ index)
            (targetCode ·ₘ index)
            sourceDepthId targetDepthId
            hCutoff hSourceAt hTargetAt))

@[formula_check]
theorem canonical_project_shift_code_condition_with_ids_check
    (cutoff sourceCode targetCode : SetTerm)
    (indexId sourceDepthId targetDepthId : FreeVarId)
    (hCutoff : Term.CheckCertificate cutoff SetSort.set)
    (hSource : Term.CheckCertificate sourceCode SetSort.set)
    (hTarget : Term.CheckCertificate targetCode SetSort.set) :
    Formula.CheckCertificate
      (canonical_project_shift_code_condition_with_ids
        cutoff sourceCode targetCode
        indexId sourceDepthId targetDepthId) :=
  Formula.check_certificate_of_admissible
    (canonical_project_shift_code_condition_with_ids_admissible
      cutoff sourceCode targetCode
      indexId sourceDepthId targetDepthId
      hCutoff.admissible hSource.admissible hTarget.admissible)

/-! ## 闭项替换合同 -/

/--
闭项替换逐参数穿过二元 cutoff-shift 关系。

三个新鲜性条件恰好对应索引、源深度和目标深度三个内部 binder；外部三个代码项
按普通项替换同步更新。
-/
theorem canonical_project_shift_code_condition_with_ids_substitute_closed
    (cutoff sourceCode targetCode replacement
      cutoffResult sourceCodeResult targetCodeResult : SetTerm)
    (sourceId indexId sourceDepthId targetDepthId : FreeVarId)
    (hSourceNeIndex : sourceId ≠ indexId)
    (hSourceNeSourceDepth : sourceId ≠ sourceDepthId)
    (hSourceNeTargetDepth : sourceId ≠ targetDepthId)
    (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement)
    (hCutoffSubstitution :
      Term.substituteFree SetSort.set sourceId replacement cutoff =
        cutoffResult)
    (hSourceCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement sourceCode =
        sourceCodeResult)
    (hTargetCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement targetCode =
        targetCodeResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (canonical_project_shift_code_condition_with_ids
          cutoff sourceCode targetCode
          indexId sourceDepthId targetDepthId) =
      canonical_project_shift_code_condition_with_ids
        cutoffResult sourceCodeResult targetCodeResult
        indexId sourceDepthId targetDepthId := by
  have hReplacementFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport replacement := by
    rw [hReplacement.2]
    exact List.not_mem_nil
  have hComm
      (id : FreeVarId) (depth : Nat) (formula : SetFormula)
      (hDistinct : sourceId ≠ id) :
      Formula.substituteFree SetSort.set sourceId replacement
          (Formula.closeFreeAt SetSort.set id depth formula) =
        Formula.closeFreeAt SetSort.set id depth
          (Formula.substituteFree SetSort.set sourceId replacement
            formula) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId id depth replacement formula
      hDistinct hReplacement.1.2 (hReplacementFresh id)).symm
  have hNumeralFixed (value : Nat) :
      Term.substituteFree SetSort.set sourceId replacement
          (numₘ(value)) =
        numₘ(value) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hFiniteSequenceSubstitution
      (sequence sequenceResult : SetTerm)
      (hSequenceSubstitution :
        Term.substituteFree SetSort.set sourceId replacement sequence =
          sequenceResult) :
      Formula.substituteFree SetSort.set sourceId replacement
          (finite_sequence_condition sequence) =
        finite_sequence_condition sequenceResult := by
    simp [finite_sequence_condition, Formula.substituteFree,
      Term.substituteFree,
      hSequenceSubstitution]
  unfold canonical_project_shift_code_condition_with_ids
  unfold canonical_project_shift_token_condition_with_ids
  unfold canonical_project_shift_fixed_token_condition
  simp [Formula.substituteFree, Term.substituteFree,
    canonical_binder_shift_fixed_token_condition_substituteFree,
    canonical_shifted_depth_condition,
    hCutoffSubstitution, hSourceCodeSubstitution,
    hTargetCodeSubstitution,
    hFiniteSequenceSubstitution sourceCode sourceCodeResult
      hSourceCodeSubstitution,
    hFiniteSequenceSubstitution targetCode targetCodeResult
      hTargetCodeSubstitution,
    hNumeralFixed,
    hComm indexId 0 _ hSourceNeIndex,
    hComm sourceDepthId 0 _ hSourceNeSourceDepth,
    hComm targetDepthId 0 _ hSourceNeTargetDepth,
    Ne.symm hSourceNeIndex,
    Ne.symm hSourceNeSourceDepth,
    Ne.symm hSourceNeTargetDepth]

/-- 标准三元模板满足公共句法边界。 -/
theorem canonical_project_shift_code_template_admissible :
    Formula.Admissible
      (canonical_project_shift_code_condition
        (x#0) (x#1) (x#2)) := by
  apply Formula.check_admissible_sound
  native_decide

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
