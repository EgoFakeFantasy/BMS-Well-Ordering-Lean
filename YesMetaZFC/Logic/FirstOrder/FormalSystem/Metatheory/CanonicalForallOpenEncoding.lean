import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.CanonicalBinderShift

/-!
# Canonical 全称开式的前向 token 图

本模块给出一次最外层全称开式的直接二元图。输入是量词体在 binder 内部使用的
canonical token 串，输出是用一个给定自由变量打开最外层 binder 后的根层 token 串：

* 最外层 `bound 0` 变为给定自由变量；
* 其余 `bound (d + 1)` 变为 `bound d`；
* 其他 token 保持不变。

该关系只用于 checked transcript 的失败适配。它不恢复 trace，也不替代原有
`canonical_forall_closure_code_condition`；后者仍是逻辑闭包正确性的主关系。
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

/-! ## 外部逐 token 图 -/

/-- 最外层全称开式在单个 canonical token 上的图。 -/
inductive CanonicalForallOpenToken (variableToken : Nat) :
    Nat → Nat → Prop where
  | logical (symbol : LogicalSymbolKind) :
      CanonicalForallOpenToken variableToken
        (Numbered.logical_token symbol)
        (Numbered.logical_token symbol)
  | membership :
      CanonicalForallOpenToken variableToken
        Numbered.membership_token
        Numbered.membership_token
  | free (id : FreeVarId) :
      CanonicalForallOpenToken variableToken
        (Numbered.variable_token (free_name id))
        (Numbered.variable_token (free_name id))
  | outer :
      CanonicalForallOpenToken variableToken
        (Numbered.variable_token (bound_name 0))
        variableToken
  | bound (depth : Nat) :
      CanonicalForallOpenToken variableToken
        (Numbered.variable_token (bound_name (depth + 1)))
        (Numbered.variable_token (bound_name depth))
  | constant (index : Nat) :
      CanonicalForallOpenToken variableToken
        (Numbered.constant_token index)
        (Numbered.constant_token index)
  | function (arityPredecessor index : Nat) :
      CanonicalForallOpenToken variableToken
        (Numbered.function_token arityPredecessor index)
        (Numbered.function_token arityPredecessor index)
  | predicate (arityPredecessor index : Nat) :
      CanonicalForallOpenToken variableToken
        (Numbered.predicate_token arityPredecessor index)
        (Numbered.predicate_token arityPredecessor index)

/-- 两条 token 串逐点满足同一次最外层开式。 -/
inductive CanonicalForallOpenTokens (variableToken : Nat) :
    List Nat → List Nat → Prop where
  | nil :
      CanonicalForallOpenTokens variableToken [] []
  | cons
      {sourceToken targetToken : Nat}
      {sourceTokens targetTokens : List Nat}
      (head :
        CanonicalForallOpenToken variableToken
          sourceToken targetToken)
      (tail :
        CanonicalForallOpenTokens variableToken
          sourceTokens targetTokens) :
      CanonicalForallOpenTokens variableToken
        (sourceToken :: sourceTokens)
        (targetToken :: targetTokens)

namespace CanonicalForallOpenTokens

theorem length_eq
    {variableToken : Nat}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalForallOpenTokens variableToken
        sourceTokens targetTokens) :
    sourceTokens.length = targetTokens.length := by
  induction relation with
  | nil =>
      rfl
  | cons _ _ ih =>
      simp [ih]

/-- 源串一次成功读取可在目标串同一位置读取到开式后的 token。 -/
theorem getElem?_relation
    {variableToken : Nat}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalForallOpenTokens variableToken
        sourceTokens targetTokens)
    {index sourceToken : Nat}
    (sourceGet : sourceTokens[index]? = some sourceToken) :
    ∃ targetToken,
      targetTokens[index]? = some targetToken ∧
        CanonicalForallOpenToken variableToken
          sourceToken targetToken := by
  induction relation generalizing index sourceToken with
  | nil =>
      simp at sourceGet
  | @cons sourceHead targetHead sourceTail targetTail head tail ih =>
      cases index with
      | zero =>
          simp at sourceGet
          subst sourceToken
          exact ⟨targetHead, by simp, head⟩
      | succ index =>
          simp at sourceGet
          exact ih sourceGet

/-- 目标串一次成功读取可在源串同一位置读取到开式前 token。 -/
theorem getElem?_source_relation
    {variableToken : Nat}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalForallOpenTokens variableToken
        sourceTokens targetTokens)
    {index targetToken : Nat}
    (targetGet : targetTokens[index]? = some targetToken) :
    ∃ sourceToken,
      sourceTokens[index]? = some sourceToken ∧
        CanonicalForallOpenToken variableToken
          sourceToken targetToken := by
  induction relation generalizing index targetToken with
  | nil =>
      simp at targetGet
  | @cons sourceHead targetHead sourceTail targetTail head tail ih =>
      cases index with
      | zero =>
          simp at targetGet
          subst targetToken
          exact ⟨sourceHead, by simp, head⟩
      | succ index =>
          simp at targetGet
          exact ih targetGet

/--
一次 canonical binder-shift 后把自由变量替换为 `bound 0`，再做开式会回到原串。
-/
theorem of_binder_shift_substitution
    {sourceTokens shiftedTokens : List Nat}
    (eigen : FreeVarId)
    (relation :
      CanonicalBinderShiftTokens sourceTokens shiftedTokens) :
    CanonicalForallOpenTokens
      (Numbered.variable_token (free_name eigen))
      (substitute_tokens shiftedTokens
        (Numbered.variable_token (free_name eigen))
        [Numbered.variable_token (bound_name 0)])
      sourceTokens := by
  induction relation with
  | nil =>
      exact .nil
  | cons head tail ih =>
      cases head with
      | logical symbol =>
          simpa [substitute_tokens_cons, substitution_piece_tokens,
            logical_token_ne_variable_token] using
            CanonicalForallOpenTokens.cons
              (CanonicalForallOpenToken.logical
                (variableToken :=
                  Numbered.variable_token (free_name eigen))
                symbol)
              ih
      | membership =>
          simpa [substitute_tokens_cons, substitution_piece_tokens,
            membership_token_ne_variable_token] using
            CanonicalForallOpenTokens.cons
              (CanonicalForallOpenToken.membership
                (variableToken :=
                  Numbered.variable_token (free_name eigen)))
              ih
      | free id =>
          by_cases hId : id = eigen
          · subst id
            simpa [substitute_tokens_cons, substitution_piece_tokens] using
              CanonicalForallOpenTokens.cons
                (CanonicalForallOpenToken.outer
                  (variableToken :=
                    Numbered.variable_token (free_name eigen)))
                ih
          · have hToken :
                Numbered.variable_token (free_name id) ≠
                  Numbered.variable_token (free_name eigen) := by
              exact fun h =>
                hId (free_name_injective
                  (variable_token_injective h))
            simpa [substitute_tokens_cons, substitution_piece_tokens,
              hToken] using
              CanonicalForallOpenTokens.cons
                (CanonicalForallOpenToken.free
                  (variableToken :=
                    Numbered.variable_token (free_name eigen))
                  id)
                ih
      | bound depth =>
          have hToken :
              Numbered.variable_token (bound_name (depth + 1)) ≠
                Numbered.variable_token (free_name eigen) := by
            exact fun h =>
              (free_name_ne_bound_name eigen (depth + 1))
                (variable_token_injective h).symm
          simpa [substitute_tokens_cons, substitution_piece_tokens,
            hToken] using
            CanonicalForallOpenTokens.cons
              (CanonicalForallOpenToken.bound
                (variableToken :=
                  Numbered.variable_token (free_name eigen))
                depth)
              ih
      | constant index =>
          simpa [substitute_tokens_cons, substitution_piece_tokens,
            constant_token_ne_variable_token] using
            CanonicalForallOpenTokens.cons
              (CanonicalForallOpenToken.constant
                (variableToken :=
                  Numbered.variable_token (free_name eigen))
                index)
              ih
      | function arity index =>
          simpa [substitute_tokens_cons, substitution_piece_tokens,
            function_token_ne_variable_token] using
            CanonicalForallOpenTokens.cons
              (CanonicalForallOpenToken.function
                (variableToken :=
                  Numbered.variable_token (free_name eigen))
                arity index)
              ih
      | predicate arity index =>
          simpa [substitute_tokens_cons, substitution_piece_tokens,
            predicate_token_ne_variable_token] using
            CanonicalForallOpenTokens.cons
              (CanonicalForallOpenToken.predicate
                (variableToken :=
                  Numbered.variable_token (free_name eigen))
                arity index)
              ih

end CanonicalForallOpenTokens

/-! ## 对象层前向图 -/

/--
开式图的最小逆向见证。

普通 token 在 opening 中保持不变；bound token 则保存其深度，并用已知的 shifted
source 编码给出有限上界。该条件只保证二元 opening 图的函数性，不暴露新的反演层。
-/
def canonical_forall_open_reverse_guard_with_id
    (sourceValue targetValue : SetTerm)
    (boundDepthId : FreeVarId) : SetFormula :=
  (targetValue ≐ₘ sourceValue) ∨ₘ
    (∃ₘ[SetSort.set, boundDepthId],
      ((x#boundDepthId ∈ₘ ωₘ) ∧ₘ
          (x#boundDepthId ∈ₘ Sₘ(sourceValue))) ∧ₘ
        ((sourceValue ≐ₘ
          variable_symbol_number_term
            (Sₘ(Sₘ(Sₘ(numₘ(2) *ₘ x#boundDepthId))))) ∧ₘ
        (targetValue ≐ₘ
          variable_symbol_number_term
            (Sₘ(numₘ(2) *ₘ x#boundDepthId)))))

/-- opening 逆向护栏只依赖左右 token 值。 -/
theorem canonical_forall_open_reverse_guard_with_id_freeSupport_subset
    (sourceValue targetValue : SetTerm)
    (boundDepthId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (canonical_forall_open_reverse_guard_with_id
              sourceValue targetValue boundDepthId) →
        freeVariable ∈ Term.freeSupport sourceValue ∨
          freeVariable ∈ Term.freeSupport targetValue := by
  intro freeVariable hMember
  by_cases hSource :
      freeVariable ∈ Term.freeSupport sourceValue
  · exact Or.inl hSource
  by_cases hTarget :
      freeVariable ∈ Term.freeSupport targetValue
  · exact Or.inr hTarget
  · exfalso
    simp_all [
      canonical_forall_open_reverse_guard_with_id,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]

theorem canonical_forall_open_reverse_guard_with_id_admissible
    (sourceValue targetValue : SetTerm)
    (boundDepthId : FreeVarId)
    (hSource : Term.Admissible sourceValue SetSort.set)
    (hTarget : Term.Admissible targetValue SetSort.set) :
    Formula.Admissible
      (canonical_forall_open_reverse_guard_with_id
        sourceValue targetValue boundDepthId) := by
  let depth : SetTerm := x#boundDepthId
  have hDepth :
      Term.Admissible depth SetSort.set :=
    set_variable_admissible boundDepthId
  have hDouble :
      Term.Admissible (numₘ(2) *ₘ depth) SetSort.set :=
    natural_multiplication_term_admissible
      (numₘ(2)) depth
      (finite_numeral_term_admissible 2) hDepth
  have hBoundName :
      Term.Admissible
        (Sₘ(numₘ(2) *ₘ depth)) SetSort.set :=
    successor_term_admissible _ hDouble
  have hShiftedBoundName :
      Term.Admissible
        (Sₘ(Sₘ(Sₘ(numₘ(2) *ₘ depth))))
        SetSort.set :=
    successor_term_admissible _ <|
      successor_term_admissible _ <|
        successor_term_admissible _ hDouble
  have hBody :
      Formula.Admissible
        (((depth ∈ₘ ωₘ) ∧ₘ
            (depth ∈ₘ Sₘ(sourceValue))) ∧ₘ
          ((sourceValue ≐ₘ
            variable_symbol_number_term
              (Sₘ(Sₘ(Sₘ(numₘ(2) *ₘ depth))))) ∧ₘ
          (targetValue ≐ₘ
            variable_symbol_number_term
              (Sₘ(numₘ(2) *ₘ depth))))) :=
    Formula.Admissible.conj
      (Formula.Admissible.conj
        (membership_formula_admissible hDepth omega_term_admissible)
        (membership_formula_admissible hDepth
          (successor_term_admissible sourceValue hSource)))
      (Formula.Admissible.conj
        (Formula.Admissible.equal hSource
          (variable_symbol_number_term_admissible
            _ hShiftedBoundName))
        (Formula.Admissible.equal hTarget
          (variable_symbol_number_term_admissible
            _ hBoundName)))
  unfold canonical_forall_open_reverse_guard_with_id
  exact Formula.Admissible.disj
    (Formula.Admissible.equal hTarget hSource)
    (Formula.Admissible.exists_closeFreeAt
      SetSort.set boundDepthId hBody)

/--
单 token 开式条件。`variableCode` 是 singleton 变量符号码，故其第零项就是替换
最外层 binder 的目标 token。
-/
def canonical_forall_open_token_condition_with_ids
    (sourceValue variableCode targetValue : SetTerm)
    (freeId boundDepthId constantId functionArityId functionIndexId
      predicateArityId predicateIndexId : FreeVarId) : SetFormula :=
  let outerCase :=
    (sourceValue ≐ₘ canonical_outer_binder_variable_code_term ·ₘ numₘ(0)) ∧ₘ
      (targetValue ≐ₘ variableCode ·ₘ numₘ(0))
  outerCase ∨ₘ
    ((¬ₘ (sourceValue ≐ₘ
        canonical_outer_binder_variable_code_term ·ₘ numₘ(0))) ∧ₘ
      (canonical_binder_shift_token_condition_with_ids
          targetValue sourceValue
          freeId boundDepthId constantId
          functionArityId functionIndexId
          predicateArityId predicateIndexId ∧ₘ
        canonical_forall_open_reverse_guard_with_id
          sourceValue targetValue boundDepthId))

/-- 量词体代码逐点开式为根层公式代码。 -/
def canonical_forall_open_code_condition_with_ids
    (sourceCode variableCode targetCode : SetTerm)
    (indexId freeId boundDepthId constantId functionArityId functionIndexId
      predicateArityId predicateIndexId : FreeVarId) : SetFormula :=
  (((formula_codeₘ(sourceCode) ∧ₘ
      formula_codeₘ(targetCode)) ∧ₘ
      (domₘ(sourceCode) ≐ₘ domₘ(targetCode))) ∧ₘ
    (∀ₘ[SetSort.set, indexId],
      (x#indexId ∈ₘ domₘ(sourceCode)) ⟶ₘ
        canonical_forall_open_token_condition_with_ids
          (sourceCode ·ₘ x#indexId) variableCode
          (targetCode ·ₘ x#indexId)
          freeId boundDepthId constantId
          functionArityId functionIndexId
          predicateArityId predicateIndexId))

/-- 逐点 opening 条件的自由变量只来自三个公开代码参数。 -/
theorem canonical_forall_open_code_condition_with_ids_freeSupport_subset
    (sourceCode variableCode targetCode : SetTerm)
    (indexId freeId boundDepthId constantId functionArityId functionIndexId
      predicateArityId predicateIndexId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (canonical_forall_open_code_condition_with_ids
              sourceCode variableCode targetCode
              indexId freeId boundDepthId constantId
              functionArityId functionIndexId
              predicateArityId predicateIndexId) →
        freeVariable ∈ Term.freeSupport sourceCode ∨
          freeVariable ∈ Term.freeSupport variableCode ∨
            freeVariable ∈ Term.freeSupport targetCode := by
  intro freeVariable hMember
  by_cases hSource :
      freeVariable ∈ Term.freeSupport sourceCode
  · exact Or.inl hSource
  by_cases hVariable :
      freeVariable ∈ Term.freeSupport variableCode
  · exact Or.inr (Or.inl hVariable)
  by_cases hTarget :
      freeVariable ∈ Term.freeSupport targetCode
  · exact Or.inr (Or.inr hTarget)
  · exfalso
    simp_all [
      canonical_forall_open_code_condition_with_ids,
      canonical_forall_open_token_condition_with_ids,
      canonical_forall_open_reverse_guard_with_id,
      canonical_binder_shift_token_condition_with_ids,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    grind

/-- 从完整全称公式码前向得到其 canonical 开式代码。 -/
def canonical_forall_open_code_condition
    (sourceCode variableCode targetCode : SetTerm) : SetFormula :=
  ∃ₘ[SetSort.set, 460],
    ((formula_codeₘ(x#460) ∧ₘ
        (sourceCode ≐ₘ
          forall_codeₘ(
            canonical_outer_binder_variable_code_term,
            x#460))) ∧ₘ
      canonical_forall_open_code_condition_with_ids
        (x#460) variableCode targetCode
        461 462 463 464 465 466 467 468)

/--
Canonical 开式关系只依赖全称公式码、开式变量码与结果公式码。

量词体代码及逐点见证均在关系内部关闭。
-/
theorem canonical_forall_open_code_condition_freeSupport_subset
    (sourceCode variableCode targetCode : SetTerm) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (canonical_forall_open_code_condition
              sourceCode variableCode targetCode) →
      freeVariable ∈ Term.freeSupport sourceCode ∨
        freeVariable ∈ Term.freeSupport variableCode ∨
          freeVariable ∈ Term.freeSupport targetCode := by
  intro freeVariable hMember
  by_cases hSource :
      freeVariable ∈ Term.freeSupport sourceCode
  · exact Or.inl hSource
  by_cases hVariable :
      freeVariable ∈ Term.freeSupport variableCode
  · exact Or.inr (Or.inl hVariable)
  by_cases hTarget :
      freeVariable ∈ Term.freeSupport targetCode
  · exact Or.inr (Or.inr hTarget)
  · exfalso
    simp_all [
      canonical_forall_open_code_condition,
      canonical_forall_open_code_condition_with_ids,
      canonical_forall_open_token_condition_with_ids,
      canonical_forall_open_reverse_guard_with_id,
      canonical_binder_shift_token_condition_with_ids,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    grind

theorem canonical_forall_open_token_condition_with_ids_admissible
    (sourceValue variableCode targetValue : SetTerm)
    (freeId boundDepthId constantId functionArityId functionIndexId
      predicateArityId predicateIndexId : FreeVarId)
    (hSource : Term.Admissible sourceValue SetSort.set)
    (hVariable : Term.Admissible variableCode SetSort.set)
    (hTarget : Term.Admissible targetValue SetSort.set) :
    Formula.Admissible
      (canonical_forall_open_token_condition_with_ids
        sourceValue variableCode targetValue
        freeId boundDepthId constantId
        functionArityId functionIndexId
        predicateArityId predicateIndexId) := by
  have hGuard :=
    canonical_forall_open_reverse_guard_with_id_admissible
      sourceValue targetValue boundDepthId hSource hTarget
  have hZero : Term.Admissible (numₘ(0)) SetSort.set :=
    finite_numeral_term_admissible 0
  have hOuterSource :
      Term.Admissible
        (canonical_outer_binder_variable_code_term ·ₘ numₘ(0))
        SetSort.set :=
    function_application_term_admissible
      canonical_outer_binder_variable_code_term (numₘ(0))
      (variable_code_term_admissible _
        (finite_numeral_term_admissible 1))
      hZero
  have hOuterTarget :
      Term.Admissible (variableCode ·ₘ numₘ(0)) SetSort.set :=
    function_application_term_admissible
      variableCode (numₘ(0)) hVariable hZero
  have hOuter :
      Formula.Admissible
        ((sourceValue ≐ₘ
            canonical_outer_binder_variable_code_term ·ₘ numₘ(0)) ∧ₘ
          (targetValue ≐ₘ variableCode ·ₘ numₘ(0))) :=
    Formula.Admissible.conj
      (Formula.Admissible.equal hSource hOuterSource)
      (Formula.Admissible.equal hTarget hOuterTarget)
  have hShift :=
    canonical_binder_shift_token_condition_with_ids_admissible
      targetValue sourceValue
      freeId boundDepthId constantId
      functionArityId functionIndexId
      predicateArityId predicateIndexId
      hTarget hSource
  have hNotOuter :
      Formula.Admissible
        (¬ₘ (sourceValue ≐ₘ
          canonical_outer_binder_variable_code_term ·ₘ numₘ(0))) :=
    Formula.Admissible.neg <|
      Formula.Admissible.equal hSource hOuterSource
  simpa [canonical_forall_open_token_condition_with_ids] using
    Formula.Admissible.disj hOuter <|
      Formula.Admissible.conj hNotOuter <|
        Formula.Admissible.conj hShift hGuard

theorem canonical_forall_open_code_condition_with_ids_admissible
    (sourceCode variableCode targetCode : SetTerm)
    (indexId freeId boundDepthId constantId functionArityId functionIndexId
      predicateArityId predicateIndexId : FreeVarId)
    (hSource : Term.Admissible sourceCode SetSort.set)
    (hVariable : Term.Admissible variableCode SetSort.set)
    (hTarget : Term.Admissible targetCode SetSort.set) :
    Formula.Admissible
      (canonical_forall_open_code_condition_with_ids
        sourceCode variableCode targetCode
        indexId freeId boundDepthId constantId
        functionArityId functionIndexId
        predicateArityId predicateIndexId) := by
  have hIndex :
      Term.Admissible (x#indexId) SetSort.set :=
    set_variable_admissible indexId
  have hSourceValue :
      Term.Admissible (sourceCode ·ₘ x#indexId) SetSort.set :=
    function_application_term_admissible
      sourceCode (x#indexId) hSource hIndex
  have hTargetValue :
      Term.Admissible (targetCode ·ₘ x#indexId) SetSort.set :=
    function_application_term_admissible
      targetCode (x#indexId) hTarget hIndex
  have hPoint :
      Formula.Admissible
        ((x#indexId ∈ₘ domₘ(sourceCode)) ⟶ₘ
          canonical_forall_open_token_condition_with_ids
            (sourceCode ·ₘ x#indexId) variableCode
            (targetCode ·ₘ x#indexId)
            freeId boundDepthId constantId
            functionArityId functionIndexId
            predicateArityId predicateIndexId) :=
    Formula.Admissible.imp
      (membership_formula_admissible hIndex
        (domain_term_admissible sourceCode hSource))
      (canonical_forall_open_token_condition_with_ids_admissible
        (sourceCode ·ₘ x#indexId) variableCode
        (targetCode ·ₘ x#indexId)
        freeId boundDepthId constantId
        functionArityId functionIndexId
        predicateArityId predicateIndexId
        hSourceValue hVariable hTargetValue)
  exact Formula.Admissible.conj
    (Formula.Admissible.conj
      (Formula.Admissible.conj
        (is_formula_code_formula_admissible hSource)
        (is_formula_code_formula_admissible hTarget))
      (Formula.Admissible.equal
        (domain_term_admissible sourceCode hSource)
        (domain_term_admissible targetCode hTarget)))
    (Formula.Admissible.forall_closeFreeAt
      SetSort.set indexId hPoint)

theorem canonical_forall_open_code_condition_admissible
    (sourceCode variableCode targetCode : SetTerm)
    (hSource : Term.Admissible sourceCode SetSort.set)
    (hVariable : Term.Admissible variableCode SetSort.set)
    (hTarget : Term.Admissible targetCode SetSort.set) :
    Formula.Admissible
      (canonical_forall_open_code_condition
        sourceCode variableCode targetCode) := by
  have hBody :
      Term.Admissible (x#460) SetSort.set :=
    set_variable_admissible 460
  have hUniversal :
      Term.Admissible
        (forall_codeₘ(
          canonical_outer_binder_variable_code_term,
          x#460)) SetSort.set :=
    universal_formula_code_term_admissible
      canonical_outer_binder_variable_code_term (x#460)
      (variable_code_term_admissible _
        (finite_numeral_term_admissible 1))
      hBody
  have hInner :
      Formula.Admissible
        ((formula_codeₘ(x#460) ∧ₘ
            (sourceCode ≐ₘ
              forall_codeₘ(
                canonical_outer_binder_variable_code_term,
                x#460))) ∧ₘ
          canonical_forall_open_code_condition_with_ids
            (x#460) variableCode targetCode
            461 462 463 464 465 466 467 468) :=
    Formula.Admissible.conj
      (Formula.Admissible.conj
        (is_formula_code_formula_admissible hBody)
        (Formula.Admissible.equal hSource hUniversal))
      (canonical_forall_open_code_condition_with_ids_admissible
        (x#460) variableCode targetCode
        461 462 463 464 465 466 467 468
        hBody hVariable hTarget)
  simpa [canonical_forall_open_code_condition] using
    Formula.Admissible.exists_closeFreeAt
      SetSort.set 460 hInner

@[formula_check]
theorem canonical_forall_open_code_condition_check
    (sourceCode variableCode targetCode : SetTerm)
    (hSource : Term.CheckCertificate sourceCode SetSort.set)
    (hVariable : Term.CheckCertificate variableCode SetSort.set)
    (hTarget : Term.CheckCertificate targetCode SetSort.set) :
    Formula.CheckCertificate
      (canonical_forall_open_code_condition
        sourceCode variableCode targetCode) :=
  Formula.check_admissible_complete <|
    canonical_forall_open_code_condition_admissible
      sourceCode variableCode targetCode
      hSource.admissible hVariable.admissible hTarget.admissible

/-! ## 标准 token 序列的对象层回放 -/

/--
单 token 的开式图从三个已对齐的对象值恢复。

普通分支恰好是既有 binder-shift 图的反向端点；只有最外层 `bound 0` 分支直接
使用变量 singleton 码在零点的值。
-/
theorem canonical_forall_open_token_condition_with_ids_of_values
    {variableToken sourceToken targetToken : Nat}
    {Γ : Context signature}
    (relation :
      CanonicalForallOpenToken variableToken
        sourceToken targetToken)
    (freshBase : FreeVarId)
    (sourceValue variableCode targetValue : SetTerm)
    (hSourceValue :
      Term.Admissible sourceValue SetSort.set)
    (hVariableCode :
      Term.Admissible variableCode SetSort.set)
    (hTargetValue :
      Term.Admissible targetValue SetSort.set)
    (hSourceFreshFrom :
      ∀ id, freshBase ≤ id →
        (SetSort.set, id) ∉ Term.freeSupport sourceValue)
    (hTargetFreshFrom :
      ∀ id, freshBase ≤ id →
        (SetSort.set, id) ∉ Term.freeSupport targetValue)
    (hSourceEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        sourceValue ≐ₘ numₘ(sourceToken))
    (hVariableValue :
      Γ ⊢ₘ[godel_quotation_theory]
        (variableCode ·ₘ numₘ(0)) ≐ₘ
          numₘ(variableToken))
    (hTargetEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        targetValue ≐ₘ numₘ(targetToken)) :
    Γ ⊢ₘ[godel_quotation_theory]
      canonical_forall_open_token_condition_with_ids
        sourceValue variableCode targetValue
        freshBase (freshBase + 1) (freshBase + 2)
        (freshBase + 3) (freshBase + 4)
        (freshBase + 5) (freshBase + 6) := by
  have hBoundStandard :
      ⊢ₘ[godel_quotation_theory]
        canonical_outer_binder_variable_code_term ≐ₘ
          standard_token_sequence
            [Numbered.variable_token (bound_name 0)] := by
    simpa [canonical_outer_binder_variable_code_term,
      bound_name] using
      named_variable_code_eq_standard_token_sequence 1
  have hBoundApplication :
      ⊢ₘ[godel_quotation_theory]
        (canonical_outer_binder_variable_code_term ·ₘ
            numₘ(0)) ≐ₘ
          (standard_token_sequence
              [Numbered.variable_token (bound_name 0)] ·ₘ
            numₘ(0)) :=
    function_application_term_congr_function_of_equality
      canonical_outer_binder_variable_code_term
      (standard_token_sequence
        [Numbered.variable_token (bound_name 0)])
      (numₘ(0))
      (variable_code_term_admissible _
        (finite_numeral_term_admissible 1))
      (standard_token_sequence_admissible _)
      (finite_numeral_term_admissible 0)
      hBoundStandard
  have hBoundAtZero :
      ⊢ₘ[godel_quotation_theory]
        (standard_token_sequence
            [Numbered.variable_token (bound_name 0)] ·ₘ
          numₘ(0)) ≐ₘ
            numₘ(Numbered.variable_token (bound_name 0)) := by
    simpa using
      gq_weaken_standard_sequence
        (standard_token_sequence_apply_getElem?
          [Numbered.variable_token (bound_name 0)]
          (by simp))
  have hBoundValue :
      Γ ⊢ₘ[godel_quotation_theory]
        (canonical_outer_binder_variable_code_term ·ₘ
            numₘ(0)) ≐ₘ
          numₘ(Numbered.variable_token (bound_name 0)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        Metatheory.Derives.equality_trans
          hBoundApplication hBoundAtZero
  have hNotOuter
      (hNe :
        sourceToken ≠ Numbered.variable_token (bound_name 0)) :
      Γ ⊢ₘ[godel_quotation_theory]
        ¬ₘ (sourceValue ≐ₘ
          canonical_outer_binder_variable_code_term ·ₘ numₘ(0)) := by
    apply FirstOrder.Derives.negIntro
      (hBodyCheck := Formula.check_admissible_complete <|
        Formula.Admissible.equal hSourceValue <|
          function_application_term_admissible
            canonical_outer_binder_variable_code_term (numₘ(0))
            (variable_code_term_admissible _
              (finite_numeral_term_admissible 1))
            (finite_numeral_term_admissible 0))
    let Δ : Context signature :=
      (sourceValue ≐ₘ
        canonical_outer_binder_variable_code_term ·ₘ numₘ(0)) :: Γ
    have hOuter :
        Δ ⊢ₘ[godel_quotation_theory]
          sourceValue ≐ₘ
            canonical_outer_binder_variable_code_term ·ₘ numₘ(0) :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hNumeral :
        Δ ⊢ₘ[godel_quotation_theory]
          numₘ(sourceToken) ≐ₘ
            numₘ(Numbered.variable_token (bound_name 0)) :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm <|
          FirstOrder.Derives.context_weaken_cons hSourceEquality) <|
        Metatheory.Derives.equality_trans hOuter <|
          FirstOrder.Derives.context_weaken_cons hBoundValue
    exact FirstOrder.Derives.negElim hNumeral <|
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp [Δ]) <|
          gq_weaken_standard_sequence <|
            standard_sequence_finite_numeral_ne hNe
  have hFixedGuard
      (hFixed : targetToken = sourceToken) :
      Γ ⊢ₘ[godel_quotation_theory]
        canonical_forall_open_reverse_guard_with_id
          sourceValue targetValue (freshBase + 1) := by
    subst targetToken
    rw [canonical_forall_open_reverse_guard_with_id]
    exact FirstOrder.Derives.disjIntroLeft <|
      Metatheory.Derives.equality_trans hTargetEquality <|
        Metatheory.Derives.equality_symm hSourceEquality
  have hShift
      (hNe :
        sourceToken ≠ Numbered.variable_token (bound_name 0))
      (shift :
        CanonicalBinderShiftToken targetToken sourceToken)
      (hGuard :
        Γ ⊢ₘ[godel_quotation_theory]
          canonical_forall_open_reverse_guard_with_id
            sourceValue targetValue (freshBase + 1)) :
      Γ ⊢ₘ[godel_quotation_theory]
        canonical_forall_open_token_condition_with_ids
          sourceValue variableCode targetValue
          freshBase (freshBase + 1) (freshBase + 2)
          (freshBase + 3) (freshBase + 4)
          (freshBase + 5) (freshBase + 6) := by
    rw [canonical_forall_open_token_condition_with_ids]
    exact FirstOrder.Derives.disjIntroRight <|
      FirstOrder.Derives.conjIntro (hNotOuter hNe) <|
        FirstOrder.Derives.conjIntro
          (canonical_binder_shift_token_condition_with_ids_of_values
            shift freshBase targetValue sourceValue
            hTargetValue hSourceValue
            hTargetFreshFrom hSourceFreshFrom
            hTargetEquality hSourceEquality)
          hGuard
  cases relation with
  | logical symbol =>
      exact hShift
        (logical_token_ne_variable_token symbol (bound_name 0))
        (.logical symbol)
        (hFixedGuard rfl)
  | membership =>
      exact hShift
        (membership_token_ne_variable_token (bound_name 0))
        .membership
        (hFixedGuard rfl)
  | free id =>
      exact hShift
        (fun h =>
          free_name_ne_bound_name id 0 <|
            variable_token_injective h)
        (.free id)
        (hFixedGuard rfl)
  | outer =>
      have hSourceOuter :
          Γ ⊢ₘ[godel_quotation_theory]
            sourceValue ≐ₘ
              canonical_outer_binder_variable_code_term ·ₘ
                numₘ(0) :=
        Metatheory.Derives.equality_trans hSourceEquality
          (Metatheory.Derives.equality_symm hBoundValue)
      have hTargetOuter :
          Γ ⊢ₘ[godel_quotation_theory]
            targetValue ≐ₘ variableCode ·ₘ numₘ(0) :=
        Metatheory.Derives.equality_trans hTargetEquality
          (Metatheory.Derives.equality_symm hVariableValue)
      rw [canonical_forall_open_token_condition_with_ids]
      exact FirstOrder.Derives.disjIntroLeft
          (hRightCheck := Formula.check_admissible_complete <|
            Formula.Admissible.conj
              (Formula.Admissible.neg <|
                Formula.Admissible.equal hSourceValue <|
                  function_application_term_admissible
                    canonical_outer_binder_variable_code_term
                    (numₘ(0))
                    (variable_code_term_admissible _ <|
                      finite_numeral_term_admissible 1)
                    (finite_numeral_term_admissible 0))
              (Formula.Admissible.conj
                (canonical_binder_shift_token_condition_with_ids_admissible
                  targetValue sourceValue
                  freshBase (freshBase + 1) (freshBase + 2)
                  (freshBase + 3) (freshBase + 4)
                  (freshBase + 5) (freshBase + 6)
                  hTargetValue hSourceValue)
                (canonical_forall_open_reverse_guard_with_id_admissible
                  sourceValue targetValue (freshBase + 1)
                  hSourceValue hTargetValue))) <|
        FirstOrder.Derives.conjIntro
          hSourceOuter hTargetOuter
  | bound depth =>
      let baseIndex := 2 * depth
      let sourceIndex := Nat.succ baseIndex
      let shiftedIndex :=
        Nat.succ (Nat.succ (Nat.succ baseIndex))
      let indexProduct := numₘ(2) *ₘ numₘ(depth)
      have hIndexProduct :
          Term.Admissible indexProduct SetSort.set :=
        natural_multiplication_term_admissible
          (numₘ(2)) (numₘ(depth))
          (finite_numeral_term_admissible 2)
          (finite_numeral_term_admissible depth)
      have hBaseIndex :
          ⊢ₘ[godel_quotation_theory]
            numₘ(baseIndex) ≐ₘ indexProduct := by
        simpa [baseIndex, indexProduct] using
          gq_weaken_standard_sequence <|
            standard_token_sequence_finite_numeral_multiplication
              2 depth
      have hSourceIndexRaw :=
        successor_term_congr_of_equality
          (numₘ(baseIndex)) indexProduct
          (finite_numeral_term_admissible baseIndex)
          hIndexProduct hBaseIndex
      have hSourceIndex :
          ⊢ₘ[godel_quotation_theory]
            numₘ(sourceIndex) ≐ₘ Sₘ(indexProduct) := by
        simpa [sourceIndex, finite_numeral_term] using
          hSourceIndexRaw
      have hShiftedIndex₂Raw :=
        successor_term_congr_of_equality
          (numₘ(sourceIndex)) (Sₘ(indexProduct))
          (finite_numeral_term_admissible sourceIndex)
          (successor_term_admissible indexProduct hIndexProduct)
          hSourceIndex
      have hShiftedIndex₂ :
          ⊢ₘ[godel_quotation_theory]
            numₘ(Nat.succ sourceIndex) ≐ₘ
              Sₘ(Sₘ(indexProduct)) := by
        simpa [finite_numeral_term] using hShiftedIndex₂Raw
      have hShiftedIndexRaw :=
        successor_term_congr_of_equality
          (numₘ(Nat.succ sourceIndex))
          (Sₘ(Sₘ(indexProduct)))
          (finite_numeral_term_admissible
            (Nat.succ sourceIndex))
          (successor_term_admissible _ <|
            successor_term_admissible _ hIndexProduct)
          hShiftedIndex₂
      have hShiftedIndex :
          ⊢ₘ[godel_quotation_theory]
            numₘ(shiftedIndex) ≐ₘ
              Sₘ(Sₘ(Sₘ(indexProduct))) := by
        simpa [shiftedIndex, sourceIndex,
          finite_numeral_term] using hShiftedIndexRaw
      have hSourceName :
          bound_name depth = sourceIndex := by
        simp [bound_name, sourceIndex, baseIndex]
      have hShiftedName :
          bound_name (depth + 1) = shiftedIndex := by
        simp [bound_name, shiftedIndex, baseIndex]
        omega
      have hUnshiftedValue :
          ⊢ₘ[godel_quotation_theory]
            numₘ(Numbered.variable_token (bound_name depth)) ≐ₘ
              variable_symbol_number_term
                (Sₘ(indexProduct)) := by
        rw [hSourceName]
        simpa [Numbered.variable_token,
          variable_symbol_number_term] using
          gq_binder_shift_indexed_prime_power_value
            3 sourceIndex (Sₘ(indexProduct))
            (successor_term_admissible
              indexProduct hIndexProduct)
            hSourceIndex
      have hShiftedValue :
          ⊢ₘ[godel_quotation_theory]
            numₘ(Numbered.variable_token
              (bound_name (depth + 1))) ≐ₘ
              variable_symbol_number_term
                (Sₘ(Sₘ(Sₘ(indexProduct)))) := by
        rw [hShiftedName]
        simpa [Numbered.variable_token,
          variable_symbol_number_term] using
          gq_binder_shift_indexed_prime_power_value
            3 shiftedIndex
            (Sₘ(Sₘ(Sₘ(indexProduct))))
            (successor_term_admissible _ <|
              successor_term_admissible _ <|
                successor_term_admissible _ hIndexProduct)
            hShiftedIndex
      have hDepthBoundRaw :
          ⊢ₘ[godel_quotation_theory]
            numₘ(depth) ∈ₘ
              Sₘ(numₘ(Numbered.variable_token
                (bound_name (depth + 1)))) := by
        have hDepthName :
            depth < bound_name (depth + 1) := by
          simp [bound_name]
          omega
        have hDepthToken :
            depth <
              Numbered.variable_token
                  (bound_name (depth + 1)) + 1 :=
          Nat.lt_trans hDepthName <|
            Numbered.variable_name_lt_token_succ
              (bound_name (depth + 1))
        simpa [finite_numeral_term] using
          gq_weaken_standard_sequence <|
            standard_sequence_finite_numeral_mem_of_lt
              depth
              (Numbered.variable_token
                (bound_name (depth + 1)) + 1)
              hDepthToken
      have hSourceSuccessor :
          Γ ⊢ₘ[godel_quotation_theory]
            Sₘ(numₘ(Numbered.variable_token
              (bound_name (depth + 1)))) ≐ₘ
              Sₘ(sourceValue) :=
        successor_term_congr_of_equality
          (numₘ(Numbered.variable_token
            (bound_name (depth + 1))))
          sourceValue
          (finite_numeral_term_admissible _)
          hSourceValue
          (Metatheory.Derives.equality_symm
            hSourceEquality)
      have hDepthBound :
          Γ ⊢ₘ[godel_quotation_theory]
            numₘ(depth) ∈ₘ Sₘ(sourceValue) :=
        FirstOrder.Derives.iffElimRight
          (membership_right_iff_of_equality
            (numₘ(depth))
            (Sₘ(numₘ(Numbered.variable_token
              (bound_name (depth + 1)))))
            (Sₘ(sourceValue))
            (finite_numeral_term_admissible depth)
            (successor_term_admissible _ <|
              finite_numeral_term_admissible _)
            (successor_term_admissible sourceValue hSourceValue)
            hSourceSuccessor)
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Γ) (by simp) hDepthBoundRaw)
      have hSourceEncoding :
          Γ ⊢ₘ[godel_quotation_theory]
            sourceValue ≐ₘ
              variable_symbol_number_term
                (Sₘ(Sₘ(Sₘ(indexProduct)))) :=
        Metatheory.Derives.equality_trans hSourceEquality <|
          FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Γ) (by simp) hShiftedValue
      have hTargetEncoding :
          Γ ⊢ₘ[godel_quotation_theory]
            targetValue ≐ₘ
              variable_symbol_number_term
                (Sₘ(indexProduct)) :=
        Metatheory.Derives.equality_trans hTargetEquality <|
          FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Γ) (by simp) hUnshiftedValue
      have hGuardBase :
          Γ ⊢ₘ[godel_quotation_theory]
            (((numₘ(depth) ∈ₘ ωₘ) ∧ₘ
                (numₘ(depth) ∈ₘ Sₘ(sourceValue))) ∧ₘ
              ((sourceValue ≐ₘ
                  variable_symbol_number_term
                    (Sₘ(Sₘ(Sₘ(indexProduct))))) ∧ₘ
                (targetValue ≐ₘ
                  variable_symbol_number_term
                    (Sₘ(indexProduct))))) :=
        FirstOrder.Derives.conjIntro
          (FirstOrder.Derives.conjIntro
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Γ) (by simp) <|
                gq_weaken_standard_sequence <|
                  standard_sequence_finite_numeral_mem_omega depth)
            hDepthBound)
          (FirstOrder.Derives.conjIntro
            hSourceEncoding hTargetEncoding)
      have hSourceFixed :
          Term.substituteFree SetSort.set
              (freshBase + 1) (numₘ(depth)) sourceValue =
            sourceValue :=
        Term.substituteFree_eq_self_of_not_mem
          SetSort.set (freshBase + 1) (numₘ(depth))
          sourceValue
          (hSourceFreshFrom (freshBase + 1)
            (Nat.le_succ freshBase))
      have hTargetFixed :
          Term.substituteFree SetSort.set
              (freshBase + 1) (numₘ(depth)) targetValue =
            targetValue :=
        Term.substituteFree_eq_self_of_not_mem
          SetSort.set (freshBase + 1) (numₘ(depth))
          targetValue
          (hTargetFreshFrom (freshBase + 1)
            (Nat.le_succ freshBase))
      have hGuard :
          Γ ⊢ₘ[godel_quotation_theory]
            canonical_forall_open_reverse_guard_with_id
              sourceValue targetValue (freshBase + 1) := by
        rw [canonical_forall_open_reverse_guard_with_id]
        exact FirstOrder.Derives.disjIntroRight <| by
          nd_apply FirstOrder.Derives.exists_intro
            (sort := SetSort.set)
            (term := numₘ(depth))
          simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
            Term.openAt_closeFreeAt_eq_substituteFree,
            Formula.openAt, Formula.closeFreeAt,
            Formula.next_depth, Formula.substituteFree,
            Term.openAt, Term.closeFreeAt, Term.substituteFree,
            set_variable, set_bound_variable, indexProduct,
            hSourceFixed, hTargetFixed,
            gq_binder_shift_numeral_open,
            gq_binder_shift_numeral_close] using hGuardBase
      exact hShift
        (fun h => by
          have hDepth :=
            bound_name_injective (variable_token_injective h)
          exact Nat.succ_ne_zero depth hDepth)
        (.bound depth)
        hGuard
  | constant index =>
      exact hShift
        (constant_token_ne_variable_token index (bound_name 0))
        (.constant index)
        (hFixedGuard rfl)
  | function arityPredecessor index =>
      exact hShift
        (function_token_ne_variable_token
          arityPredecessor index (bound_name 0))
        (.function arityPredecessor index)
        (hFixedGuard rfl)
  | predicate arityPredecessor index =>
      exact hShift
        (predicate_token_ne_variable_token
          arityPredecessor index (bound_name 0))
        (.predicate arityPredecessor index)
        (hFixedGuard rfl)

/-- 开式 token 串在一个具体下标等式分支上满足对象层逐点条件。 -/
private theorem canonical_forall_open_at_index_equality
    {variableToken : Nat}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalForallOpenTokens variableToken
        sourceTokens targetTokens)
    (variableCode : SetTerm)
    (hVariableCode :
      Term.Admissible variableCode SetSort.set)
    (hVariableValue :
      ⊢ₘ[godel_quotation_theory]
        (variableCode ·ₘ numₘ(0)) ≐ₘ
          numₘ(variableToken))
    (indexId : FreeVarId)
    (index : Nat)
    (hIndex : index < sourceTokens.length) :
    ⊢ₘ[godel_quotation_theory]
      ((x#indexId) ≐ₘ numₘ(index)) ⟶ₘ
        canonical_forall_open_token_condition_with_ids
          (standard_token_sequence sourceTokens ·ₘ x#indexId)
          variableCode
          (standard_token_sequence targetTokens ·ₘ x#indexId)
          (indexId + 1) (indexId + 2) (indexId + 3)
          (indexId + 4) (indexId + 5) (indexId + 6)
          (indexId + 7) := by
  let sourceSequence := standard_token_sequence sourceTokens
  let targetSequence := standard_token_sequence targetTokens
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
    standard_token_sequence_admissible sourceTokens
  have hTarget :
      Term.Admissible targetSequence SetSort.set :=
    standard_token_sequence_admissible targetTokens
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
      Γ ⊢ₘ[godel_quotation_theory]
        point ≐ₘ numₘ(index) := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := godel_quotation_theory)
        (Γ := Γ) (φ := equality) (by simp [Γ]))
  have hSourceArgument :
      Γ ⊢ₘ[godel_quotation_theory]
        (sourceSequence ·ₘ point) ≐ₘ
          (sourceSequence ·ₘ numₘ(index)) :=
    function_application_term_congr_argument_of_equality
      sourceSequence point (numₘ(index))
      hSource hPoint hNumeral hEquality
  have hTargetArgument :
      Γ ⊢ₘ[godel_quotation_theory]
        (targetSequence ·ₘ point) ≐ₘ
          (targetSequence ·ₘ numₘ(index)) :=
    function_application_term_congr_argument_of_equality
      targetSequence point (numₘ(index))
      hTarget hPoint hNumeral hEquality
  have hSourceAtNumeral :
      Γ ⊢ₘ[godel_quotation_theory]
        (sourceSequence ·ₘ numₘ(index)) ≐ₘ
          numₘ(sourceToken) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
        simpa [sourceSequence] using
          gq_weaken_standard_sequence
            (standard_token_sequence_apply_getElem?
              sourceTokens hSourceGet)
  have hTargetAtNumeral :
      Γ ⊢ₘ[godel_quotation_theory]
        (targetSequence ·ₘ numₘ(index)) ≐ₘ
          numₘ(targetToken) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
        simpa [targetSequence] using
          gq_weaken_standard_sequence
            (standard_token_sequence_apply_getElem?
              targetTokens hTargetGet)
  have hSourceEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        (sourceSequence ·ₘ point) ≐ₘ
          numₘ(sourceToken) :=
    Metatheory.Derives.equality_trans
      hSourceArgument hSourceAtNumeral
  have hTargetEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        (targetSequence ·ₘ point) ≐ₘ
          numₘ(targetToken) :=
    Metatheory.Derives.equality_trans
      hTargetArgument hTargetAtNumeral
  have hSourcePointSupport :
      Term.freeSupport (sourceSequence ·ₘ point) =
        [(SetSort.set, indexId)] := by
    simp [sourceSequence, point,
      Term.freeSupport, Term.freeSupportList,
      standard_token_sequence_freeSupport_nil] <;> rfl
  have hTargetPointSupport :
      Term.freeSupport (targetSequence ·ₘ point) =
        [(SetSort.set, indexId)] := by
    simp [targetSequence, point,
      Term.freeSupport, Term.freeSupportList,
      standard_token_sequence_freeSupport_nil] <;> rfl
  have hSourceFreshFrom :
      ∀ id, indexId + 1 ≤ id →
        (SetSort.set, id) ∉
          Term.freeSupport (sourceSequence ·ₘ point) := by
    intro id hLower hMember
    rw [hSourcePointSupport] at hMember
    have hPair :
        (SetSort.set, id) = (SetSort.set, indexId) :=
      List.mem_singleton.mp hMember
    have hId : id = indexId := congrArg Prod.snd hPair
    have hStrict : indexId < id := Nat.lt_of_succ_le hLower
    rw [hId] at hStrict
    exact (Nat.lt_irrefl indexId) hStrict
  have hTargetFreshFrom :
      ∀ id, indexId + 1 ≤ id →
        (SetSort.set, id) ∉
          Term.freeSupport (targetSequence ·ₘ point) := by
    intro id hLower hMember
    rw [hTargetPointSupport] at hMember
    have hPair :
        (SetSort.set, id) = (SetSort.set, indexId) :=
      List.mem_singleton.mp hMember
    have hId : id = indexId := congrArg Prod.snd hPair
    have hStrict : indexId < id := Nat.lt_of_succ_le hLower
    rw [hId] at hStrict
    exact (Nat.lt_irrefl indexId) hStrict
  have hCondition :=
    canonical_forall_open_token_condition_with_ids_of_values
      tokenRelation (indexId + 1)
      (sourceSequence ·ₘ point) variableCode
      (targetSequence ·ₘ point)
      hSourcePoint hVariableCode hTargetPoint
      hSourceFreshFrom hTargetFreshFrom
      hSourceEquality
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) hVariableValue)
      hTargetEquality
  simpa [Γ, equality, sourceSequence, targetSequence,
    point, Nat.add_assoc] using hCondition

/-- 开式 token 串在其整个标准定义域上逐点满足对象层前向图。 -/
theorem canonical_forall_open_standard_sequences_pointwise
    {variableToken : Nat}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalForallOpenTokens variableToken
        sourceTokens targetTokens)
    (variableCode : SetTerm)
    (hVariableCode :
      Term.Admissible variableCode SetSort.set)
    (hVariableValue :
      ⊢ₘ[godel_quotation_theory]
        (variableCode ·ₘ numₘ(0)) ≐ₘ
          numₘ(variableToken))
    (indexId : FreeVarId) :
    ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, indexId],
        ((x#indexId ∈ₘ
            domₘ(standard_token_sequence sourceTokens)) ⟶ₘ
          canonical_forall_open_token_condition_with_ids
            (standard_token_sequence sourceTokens ·ₘ x#indexId)
            variableCode
            (standard_token_sequence targetTokens ·ₘ x#indexId)
            (indexId + 1) (indexId + 2) (indexId + 3)
            (indexId + 4) (indexId + 5) (indexId + 6)
            (indexId + 7)) := by
  let sourceSequence := standard_token_sequence sourceTokens
  let targetSequence := standard_token_sequence targetTokens
  let point : SetTerm := x#indexId
  let conclusion : SetFormula :=
    canonical_forall_open_token_condition_with_ids
      (sourceSequence ·ₘ point) variableCode
      (targetSequence ·ₘ point)
      (indexId + 1) (indexId + 2) (indexId + 3)
      (indexId + 4) (indexId + 5) (indexId + 6)
      (indexId + 7)
  have hPoint :
      Term.Admissible point SetSort.set := by
    simpa [point] using set_variable_admissible indexId
  have hSource :
      Term.Admissible sourceSequence SetSort.set :=
    standard_token_sequence_admissible sourceTokens
  have hTarget :
      Term.Admissible targetSequence SetSort.set :=
    standard_token_sequence_admissible targetTokens
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
  have hConclusion : Formula.Admissible conclusion := by
    simpa [conclusion] using
      canonical_forall_open_token_condition_with_ids_admissible
        (sourceSequence ·ₘ point) variableCode
        (targetSequence ·ₘ point)
        (indexId + 1) (indexId + 2) (indexId + 3)
        (indexId + 4) (indexId + 5) (indexId + 6)
        (indexId + 7)
        hSourcePoint hVariableCode hTargetPoint
  have hCases :
      ⊢ₘ[godel_quotation_theory]
        stdseq_numeral_member_condition
            sourceTokens.length point ⟶ₘ
          conclusion :=
    stdseq_numeral_member_condition_elim_of_theory
      sourceTokens.length point conclusion
      (fun index hIndex => by
        simpa [conclusion, sourceSequence,
          targetSequence, point] using
          canonical_forall_open_at_index_equality
            relation variableCode hVariableCode
            hVariableValue indexId index hIndex)
  have hDomain :
      Term.Admissible (domₘ(sourceSequence)) SetSort.set :=
    domain_term_admissible sourceSequence hSource
  have hNumeral :
      Term.Admissible
        (numₘ(sourceTokens.length)) SetSort.set :=
    finite_numeral_term_admissible sourceTokens.length
  have hDomainEq :
      ⊢ₘ[godel_quotation_theory]
        domₘ(sourceSequence) ≐ₘ
          numₘ(sourceTokens.length) := by
    simpa [sourceSequence] using
      gq_weaken_standard_sequence
        (standard_token_sequence_domain_eq_length sourceTokens)
  have hDomainIff :=
    membership_right_iff_of_equality
      point (domₘ(sourceSequence))
      (numₘ(sourceTokens.length))
      hPoint hDomain hNumeral hDomainEq
  have hNumeralIff :
      ⊢ₘ[godel_quotation_theory]
        (point ∈ₘ numₘ(sourceTokens.length)) ↔ₘ
          stdseq_numeral_member_condition
            sourceTokens.length point :=
    gq_weaken_standard_sequence
      (stdseq_numeral_member_iff
        sourceTokens.length point hPoint)
  have hOpen :
      ⊢ₘ[godel_quotation_theory]
        (point ∈ₘ domₘ(sourceSequence)) ⟶ₘ
          conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    have hMembership :
        [point ∈ₘ domₘ(sourceSequence)]
          ⊢ₘ[godel_quotation_theory]
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
      ∀ formula, godel_quotation_theory formula →
        (SetSort.set, indexId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    rw [(godel_quotation_theory_sentence hFormula).2]
    exact List.not_mem_nil
  have hGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := godel_quotation_theory) (Γ := [])
      (sort := SetSort.set) (eigen := indexId)
      hTheoryFresh (by simp) hOpen
  simpa [sourceSequence, targetSequence,
    point, conclusion] using hGeneralized

/-- 两条标准 token 序列满足完整的对象层全称开式关系。 -/
theorem canonical_forall_open_standard_sequences_code_condition_with_ids
    {variableToken : Nat}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalForallOpenTokens variableToken
        sourceTokens targetTokens)
    (variableCode : SetTerm)
    (hVariableCode :
      Term.Admissible variableCode SetSort.set)
    (hVariableValue :
      ⊢ₘ[godel_quotation_theory]
        (variableCode ·ₘ numₘ(0)) ≐ₘ
          numₘ(variableToken))
    (hSourceFormula :
      ⊢ₘ[godel_quotation_theory]
        formula_codeₘ(standard_token_sequence sourceTokens))
    (hTargetFormula :
      ⊢ₘ[godel_quotation_theory]
        formula_codeₘ(standard_token_sequence targetTokens))
    (indexId : FreeVarId) :
    ⊢ₘ[godel_quotation_theory]
      canonical_forall_open_code_condition_with_ids
        (standard_token_sequence sourceTokens)
        variableCode
        (standard_token_sequence targetTokens)
        indexId (indexId + 1) (indexId + 2) (indexId + 3)
        (indexId + 4) (indexId + 5) (indexId + 6)
        (indexId + 7) := by
  let sourceSequence := standard_token_sequence sourceTokens
  let targetSequence := standard_token_sequence targetTokens
  have hSourceDomain :
      ⊢ₘ[godel_quotation_theory]
        domₘ(sourceSequence) ≐ₘ
          numₘ(sourceTokens.length) := by
    simpa [sourceSequence] using
      gq_weaken_standard_sequence
        (standard_token_sequence_domain_eq_length sourceTokens)
  have hTargetDomain :
      ⊢ₘ[godel_quotation_theory]
        domₘ(targetSequence) ≐ₘ
          numₘ(sourceTokens.length) := by
    simpa [targetSequence, relation.length_eq] using
      gq_weaken_standard_sequence
        (standard_token_sequence_domain_eq_length targetTokens)
  have hDomainEquality :
      ⊢ₘ[godel_quotation_theory]
        domₘ(sourceSequence) ≐ₘ domₘ(targetSequence) :=
    Metatheory.Derives.equality_trans hSourceDomain
      (Metatheory.Derives.equality_symm hTargetDomain)
  have hPointwise :=
    canonical_forall_open_standard_sequences_pointwise
      relation variableCode hVariableCode
      hVariableValue indexId
  rw [canonical_forall_open_code_condition_with_ids]
  exact FirstOrder.Derives.conjIntro
    (FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro
        (by simpa [sourceSequence] using hSourceFormula)
        (by simpa [targetSequence] using hTargetFormula))
      (by simpa [sourceSequence, targetSequence] using
        hDomainEquality))
    hPointwise

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
