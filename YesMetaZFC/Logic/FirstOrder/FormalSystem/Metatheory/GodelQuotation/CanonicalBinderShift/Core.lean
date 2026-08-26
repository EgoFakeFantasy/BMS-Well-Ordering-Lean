import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Substitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncoding
/-!
# 规范 quotation 的 binder 深度平移基础层
规范 quotation 使用偶数名字编码自由变量、奇数名字编码 binder。把同一公式放入一个
新的外层量词体时，自由变量和非变量 token 保持不变，而原有每个 binder 名
`2d+1` 必须统一变成 `2d+3`。
本模块先在外部 token 层给出签名无关的同步关系，再证明任意可编号单排序签名的
quotation 在入口深度增加一层时满足该关系。本基础层同时给出单 token 的对象条件，
供后续标准序列与代码运输模块直接消费。
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
/-! ## 外部 token 同步关系 -/
/-- 单个 quotation token 在 binder 入口深度增加一层时的精确对应。 -/
inductive CanonicalBinderShiftToken : Nat → Nat → Prop where
  | logical (symbol : LogicalSymbolKind) :
      CanonicalBinderShiftToken (Numbered.logical_token symbol) (Numbered.logical_token symbol)
  | membership :
      CanonicalBinderShiftToken
        Numbered.membership_token
        Numbered.membership_token
  | free (id : FreeVarId) :
      CanonicalBinderShiftToken (Numbered.variable_token (free_name id)) (Numbered.variable_token (free_name id))
  | bound (depth : Nat) :
      CanonicalBinderShiftToken (Numbered.variable_token (bound_name depth)) (Numbered.variable_token (bound_name (depth + 1)))
  | constant (index : Nat) :
      CanonicalBinderShiftToken (Numbered.constant_token index) (Numbered.constant_token index)
  | function (arityPredecessor index : Nat) :
      CanonicalBinderShiftToken (Numbered.function_token arityPredecessor index) (Numbered.function_token arityPredecessor index)
  | predicate (arityPredecessor index : Nat) :
      CanonicalBinderShiftToken (Numbered.predicate_token arityPredecessor index) (Numbered.predicate_token arityPredecessor index)
/-- 两条 token 串逐点满足规范 binder 深度平移。 -/
inductive CanonicalBinderShiftTokens : List Nat → List Nat → Prop where
  | nil : CanonicalBinderShiftTokens [] []
  | cons
      {sourceToken targetToken : Nat}
      {sourceTokens targetTokens : List Nat} (head :
        CanonicalBinderShiftToken sourceToken targetToken) (tail :
        CanonicalBinderShiftTokens sourceTokens targetTokens) :
      CanonicalBinderShiftTokens (sourceToken :: sourceTokens) (targetToken :: targetTokens)
/-- 两列 token 串逐项满足规范 binder 深度平移。 -/
inductive CanonicalBinderShiftTokenLists :
    List (List Nat) → List (List Nat) → Prop where
  | nil : CanonicalBinderShiftTokenLists [] []
  | cons
      {sourceHead targetHead : List Nat}
      {sourceTail targetTail : List (List Nat)} (head :
        CanonicalBinderShiftTokens sourceHead targetHead) (tail :
        CanonicalBinderShiftTokenLists sourceTail targetTail) :
      CanonicalBinderShiftTokenLists (sourceHead :: sourceTail) (targetHead :: targetTail)
/--
左右局部 binder 环境的同步关系。
目标环境末尾额外保留新加入的最外层 binder；每进入一个原公式内部 binder，左右
环境表头分别压入深度 `d` 与 `d+1` 的规范名字。
-/
inductive CanonicalBinderShiftEnvironment :
    List Nat → List Nat → Prop where
  | base :
      CanonicalBinderShiftEnvironment
        [] [bound_name 0]
  | cons (depth : Nat)
      {sourceNames targetNames : List Nat} (tail :
        CanonicalBinderShiftEnvironment
          sourceNames targetNames) :
      CanonicalBinderShiftEnvironment (bound_name depth :: sourceNames) (bound_name (depth + 1) :: targetNames)
namespace CanonicalBinderShiftTokens
/-- 单 token 对应提升为 singleton token 串对应。 -/
theorem singleton
    {sourceToken targetToken : Nat} (token :
      CanonicalBinderShiftToken sourceToken targetToken) :
    CanonicalBinderShiftTokens
      [sourceToken] [targetToken] :=
  .cons token .nil
/-- 逐点平移关系对列表拼接封闭。 -/
theorem append
    {sourceLeft sourceRight targetLeft targetRight : List Nat} (left :
      CanonicalBinderShiftTokens sourceLeft targetLeft) (right :
      CanonicalBinderShiftTokens sourceRight targetRight) :
    CanonicalBinderShiftTokens (sourceLeft ++ sourceRight) (targetLeft ++ targetRight) := by
  induction left with
  | nil =>
      simpa using right
  | cons head tail ih =>
      exact .cons head ih
/-- 同步关系保持 token 串长度。 -/
theorem length_eq
    {sourceTokens targetTokens : List Nat} (relation :
      CanonicalBinderShiftTokens sourceTokens targetTokens) :
    sourceTokens.length = targetTokens.length := by
  induction relation with
  | nil =>
      rfl
  | cons _ _ ih =>
      simp [ih]
/-- 源串一次成功读取可在目标串同一位置读取到同步 token。 -/
theorem getElem?_relation
    {sourceTokens targetTokens : List Nat} (relation :
      CanonicalBinderShiftTokens sourceTokens targetTokens)
    {index sourceToken : Nat} (sourceGet :
      sourceTokens[index]? = some sourceToken) :
    ∃ targetToken,
      targetTokens[index]? = some targetToken ∧
        CanonicalBinderShiftToken sourceToken targetToken := by
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
/-- 目标串一次成功读取可在源串同一位置读取到同步 token。 -/
theorem getElem?_source_relation
    {sourceTokens targetTokens : List Nat} (relation :
      CanonicalBinderShiftTokens sourceTokens targetTokens)
    {index targetToken : Nat} (targetGet :
      targetTokens[index]? = some targetToken) :
    ∃ sourceToken,
      sourceTokens[index]? = some sourceToken ∧
        CanonicalBinderShiftToken sourceToken targetToken := by
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
/-- 两列同步 token 串 flatten 后仍逐点同步。 -/
theorem flatten
    {source target : List (List Nat)} (relation :
      CanonicalBinderShiftTokenLists source target) :
    CanonicalBinderShiftTokens
      source.flatten target.flatten := by
  induction relation with
  | nil =>
      exact .nil
  | cons head tail ih =>
      simpa using head.append ih
/-- 等式 token 构造保持规范 binder 深度平移。 -/
theorem equality
    {sourceLeft sourceRight targetLeft targetRight : List Nat} (left :
      CanonicalBinderShiftTokens sourceLeft targetLeft) (right :
      CanonicalBinderShiftTokens sourceRight targetRight) :
    CanonicalBinderShiftTokens (Numbered.equality_tokens sourceLeft sourceRight) (Numbered.equality_tokens targetLeft targetRight) := by
  simpa [Numbered.equality_tokens, List.append_assoc] using (singleton (.logical .leftParenthesis)).append <|
      left.append <| (singleton (.logical .equality)).append <|
          right.append <|
            singleton (.logical .rightParenthesis)
/-- 隶属原子 token 构造保持规范 binder 深度平移。 -/
theorem membership
    {sourceLeft sourceRight targetLeft targetRight : List Nat} (left :
      CanonicalBinderShiftTokens sourceLeft targetLeft) (right :
      CanonicalBinderShiftTokens sourceRight targetRight) :
    CanonicalBinderShiftTokens (Numbered.membership_tokens sourceLeft sourceRight) (Numbered.membership_tokens targetLeft targetRight) := by
  simpa [Numbered.membership_tokens, List.append_assoc] using (singleton (.logical .leftParenthesis)).append <|
      left.append <| (singleton .membership).append <|
          right.append <|
            singleton (.logical .rightParenthesis)
/-- 正元函数应用 token 构造保持规范 binder 深度平移。 -/
theorem function_application (arityPredecessor index : Nat)
    {sourceArguments targetArguments : List (List Nat)} (arguments :
      CanonicalBinderShiftTokenLists
        sourceArguments targetArguments) :
    CanonicalBinderShiftTokens (Numbered.function_application_tokens
        arityPredecessor index sourceArguments) (Numbered.function_application_tokens
        arityPredecessor index targetArguments) := by
  simpa [Numbered.function_application_tokens,
    List.append_assoc] using (singleton (.function arityPredecessor index)).append <| (singleton (.logical .leftParenthesis)).append <|
        (flatten arguments).append <|
          singleton (.logical .rightParenthesis)
/-- 正元谓词应用 token 构造保持规范 binder 深度平移。 -/
theorem predicate_application (arityPredecessor index : Nat)
    {sourceArguments targetArguments : List (List Nat)} (arguments :
      CanonicalBinderShiftTokenLists
        sourceArguments targetArguments) :
    CanonicalBinderShiftTokens (Numbered.predicate_application_tokens
        arityPredecessor index sourceArguments) (Numbered.predicate_application_tokens
        arityPredecessor index targetArguments) := by
  simpa [Numbered.predicate_application_tokens,
    List.append_assoc] using (singleton (.predicate arityPredecessor index)).append <| (singleton (.logical .leftParenthesis)).append <|
        (flatten arguments).append <|
          singleton (.logical .rightParenthesis)
/-- 否定 token 构造保持规范 binder 深度平移。 -/
theorem negation
    {sourceBody targetBody : List Nat} (body :
      CanonicalBinderShiftTokens sourceBody targetBody) :
    CanonicalBinderShiftTokens (Numbered.negation_tokens sourceBody) (Numbered.negation_tokens targetBody) := by
  simpa [Numbered.negation_tokens, List.append_assoc] using (singleton (.logical .leftParenthesis)).append <| (singleton (.logical .negation)).append <|
        body.append <|
          singleton (.logical .rightParenthesis)
/-- 蕴含 token 构造保持规范 binder 深度平移。 -/
theorem implication
    {sourceLeft sourceRight targetLeft targetRight : List Nat} (left :
      CanonicalBinderShiftTokens sourceLeft targetLeft) (right :
      CanonicalBinderShiftTokens sourceRight targetRight) :
    CanonicalBinderShiftTokens (Numbered.implication_tokens sourceLeft sourceRight) (Numbered.implication_tokens targetLeft targetRight) := by
  simpa [Numbered.implication_tokens, List.append_assoc] using (singleton (.logical .leftParenthesis)).append <|
      left.append <| (singleton (.logical .implication)).append <|
          right.append <|
            singleton (.logical .rightParenthesis)
/-- 全称 token 构造把当前 binder 深度同步后移一层。 -/
theorem universal (depth : Nat)
    {sourceBody targetBody : List Nat} (body :
      CanonicalBinderShiftTokens sourceBody targetBody) :
    CanonicalBinderShiftTokens (Numbered.universal_tokens (bound_name depth) sourceBody) (Numbered.universal_tokens (bound_name (depth + 1)) targetBody) := by
  simpa [Numbered.universal_tokens, List.append_assoc] using (singleton (.logical .leftParenthesis)).append <| (singleton (.logical .universal)).append <|
        (singleton (.bound depth)).append <|
          body.append <|
            singleton (.logical .rightParenthesis)
end CanonicalBinderShiftTokens
namespace CanonicalBinderShiftEnvironment
/--
源环境中成功读取的每个名字，在目标环境同一 de Bruijn 位置读到其后继深度名字。
-/
theorem getElem?_shift
    {sourceNames targetNames : List Nat} (environment :
      CanonicalBinderShiftEnvironment
        sourceNames targetNames)
    {index sourceName : Nat} (sourceGet :
      sourceNames[index]? = some sourceName) :
    ∃ depth,
      sourceName = bound_name depth ∧
        targetNames[index]? =
          some (bound_name (depth + 1)) := by
  induction environment generalizing index sourceName with
  | base =>
      simp at sourceGet
  | @cons depth sourceNames targetNames tail ih =>
      cases index with
      | zero =>
          simp at sourceGet
          subst sourceName
          exact ⟨depth, rfl, by simp⟩
      | succ index =>
          simp at sourceGet
          exact ih sourceGet
end CanonicalBinderShiftEnvironment
/-! ## 项 quotation 的深度平移 -/
/--
同一项在同步 binder 环境中 quotation 后，所得 token 串逐点满足规范深度平移。
本定理同时递归参数列表，因而适用于任意可编号单排序签名中的常元和正元函数。
-/
theorem quote_term_tokens_with?_canonical_binder_shift
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {sourceNames targetNames : List Nat} (environment :
      CanonicalBinderShiftEnvironment sourceNames targetNames) (term : Term σ)
    {sourceTokens targetTokens : List Nat} (sourceQuote :
      Numbered.quote_term_tokens_with?
          free_name sourceNames term =
        some sourceTokens) (targetQuote :
      Numbered.quote_term_tokens_with?
          free_name targetNames term =
        some targetTokens) :
    CanonicalBinderShiftTokens sourceTokens targetTokens := by
  refine Term.rec (motive_1 := fun term =>
      ∀ {sourceTokens targetTokens : List Nat},
        Numbered.quote_term_tokens_with?
            free_name sourceNames term =
          some sourceTokens →
        Numbered.quote_term_tokens_with?
            free_name targetNames term =
          some targetTokens →
        CanonicalBinderShiftTokens sourceTokens targetTokens) (motive_2 := fun terms =>
      ∀ {sourceTokenLists targetTokenLists : List (List Nat)},
        terms.mapM (Numbered.quote_term_tokens_with?
              free_name sourceNames) =
          some sourceTokenLists →
        terms.mapM (Numbered.quote_term_tokens_with?
              free_name targetNames) =
          some targetTokenLists →
        CanonicalBinderShiftTokenLists
          sourceTokenLists targetTokenLists)
    ?_ ?_ ?_ ?_ term sourceQuote targetQuote
  · intro sourceVar sourceTokens targetTokens
      sourceQuote targetQuote
    cases sourceVar with
    | bvar sort index =>
        cases sourceNameEquation :
            sourceNames[index]? with
        | none =>
            simp [Numbered.quote_term_tokens_with?,
              sourceNameEquation] at sourceQuote
        | some sourceName =>
            obtain ⟨depth, rfl, targetNameEquation⟩ :=
              environment.getElem?_shift sourceNameEquation
            simp [Numbered.quote_term_tokens_with?,
              sourceNameEquation] at sourceQuote
            simp [Numbered.quote_term_tokens_with?,
              targetNameEquation] at targetQuote
            subst sourceTokens
            subst targetTokens
            exact CanonicalBinderShiftTokens.singleton (.bound depth)
    | fvar sort id =>
        simp [Numbered.quote_term_tokens_with?] at sourceQuote
        simp [Numbered.quote_term_tokens_with?] at targetQuote
        subst sourceTokens
        subst targetTokens
        exact CanonicalBinderShiftTokens.singleton (.free id)
  · intro function arguments argumentsInduction
      sourceTokens targetTokens sourceQuote targetQuote
    cases sourceArgumentsEquation :
        arguments.mapM (Numbered.quote_term_tokens_with?
            free_name sourceNames) with
    | none =>
        simp [Numbered.quote_term_tokens_with?,
          sourceArgumentsEquation] at sourceQuote
    | some sourceArguments =>
        cases targetArgumentsEquation :
            arguments.mapM (Numbered.quote_term_tokens_with?
                free_name targetNames) with
        | none =>
            simp [Numbered.quote_term_tokens_with?,
              targetArgumentsEquation] at targetQuote
        | some targetArguments =>
            have argumentsRelation :=
              argumentsInduction sourceArgumentsEquation
                targetArgumentsEquation
            cases sourceArguments with
            | nil =>
                cases argumentsRelation with
                | nil =>
                    simp [Numbered.quote_term_tokens_with?,
                      sourceArgumentsEquation] at sourceQuote
                    simp [Numbered.quote_term_tokens_with?,
                      targetArgumentsEquation] at targetQuote
                    subst sourceTokens
                    subst targetTokens
                    exact CanonicalBinderShiftTokens.singleton (.constant (QuotationNumbering.function_number
                          function))
            | cons sourceHead sourceTail =>
                cases argumentsRelation with
                | cons head tail =>
                    simp [Numbered.quote_term_tokens_with?,
                      sourceArgumentsEquation] at sourceQuote
                    simp [Numbered.quote_term_tokens_with?,
                      targetArgumentsEquation] at targetQuote
                    subst sourceTokens
                    subst targetTokens
                    exact
                      CanonicalBinderShiftTokens.function_application (arguments.length - 1) (QuotationNumbering.function_number function) (.cons head tail)
  · intro sourceTokenLists targetTokenLists
      sourceQuote targetQuote
    simp at sourceQuote targetQuote
    subst sourceTokenLists
    subst targetTokenLists
    exact .nil
  · intro head tail headInduction tailInduction
      sourceTokenLists targetTokenLists
      sourceQuote targetQuote
    cases sourceHeadEquation :
        Numbered.quote_term_tokens_with?
          free_name sourceNames head <;>
      cases sourceTailEquation :
        tail.mapM (Numbered.quote_term_tokens_with?
            free_name sourceNames) <;>
      cases targetHeadEquation :
        Numbered.quote_term_tokens_with?
          free_name targetNames head <;>
      cases targetTailEquation :
        tail.mapM (Numbered.quote_term_tokens_with?
            free_name targetNames) <;>
      simp_all
    subst sourceTokenLists
    subst targetTokenLists
    exact .cons headInduction tailInduction
/-!
参数列表版本作为关系原子与函数应用的公共递归接口；调用方无需重新展开
`List.mapM`。
-/
theorem quote_terms_tokens_with?_canonical_binder_shift
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {sourceNames targetNames : List Nat} (environment :
      CanonicalBinderShiftEnvironment sourceNames targetNames) (terms : List (Term σ))
    {sourceTokenLists targetTokenLists : List (List Nat)} (sourceQuote :
      terms.mapM (Numbered.quote_term_tokens_with?
            free_name sourceNames) =
        some sourceTokenLists) (targetQuote :
      terms.mapM (Numbered.quote_term_tokens_with?
            free_name targetNames) =
        some targetTokenLists) :
    CanonicalBinderShiftTokenLists
      sourceTokenLists targetTokenLists := by
  induction terms generalizing
      sourceTokenLists targetTokenLists with
  | nil =>
      simp at sourceQuote targetQuote
      subst sourceTokenLists
      subst targetTokenLists
      exact .nil
  | cons head tail ih =>
      cases sourceHeadEquation :
          Numbered.quote_term_tokens_with?
            free_name sourceNames head <;>
        cases sourceTailEquation :
          tail.mapM (Numbered.quote_term_tokens_with?
              free_name sourceNames) <;>
        cases targetHeadEquation :
          Numbered.quote_term_tokens_with?
            free_name targetNames head <;>
        cases targetTailEquation :
          tail.mapM (Numbered.quote_term_tokens_with?
              free_name targetNames) <;>
        simp_all
      subst sourceTokenLists
      subst targetTokenLists
      exact .cons (quote_term_tokens_with?_canonical_binder_shift
          environment head sourceHeadEquation targetHeadEquation)
        ih
/-! ## Hilbert quotation 的深度平移 -/
/--
同一 Hilbert 核公式在入口深度 `depth` 与 `depth + 1` 处 quotation，所得 token 串
逐点满足规范 binder 平移。
递归进入原公式自己的量词时，左右环境同步压入 `bound_name depth` 与
`bound_name (depth + 1)`；因此结论同时覆盖任意量词嵌套深度。
-/
theorem quote_hilbert_tokens_with?_canonical_binder_shift
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (formula : Formula σ)
    {sourceNames targetNames : List Nat} (environment :
      CanonicalBinderShiftEnvironment sourceNames targetNames) (depth : Nat)
    {sourceTokens targetTokens : List Nat} (sourceQuote :
      Numbered.quote_hilbert_tokens_with?
          free_name bound_name sourceNames depth formula =
        some sourceTokens) (targetQuote :
      Numbered.quote_hilbert_tokens_with?
          free_name bound_name targetNames (depth + 1) formula =
        some targetTokens) :
    CanonicalBinderShiftTokens sourceTokens targetTokens := by
  induction formula generalizing
      sourceNames targetNames depth
      sourceTokens targetTokens with
  | falsum =>
      simp [Numbered.quote_hilbert_tokens_with?] at sourceQuote
  | truth =>
      simp [Numbered.quote_hilbert_tokens_with?] at sourceQuote
  | rel relation arguments =>
      cases relationKindEquation :
          numbering.relation_kind relation with
      | membership =>
          cases arguments with
          | nil =>
              simp [Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?,
                relationKindEquation] at sourceQuote
          | cons left rest =>
              cases rest with
              | nil =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?,
                    relationKindEquation] at sourceQuote
              | cons right tail =>
                  cases tail with
                  | cons extra tail =>
                      simp [Numbered.quote_hilbert_tokens_with?,
                        Numbered.quote_relation_tokens_with?,
                        relationKindEquation] at sourceQuote
                  | nil =>
                      cases sourceLeftEquation :
                          Numbered.quote_term_tokens_with?
                            free_name sourceNames left with
                      | none =>
                          simp [Numbered.quote_hilbert_tokens_with?,
                            Numbered.quote_relation_tokens_with?,
                            relationKindEquation,
                            sourceLeftEquation] at sourceQuote
                      | some sourceLeftTokens =>
                          cases sourceRightEquation :
                              Numbered.quote_term_tokens_with?
                                free_name sourceNames right with
                          | none =>
                              simp [Numbered.quote_hilbert_tokens_with?,
                                Numbered.quote_relation_tokens_with?,
                                relationKindEquation,
                                sourceLeftEquation,
                                sourceRightEquation] at sourceQuote
                          | some sourceRightTokens =>
                              cases targetLeftEquation :
                                  Numbered.quote_term_tokens_with?
                                    free_name targetNames left with
                              | none =>
                                  simp [Numbered.quote_hilbert_tokens_with?,
                                    Numbered.quote_relation_tokens_with?,
                                    relationKindEquation,
                                    targetLeftEquation] at targetQuote
                              | some targetLeftTokens =>
                                  cases targetRightEquation :
                                      Numbered.quote_term_tokens_with?
                                        free_name targetNames right with
                                  | none =>
                                      simp [
                                        Numbered.quote_hilbert_tokens_with?,
                                        Numbered.quote_relation_tokens_with?,
                                        relationKindEquation,
                                        targetLeftEquation,
                                        targetRightEquation] at targetQuote
                                  | some targetRightTokens =>
                                      simp [
                                        Numbered.quote_hilbert_tokens_with?,
                                        Numbered.quote_relation_tokens_with?,
                                        relationKindEquation,
                                        sourceLeftEquation,
                                        sourceRightEquation] at sourceQuote
                                      simp [
                                        Numbered.quote_hilbert_tokens_with?,
                                        Numbered.quote_relation_tokens_with?,
                                        relationKindEquation,
                                        targetLeftEquation,
                                        targetRightEquation] at targetQuote
                                      subst sourceTokens
                                      subst targetTokens
                                      exact
                                        CanonicalBinderShiftTokens.membership (quote_term_tokens_with?_canonical_binder_shift
                                            environment left
                                            sourceLeftEquation
                                            targetLeftEquation) (quote_term_tokens_with?_canonical_binder_shift
                                            environment right
                                            sourceRightEquation
                                            targetRightEquation)
      | predicate =>
          cases arguments with
          | nil =>
              simp [Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?,
                relationKindEquation] at sourceQuote
          | cons head tail =>
              cases sourceArgumentsEquation : (head :: tail).mapM (Numbered.quote_term_tokens_with?
                      free_name sourceNames) with
              | none =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?,
                    relationKindEquation,
                    sourceArgumentsEquation] at sourceQuote
              | some sourceArguments =>
                  cases targetArgumentsEquation : (head :: tail).mapM (Numbered.quote_term_tokens_with?
                          free_name targetNames) with
                  | none =>
                      simp [Numbered.quote_hilbert_tokens_with?,
                        Numbered.quote_relation_tokens_with?,
                        relationKindEquation,
                        targetArgumentsEquation] at targetQuote
                  | some targetArguments =>
                      simp [Numbered.quote_hilbert_tokens_with?,
                        Numbered.quote_relation_tokens_with?,
                        relationKindEquation,
                        sourceArgumentsEquation] at sourceQuote
                      simp [Numbered.quote_hilbert_tokens_with?,
                        Numbered.quote_relation_tokens_with?,
                        relationKindEquation,
                        targetArgumentsEquation] at targetQuote
                      subst sourceTokens
                      subst targetTokens
                      exact
                        CanonicalBinderShiftTokens.predicate_application
                          tail.length (QuotationNumbering.relation_number relation) (quote_terms_tokens_with?_canonical_binder_shift
                            environment (head :: tail)
                            sourceArgumentsEquation
                            targetArgumentsEquation)
  | equal left right =>
      cases sourceLeftEquation :
          Numbered.quote_term_tokens_with?
            free_name sourceNames left with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            sourceLeftEquation] at sourceQuote
      | some sourceLeftTokens =>
          cases sourceRightEquation :
              Numbered.quote_term_tokens_with?
                free_name sourceNames right with
          | none =>
              simp [Numbered.quote_hilbert_tokens_with?,
                sourceLeftEquation,
                sourceRightEquation] at sourceQuote
          | some sourceRightTokens =>
              cases targetLeftEquation :
                  Numbered.quote_term_tokens_with?
                    free_name targetNames left with
              | none =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    targetLeftEquation] at targetQuote
              | some targetLeftTokens =>
                  cases targetRightEquation :
                      Numbered.quote_term_tokens_with?
                        free_name targetNames right with
                  | none =>
                      simp [Numbered.quote_hilbert_tokens_with?,
                        targetLeftEquation,
                        targetRightEquation] at targetQuote
                  | some targetRightTokens =>
                      simp [Numbered.quote_hilbert_tokens_with?,
                        sourceLeftEquation,
                        sourceRightEquation] at sourceQuote
                      simp [Numbered.quote_hilbert_tokens_with?,
                        targetLeftEquation,
                        targetRightEquation] at targetQuote
                      subst sourceTokens
                      subst targetTokens
                      exact
                        CanonicalBinderShiftTokens.equality (quote_term_tokens_with?_canonical_binder_shift
                            environment left sourceLeftEquation
                            targetLeftEquation) (quote_term_tokens_with?_canonical_binder_shift
                            environment right sourceRightEquation
                            targetRightEquation)
  | neg body induction =>
      cases sourceBodyEquation :
          Numbered.quote_hilbert_tokens_with?
            free_name bound_name
            sourceNames depth body with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            sourceBodyEquation] at sourceQuote
      | some sourceBodyTokens =>
          cases targetBodyEquation :
              Numbered.quote_hilbert_tokens_with?
                free_name bound_name
                targetNames (depth + 1) body with
          | none =>
              simp [Numbered.quote_hilbert_tokens_with?,
                targetBodyEquation] at targetQuote
          | some targetBodyTokens =>
              simp [Numbered.quote_hilbert_tokens_with?,
                sourceBodyEquation] at sourceQuote
              simp [Numbered.quote_hilbert_tokens_with?,
                targetBodyEquation] at targetQuote
              subst sourceTokens
              subst targetTokens
              exact CanonicalBinderShiftTokens.negation (induction environment depth
                  sourceBodyEquation targetBodyEquation)
  | conj left right =>
      simp [Numbered.quote_hilbert_tokens_with?] at sourceQuote
  | disj left right =>
      simp [Numbered.quote_hilbert_tokens_with?] at sourceQuote
  | imp left right leftInduction rightInduction =>
      cases sourceLeftEquation :
          Numbered.quote_hilbert_tokens_with?
            free_name bound_name
            sourceNames depth left with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            sourceLeftEquation] at sourceQuote
      | some sourceLeftTokens =>
          cases sourceRightEquation :
              Numbered.quote_hilbert_tokens_with?
                free_name bound_name
                sourceNames depth right with
          | none =>
              simp [Numbered.quote_hilbert_tokens_with?,
                sourceLeftEquation,
                sourceRightEquation] at sourceQuote
          | some sourceRightTokens =>
              cases targetLeftEquation :
                  Numbered.quote_hilbert_tokens_with?
                    free_name bound_name
                    targetNames (depth + 1) left with
              | none =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    targetLeftEquation] at targetQuote
              | some targetLeftTokens =>
                  cases targetRightEquation :
                      Numbered.quote_hilbert_tokens_with?
                        free_name bound_name
                        targetNames (depth + 1) right with
                  | none =>
                      simp [Numbered.quote_hilbert_tokens_with?,
                        targetLeftEquation,
                        targetRightEquation] at targetQuote
                  | some targetRightTokens =>
                      simp [Numbered.quote_hilbert_tokens_with?,
                        sourceLeftEquation,
                        sourceRightEquation] at sourceQuote
                      simp [Numbered.quote_hilbert_tokens_with?,
                        targetLeftEquation,
                        targetRightEquation] at targetQuote
                      subst sourceTokens
                      subst targetTokens
                      exact CanonicalBinderShiftTokens.implication (leftInduction environment depth
                          sourceLeftEquation targetLeftEquation) (rightInduction environment depth
                          sourceRightEquation targetRightEquation)
  | iff left right =>
      simp [Numbered.quote_hilbert_tokens_with?] at sourceQuote
  | forallE sort body induction =>
      cases sourceBodyEquation :
          Numbered.quote_hilbert_tokens_with?
            free_name bound_name (bound_name depth :: sourceNames) (depth + 1) body with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            sourceBodyEquation] at sourceQuote
      | some sourceBodyTokens =>
          cases targetBodyEquation :
              Numbered.quote_hilbert_tokens_with?
                free_name bound_name (bound_name (depth + 1) :: targetNames) ((depth + 1) + 1) body with
          | none =>
              simp [Numbered.quote_hilbert_tokens_with?,
                targetBodyEquation] at targetQuote
          | some targetBodyTokens =>
              simp [Numbered.quote_hilbert_tokens_with?,
                sourceBodyEquation] at sourceQuote
              simp [Numbered.quote_hilbert_tokens_with?,
                targetBodyEquation] at targetQuote
              subst sourceTokens
              subst targetTokens
              exact CanonicalBinderShiftTokens.universal depth (induction (.cons depth environment) (depth + 1)
                  sourceBodyEquation
                  targetBodyEquation)
  | existsE sort body =>
      simp [Numbered.quote_hilbert_tokens_with?] at sourceQuote
/-! ## 对象算术准备 -/
/-- quotation 理论中的乘法项对左右两个已证明等式保持合同。 -/
private theorem gq_binder_shift_multiplication_congr (leftSource leftTarget rightSource rightTarget : SetTerm) (hLeftSource :
      Term.Admissible leftSource SetSort.set) (hLeftTarget :
      Term.Admissible leftTarget SetSort.set) (hRightSource :
      Term.Admissible rightSource SetSort.set) (hRightTarget :
      Term.Admissible rightTarget SetSort.set) (hLeft :
      ⊢ₘ[godel_quotation_theory]
        leftSource ≐ₘ leftTarget) (hRight :
      ⊢ₘ[godel_quotation_theory]
        rightSource ≐ₘ rightTarget) :
    ⊢ₘ[godel_quotation_theory] (leftSource *ₘ rightSource) ≐ₘ (leftTarget *ₘ rightTarget) := by
  let leftParameter :=
    FreshVariable.fresh_id SetSort.set
      [leftSource ≐ₘ leftSource,
        rightSource ≐ₘ rightSource]
  let leftContext : SetTerm := (x#leftParameter) *ₘ rightSource
  have hLeftSourceFresh : (SetSort.set, leftParameter) ∉
        Term.freeSupport leftSource := by
    dsimp [leftParameter]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
          [leftSource ≐ₘ leftSource,
            rightSource ≐ₘ rightSource]) (formula := leftSource ≐ₘ leftSource) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hRightSourceFresh : (SetSort.set, leftParameter) ∉
        Term.freeSupport rightSource := by
    dsimp [leftParameter]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
          [leftSource ≐ₘ leftSource,
            rightSource ≐ₘ rightSource]) (formula := rightSource ≐ₘ rightSource) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hLeftContext :
      Term.Admissible leftContext SetSort.set :=
    natural_multiplication_term_admissible (x#leftParameter) rightSource (set_variable_admissible leftParameter)
      hRightSource
  have hLeftRaw :=
    Metatheory.Derives.term_substituteFree_congr_of_equality
      SetSort.set leftParameter
      leftSource leftTarget leftContext
      hLeftSource hLeftTarget hLeftContext
      hLeftSourceFresh hLeft
  have hRightSourceFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set leftParameter
          replacement rightSource =
        rightSource :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set leftParameter replacement rightSource
      hRightSourceFresh
  have hLeftStep :
      ⊢ₘ[godel_quotation_theory] (leftSource *ₘ rightSource) ≐ₘ (leftTarget *ₘ rightSource) := by
    simpa [leftContext, natural_multiplication_term,
      Term.substituteFree, set_variable,
      hRightSourceFixed] using hLeftRaw
  let rightParameter :=
    FreshVariable.fresh_id SetSort.set
      [rightSource ≐ₘ rightSource,
        leftTarget ≐ₘ leftTarget]
  let rightContext : SetTerm :=
    leftTarget *ₘ (x#rightParameter)
  have hRightSourceFresh' : (SetSort.set, rightParameter) ∉
        Term.freeSupport rightSource := by
    dsimp [rightParameter]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
          [rightSource ≐ₘ rightSource,
            leftTarget ≐ₘ leftTarget]) (formula := rightSource ≐ₘ rightSource) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hLeftTargetFresh : (SetSort.set, rightParameter) ∉
        Term.freeSupport leftTarget := by
    dsimp [rightParameter]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
          [rightSource ≐ₘ rightSource,
            leftTarget ≐ₘ leftTarget]) (formula := leftTarget ≐ₘ leftTarget) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hRightContext :
      Term.Admissible rightContext SetSort.set :=
    natural_multiplication_term_admissible
      leftTarget (x#rightParameter)
      hLeftTarget (set_variable_admissible rightParameter)
  have hRightRaw :=
    Metatheory.Derives.term_substituteFree_congr_of_equality
      SetSort.set rightParameter
      rightSource rightTarget rightContext
      hRightSource hRightTarget hRightContext
      hRightSourceFresh' hRight
  have hLeftTargetFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set rightParameter
          replacement leftTarget =
        leftTarget :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set rightParameter replacement leftTarget
      hLeftTargetFresh
  have hRightStep :
      ⊢ₘ[godel_quotation_theory] (leftTarget *ₘ rightSource) ≐ₘ (leftTarget *ₘ rightTarget) := by
    simpa [rightContext, natural_multiplication_term,
      Term.substituteFree, set_variable,
      hLeftTargetFixed] using hRightRaw
  exact Metatheory.Derives.equality_trans hLeftStep hRightStep
/--
若对象项已经等于具体下标 numeral，则相应带后继指数的素数幂项取标准外部值。
-/
theorem gq_binder_shift_indexed_prime_power_value (prime index : Nat) (indexTerm : SetTerm) (hIndexTerm :
      Term.Admissible indexTerm SetSort.set) (hIndexValue :
      ⊢ₘ[godel_quotation_theory]
        numₘ(index) ≐ₘ indexTerm) :
    ⊢ₘ[godel_quotation_theory]
      numₘ(prime ^ (index + 1)) ≐ₘ
        indexed_prime_power_code_term prime indexTerm := by
  have hNumeralPower :
      ⊢ₘ[godel_quotation_theory]
        numₘ(prime ^ (index + 1)) ≐ₘ
          indexed_prime_power_code_term
            prime (numₘ(index)) := by
    exact gq_weaken_standard_sequence <| by
      simpa [indexed_prime_power_code_term,
        prime_power_code_term, finite_numeral_term] using
        standard_token_sequence_finite_numeral_exponentiation
          prime (index + 1)
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [numₘ(index) ≐ₘ numₘ(index)]
  let context : SetTerm :=
    indexed_prime_power_code_term
      prime (x#parameter)
  have hContext :
      Term.Admissible context SetSort.set :=
    indexed_prime_power_code_term_admissible
      prime (x#parameter) (set_variable_admissible parameter)
  have hIndexFresh : (SetSort.set, parameter) ∉
        Term.freeSupport (numₘ(index)) := by
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hCongruenceRaw :=
    Metatheory.Derives.term_substituteFree_congr_of_equality
      SetSort.set parameter (numₘ(index)) indexTerm context (finite_numeral_term_admissible index)
      hIndexTerm hContext hIndexFresh hIndexValue
  have hCongruence :
      ⊢ₘ[godel_quotation_theory]
        indexed_prime_power_code_term
            prime (numₘ(index)) ≐ₘ
          indexed_prime_power_code_term
            prime indexTerm := by
    have hPrimeFixed (replacement : SetTerm) :
        Term.substituteFree SetSort.set parameter
            replacement (numₘ(prime)) =
          numₘ(prime) := by
      apply Term.substituteFree_eq_self_of_not_mem
      rw [finite_numeral_term_freeSupport]
      exact List.not_mem_nil
    simpa [context, indexed_prime_power_code_term,
      prime_power_code_term, natural_exponentiation_term,
      successor_term, Term.substituteFree,
      set_variable, hPrimeFixed] using hCongruenceRaw
  exact Metatheory.Derives.equality_trans hNumeralPower hCongruence
/-- 两个 indexed prime power 的乘积取得标准外部乘积值。 -/
theorem gq_binder_shift_binary_symbol_value (rightPrime arityPredecessor index : Nat) :
    ⊢ₘ[godel_quotation_theory]
      numₘ(
        3 ^ (arityPredecessor + 1) *
          rightPrime ^ (index + 1)) ≐ₘ (indexed_prime_power_code_term
            3 (numₘ(arityPredecessor)) *ₘ
          indexed_prime_power_code_term
            rightPrime (numₘ(index))) := by
  let leftValue := 3 ^ (arityPredecessor + 1)
  let rightValue := rightPrime ^ (index + 1)
  let leftPower :=
    indexed_prime_power_code_term
      3 (numₘ(arityPredecessor))
  let rightPower :=
    indexed_prime_power_code_term
      rightPrime (numₘ(index))
  have hLeftPower :
      ⊢ₘ[godel_quotation_theory]
        numₘ(leftValue) ≐ₘ leftPower := by
    simpa [leftValue, leftPower] using
      gq_binder_shift_indexed_prime_power_value
        3 arityPredecessor (numₘ(arityPredecessor)) (finite_numeral_term_admissible arityPredecessor) (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) (numₘ(arityPredecessor)))
  have hRightPower :
      ⊢ₘ[godel_quotation_theory]
        numₘ(rightValue) ≐ₘ rightPower := by
    simpa [rightValue, rightPower] using
      gq_binder_shift_indexed_prime_power_value
        rightPrime index (numₘ(index)) (finite_numeral_term_admissible index) (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) (numₘ(index)))
  have hProductNumeral :
      ⊢ₘ[godel_quotation_theory]
        numₘ(leftValue * rightValue) ≐ₘ (numₘ(leftValue) *ₘ numₘ(rightValue)) :=
    gq_weaken_standard_sequence <|
      standard_token_sequence_finite_numeral_multiplication
        leftValue rightValue
  have hProductCongruence :
      ⊢ₘ[godel_quotation_theory] (numₘ(leftValue) *ₘ numₘ(rightValue)) ≐ₘ (leftPower *ₘ rightPower) :=
    gq_binder_shift_multiplication_congr (numₘ(leftValue)) leftPower (numₘ(rightValue)) rightPower (finite_numeral_term_admissible leftValue)
      (indexed_prime_power_code_term_admissible
        3 (numₘ(arityPredecessor)) (finite_numeral_term_admissible arityPredecessor)) (finite_numeral_term_admissible rightValue)
      (indexed_prime_power_code_term_admissible
        rightPrime (numₘ(index)) (finite_numeral_term_admissible index))
      hLeftPower hRightPower
  simpa [leftValue, rightValue, leftPower, rightPower] using
    (Metatheory.Derives.equality_trans
      hProductNumeral hProductCongruence)
/-! ## 单 token 关系的对象表示 -/
/-- 一个固定逻辑 token 的外部 numeral 等于其对象语言符号数值项。 -/
theorem gq_binder_shift_logical_symbol_value (symbol : LogicalSymbolKind) :
    ⊢ₘ[godel_quotation_theory]
      numₘ(Numbered.logical_token symbol) ≐ₘ
        logical_symbol_number_term symbol := by
  exact gq_weaken_standard_sequence <| by
    simpa [Numbered.logical_token,
      logical_symbol_number_term,
      prime_power_code_term] using
      standard_token_sequence_finite_numeral_exponentiation
        2 (logical_symbol_exponent symbol)
/-- 隶属 token 的外部 numeral 等于其对象语言符号数值项。 -/
theorem gq_binder_shift_membership_symbol_value :
    ⊢ₘ[godel_quotation_theory]
      numₘ(Numbered.membership_token) ≐ₘ
        membership_symbol_number_term := by
  exact gq_weaken_standard_sequence <| by
    simpa [Numbered.membership_token,
      membership_symbol_number_term,
      prime_power_code_term] using
      standard_token_sequence_finite_numeral_exponentiation 2 7
/-- 八个固定逻辑 token 分别落入对象层固定 token 枚举。 -/
theorem gq_binder_shift_fixed_logical_condition (symbol : LogicalSymbolKind) :
    ⊢ₘ[godel_quotation_theory]
      canonical_binder_shift_fixed_token_condition (numₘ(Numbered.logical_token symbol)) := by
  have hValue :=
    gq_binder_shift_logical_symbol_value symbol
  have hCondition :=
    canonical_binder_shift_fixed_token_condition_admissible (numₘ(Numbered.logical_token symbol)) (finite_numeral_term_admissible
        (Numbered.logical_token symbol))
  cases symbol with
  | equality =>
      exact FirstOrder.Derives.disjIntroLeft hValue
  | negation =>
      have hTail₁ := Formula.Admissible.disj_right hCondition
      exact FirstOrder.Derives.disjIntroRight <|
          FirstOrder.Derives.disjIntroLeft hValue
  | implication =>
      have hTail₁ := Formula.Admissible.disj_right hCondition
      have hTail₂ := Formula.Admissible.disj_right hTail₁
      exact FirstOrder.Derives.disjIntroRight <|
          FirstOrder.Derives.disjIntroRight <|
              FirstOrder.Derives.disjIntroLeft hValue
  | universal =>
      have hTail₁ := Formula.Admissible.disj_right hCondition
      have hTail₂ := Formula.Admissible.disj_right hTail₁
      have hTail₃ := Formula.Admissible.disj_right hTail₂
      exact FirstOrder.Derives.disjIntroRight <|
          FirstOrder.Derives.disjIntroRight <|
              FirstOrder.Derives.disjIntroRight <|
                  FirstOrder.Derives.disjIntroLeft hValue
  | leftParenthesis =>
      have hTail₁ := Formula.Admissible.disj_right hCondition
      have hTail₂ := Formula.Admissible.disj_right hTail₁
      have hTail₃ := Formula.Admissible.disj_right hTail₂
      have hTail₄ := Formula.Admissible.disj_right hTail₃
      exact FirstOrder.Derives.disjIntroRight <|
          FirstOrder.Derives.disjIntroRight <|
              FirstOrder.Derives.disjIntroRight <|
                  FirstOrder.Derives.disjIntroRight <|
                      FirstOrder.Derives.disjIntroLeft hValue
  | rightParenthesis =>
      have hTail₁ := Formula.Admissible.disj_right hCondition
      have hTail₂ := Formula.Admissible.disj_right hTail₁
      have hTail₃ := Formula.Admissible.disj_right hTail₂
      have hTail₄ := Formula.Admissible.disj_right hTail₃
      have hTail₅ := Formula.Admissible.disj_right hTail₄
      exact FirstOrder.Derives.disjIntroRight <|
          FirstOrder.Derives.disjIntroRight <|
              FirstOrder.Derives.disjIntroRight <|
                  FirstOrder.Derives.disjIntroRight <|
                      FirstOrder.Derives.disjIntroRight <|
                          FirstOrder.Derives.disjIntroLeft hValue
  | existential =>
      have hTail₁ := Formula.Admissible.disj_right hCondition
      have hTail₂ := Formula.Admissible.disj_right hTail₁
      have hTail₃ := Formula.Admissible.disj_right hTail₂
      have hTail₄ := Formula.Admissible.disj_right hTail₃
      have hTail₅ := Formula.Admissible.disj_right hTail₄
      have hTail₆ := Formula.Admissible.disj_right hTail₅
      exact FirstOrder.Derives.disjIntroRight <|
          FirstOrder.Derives.disjIntroRight <|
              FirstOrder.Derives.disjIntroRight <|
                  FirstOrder.Derives.disjIntroRight <|
                      FirstOrder.Derives.disjIntroRight <|
                          FirstOrder.Derives.disjIntroRight <|
                              FirstOrder.Derives.disjIntroLeft hValue
  | conjunction =>
      have hTail₁ := Formula.Admissible.disj_right hCondition
      have hTail₂ := Formula.Admissible.disj_right hTail₁
      have hTail₃ := Formula.Admissible.disj_right hTail₂
      have hTail₄ := Formula.Admissible.disj_right hTail₃
      have hTail₅ := Formula.Admissible.disj_right hTail₄
      have hTail₆ := Formula.Admissible.disj_right hTail₅
      have hTail₇ := Formula.Admissible.disj_right hTail₆
      exact FirstOrder.Derives.disjIntroRight <|
          FirstOrder.Derives.disjIntroRight <|
              FirstOrder.Derives.disjIntroRight <|
                  FirstOrder.Derives.disjIntroRight <|
                      FirstOrder.Derives.disjIntroRight <|
                          FirstOrder.Derives.disjIntroRight <|
                              FirstOrder.Derives.disjIntroRight <|
                                  FirstOrder.Derives.disjIntroLeft hValue
/-- 隶属 token 是固定 token 枚举的最后一个分支。 -/
theorem gq_binder_shift_fixed_membership_condition :
    ⊢ₘ[godel_quotation_theory]
      canonical_binder_shift_fixed_token_condition (numₘ(Numbered.membership_token)) := by
  have hCondition :=
    canonical_binder_shift_fixed_token_condition_admissible (numₘ(Numbered.membership_token)) (finite_numeral_term_admissible
        Numbered.membership_token)
  have hTail₁ := Formula.Admissible.disj_right hCondition
  have hTail₂ := Formula.Admissible.disj_right hTail₁
  have hTail₃ := Formula.Admissible.disj_right hTail₂
  have hTail₄ := Formula.Admissible.disj_right hTail₃
  have hTail₅ := Formula.Admissible.disj_right hTail₄
  have hTail₆ := Formula.Admissible.disj_right hTail₅
  have hTail₇ := Formula.Admissible.disj_right hTail₆
  have hTail₈ := Formula.Admissible.disj_right hTail₇
  exact FirstOrder.Derives.disjIntroRight <|
      FirstOrder.Derives.disjIntroRight <|
          FirstOrder.Derives.disjIntroRight <|
              FirstOrder.Derives.disjIntroRight <|
                  FirstOrder.Derives.disjIntroRight <|
                      FirstOrder.Derives.disjIntroRight <|
                          FirstOrder.Derives.disjIntroRight <|
                              FirstOrder.Derives.disjIntroRight <|
                                  FirstOrder.Derives.disjIntroLeft
                                    gq_binder_shift_membership_symbol_value
/-- 有限 numeral 对任意 de Bruijn 打开保持不变。 -/
theorem gq_binder_shift_numeral_open (value depth : Nat) (replacement : SetTerm) :
    Term.openAt SetSort.set depth replacement (numₘ(value)) =
      numₘ(value) :=
  Term.openAt_eq_self_of_boundClosed
    SetSort.set depth replacement (numₘ(value)) (finite_numeral_term_admissible value).2
/-- 有限 numeral 对任意自由变量闭合保持不变。 -/
theorem gq_binder_shift_numeral_close (value : Nat) (id : FreeVarId) (depth : Nat) :
    Term.closeFreeAt SetSort.set id depth (numₘ(value)) =
      numₘ(value) :=
  Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
    SetSort.set id depth (numₘ(value)) (finite_numeral_term_admissible value).2 (by simp [finite_numeral_term_freeSupport])
/-- 有限 numeral 对任意自由变量替换保持不变；后续序列代码运输复用此结论。 -/
theorem gq_binder_shift_numeral_substitute (value : Nat) (id : FreeVarId) (replacement : SetTerm) :
    Term.substituteFree SetSort.set id replacement (numₘ(value)) =
      numₘ(value) :=
  Term.substituteFree_eq_self_of_not_mem
    SetSort.set id replacement (numₘ(value)) (by simp [finite_numeral_term_freeSupport])
/--
外部单 token 平移关系在对象 quotation 理论中满足公开的 token 条件。
六类非固定 token 均以其规范自然数参数为存在见证；bound 分支额外把下标连续取三次
后继，精确对应名字 `2d+1 ↦ 2d+3`。
-/
theorem canonical_binder_shift_token_condition_with_ids_of_relation
    {sourceToken targetToken : Nat} (relation :
      CanonicalBinderShiftToken sourceToken targetToken) (freshBase : FreeVarId) :
    ⊢ₘ[godel_quotation_theory]
      canonical_binder_shift_token_condition_with_ids (numₘ(sourceToken)) (numₘ(targetToken))
        freshBase (freshBase + 1) (freshBase + 2) (freshBase + 3) (freshBase + 4) (freshBase + 5) (freshBase + 6) := by
  have hConditionCheck :=
    canonical_binder_shift_token_condition_with_ids_check
      (numₘ(sourceToken)) (numₘ(targetToken))
      freshBase (freshBase + 1) (freshBase + 2)
      (freshBase + 3) (freshBase + 4)
      (freshBase + 5) (freshBase + 6)
      (finite_numeral_term_check sourceToken)
      (finite_numeral_term_check targetToken)
  rw [canonical_binder_shift_token_condition_with_ids] at hConditionCheck
  rcases Formula.CheckCertificate.disj_iff.mp hConditionCheck with
    ⟨hFixedCheck, hTail₁Check⟩
  rcases Formula.CheckCertificate.disj_iff.mp hTail₁Check with
    ⟨hFreeCheck, hTail₂Check⟩
  rcases Formula.CheckCertificate.disj_iff.mp hTail₂Check with
    ⟨hBoundCheck, hTail₃Check⟩
  rcases Formula.CheckCertificate.disj_iff.mp hTail₃Check with
    ⟨hConstantCheck, hTail₄Check⟩
  rcases Formula.CheckCertificate.disj_iff.mp hTail₄Check with
    ⟨hFunctionCheck, hPredicateCheck⟩
  cases relation with
  | logical symbol =>
      rw [canonical_binder_shift_token_condition_with_ids]
      have hBase :=
        FirstOrder.Derives.conjIntro (gq_binder_shift_fixed_logical_condition symbol) (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set) (numₘ(Numbered.logical_token symbol)))
      exact FirstOrder.Derives.disjIntroLeft
        (hRightCheck := hTail₁Check) hBase
  | membership =>
      rw [canonical_binder_shift_token_condition_with_ids]
      have hBase :=
        FirstOrder.Derives.conjIntro
          gq_binder_shift_fixed_membership_condition (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set)
            (term := numₘ(Numbered.membership_token))
            (hTermCheck :=
              finite_numeral_term_check Numbered.membership_token))
      exact FirstOrder.Derives.disjIntroLeft
        (hRightCheck := hTail₁Check) hBase
  | free id =>
      let indexTerm :=
        numₘ(2) *ₘ numₘ(id)
      have hIndexTerm :
          Term.Admissible indexTerm SetSort.set :=
        natural_multiplication_term_admissible (numₘ(2)) (numₘ(id)) (finite_numeral_term_admissible 2) (finite_numeral_term_admissible id)
      have hIndexValue :
          ⊢ₘ[godel_quotation_theory]
            numₘ(free_name id) ≐ₘ indexTerm := by
        simpa [indexTerm, free_name] using (gq_weaken_standard_sequence <|
            standard_token_sequence_finite_numeral_multiplication
              2 id)
      have hSourceValue :
          ⊢ₘ[godel_quotation_theory]
            numₘ(Numbered.variable_token (free_name id)) ≐ₘ
              variable_symbol_number_term indexTerm := by
        simpa [Numbered.variable_token,
          variable_symbol_number_term] using
          gq_binder_shift_indexed_prime_power_value
            3 (free_name id) indexTerm
            hIndexTerm hIndexValue
      have hTargetSource :
          ⊢ₘ[godel_quotation_theory]
            numₘ(Numbered.variable_token (free_name id)) ≐ₘ
              numₘ(Numbered.variable_token (free_name id)) :=
        FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (numₘ(Numbered.variable_token (free_name id)))
      have hWitnessBound :
          ⊢ₘ[godel_quotation_theory]
            numₘ(id) ∈ₘ
              Sₘ(numₘ(Numbered.variable_token
                (free_name id))) := by
        have hIdName :
            id ≤ free_name id := by
          simpa [free_name] using
            (Nat.le_mul_of_pos_left id (by decide : 0 < 2))
        have hIdToken :
            id <
              Numbered.variable_token (free_name id) + 1 :=
          Nat.lt_of_le_of_lt hIdName
            (Numbered.variable_name_lt_token_succ
              (free_name id))
        simpa [finite_numeral_term] using
          (gq_weaken_standard_sequence <|
            standard_sequence_finite_numeral_mem_of_lt
              id
              (Numbered.variable_token (free_name id) + 1)
              hIdToken)
      have hBase :
          ⊢ₘ[godel_quotation_theory] ((((numₘ(id) ∈ₘ ωₘ) ∧ₘ
                (numₘ(id) ∈ₘ Sₘ(numₘ(Numbered.variable_token
                  (free_name id))))) ∧ₘ
              (numₘ(Numbered.variable_token (free_name id)) ≐ₘ
                variable_symbol_number_term indexTerm)) ∧ₘ
            (numₘ(Numbered.variable_token (free_name id)) ≐ₘ
              numₘ(Numbered.variable_token (free_name id)))) :=
        FirstOrder.Derives.conjIntro
          (FirstOrder.Derives.conjIntro
            (FirstOrder.Derives.conjIntro
              (gq_weaken_standard_sequence
                (standard_sequence_finite_numeral_mem_omega id))
              hWitnessBound)
            hSourceValue)
          hTargetSource
      rw [canonical_binder_shift_token_condition_with_ids]
      exact FirstOrder.Derives.disjIntroRight
          (hLeftCheck := hFixedCheck) <|
        FirstOrder.Derives.disjIntroLeft
          (hRightCheck := hTail₂Check) <| by
            nd_apply FirstOrder.Derives.exists_intro
              (sort := SetSort.set)
              (term := numₘ(id))
            simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
              Formula.openAt, Formula.closeFreeAt,
              Formula.next_depth, Formula.substituteFree,
              Term.openAt, Term.closeFreeAt, Term.substituteFree,
              set_variable, set_bound_variable,
              indexTerm,
              gq_binder_shift_numeral_open,
              gq_binder_shift_numeral_close] using hBase
  | bound depth =>
      let baseIndex := 2 * depth
      let sourceIndex := Nat.succ baseIndex
      let targetIndex :=
        Nat.succ (Nat.succ (Nat.succ baseIndex))
      let indexProduct :=
        numₘ(2) *ₘ numₘ(depth)
      have hIndexProduct :
          Term.Admissible indexProduct SetSort.set :=
        natural_multiplication_term_admissible (numₘ(2)) (numₘ(depth)) (finite_numeral_term_admissible 2) (finite_numeral_term_admissible depth)
      have hBaseIndex :
          ⊢ₘ[godel_quotation_theory]
            numₘ(baseIndex) ≐ₘ indexProduct := by
        simpa [baseIndex, indexProduct] using (gq_weaken_standard_sequence <|
            standard_token_sequence_finite_numeral_multiplication
              2 depth)
      have hSourceIndexRaw :=
        successor_term_congr_of_equality (numₘ(baseIndex)) indexProduct (finite_numeral_term_admissible baseIndex)
          hIndexProduct hBaseIndex
      have hSourceIndex :
          ⊢ₘ[godel_quotation_theory]
            numₘ(sourceIndex) ≐ₘ
              Sₘ(indexProduct) := by
        simpa [sourceIndex, finite_numeral_term] using
          hSourceIndexRaw
      have hTargetIndex₂Raw :=
        successor_term_congr_of_equality (numₘ(sourceIndex)) (Sₘ(indexProduct)) (finite_numeral_term_admissible sourceIndex) (successor_term_admissible
            indexProduct hIndexProduct)
          hSourceIndex
      have hTargetIndex₂ :
          ⊢ₘ[godel_quotation_theory]
            numₘ(Nat.succ sourceIndex) ≐ₘ
              Sₘ(Sₘ(indexProduct)) := by
        simpa [finite_numeral_term] using hTargetIndex₂Raw
      have hTargetIndexRaw :=
        successor_term_congr_of_equality (numₘ(Nat.succ sourceIndex)) (Sₘ(Sₘ(indexProduct))) (finite_numeral_term_admissible (Nat.succ sourceIndex))
          (successor_term_admissible (Sₘ(indexProduct)) (successor_term_admissible
              indexProduct hIndexProduct))
          hTargetIndex₂
      have hTargetIndex :
          ⊢ₘ[godel_quotation_theory]
            numₘ(targetIndex) ≐ₘ
              Sₘ(Sₘ(Sₘ(indexProduct))) := by
        simpa [targetIndex, sourceIndex,
          finite_numeral_term] using hTargetIndexRaw
      have hSourceName :
          bound_name depth = sourceIndex := by
        simp [bound_name, sourceIndex, baseIndex]
      have hTargetName :
          bound_name (depth + 1) = targetIndex := by
        simp [bound_name, targetIndex, baseIndex]
        omega
      have hSourceValue :
          ⊢ₘ[godel_quotation_theory]
            numₘ(Numbered.variable_token (bound_name depth)) ≐ₘ
              variable_symbol_number_term (Sₘ(indexProduct)) := by
        rw [hSourceName]
        simpa [Numbered.variable_token,
          variable_symbol_number_term] using
          gq_binder_shift_indexed_prime_power_value
            3 sourceIndex (Sₘ(indexProduct)) (successor_term_admissible
              indexProduct hIndexProduct)
            hSourceIndex
      have hTargetValue :
          ⊢ₘ[godel_quotation_theory]
            numₘ(
                Numbered.variable_token (bound_name (depth + 1))) ≐ₘ
              variable_symbol_number_term (Sₘ(Sₘ(Sₘ(indexProduct)))) := by
        rw [hTargetName]
        simpa [Numbered.variable_token,
          variable_symbol_number_term] using
          gq_binder_shift_indexed_prime_power_value
            3 targetIndex (Sₘ(Sₘ(Sₘ(indexProduct)))) (successor_term_admissible (Sₘ(Sₘ(indexProduct))) (successor_term_admissible (Sₘ(indexProduct))
                (successor_term_admissible
                  indexProduct hIndexProduct)))
            hTargetIndex
      have hWitnessBound :
          ⊢ₘ[godel_quotation_theory]
            numₘ(depth) ∈ₘ
              Sₘ(numₘ(Numbered.variable_token
                (bound_name depth))) := by
        have hDepthName :
            depth < bound_name depth := by
          simp [bound_name]
          omega
        have hDepthToken :
            depth <
              Numbered.variable_token (bound_name depth) + 1 :=
          Nat.lt_trans hDepthName
            (Numbered.variable_name_lt_token_succ
              (bound_name depth))
        simpa [finite_numeral_term] using
          (gq_weaken_standard_sequence <|
            standard_sequence_finite_numeral_mem_of_lt
              depth
              (Numbered.variable_token (bound_name depth) + 1)
              hDepthToken)
      have hBase :
          ⊢ₘ[godel_quotation_theory] ((((numₘ(depth) ∈ₘ ωₘ) ∧ₘ
                (numₘ(depth) ∈ₘ Sₘ(numₘ(Numbered.variable_token
                  (bound_name depth))))) ∧ₘ
              (numₘ(Numbered.variable_token (bound_name depth)) ≐ₘ
                variable_symbol_number_term (Sₘ(indexProduct)))) ∧ₘ
            (numₘ(Numbered.variable_token (bound_name (depth + 1))) ≐ₘ
              variable_symbol_number_term (Sₘ(Sₘ(Sₘ(indexProduct)))))) :=
        FirstOrder.Derives.conjIntro
          (FirstOrder.Derives.conjIntro
            (FirstOrder.Derives.conjIntro
              (gq_weaken_standard_sequence
                (standard_sequence_finite_numeral_mem_omega depth))
              hWitnessBound)
            hSourceValue)
          hTargetValue
      rw [canonical_binder_shift_token_condition_with_ids]
      exact FirstOrder.Derives.disjIntroRight
          (hLeftCheck := hFixedCheck) <|
        FirstOrder.Derives.disjIntroRight
            (hLeftCheck := hFreeCheck) <|
          FirstOrder.Derives.disjIntroLeft
            (hRightCheck := hTail₃Check) <| by
                nd_apply FirstOrder.Derives.exists_intro
                  (sort := SetSort.set)
                  (term := numₘ(depth))
                simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
                  Formula.openAt, Formula.closeFreeAt,
                  Formula.next_depth, Formula.substituteFree,
                  Term.openAt, Term.closeFreeAt,
                  Term.substituteFree, set_variable,
                  set_bound_variable, indexProduct,
                  gq_binder_shift_numeral_open,
                  gq_binder_shift_numeral_close] using hBase
  | constant index =>
      have hIndexReflexive :
          ⊢ₘ[godel_quotation_theory]
            numₘ(index) ≐ₘ numₘ(index) :=
        FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) (numₘ(index))
      have hSourceValue :
          ⊢ₘ[godel_quotation_theory]
            numₘ(Numbered.constant_token index) ≐ₘ
              constant_symbol_number_term (numₘ(index)) := by
        simpa [Numbered.constant_token,
          constant_symbol_number_term] using
          gq_binder_shift_indexed_prime_power_value
            5 index (numₘ(index)) (finite_numeral_term_admissible index)
            hIndexReflexive
      have hTargetSource :
          ⊢ₘ[godel_quotation_theory]
            numₘ(Numbered.constant_token index) ≐ₘ
              numₘ(Numbered.constant_token index) :=
        FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (numₘ(Numbered.constant_token index))
      have hBase :
          ⊢ₘ[godel_quotation_theory] (((numₘ(index) ∈ₘ ωₘ) ∧ₘ (numₘ(Numbered.constant_token index) ≐ₘ
                  constant_symbol_number_term (numₘ(index)))) ∧ₘ (numₘ(Numbered.constant_token index) ≐ₘ
                numₘ(Numbered.constant_token index))) :=
        FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro (gq_weaken_standard_sequence (standard_sequence_finite_numeral_mem_omega index))
            hSourceValue)
          hTargetSource
      rw [canonical_binder_shift_token_condition_with_ids]
      exact FirstOrder.Derives.disjIntroRight
          (hLeftCheck := hFixedCheck) <|
        FirstOrder.Derives.disjIntroRight
            (hLeftCheck := hFreeCheck) <|
          FirstOrder.Derives.disjIntroRight
              (hLeftCheck := hBoundCheck) <|
            FirstOrder.Derives.disjIntroLeft
              (hRightCheck := hTail₄Check) <| by
                    nd_apply FirstOrder.Derives.exists_intro
                      (sort := SetSort.set)
                      (term := numₘ(index))
                    simpa [
                      Formula.openAt_closeFreeAt_eq_substituteFree,
                      Formula.openAt, Formula.closeFreeAt,
                      Formula.next_depth, Formula.substituteFree,
                      Term.openAt, Term.closeFreeAt,
                      Term.substituteFree, set_variable,
                      set_bound_variable,
                      gq_binder_shift_numeral_open,
                      gq_binder_shift_numeral_close] using hBase
  | function arityPredecessor index =>
      have hSourceValue :
          ⊢ₘ[godel_quotation_theory]
            numₘ(
                Numbered.function_token
                  arityPredecessor index) ≐ₘ
              coded_function_symbol_number_term (numₘ(arityPredecessor)) (numₘ(index)) := by
        simpa [Numbered.function_token,
          coded_function_symbol_number_term] using
          gq_binder_shift_binary_symbol_value
            5 arityPredecessor index
      have hTargetSource :
          ⊢ₘ[godel_quotation_theory]
            numₘ(
                Numbered.function_token
                  arityPredecessor index) ≐ₘ
              numₘ(
                Numbered.function_token
                  arityPredecessor index) :=
        FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (numₘ(Numbered.function_token
            arityPredecessor index))
      have hBase :
          ⊢ₘ[godel_quotation_theory] ((((numₘ(arityPredecessor) ∈ₘ ωₘ) ∧ₘ (numₘ(index) ∈ₘ ωₘ)) ∧ₘ (numₘ(
                  Numbered.function_token
                    arityPredecessor index) ≐ₘ
                coded_function_symbol_number_term (numₘ(arityPredecessor)) (numₘ(index)))) ∧ₘ (numₘ(
                  Numbered.function_token
                    arityPredecessor index) ≐ₘ
                numₘ(
                  Numbered.function_token
                    arityPredecessor index))) :=
        FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro (gq_weaken_standard_sequence
                (standard_sequence_finite_numeral_mem_omega
                  arityPredecessor)) (gq_weaken_standard_sequence (standard_sequence_finite_numeral_mem_omega index)))
            hSourceValue)
          hTargetSource
      rw [canonical_binder_shift_token_condition_with_ids]
      exact FirstOrder.Derives.disjIntroRight
          (hLeftCheck := hFixedCheck) <|
        FirstOrder.Derives.disjIntroRight
            (hLeftCheck := hFreeCheck) <|
          FirstOrder.Derives.disjIntroRight
              (hLeftCheck := hBoundCheck) <|
            FirstOrder.Derives.disjIntroRight
                (hLeftCheck := hConstantCheck) <|
              FirstOrder.Derives.disjIntroLeft
                (hRightCheck := hPredicateCheck) <| by
                        nd_apply FirstOrder.Derives.exists_intro
                          (sort := SetSort.set)
                          (term := numₘ(arityPredecessor))
                        nd_apply FirstOrder.Derives.exists_intro
                          (sort := SetSort.set)
                          (term := numₘ(index))
                        simpa [
                          Formula.openAt_closeFreeAt_eq_substituteFree,
                          Formula.openAt, Formula.closeFreeAt,
                          Formula.next_depth, Formula.substituteFree,
                          Term.openAt, Term.closeFreeAt,
                          Term.substituteFree, set_variable,
                          set_bound_variable,
                          gq_binder_shift_numeral_open,
                          gq_binder_shift_numeral_close] using hBase
  | predicate arityPredecessor index =>
      have hSourceValue :
          ⊢ₘ[godel_quotation_theory]
            numₘ(
                Numbered.predicate_token
                  arityPredecessor index) ≐ₘ
              coded_predicate_symbol_number_term (numₘ(arityPredecessor)) (numₘ(index)) := by
        simpa [Numbered.predicate_token,
          coded_predicate_symbol_number_term] using
          gq_binder_shift_binary_symbol_value
            7 arityPredecessor index
      have hTargetSource :
          ⊢ₘ[godel_quotation_theory]
            numₘ(
                Numbered.predicate_token
                  arityPredecessor index) ≐ₘ
              numₘ(
                Numbered.predicate_token
                  arityPredecessor index) :=
        FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set)
          (numₘ(Numbered.predicate_token
            arityPredecessor index))
      have hBase :
          ⊢ₘ[godel_quotation_theory] ((((numₘ(arityPredecessor) ∈ₘ ωₘ) ∧ₘ (numₘ(index) ∈ₘ ωₘ)) ∧ₘ (numₘ(
                  Numbered.predicate_token
                    arityPredecessor index) ≐ₘ
                coded_predicate_symbol_number_term (numₘ(arityPredecessor)) (numₘ(index)))) ∧ₘ (numₘ(
                  Numbered.predicate_token
                    arityPredecessor index) ≐ₘ
                numₘ(
                  Numbered.predicate_token
                    arityPredecessor index))) :=
        FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro (gq_weaken_standard_sequence
                (standard_sequence_finite_numeral_mem_omega
                  arityPredecessor)) (gq_weaken_standard_sequence (standard_sequence_finite_numeral_mem_omega index)))
            hSourceValue)
          hTargetSource
      rw [canonical_binder_shift_token_condition_with_ids]
      exact FirstOrder.Derives.disjIntroRight
          (hLeftCheck := hFixedCheck) <|
        FirstOrder.Derives.disjIntroRight
            (hLeftCheck := hFreeCheck) <|
          FirstOrder.Derives.disjIntroRight
              (hLeftCheck := hBoundCheck) <|
            FirstOrder.Derives.disjIntroRight
                (hLeftCheck := hConstantCheck) <|
              FirstOrder.Derives.disjIntroRight
                (hLeftCheck := hFunctionCheck) <| by
                        nd_apply FirstOrder.Derives.exists_intro
                          (sort := SetSort.set)
                          (term := numₘ(arityPredecessor))
                        nd_apply FirstOrder.Derives.exists_intro
                          (sort := SetSort.set)
                          (term := numₘ(index))
                        simpa [
                          Formula.openAt_closeFreeAt_eq_substituteFree,
                          Formula.openAt, Formula.closeFreeAt,
                          Formula.next_depth, Formula.substituteFree,
                          Term.openAt, Term.closeFreeAt,
                          Term.substituteFree, set_variable,
                          set_bound_variable,
                          gq_binder_shift_numeral_open,
                          gq_binder_shift_numeral_close] using hBase
/-- 自动新鲜编号封装下的单 token 对象表示。 -/
theorem canonical_binder_shift_token_condition_of_relation
    {sourceToken targetToken : Nat} (relation :
      CanonicalBinderShiftToken sourceToken targetToken) :
    ⊢ₘ[godel_quotation_theory]
      canonical_binder_shift_token_condition (numₘ(sourceToken)) (numₘ(targetToken)) := by
  rw [canonical_binder_shift_token_condition]
  exact
    canonical_binder_shift_token_condition_with_ids_of_relation
      relation _
/--
把单 token 条件从标准 numeral 运输到任意两个已对齐的对象项。
显式见证编号保持固定，因此这里只做普通 Leibniz 等词运输。调用方只需保证从
`freshBase` 起的编号不出现在两个对象值中；这既覆盖闭项，也允许值依赖更小编号的
外层逐点指标，并保证运输与七个存在见证的闭包严格交换。
-/
theorem canonical_binder_shift_token_condition_with_ids_of_values
    {sourceToken targetToken : Nat}
    {Γ : Context signature} (relation :
      CanonicalBinderShiftToken sourceToken targetToken) (freshBase : FreeVarId) (sourceValue targetValue : SetTerm) (hSourceValue :
      Term.Admissible sourceValue SetSort.set) (hTargetValue :
      Term.Admissible targetValue SetSort.set) (hSourceFreshFrom :
      ∀ id, freshBase ≤ id → (SetSort.set, id) ∉ Term.freeSupport sourceValue) (hTargetFreshFrom :
      ∀ id, freshBase ≤ id → (SetSort.set, id) ∉ Term.freeSupport targetValue) (hSourceEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        sourceValue ≐ₘ numₘ(sourceToken)) (hTargetEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        targetValue ≐ₘ numₘ(targetToken)) :
    Γ ⊢ₘ[godel_quotation_theory]
      canonical_binder_shift_token_condition_with_ids
        sourceValue targetValue
        freshBase (freshBase + 1) (freshBase + 2) (freshBase + 3) (freshBase + 4) (freshBase + 5) (freshBase + 6) := by
  let sourceParameter := freshBase + 7
  let targetParameter := freshBase + 8
  let numeralTarget := numₘ(targetToken)
  have hSourceHoleFresh : (SetSort.set, sourceParameter) ∉
        Term.freeSupport sourceValue := by
    exact hSourceFreshFrom sourceParameter (by
      simp [sourceParameter])
  have hTargetHoleFresh : (SetSort.set, targetParameter) ∉
        Term.freeSupport sourceValue := by
    exact hSourceFreshFrom targetParameter (by
      simp [targetParameter])
  have hFreshBaseLeAdd (offset : Nat) :
      freshBase ≤ freshBase + offset := by
    exact Nat.le_add_right freshBase offset
  have hSourceFixedByTarget :
      Term.substituteFree SetSort.set targetParameter
          targetValue sourceValue =
        sourceValue :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set targetParameter targetValue sourceValue
      hTargetHoleFresh
  have hSourceFixedByTargetNumeral :
      Term.substituteFree SetSort.set targetParameter (numₘ(targetToken)) sourceValue =
        sourceValue :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set targetParameter (numₘ(targetToken))
      sourceValue hTargetHoleFresh
  have hSourceCloseCommute (closedId : FreeVarId) (depth : Nat) (formula : SetFormula) (hLower : freshBase ≤ closedId)
      (hDistinct : sourceParameter ≠ closedId) :
      Formula.substituteFree SetSort.set sourceParameter
          sourceValue (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth (Formula.substituteFree SetSort.set sourceParameter
            sourceValue formula) := by
    exact (Formula.closeFreeAt_substituteFree_comm
        SetSort.set sourceParameter closedId depth
        sourceValue formula hDistinct hSourceValue.2 (hSourceFreshFrom closedId hLower)).symm
  have hTargetCloseCommute (closedId : FreeVarId) (depth : Nat) (formula : SetFormula) (hLower : freshBase ≤ closedId)
      (hDistinct : targetParameter ≠ closedId) :
      Formula.substituteFree SetSort.set targetParameter
          targetValue (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth (Formula.substituteFree SetSort.set targetParameter
            targetValue formula) := by
    exact (Formula.closeFreeAt_substituteFree_comm
        SetSort.set targetParameter closedId depth
        targetValue formula hDistinct hTargetValue.2 (hTargetFreshFrom closedId hLower)).symm
  have hNumeralCloseCommute (parameter closedId : FreeVarId) (depth value : Nat) (formula : SetFormula) (hDistinct : parameter ≠ closedId) :
      Formula.substituteFree SetSort.set parameter (numₘ(value)) (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth (Formula.substituteFree SetSort.set parameter (numₘ(value)) formula) := by
    exact (Formula.closeFreeAt_substituteFree_comm
        SetSort.set parameter closedId depth (numₘ(value)) formula hDistinct (finite_numeral_term_admissible value).2
        (by simp [finite_numeral_term_freeSupport])).symm
  let sourceBody : SetFormula :=
    canonical_binder_shift_token_condition_with_ids (x#sourceParameter) numeralTarget
      freshBase (freshBase + 1) (freshBase + 2) (freshBase + 3) (freshBase + 4) (freshBase + 5) (freshBase + 6)
  have hNumeralCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        canonical_binder_shift_token_condition_with_ids (numₘ(sourceToken)) (numₘ(targetToken))
          freshBase (freshBase + 1) (freshBase + 2) (freshBase + 3) (freshBase + 4) (freshBase + 5) (freshBase + 6) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) (canonical_binder_shift_token_condition_with_ids_of_relation
        relation freshBase)
  have hSourceIffRaw :=
    Metatheory.Derives.equality_iff_of_equality (T := godel_quotation_theory) (Γ := Γ) (sort := SetSort.set) (eigen := sourceParameter) (left := sourceValue)
      (right := numₘ(sourceToken)) (body := sourceBody)
      hSourceEquality
  have hSourceIff :
      Γ ⊢ₘ[godel_quotation_theory]
        canonical_binder_shift_token_condition_with_ids
            sourceValue numeralTarget
            freshBase (freshBase + 1) (freshBase + 2) (freshBase + 3) (freshBase + 4) (freshBase + 5) (freshBase + 6) ↔ₘ
          canonical_binder_shift_token_condition_with_ids (numₘ(sourceToken)) numeralTarget
            freshBase (freshBase + 1) (freshBase + 2) (freshBase + 3) (freshBase + 4) (freshBase + 5) (freshBase + 6) := by
    simpa [sourceBody, sourceParameter, numeralTarget,
      canonical_binder_shift_token_condition_with_ids,
      Formula.substituteFree, Term.substituteFree,
      set_variable, hSourceHoleFresh,
      hSourceCloseCommute,
      hFreshBaseLeAdd,
      hNumeralCloseCommute,
      gq_binder_shift_numeral_substitute] using hSourceIffRaw
  have hAtSource :
      Γ ⊢ₘ[godel_quotation_theory]
        canonical_binder_shift_token_condition_with_ids
          sourceValue numeralTarget
          freshBase (freshBase + 1) (freshBase + 2) (freshBase + 3) (freshBase + 4) (freshBase + 5) (freshBase + 6) :=
    FirstOrder.Derives.iffElimLeft hSourceIff <| by
      simpa [numeralTarget] using hNumeralCondition
  let targetBody : SetFormula :=
    canonical_binder_shift_token_condition_with_ids
      sourceValue (x#targetParameter)
      freshBase (freshBase + 1) (freshBase + 2) (freshBase + 3) (freshBase + 4) (freshBase + 5) (freshBase + 6)
  have hTargetIffRaw :=
    Metatheory.Derives.equality_iff_of_equality (T := godel_quotation_theory) (Γ := Γ) (sort := SetSort.set) (eigen := targetParameter) (left := targetValue)
      (right := numₘ(targetToken)) (body := targetBody)
      hTargetEquality
  have hTargetIff :
      Γ ⊢ₘ[godel_quotation_theory]
        canonical_binder_shift_token_condition_with_ids
            sourceValue targetValue
            freshBase (freshBase + 1) (freshBase + 2) (freshBase + 3) (freshBase + 4) (freshBase + 5) (freshBase + 6) ↔ₘ
          canonical_binder_shift_token_condition_with_ids
            sourceValue numeralTarget
            freshBase (freshBase + 1) (freshBase + 2) (freshBase + 3) (freshBase + 4) (freshBase + 5) (freshBase + 6) := by
    simpa [targetBody, targetParameter, numeralTarget,
      canonical_binder_shift_token_condition_with_ids,
      Formula.substituteFree, Term.substituteFree,
      set_variable, hTargetHoleFresh,
      hSourceFixedByTarget, hSourceFixedByTargetNumeral,
      hTargetCloseCommute,
      hFreshBaseLeAdd,
      hNumeralCloseCommute,
      gq_binder_shift_numeral_substitute] using hTargetIffRaw
  exact FirstOrder.Derives.iffElimLeft
    hTargetIff hAtSource
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
