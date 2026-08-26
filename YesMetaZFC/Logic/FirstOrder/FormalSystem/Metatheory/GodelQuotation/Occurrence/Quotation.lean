import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Substitution
/-!
# Gödel quotation 的 token 出现性前端
本模块证明规范 quotation 的名字域分离、binder 深度避让与量词后继不变量。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
universe u v w
set_option autoImplicit false
/-! ## 元层 token 新鲜性 -/
/--
若目标名字既不在 bound 环境中，也不在自由命名函数的像中，则项 quotation 不含
对应变量 token。
与 `quote_term_tokens_with?_target_not_mem` 不同，本定理不依赖某个具体自由变量的
新鲜性，专门服务自由名字域与 binder 名字域的全局分离。
-/
private theorem quote_term_tokens_with?_name_not_mem
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming : FreeVarId → Nat) (boundNames : List Nat) (targetName : Nat) (hFreeNames :
      ∀ id, freeNaming id ≠ targetName) (hBoundNames : targetName ∉ boundNames)
    {term : Term σ} {tokens : List Nat} (hQuote :
      Numbered.quote_term_tokens_with?
        freeNaming boundNames term = some tokens) :
    Numbered.variable_token targetName ∉ tokens := by
  refine Term.rec (motive_1 := fun term =>
      ∀ tokens,
        Numbered.quote_term_tokens_with?
            freeNaming boundNames term = some tokens →
          Numbered.variable_token targetName ∉ tokens) (motive_2 := fun terms =>
      ∀ pieces,
        terms.mapM (Numbered.quote_term_tokens_with?
              freeNaming boundNames) = some pieces →
          ∀ piece, piece ∈ pieces →
            Numbered.variable_token targetName ∉ piece)
    ?_ ?_ ?_ ?_ term tokens hQuote
  · intro sourceVar sourceTokens hSourceQuote
    cases sourceVar with
    | bvar sort index =>
        cases hName : boundNames[index]? with
        | none =>
            simp [Numbered.quote_term_tokens_with?,
              hName] at hSourceQuote
        | some name =>
            have hNames : name ≠ targetName := by
              intro hEqual
              apply hBoundNames
              rw [← hEqual]
              exact List.mem_of_getElem? hName
            simp [Numbered.quote_term_tokens_with?,
              hName] at hSourceQuote
            subst sourceTokens
            simpa using (variable_token_ne_variable_token hNames).symm
    | fvar sort id =>
        simp [Numbered.quote_term_tokens_with?] at hSourceQuote
        subst sourceTokens
        simpa using (variable_token_ne_variable_token (hFreeNames id)).symm
  · intro function arguments ih resultTokens hResultQuote
    cases hArgumentTokens :
        arguments.mapM (Numbered.quote_term_tokens_with?
            freeNaming boundNames) with
    | none =>
        simp [Numbered.quote_term_tokens_with?,
          hArgumentTokens] at hResultQuote
    | some argumentTokens =>
        have hPieces :
            ∀ piece, piece ∈ argumentTokens →
              Numbered.variable_token targetName ∉ piece :=
          ih argumentTokens hArgumentTokens
        cases argumentTokens with
        | nil =>
            simp [Numbered.quote_term_tokens_with?,
              hArgumentTokens] at hResultQuote
            subst resultTokens
            simpa using (constant_token_ne_variable_token (QuotationNumbering.function_number function)
                targetName).symm
        | cons head tail =>
            simp [Numbered.quote_term_tokens_with?,
              hArgumentTokens] at hResultQuote
            subst resultTokens
            have hFlatten :
                Numbered.variable_token targetName ∉ (head :: tail).flatten := by
              intro hMember
              rcases List.mem_flatten.mp hMember with
                ⟨piece, hPiece, hToken⟩
              exact hPieces piece hPiece hToken
            simpa [Numbered.function_application_tokens, (function_token_ne_variable_token (arguments.length - 1) (QuotationNumbering.function_number function)
                targetName).symm, (logical_token_ne_variable_token
                .leftParenthesis targetName).symm, (logical_token_ne_variable_token
                .rightParenthesis targetName).symm] using
              hFlatten
  · intro pieces hPieces piece hPiece
    simp at hPieces
    subst pieces
    simp at hPiece
  · intro head tail ihHead ihTail pieces hPieces piece hPiece
    cases hHeadTokens :
        Numbered.quote_term_tokens_with?
          freeNaming boundNames head with
    | none =>
        simp [hHeadTokens] at hPieces
    | some headTokens =>
        cases hTailTokens :
            tail.mapM (Numbered.quote_term_tokens_with?
                freeNaming boundNames) with
        | none =>
            simp [hHeadTokens, hTailTokens] at hPieces
        | some tailTokens =>
            simp [hHeadTokens, hTailTokens] at hPieces
            subst pieces
            simp only [List.mem_cons] at hPiece
            rcases hPiece with rfl | hPiece
            · exact ihHead _ hHeadTokens
            · exact ihTail tailTokens hTailTokens piece hPiece
/-! ## 规范 binder 深度避让 -/
mutual
  /--
  项在入口深度 `entryDepth` 下不引用绝对 binder 深度 `targetDepth`。
  绝对深度把 de Bruijn index 重新解释为 quotation 使用的 binder 编号；该谓词因此
  不会随着进入内部量词而改变目标，适合描述 schema 为局部变量预留的空槽。
  -/
  def quotation_term_avoids_bound_depth
      {σ : Signature.{u, v, w}} (entryDepth targetDepth : Nat) : Term σ → Prop
    | .var (.bvar _ index) =>
        entryDepth - index - 1 ≠ targetDepth
    | .var (.fvar _ _) =>
        True
    | .app _ arguments =>
        quotation_terms_avoid_bound_depth
          entryDepth targetDepth arguments
  /-- 项列表逐项避开同一个绝对 binder 深度。 -/
  def quotation_terms_avoid_bound_depth
      {σ : Signature.{u, v, w}} (entryDepth targetDepth : Nat) :
      List (Term σ) → Prop
    | [] =>
        True
    | term :: terms =>
        quotation_term_avoids_bound_depth
            entryDepth targetDepth term ∧
          quotation_terms_avoid_bound_depth
            entryDepth targetDepth terms
end
/--
公式在入口深度 `entryDepth` 下不引用绝对 binder 深度 `targetDepth`。
进入量词时，新 binder 的绝对深度就是当前 `entryDepth`，其余引用在递增后的入口
深度中继续检查。该定义覆盖完整公式语法；Hilbert quotation 只消费其中的核心分支。
-/
def quotation_formula_avoids_bound_depth
    {σ : Signature.{u, v, w}} (entryDepth targetDepth : Nat) :
    Formula σ → Prop
  | .falsum | .truth =>
      True
  | .rel _ arguments =>
      quotation_terms_avoid_bound_depth
        entryDepth targetDepth arguments
  | .equal left right =>
      quotation_term_avoids_bound_depth
          entryDepth targetDepth left ∧
        quotation_term_avoids_bound_depth
          entryDepth targetDepth right
  | .neg body =>
      quotation_formula_avoids_bound_depth
        entryDepth targetDepth body
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      quotation_formula_avoids_bound_depth
          entryDepth targetDepth left ∧
        quotation_formula_avoids_bound_depth
          entryDepth targetDepth right
  | .forallE _ body
  | .existsE _ body =>
      entryDepth ≠ targetDepth ∧
        quotation_formula_avoids_bound_depth (entryDepth + 1) targetDepth body
/-- 规范 binder 环境的第 `index` 项正是相应绝对深度的奇数名字。 -/
theorem canonical_bound_names_getElem? (entryDepth index : Nat) (hIndex : index < entryDepth) : (canonical_bound_names entryDepth)[index]? =
      some (bound_name (entryDepth - index - 1)) := by
  induction entryDepth generalizing index with
  | zero =>
      omega
  | succ entryDepth ih =>
      cases index with
      | zero =>
          simp [canonical_bound_names]
      | succ index =>
          have hPrevious : index < entryDepth := by
            omega
          have hArithmetic :
              entryDepth + 1 - (index + 1) - 1 =
                entryDepth - index - 1 := by
            omega
          simpa [canonical_bound_names, hArithmetic] using
            ih index hPrevious
/--
若项避开某个绝对 binder 深度，则规范 token quotation 不含该 binder 的变量 token。
-/
theorem quote_term_tokens_with?_avoid_bound_depth
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol] (entryDepth targetDepth : Nat)
    {term : Term σ} {tokens : List Nat} (hAvoid :
      quotation_term_avoids_bound_depth
        entryDepth targetDepth term) (hQuote :
      Numbered.quote_term_tokens_with?
        free_name (canonical_bound_names entryDepth) term =
          some tokens) :
    Numbered.variable_token (bound_name targetDepth) ∉ tokens := by
  refine Term.rec (motive_1 := fun term =>
      ∀ tokens,
        quotation_term_avoids_bound_depth
            entryDepth targetDepth term →
        Numbered.quote_term_tokens_with?
            free_name (canonical_bound_names entryDepth) term =
          some tokens →
        Numbered.variable_token (bound_name targetDepth) ∉ tokens) (motive_2 := fun terms =>
      ∀ pieces,
        quotation_terms_avoid_bound_depth
            entryDepth targetDepth terms →
        terms.mapM (Numbered.quote_term_tokens_with?
              free_name (canonical_bound_names entryDepth)) =
          some pieces →
        ∀ piece, piece ∈ pieces →
          Numbered.variable_token (bound_name targetDepth) ∉ piece)
    ?_ ?_ ?_ ?_ term tokens hAvoid hQuote
  · intro sourceVar sourceTokens hSourceAvoid hSourceQuote
    cases sourceVar with
    | bvar sort index =>
        cases hName : (canonical_bound_names entryDepth)[index]? with
        | none =>
            simp [Numbered.quote_term_tokens_with?,
              hName] at hSourceQuote
        | some name =>
            have hIndex : index < entryDepth := by
              simpa using (List.getElem?_eq_some_iff.mp hName).1
            have hCanonical :=
              canonical_bound_names_getElem?
                entryDepth index hIndex
            have hNameValue :
                name =
                  bound_name (entryDepth - index - 1) :=
              Option.some.inj (hName.symm.trans hCanonical)
            have hNames :
                name ≠ bound_name targetDepth := by
              intro hEqual
              exact hSourceAvoid <|
                bound_name_injective (hNameValue.symm.trans hEqual)
            simp [Numbered.quote_term_tokens_with?,
              hName] at hSourceQuote
            subst sourceTokens
            simpa using (variable_token_ne_variable_token hNames).symm
    | fvar sort id =>
        simp [Numbered.quote_term_tokens_with?] at hSourceQuote
        subst sourceTokens
        simpa using (variable_token_ne_variable_token (free_name_ne_bound_name id targetDepth)).symm
  · intro function arguments ih resultTokens
      hResultAvoid hResultQuote
    cases hArgumentTokens :
        arguments.mapM (Numbered.quote_term_tokens_with?
            free_name (canonical_bound_names entryDepth)) with
    | none =>
        simp [Numbered.quote_term_tokens_with?,
          hArgumentTokens] at hResultQuote
    | some argumentTokens =>
        have hPieces :
            ∀ piece, piece ∈ argumentTokens →
              Numbered.variable_token (bound_name targetDepth) ∉ piece :=
          ih argumentTokens hResultAvoid hArgumentTokens
        cases argumentTokens with
        | nil =>
            simp [Numbered.quote_term_tokens_with?,
              hArgumentTokens] at hResultQuote
            subst resultTokens
            simpa using (constant_token_ne_variable_token (QuotationNumbering.function_number function) (bound_name targetDepth)).symm
        | cons head tail =>
            simp [Numbered.quote_term_tokens_with?,
              hArgumentTokens] at hResultQuote
            subst resultTokens
            have hFlatten :
                Numbered.variable_token (bound_name targetDepth) ∉ (head :: tail).flatten := by
              intro hMember
              rcases List.mem_flatten.mp hMember with
                ⟨piece, hPiece, hToken⟩
              exact hPieces piece hPiece hToken
            simpa [Numbered.function_application_tokens, (function_token_ne_variable_token (arguments.length - 1) (QuotationNumbering.function_number function)
                (bound_name targetDepth)).symm, (logical_token_ne_variable_token
                .leftParenthesis (bound_name targetDepth)).symm, (logical_token_ne_variable_token
                .rightParenthesis (bound_name targetDepth)).symm] using
              hFlatten
  · intro pieces _ hPieces piece hPiece
    simp at hPieces
    subst pieces
    simp at hPiece
  · intro head tail ihHead ihTail pieces
      hPiecesAvoid hPieces piece hPiece
    cases hHeadTokens :
        Numbered.quote_term_tokens_with?
          free_name (canonical_bound_names entryDepth) head with
    | none =>
        simp [hHeadTokens] at hPieces
    | some headTokens =>
        cases hTailTokens :
            tail.mapM (Numbered.quote_term_tokens_with?
                free_name (canonical_bound_names entryDepth)) with
        | none =>
            simp [hHeadTokens, hTailTokens] at hPieces
        | some tailTokens =>
            simp [hHeadTokens, hTailTokens] at hPieces
            subst pieces
            simp only [quotation_terms_avoid_bound_depth] at hPiecesAvoid
            simp only [List.mem_cons] at hPiece
            rcases hPiece with rfl | hPiece
            · exact ihHead _ hPiecesAvoid.1 hHeadTokens
            · exact ihTail tailTokens hPiecesAvoid.2
                hTailTokens piece hPiece
/--
项列表避开某个绝对 binder 深度时，每个 quotation 分片都避开对应变量 token。
-/
theorem quote_terms_tokens_with?_avoid_bound_depth
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol] (entryDepth targetDepth : Nat)
    {terms : List (Term σ)}
    {pieces : List (List Nat)} (hAvoid :
      quotation_terms_avoid_bound_depth
        entryDepth targetDepth terms) (hQuote :
      terms.mapM (Numbered.quote_term_tokens_with?
            free_name (canonical_bound_names entryDepth)) =
        some pieces) :
    ∀ piece, piece ∈ pieces →
      Numbered.variable_token (bound_name targetDepth) ∉ piece := by
  induction terms generalizing pieces with
  | nil =>
      simp at hQuote
      subst pieces
      simp
  | cons head tail ih =>
      simp only [
        quotation_terms_avoid_bound_depth] at hAvoid
      cases hHead :
          Numbered.quote_term_tokens_with?
            free_name (canonical_bound_names entryDepth) head with
      | none =>
          simp [hHead] at hQuote
      | some headTokens =>
          cases hTail :
              tail.mapM (Numbered.quote_term_tokens_with?
                  free_name (canonical_bound_names entryDepth)) with
          | none =>
              simp [hHead, hTail] at hQuote
          | some tailTokens =>
              simp [hHead, hTail] at hQuote
              subst pieces
              intro piece hPiece
              simp only [List.mem_cons] at hPiece
              rcases hPiece with rfl | hPiece
              · exact quote_term_tokens_with?_avoid_bound_depth
                  entryDepth targetDepth hAvoid.1 hHead
              · exact ih hAvoid.2 hTail piece hPiece
/--
Hilbert 核公式避开某个绝对 binder 深度时，其规范 quotation 不含对应变量 token。
-/
theorem quote_hilbert_tokens_with?_avoid_bound_depth
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (entryDepth targetDepth : Nat)
    {formula : Formula σ} {tokens : List Nat} (hAvoid :
      quotation_formula_avoids_bound_depth
        entryDepth targetDepth formula) (hQuote :
      Numbered.quote_hilbert_tokens_with?
          free_name bound_name (canonical_bound_names entryDepth)
          entryDepth formula =
        some tokens) :
    Numbered.variable_token (bound_name targetDepth) ∉ tokens := by
  induction formula generalizing entryDepth tokens with
  | falsum =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | truth =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | rel relation arguments =>
      cases hKind : numbering.relation_kind relation with
      | membership =>
          cases arguments with
          | nil =>
              simp [Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?,
                hKind] at hQuote
          | cons left rest =>
              cases rest with
              | nil =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?,
                    hKind] at hQuote
              | cons right tail =>
                  cases tail with
                  | cons extra tail =>
                      simp [Numbered.quote_hilbert_tokens_with?,
                        Numbered.quote_relation_tokens_with?,
                        hKind] at hQuote
                  | nil =>
                      cases hLeft :
                          Numbered.quote_term_tokens_with?
                            free_name (canonical_bound_names entryDepth)
                            left with
                      | none =>
                          simp [Numbered.quote_hilbert_tokens_with?,
                            Numbered.quote_relation_tokens_with?,
                            hKind, hLeft] at hQuote
                      | some leftTokens =>
                          cases hRight :
                              Numbered.quote_term_tokens_with?
                                free_name (canonical_bound_names entryDepth)
                                right with
                          | none =>
                              simp [
                                Numbered.quote_hilbert_tokens_with?,
                                Numbered.quote_relation_tokens_with?,
                                hKind, hLeft, hRight] at hQuote
                          | some rightTokens =>
                              simp [
                                Numbered.quote_hilbert_tokens_with?,
                                Numbered.quote_relation_tokens_with?,
                                hKind, hLeft, hRight] at hQuote
                              subst tokens
                              have hArgumentsAvoid :
                                  quotation_terms_avoid_bound_depth
                                    entryDepth targetDepth
                                    [left, right] := by
                                simpa [
                                  quotation_formula_avoids_bound_depth]
                                  using hAvoid
                              simp only [
                                quotation_terms_avoid_bound_depth] at hArgumentsAvoid
                              have hLeftToken :=
                                quote_term_tokens_with?_avoid_bound_depth
                                  entryDepth targetDepth
                                  hArgumentsAvoid.1 hLeft
                              have hRightToken :=
                                quote_term_tokens_with?_avoid_bound_depth
                                  entryDepth targetDepth
                                  hArgumentsAvoid.2.1 hRight
                              simp [Numbered.membership_tokens, (logical_token_ne_variable_token
                                  .leftParenthesis (bound_name targetDepth)).symm, (membership_token_ne_variable_token (bound_name targetDepth)).symm,
                                (logical_token_ne_variable_token
                                  .rightParenthesis (bound_name targetDepth)).symm,
                                hLeftToken, hRightToken]
      | predicate =>
          cases arguments with
          | nil =>
              simp [Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?,
                hKind] at hQuote
          | cons head tail =>
              cases hArgumentTokens : (head :: tail).mapM (Numbered.quote_term_tokens_with?
                      free_name (canonical_bound_names entryDepth)) with
              | none =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?,
                    hKind, hArgumentTokens] at hQuote
              | some argumentTokens =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?,
                    hKind, hArgumentTokens] at hQuote
                  subst tokens
                  have hArgumentsAvoid :
                      quotation_terms_avoid_bound_depth
                        entryDepth targetDepth (head :: tail) := by
                    simpa [quotation_formula_avoids_bound_depth]
                      using hAvoid
                  have hPiecesAvoid :=
                    quote_terms_tokens_with?_avoid_bound_depth
                      entryDepth targetDepth
                      hArgumentsAvoid hArgumentTokens
                  have hFlatten :
                      Numbered.variable_token (bound_name targetDepth) ∉
                        argumentTokens.flatten := by
                    intro hMember
                    rcases List.mem_flatten.mp hMember with
                      ⟨piece, hPiece, hToken⟩
                    exact hPiecesAvoid piece hPiece hToken
                  simpa [Numbered.predicate_application_tokens, (predicate_token_ne_variable_token
                      tail.length (QuotationNumbering.relation_number relation) (bound_name targetDepth)).symm, (logical_token_ne_variable_token
                      .leftParenthesis (bound_name targetDepth)).symm, (logical_token_ne_variable_token
                      .rightParenthesis (bound_name targetDepth)).symm] using
                    hFlatten
  | equal left right =>
      cases hLeft :
          Numbered.quote_term_tokens_with?
            free_name (canonical_bound_names entryDepth) left with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hLeft] at hQuote
      | some leftTokens =>
          cases hRight :
              Numbered.quote_term_tokens_with?
                free_name (canonical_bound_names entryDepth) right with
          | none =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeft, hRight] at hQuote
          | some rightTokens =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeft, hRight] at hQuote
              subst tokens
              have hTermsAvoid :
                  quotation_term_avoids_bound_depth
                      entryDepth targetDepth left ∧
                    quotation_term_avoids_bound_depth
                      entryDepth targetDepth right := by
                simpa [quotation_formula_avoids_bound_depth]
                  using hAvoid
              have hLeftToken :=
                quote_term_tokens_with?_avoid_bound_depth
                  entryDepth targetDepth hTermsAvoid.1 hLeft
              have hRightToken :=
                quote_term_tokens_with?_avoid_bound_depth
                  entryDepth targetDepth hTermsAvoid.2 hRight
              simp [Numbered.equality_tokens, (logical_token_ne_variable_token
                  .leftParenthesis (bound_name targetDepth)).symm, (logical_token_ne_variable_token
                  .equality (bound_name targetDepth)).symm, (logical_token_ne_variable_token
                  .rightParenthesis (bound_name targetDepth)).symm,
                hLeftToken, hRightToken]
  | neg body ih =>
      cases hBody :
          Numbered.quote_hilbert_tokens_with?
            free_name bound_name (canonical_bound_names entryDepth)
            entryDepth body with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hBody] at hQuote
      | some bodyTokens =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hBody] at hQuote
          subst tokens
          have hBodyAvoid :
              quotation_formula_avoids_bound_depth
                entryDepth targetDepth body := by
            simpa [quotation_formula_avoids_bound_depth]
              using hAvoid
          have hBodyToken :=
            ih entryDepth hBodyAvoid hBody
          simp [Numbered.negation_tokens, (logical_token_ne_variable_token
              .leftParenthesis (bound_name targetDepth)).symm, (logical_token_ne_variable_token
              .negation (bound_name targetDepth)).symm, (logical_token_ne_variable_token
              .rightParenthesis (bound_name targetDepth)).symm,
            hBodyToken]
  | conj left right =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | disj left right =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | imp left right ihLeft ihRight =>
      cases hLeft :
          Numbered.quote_hilbert_tokens_with?
            free_name bound_name (canonical_bound_names entryDepth)
            entryDepth left with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hLeft] at hQuote
      | some leftTokens =>
          cases hRight :
              Numbered.quote_hilbert_tokens_with?
                free_name bound_name (canonical_bound_names entryDepth)
                entryDepth right with
          | none =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeft, hRight] at hQuote
          | some rightTokens =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeft, hRight] at hQuote
              subst tokens
              have hFormulasAvoid :
                  quotation_formula_avoids_bound_depth
                      entryDepth targetDepth left ∧
                    quotation_formula_avoids_bound_depth
                      entryDepth targetDepth right := by
                simpa [quotation_formula_avoids_bound_depth]
                  using hAvoid
              have hLeftToken :=
                ihLeft entryDepth hFormulasAvoid.1 hLeft
              have hRightToken :=
                ihRight entryDepth hFormulasAvoid.2 hRight
              simp [Numbered.implication_tokens, (logical_token_ne_variable_token
                  .leftParenthesis (bound_name targetDepth)).symm, (logical_token_ne_variable_token
                  .implication (bound_name targetDepth)).symm, (logical_token_ne_variable_token
                  .rightParenthesis (bound_name targetDepth)).symm,
                hLeftToken, hRightToken]
  | iff left right =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | forallE sort body ih =>
      let binderName := bound_name entryDepth
      cases hBody :
          Numbered.quote_hilbert_tokens_with?
            free_name bound_name (binderName ::
              canonical_bound_names entryDepth) (entryDepth + 1) body with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            binderName, hBody] at hQuote
      | some bodyTokens =>
          simp [Numbered.quote_hilbert_tokens_with?,
            binderName, hBody] at hQuote
          subst tokens
          have hFormulaAvoid :
              entryDepth ≠ targetDepth ∧
                quotation_formula_avoids_bound_depth (entryDepth + 1) targetDepth body := by
            simpa [quotation_formula_avoids_bound_depth]
              using hAvoid
          have hBodyCanonical :
              Numbered.quote_hilbert_tokens_with?
                  free_name bound_name (canonical_bound_names (entryDepth + 1)) (entryDepth + 1) body =
                some bodyTokens := by
            simpa [binderName, canonical_bound_names] using
              hBody
          have hBodyToken :=
            ih (entryDepth + 1)
              hFormulaAvoid.2 hBodyCanonical
          have hBinderName :
              bound_name entryDepth ≠
                bound_name targetDepth := by
            intro hEqual
            exact hFormulaAvoid.1 (bound_name_injective hEqual)
          simp [Numbered.universal_tokens, (logical_token_ne_variable_token
              .leftParenthesis (bound_name targetDepth)).symm, (logical_token_ne_variable_token
              .universal (bound_name targetDepth)).symm, (variable_token_ne_variable_token
              hBinderName).symm, (logical_token_ne_variable_token
              .rightParenthesis (bound_name targetDepth)).symm,
            hBodyToken]
  | existsE sort body =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
/-! ## 规范 quotation 的量词后继不变量 -/
/--
逐相邻位置检查：每个全称量词 token 的直接后继都满足 `allowed`。
该扫描谓词只刻画 quotation 平坦串所需的最小局部信息，不重新实现公式解析器。
-/
def gq_universal_follower_condition (allowed : Nat → Prop) : List Nat → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      (first = Numbered.logical_token .universal →
        allowed second) ∧
      gq_universal_follower_condition allowed (second :: rest)
/--
量词后继扫描可在任意具体相邻下标处消去。
-/
theorem gq_universal_follower_condition_getElem? (allowed : Nat → Prop) (tokens : List Nat) (index current next : Nat) (hCondition :
      gq_universal_follower_condition allowed tokens) (hCurrent : tokens[index]? = some current) (hNext : tokens[index + 1]? = some next) (hUniversal :
      current = Numbered.logical_token .universal) :
    allowed next := by
  induction tokens generalizing index current next with
  | nil =>
      simp at hCurrent
  | cons first rest ih =>
      cases rest with
      | nil =>
          simp at hNext
      | cons second tail =>
          cases index with
          | zero =>
              simp at hCurrent hNext
              rw [← hNext]
              exact hCondition.1 (hCurrent.trans hUniversal)
          | succ index =>
              exact ih index current next hCondition.2 (by simpa using hCurrent) (by
                  simpa [Nat.succ_eq_add_one,
                    Nat.add_assoc] using hNext)
                hUniversal
/--
每个全称量词 token 都有一个满足 `allowed` 的直接后继。

与相邻扫描谓词相比，该索引式接口同时排除了末位裸全称 token，适合交给后续
可计算检查器和对象层有限回放。
-/
def gq_universal_successor_condition
    (allowed : Nat → Prop) (tokens : List Nat) : Prop :=
  ∀ index,
    tokens[index]? =
        some (Numbered.logical_token .universal) →
      ∃ next,
        tokens[index + 1]? = some next ∧
          allowed next
/-- quotation 分片的末 token 不是全称量词 token。 -/
private def gq_ends_not_universal : List Nat → Prop
  | [] => True
  | [last] =>
      last ≠ Numbered.logical_token .universal
  | _ :: second :: rest =>
      gq_ends_not_universal (second :: rest)
/-- 量词后继扫描与安全末端的联合不变量。 -/
private def gq_universal_follower_invariant (allowed : Nat → Prop) (tokens : List Nat) : Prop :=
  gq_universal_follower_condition allowed tokens ∧
    gq_ends_not_universal tokens
/-- 相邻扫描与安全末端共同蕴含索引式后继条件。 -/
private theorem gq_universal_follower_invariant_successor
    (allowed : Nat → Prop) :
    ∀ tokens,
      gq_universal_follower_invariant allowed tokens →
        gq_universal_successor_condition allowed tokens := by
  intro tokens hInvariant index hCurrent
  induction tokens generalizing index with
  | nil =>
      simp at hCurrent
  | cons first rest ih =>
      cases rest with
      | nil =>
          cases index with
          | zero =>
              have hFirst :
                  first ≠
                    Numbered.logical_token .universal := by
                simpa [gq_universal_follower_invariant,
                  gq_ends_not_universal] using
                  hInvariant.2
              simp at hCurrent
              exact False.elim (hFirst hCurrent)
          | succ index =>
              simp at hCurrent
      | cons second tail =>
          have hTailInvariant :
              gq_universal_follower_invariant
                allowed (second :: tail) := by
            exact
              ⟨hInvariant.1.2,
                by
                  simpa [gq_universal_follower_invariant,
                    gq_ends_not_universal] using
                    hInvariant.2⟩
          cases index with
          | zero =>
              refine ⟨second, by simp, ?_⟩
              exact hInvariant.1.1 (by
                simpa using hCurrent)
          | succ index =>
              exact ih hTailInvariant index (by
                simpa using hCurrent)
/-- 不含全称量词 token 的分片自动满足任意量词后继条件。 -/
private theorem gq_universal_follower_invariant_of_not_mem (allowed : Nat → Prop) (tokens : List Nat) (hToken :
      Numbered.logical_token .universal ∉ tokens) :
    gq_universal_follower_invariant allowed tokens := by
  induction tokens with
  | nil =>
      simp [gq_universal_follower_invariant,
        gq_universal_follower_condition,
        gq_ends_not_universal]
  | cons first rest ih =>
      cases rest with
      | nil =>
          have hFirst :
              first ≠ Numbered.logical_token .universal := by
            intro hEqual
            exact hToken (by simp [hEqual])
          exact ⟨trivial, hFirst⟩
      | cons second tail =>
          have hFirst :
              first ≠ Numbered.logical_token .universal := by
            intro hEqual
            exact hToken (by simp [hEqual])
          have hRest :
              Numbered.logical_token .universal ∉
                second :: tail := by
            intro hMember
            exact hToken (by simp [hMember])
          rcases ih hRest with ⟨hFollower, hEnd⟩
          exact
            ⟨⟨fun hEqual => False.elim (hFirst hEqual),
                hFollower⟩,
              hEnd⟩
/-- 安全末端在拼接后仍由最右非空分片决定。 -/
private theorem gq_ends_not_universal_append (left right : List Nat) (hLeft : gq_ends_not_universal left) (hRight : gq_ends_not_universal right) :
    gq_ends_not_universal (left ++ right) := by
  induction left with
  | nil =>
      simpa using hRight
  | cons first rest ih =>
      cases rest with
      | nil =>
          cases right with
          | nil =>
              simpa [gq_ends_not_universal] using hLeft
          | cons second tail =>
              simpa [gq_ends_not_universal] using hRight
      | cons second tail =>
          simpa [gq_ends_not_universal] using
            ih (by
              simpa [gq_ends_not_universal] using hLeft)
/--
两个安全 quotation 分片拼接后继续满足量词后继不变量。
左分片的末 token 非全称量词，正好排除跨越拼接边界产生伪量词前缀。
-/
private theorem gq_universal_follower_invariant_append (allowed : Nat → Prop) (left right : List Nat) (hLeft :
      gq_universal_follower_invariant allowed left) (hRight :
      gq_universal_follower_invariant allowed right) :
    gq_universal_follower_invariant allowed (left ++ right) := by
  rcases hLeft with ⟨hLeftFollower, hLeftEnd⟩
  rcases hRight with ⟨hRightFollower, hRightEnd⟩
  constructor
  · induction left with
    | nil =>
        simpa using hRightFollower
    | cons first rest ih =>
        cases rest with
        | nil =>
            cases right with
            | nil =>
                simp [gq_universal_follower_condition]
            | cons second tail =>
                have hFirst :
                    first ≠
                      Numbered.logical_token .universal := by
                  simpa [gq_ends_not_universal] using hLeftEnd
                exact
                  ⟨fun hEqual =>
                      False.elim (hFirst hEqual),
                    hRightFollower⟩
        | cons second tail =>
            rcases hLeftFollower with
              ⟨hHead, hTailFollower⟩
            exact
              ⟨hHead,
                ih hTailFollower (by
                    simpa [gq_ends_not_universal] using
                      hLeftEnd)⟩
  · exact gq_ends_not_universal_append
      left right hLeftEnd hRightEnd
private theorem gq_universal_token_ne_constant (index : Nat) :
    Numbered.logical_token .universal ≠
      Numbered.constant_token index := by
  intro hEqual
  have hParity :=
    congrArg (fun token => token % 2) hEqual
  simp [Numbered.logical_token, logical_symbol_exponent,
    Numbered.constant_token, Nat.pow_mod] at hParity
private theorem gq_universal_token_ne_function (arityPredecessor index : Nat) :
    Numbered.logical_token .universal ≠
      Numbered.function_token arityPredecessor index := by
  intro hEqual
  have hParity :=
    congrArg (fun token => token % 2) hEqual
  simp [Numbered.logical_token, logical_symbol_exponent,
    Numbered.function_token, Nat.mul_mod, Nat.pow_mod] at hParity
private theorem gq_universal_token_ne_predicate (arityPredecessor index : Nat) :
    Numbered.logical_token .universal ≠
      Numbered.predicate_token arityPredecessor index := by
  intro hEqual
  have hParity :=
    congrArg (fun token => token % 2) hEqual
  simp [Numbered.logical_token, logical_symbol_exponent,
    Numbered.predicate_token, Nat.mul_mod, Nat.pow_mod] at hParity
/-- 任意成功的项 quotation 都不包含全称量词 token。 -/
private theorem quote_term_tokens_with?_universal_not_mem
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    {term : Term σ} {tokens : List Nat} (hQuote :
      Numbered.quote_term_tokens_with?
        freeNaming boundNames term = some tokens) :
    Numbered.logical_token .universal ∉ tokens := by
  refine Term.rec (motive_1 := fun term =>
      ∀ tokens,
        Numbered.quote_term_tokens_with?
            freeNaming boundNames term = some tokens →
          Numbered.logical_token .universal ∉ tokens) (motive_2 := fun terms =>
      ∀ pieces,
        terms.mapM (Numbered.quote_term_tokens_with?
              freeNaming boundNames) = some pieces →
          ∀ piece, piece ∈ pieces →
            Numbered.logical_token .universal ∉ piece)
    ?_ ?_ ?_ ?_ term tokens hQuote
  · intro sourceVar sourceTokens hSourceQuote
    cases sourceVar with
    | bvar sort index =>
        cases hName : boundNames[index]? with
        | none =>
            simp [Numbered.quote_term_tokens_with?,
              hName] at hSourceQuote
        | some name =>
            simp [Numbered.quote_term_tokens_with?,
              hName] at hSourceQuote
            subst sourceTokens
            simpa using
              logical_token_ne_variable_token
                .universal name
    | fvar sort id =>
        simp [Numbered.quote_term_tokens_with?] at hSourceQuote
        subst sourceTokens
        simpa using
          logical_token_ne_variable_token
            .universal (freeNaming id)
  · intro function arguments ih resultTokens hResultQuote
    cases hArgumentTokens :
        arguments.mapM (Numbered.quote_term_tokens_with?
            freeNaming boundNames) with
    | none =>
        simp [Numbered.quote_term_tokens_with?,
          hArgumentTokens] at hResultQuote
    | some argumentTokens =>
        have hPieces :
            ∀ piece, piece ∈ argumentTokens →
              Numbered.logical_token .universal ∉ piece :=
          ih argumentTokens hArgumentTokens
        cases argumentTokens with
        | nil =>
            simp [Numbered.quote_term_tokens_with?,
              hArgumentTokens] at hResultQuote
            subst resultTokens
            simpa using
              gq_universal_token_ne_constant (QuotationNumbering.function_number function)
        | cons head tail =>
            simp [Numbered.quote_term_tokens_with?,
              hArgumentTokens] at hResultQuote
            subst resultTokens
            have hFlatten :
                Numbered.logical_token .universal ∉ (head :: tail).flatten := by
              intro hMember
              rcases List.mem_flatten.mp hMember with
                ⟨piece, hPiece, hToken⟩
              exact hPieces piece hPiece hToken
            have hFunction :
                Numbered.logical_token .universal ≠
                  Numbered.function_token (arguments.length - 1) (QuotationNumbering.function_number function) :=
              gq_universal_token_ne_function (arguments.length - 1) (QuotationNumbering.function_number function)
            have hLeftParenthesis :
                Numbered.logical_token .universal ≠
                  Numbered.logical_token .leftParenthesis := by
              decide
            have hRightParenthesis :
                Numbered.logical_token .universal ≠
                  Numbered.logical_token .rightParenthesis := by
              decide
            simpa [Numbered.function_application_tokens,
              hFunction, hLeftParenthesis,
              hRightParenthesis] using hFlatten
  · intro pieces hPieces piece hPiece
    simp at hPieces
    subst pieces
    simp at hPiece
  · intro head tail ihHead ihTail pieces hPieces piece hPiece
    cases hHeadTokens :
        Numbered.quote_term_tokens_with?
          freeNaming boundNames head with
    | none =>
        simp [hHeadTokens] at hPieces
    | some headTokens =>
        cases hTailTokens :
            tail.mapM (Numbered.quote_term_tokens_with?
                freeNaming boundNames) with
        | none =>
            simp [hHeadTokens, hTailTokens] at hPieces
        | some tailTokens =>
            simp [hHeadTokens, hTailTokens] at hPieces
            subst pieces
            simp only [List.mem_cons] at hPiece
            rcases hPiece with rfl | hPiece
            · exact ihHead _ hHeadTokens
            · exact ihTail tailTokens hTailTokens piece hPiece
/-- 项列表 quotation 的每个分片都不包含全称量词 token。 -/
private theorem quote_terms_tokens_with?_universal_not_mem
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    {terms : List (Term σ)} {pieces : List (List Nat)} (hQuote :
      terms.mapM (Numbered.quote_term_tokens_with?
          freeNaming boundNames) = some pieces) :
    ∀ piece, piece ∈ pieces →
      Numbered.logical_token .universal ∉ piece := by
  induction terms generalizing pieces with
  | nil =>
      simp at hQuote
      subst pieces
      simp
  | cons head tail ih =>
      cases hHead :
          Numbered.quote_term_tokens_with?
            freeNaming boundNames head with
      | none =>
          simp [hHead] at hQuote
      | some headTokens =>
          cases hTail :
              tail.mapM (Numbered.quote_term_tokens_with?
                  freeNaming boundNames) with
          | none =>
              simp [hHead, hTail] at hQuote
          | some tailTokens =>
              simp [hHead, hTail] at hQuote
              subst pieces
              intro piece hPiece
              simp only [List.mem_cons] at hPiece
              rcases hPiece with rfl | hPiece
              · exact
                  quote_term_tokens_with?_universal_not_mem
                    freeNaming boundNames hHead
              · exact ih hTail piece hPiece
/--
Hilbert quotation 中每个全称量词 token 的直接后继都是某个 `binderNaming` 产生的
变量 token。
结论保留全部 binder 深度而不压成奇偶性判断；规范层只需随后实例化
`binderNaming := bound_name`。
-/
private theorem quote_hilbert_tokens_with?_universal_follower_invariant
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming binderNaming : Nat → Nat) (boundNames : List Nat) (depth : Nat)
    {formula : Formula σ} {tokens : List Nat} (hQuote :
      Numbered.quote_hilbert_tokens_with?
        freeNaming binderNaming boundNames depth formula =
          some tokens) :
    gq_universal_follower_invariant (fun token =>
        ∃ binderDepth,
          token =
            Numbered.variable_token (binderNaming binderDepth))
      tokens := by
  let allowed : Nat → Prop := fun token =>
    ∃ binderDepth,
      token =
        Numbered.variable_token (binderNaming binderDepth)
  have hLeftParenthesis :
      Numbered.logical_token .universal ≠
        Numbered.logical_token .leftParenthesis := by
    decide
  have hRightParenthesis :
      Numbered.logical_token .universal ≠
        Numbered.logical_token .rightParenthesis := by
    decide
  have hEquality :
      Numbered.logical_token .universal ≠
        Numbered.logical_token .equality := by
    decide
  have hNegation :
      Numbered.logical_token .universal ≠
        Numbered.logical_token .negation := by
    decide
  have hImplication :
      Numbered.logical_token .universal ≠
        Numbered.logical_token .implication := by
    decide
  have hMembership :
      Numbered.logical_token .universal ≠
        Numbered.membership_token := by
    decide
  have hSingletonInvariant (token : Nat) (hToken :
        Numbered.logical_token .universal ≠ token) :
      gq_universal_follower_invariant allowed [token] :=
    gq_universal_follower_invariant_of_not_mem
      allowed [token] (by simpa using hToken)
  have hLeftInvariant :
      gq_universal_follower_invariant allowed
        [Numbered.logical_token .leftParenthesis] :=
    hSingletonInvariant _ hLeftParenthesis
  have hRightInvariant :
      gq_universal_follower_invariant allowed
        [Numbered.logical_token .rightParenthesis] :=
    hSingletonInvariant _ hRightParenthesis
  induction formula generalizing boundNames depth tokens with
  | falsum =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | truth =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | rel relation arguments =>
      cases hKind : numbering.relation_kind relation with
      | membership =>
          cases arguments with
          | nil =>
              simp [Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?,
                hKind] at hQuote
          | cons left rest =>
              cases rest with
              | nil =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?,
                    hKind] at hQuote
              | cons right tail =>
                  cases tail with
                  | cons extra tail =>
                      simp [Numbered.quote_hilbert_tokens_with?,
                        Numbered.quote_relation_tokens_with?,
                        hKind] at hQuote
                  | nil =>
                      cases hLeft :
                          Numbered.quote_term_tokens_with?
                            freeNaming boundNames left with
                      | none =>
                          simp [Numbered.quote_hilbert_tokens_with?,
                            Numbered.quote_relation_tokens_with?,
                            hKind, hLeft] at hQuote
                      | some leftTokens =>
                          cases hRight :
                              Numbered.quote_term_tokens_with?
                                freeNaming boundNames right with
                          | none =>
                              simp [Numbered.quote_hilbert_tokens_with?,
                                Numbered.quote_relation_tokens_with?,
                                hKind, hLeft, hRight] at hQuote
                          | some rightTokens =>
                              simp [Numbered.quote_hilbert_tokens_with?,
                                Numbered.quote_relation_tokens_with?,
                                hKind, hLeft, hRight] at hQuote
                              subst tokens
                              have hLeftToken :=
                                quote_term_tokens_with?_universal_not_mem
                                  freeNaming boundNames hLeft
                              have hRightToken :=
                                quote_term_tokens_with?_universal_not_mem
                                  freeNaming boundNames hRight
                              have hNoUniversal :
                                  Numbered.logical_token .universal ∉
                                    Numbered.membership_tokens
                                      leftTokens rightTokens := by
                                simpa [Numbered.membership_tokens,
                                  hLeftParenthesis, hRightParenthesis,
                                  hMembership] using
                                  And.intro hLeftToken hRightToken
                              exact
                                gq_universal_follower_invariant_of_not_mem
                                  allowed _ hNoUniversal
      | predicate =>
          cases arguments with
          | nil =>
              simp [Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?,
                hKind] at hQuote
          | cons head tail =>
              cases hArgumentTokens : (head :: tail).mapM (Numbered.quote_term_tokens_with?
                      freeNaming boundNames) with
              | none =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?,
                    hKind, hArgumentTokens] at hQuote
              | some argumentTokens =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?,
                    hKind, hArgumentTokens] at hQuote
                  subst tokens
                  have hPieces :
                      ∀ piece, piece ∈ argumentTokens →
                        Numbered.logical_token .universal ∉ piece := by
                    exact
                      quote_terms_tokens_with?_universal_not_mem
                        freeNaming boundNames hArgumentTokens
                  have hFlatten :
                      Numbered.logical_token .universal ∉
                        argumentTokens.flatten := by
                    intro hMember
                    rcases List.mem_flatten.mp hMember with
                      ⟨piece, hPiece, hToken⟩
                    exact hPieces piece hPiece hToken
                  have hPredicate :
                      Numbered.logical_token .universal ≠
                        Numbered.predicate_token tail.length (QuotationNumbering.relation_number relation) :=
                    gq_universal_token_ne_predicate
                      tail.length (QuotationNumbering.relation_number relation)
                  have hNoUniversal :
                      Numbered.logical_token .universal ∉
                        Numbered.predicate_application_tokens
                          tail.length (QuotationNumbering.relation_number relation)
                          argumentTokens := by
                    simpa [Numbered.predicate_application_tokens,
                      hPredicate, hLeftParenthesis,
                      hRightParenthesis] using hFlatten
                  exact
                    gq_universal_follower_invariant_of_not_mem
                      allowed _ hNoUniversal
  | equal left right =>
      cases hLeft :
          Numbered.quote_term_tokens_with?
            freeNaming boundNames left with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hLeft] at hQuote
      | some leftTokens =>
          cases hRight :
              Numbered.quote_term_tokens_with?
                freeNaming boundNames right with
          | none =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeft, hRight] at hQuote
          | some rightTokens =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeft, hRight] at hQuote
              subst tokens
              have hLeftToken :=
                quote_term_tokens_with?_universal_not_mem
                  freeNaming boundNames hLeft
              have hRightToken :=
                quote_term_tokens_with?_universal_not_mem
                  freeNaming boundNames hRight
              have hNoUniversal :
                  Numbered.logical_token .universal ∉
                    Numbered.equality_tokens
                      leftTokens rightTokens := by
                simpa [Numbered.equality_tokens,
                  hLeftParenthesis, hRightParenthesis,
                  hEquality] using
                  And.intro hLeftToken hRightToken
              exact
                gq_universal_follower_invariant_of_not_mem
                  allowed _ hNoUniversal
  | neg body ih =>
      cases hBody :
          Numbered.quote_hilbert_tokens_with?
            freeNaming binderNaming boundNames depth body with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hBody] at hQuote
      | some bodyTokens =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hBody] at hQuote
          subst tokens
          have hPrefix :
              gq_universal_follower_invariant allowed
                [Numbered.logical_token .leftParenthesis,
                  Numbered.logical_token .negation] :=
            gq_universal_follower_invariant_of_not_mem
              allowed _ (by simp [hLeftParenthesis, hNegation])
          have hBodyInvariant :=
            ih boundNames depth hBody
          exact
            gq_universal_follower_invariant_append
              allowed _ _ (gq_universal_follower_invariant_append
                allowed _ _ hPrefix hBodyInvariant)
              hRightInvariant
  | conj left right =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | disj left right =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | imp left right ihLeft ihRight =>
      cases hLeft :
          Numbered.quote_hilbert_tokens_with?
            freeNaming binderNaming boundNames depth left with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hLeft] at hQuote
      | some leftTokens =>
          cases hRight :
              Numbered.quote_hilbert_tokens_with?
                freeNaming binderNaming boundNames depth right with
          | none =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeft, hRight] at hQuote
          | some rightTokens =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeft, hRight] at hQuote
              subst tokens
              have hMiddle :
                  gq_universal_follower_invariant allowed
                    [Numbered.logical_token .implication] :=
                hSingletonInvariant _ hImplication
              have hLeftInvariant' :=
                ihLeft boundNames depth hLeft
              have hRightInvariant' :=
                ihRight boundNames depth hRight
              exact
                gq_universal_follower_invariant_append
                  allowed _ _ (gq_universal_follower_invariant_append
                    allowed _ _ (gq_universal_follower_invariant_append
                      allowed _ _ (gq_universal_follower_invariant_append
                        allowed _ _
                        hLeftInvariant hLeftInvariant')
                      hMiddle)
                    hRightInvariant')
                  hRightInvariant
  | iff left right =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | forallE sort body ih =>
      let binderName := binderNaming depth
      cases hBody :
          Numbered.quote_hilbert_tokens_with?
            freeNaming binderNaming (binderName :: boundNames) (depth + 1) body with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            binderName, hBody] at hQuote
      | some bodyTokens =>
          simp [Numbered.quote_hilbert_tokens_with?,
            binderName, hBody] at hQuote
          subst tokens
          have hAllowed :
              allowed (Numbered.variable_token binderName) := by
            exact ⟨depth, rfl⟩
          have hPrefix :
              gq_universal_follower_invariant allowed
                [Numbered.logical_token .leftParenthesis,
                  Numbered.logical_token .universal,
                  Numbered.variable_token binderName] := by
            constructor
            · exact
                ⟨fun hEqual =>
                    False.elim (hLeftParenthesis hEqual.symm),
                  ⟨fun _ => hAllowed, trivial⟩⟩
            · exact (logical_token_ne_variable_token
                  .universal binderName).symm
          have hBodyInvariant :=
            ih (binderName :: boundNames) (depth + 1) hBody
          exact
            gq_universal_follower_invariant_append
              allowed _ _ (gq_universal_follower_invariant_append
                allowed _ _ hPrefix hBodyInvariant)
              hRightInvariant
  | existsE sort body =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
/--
任意成功的 Hilbert quotation 中，全称 token 的直接后继都是当前 binder 命名函数
产生的变量 token。结论只暴露有限 token 串事实，不绑定任何具体反解码器。
-/
theorem quote_hilbert_tokens_with?_universal_successors
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    (freeNaming binderNaming : Nat → Nat)
    (boundNames : List Nat) (depth : Nat)
    {formula : Formula σ} {tokens : List Nat}
    (hQuote :
      Numbered.quote_hilbert_tokens_with?
          freeNaming binderNaming boundNames depth formula =
        some tokens) :
    gq_universal_successor_condition
      (fun token =>
        ∃ binderDepth,
          token =
            Numbered.variable_token
              (binderNaming binderDepth))
      tokens := by
  exact
    gq_universal_follower_invariant_successor _ _
      (quote_hilbert_tokens_with?_universal_follower_invariant
        freeNaming binderNaming boundNames depth hQuote)

/--
规范公式 quotation 的全称 token 后继是某个规范 binder 变量 token。
-/
theorem quote_tokens?_universal_successors
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {formula : Formula σ} {tokens : List Nat}
    (hQuote :
      Numbered.quote_tokens? formula = some tokens) :
    gq_universal_successor_condition
      (fun token =>
        ∃ binderDepth,
          token =
            Numbered.variable_token
              (bound_name binderDepth))
      tokens := by
  apply
    quote_hilbert_tokens_with?_universal_successors
      (σ := σ)
      free_name bound_name [] 0
  simpa [Numbered.quote_tokens?,
    Numbered.quote_tokens_with?] using hQuote

/-- 量词后继允许集合扩大时，扫描证书保持成立。 -/
private theorem gq_universal_follower_condition_mono
    {leftAllowed rightAllowed : Nat → Prop} (hAllowed :
      ∀ token, leftAllowed token → rightAllowed token) :
    ∀ tokens,
      gq_universal_follower_condition
          leftAllowed tokens →
        gq_universal_follower_condition
          rightAllowed tokens := by
  intro tokens hTokens
  induction tokens with
  | nil =>
      trivial
  | cons first rest ih =>
      cases rest with
      | nil =>
          trivial
      | cons second tail =>
          exact
            ⟨fun hUniversal =>
                hAllowed second (hTokens.1 hUniversal),
              ih hTokens.2⟩
/--
canonical Hilbert 局部 quotation 中，任何全称量词 token 的直接后继都不可能出现在
顶层闭项 quotation 中。
该定理保留当前 bound 环境与 binder 深度，专门供量词公理公式体和全称闭包的局部
quotation 使用；替换项从空 bound 环境引用，因此只含 canonical 偶数自由名字。
-/
theorem quote_hilbert_tokens_with?_universal_followers_avoid_term
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {boundNames : List Nat} {depth : Nat}
    {formula : Formula σ} {formulaTokens : List Nat}
    {replacement : Term σ} {replacementTokens : List Nat} (hFormula :
      Numbered.quote_hilbert_tokens_with?
          free_name bound_name boundNames depth formula =
        some formulaTokens) (hReplacement :
      quote_term_tokens? replacement = some replacementTokens) :
    gq_universal_follower_condition (fun token => token ∉ replacementTokens)
      formulaTokens := by
  have hFormulaInvariant :
      gq_universal_follower_invariant (fun token =>
          ∃ binderDepth,
            token =
              Numbered.variable_token (bound_name binderDepth))
        formulaTokens :=
    quote_hilbert_tokens_with?_universal_follower_invariant
      free_name bound_name boundNames depth hFormula
  apply gq_universal_follower_condition_mono (tokens := formulaTokens) (fun token hToken => ?_)
    hFormulaInvariant.1
  rcases hToken with ⟨binderDepth, rfl⟩
  unfold quote_term_tokens? at hReplacement
  exact quote_term_tokens_with?_name_not_mem
    free_name [] (bound_name binderDepth) (fun id => free_name_ne_bound_name id binderDepth) (by simp) hReplacement
/--
规范公式 quotation 中，任何全称量词 token 的直接后继都不可能出现在规范项
quotation 中。
这是偶数自由名字域与奇数 binder 名字域在平坦 token 层的完整分离证书。
-/
theorem quote_tokens?_universal_followers_avoid_term
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {formula : Formula σ} {formulaTokens : List Nat}
    {replacement : Term σ} {replacementTokens : List Nat} (hFormula :
      Numbered.quote_tokens? formula = some formulaTokens) (hReplacement :
      quote_term_tokens? replacement = some replacementTokens) :
    gq_universal_follower_condition (fun token => token ∉ replacementTokens)
      formulaTokens := by
  exact
    quote_hilbert_tokens_with?_universal_followers_avoid_term (boundNames := []) (depth := 0) (by
        simpa [Numbered.quote_tokens?,
          Numbered.quote_tokens_with?] using hFormula)
      hReplacement
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
