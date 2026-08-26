import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Occurrence.Free
import YesMetaZFC.Logic.FirstOrder.FormalSystem.ExpressionEncodingSupport

/-!
# Gödel quotation 的自由变量新鲜性

本模块把元层公式自由变量新鲜性精确运输为对象层公式码的变量集合非成员。
证明分为三步：
1. 规范 quotation 的 token 串不含对应偶数自由变量标签；
2. 标准 token 序列不满足该变量的出现条件；
3. 变量集合成员反演把出现否定提升为 `varsₘ` 非成员。
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

/-! ## 规范 quotation 的自由编号避让 -/

/--
若某个自由编号在项中对所有 sort 都不出现，则规范 quotation 不含它的偶数变量
token。对所有 sort 量化是必要的，因为通用 quotation 的自由命名只依赖编号。
-/
theorem quote_term_tokens_with?_free_name_not_mem
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    (entryDepth target : Nat)
    {term : Term σ} {tokens : List Nat}
    (hFresh :
      ∀ sort, (sort, target) ∉ Term.freeSupport term)
    (hQuote :
      Numbered.quote_term_tokens_with?
          free_name (canonical_bound_names entryDepth) term =
        some tokens) :
    Numbered.variable_token (free_name target) ∉ tokens := by
  refine Term.rec
    (motive_1 := fun term =>
      ∀ tokens,
        (∀ sort, (sort, target) ∉ Term.freeSupport term) →
        Numbered.quote_term_tokens_with?
            free_name (canonical_bound_names entryDepth) term =
          some tokens →
        Numbered.variable_token (free_name target) ∉ tokens)
    (motive_2 := fun terms =>
      ∀ pieces,
        (∀ sort,
          (sort, target) ∉ Term.freeSupportList terms) →
        terms.mapM
            (Numbered.quote_term_tokens_with?
              free_name (canonical_bound_names entryDepth)) =
          some pieces →
        ∀ piece, piece ∈ pieces →
          Numbered.variable_token (free_name target) ∉ piece)
    ?_ ?_ ?_ ?_ term tokens hFresh hQuote
  · intro sourceVar sourceTokens hSourceFresh hSourceQuote
    cases sourceVar with
    | bvar sort index =>
        cases hName :
            (canonical_bound_names entryDepth)[index]? with
        | none =>
            simp [Numbered.quote_term_tokens_with?,
              hName] at hSourceQuote
        | some name =>
            have hNameNe :
                name ≠ free_name target := by
              intro hEqual
              exact free_name_not_mem_canonical
                target entryDepth <| by
                  rw [← hEqual]
                  exact List.mem_of_getElem? hName
            simp [Numbered.quote_term_tokens_with?,
              hName] at hSourceQuote
            subst sourceTokens
            simpa using
              (variable_token_ne_variable_token hNameNe).symm
    | fvar sort identifier =>
        have hIdentifierNe :
            identifier ≠ target := by
          intro hEqual
          subst identifier
          exact hSourceFresh sort <| by
            simp [Term.freeSupport]
        have hNameNe :
            free_name identifier ≠ free_name target :=
          fun hEqual =>
            hIdentifierNe (free_name_injective hEqual)
        simp [Numbered.quote_term_tokens_with?] at hSourceQuote
        subst sourceTokens
        simpa using
          (variable_token_ne_variable_token hNameNe).symm
  · intro function arguments ih resultTokens
      hArgumentsFresh hResultQuote
    cases hArgumentTokens :
        arguments.mapM
          (Numbered.quote_term_tokens_with?
            free_name (canonical_bound_names entryDepth)) with
    | none =>
        simp [Numbered.quote_term_tokens_with?,
          hArgumentTokens] at hResultQuote
    | some argumentTokens =>
        have hPieces :
            ∀ piece, piece ∈ argumentTokens →
              Numbered.variable_token (free_name target) ∉ piece :=
          ih argumentTokens hArgumentsFresh hArgumentTokens
        cases argumentTokens with
        | nil =>
            simp [Numbered.quote_term_tokens_with?,
              hArgumentTokens] at hResultQuote
            subst resultTokens
            simpa using
              (constant_token_ne_variable_token
                (QuotationNumbering.function_number function)
                (free_name target)).symm
        | cons head tail =>
            simp [Numbered.quote_term_tokens_with?,
              hArgumentTokens] at hResultQuote
            subst resultTokens
            have hFlatten :
                Numbered.variable_token (free_name target) ∉
                  (head :: tail).flatten := by
              intro hMember
              rcases List.mem_flatten.mp hMember with
                ⟨piece, hPiece, hToken⟩
              exact hPieces piece hPiece hToken
            simpa [Numbered.function_application_tokens,
              (function_token_ne_variable_token
                (arguments.length - 1)
                (QuotationNumbering.function_number function)
                (free_name target)).symm,
              (logical_token_ne_variable_token
                .leftParenthesis (free_name target)).symm,
              (logical_token_ne_variable_token
                .rightParenthesis (free_name target)).symm] using
              hFlatten
  · intro pieces _ hPieces piece hPiece
    simp at hPieces
    subst pieces
    simp at hPiece
  · intro head tail ihHead ihTail pieces
      hTermsFresh hPieces piece hPiece
    cases hHead :
        Numbered.quote_term_tokens_with?
          free_name (canonical_bound_names entryDepth) head with
    | none =>
        simp [hHead] at hPieces
    | some headTokens =>
        cases hTail :
            tail.mapM
              (Numbered.quote_term_tokens_with?
                free_name (canonical_bound_names entryDepth)) with
        | none =>
            simp [hHead, hTail] at hPieces
        | some tailTokens =>
            simp [hHead, hTail] at hPieces
            subst pieces
            have hHeadFresh :
                ∀ sort,
                  (sort, target) ∉ Term.freeSupport head := by
              intro sort hMember
              exact hTermsFresh sort <| by
                simp [Term.freeSupportList, hMember]
            have hTailFresh :
                ∀ sort,
                  (sort, target) ∉
                    Term.freeSupportList tail := by
              intro sort hMember
              exact hTermsFresh sort <| by
                simp [Term.freeSupportList, hMember]
            simp only [List.mem_cons] at hPiece
            rcases hPiece with rfl | hPiece
            · exact ihHead _ hHeadFresh hHead
            · exact ihTail _ hTailFresh hTail _ hPiece

/-- 项列表逐分片继承指定自由编号的 token 避让。 -/
theorem quote_terms_tokens_with?_free_name_not_mem
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    (entryDepth target : Nat)
    {terms : List (Term σ)}
    {pieces : List (List Nat)}
    (hFresh :
      ∀ sort,
        (sort, target) ∉ Term.freeSupportList terms)
    (hQuote :
      terms.mapM
          (Numbered.quote_term_tokens_with?
            free_name (canonical_bound_names entryDepth)) =
        some pieces) :
    ∀ piece, piece ∈ pieces →
      Numbered.variable_token (free_name target) ∉ piece := by
  induction terms generalizing pieces with
  | nil =>
      simp at hQuote
      subst pieces
      simp
  | cons head tail ih =>
      cases hHead :
          Numbered.quote_term_tokens_with?
            free_name (canonical_bound_names entryDepth) head with
      | none =>
          simp [hHead] at hQuote
      | some headTokens =>
          cases hTail :
              tail.mapM
                (Numbered.quote_term_tokens_with?
                  free_name
                  (canonical_bound_names entryDepth)) with
          | none =>
              simp [hHead, hTail] at hQuote
          | some tailTokens =>
              simp [hHead, hTail] at hQuote
              subst pieces
              have hHeadFresh :
                  ∀ sort,
                    (sort, target) ∉ Term.freeSupport head := by
                intro sort hMember
                exact hFresh sort <| by
                  simp [Term.freeSupportList, hMember]
              have hTailFresh :
                  ∀ sort,
                    (sort, target) ∉
                      Term.freeSupportList tail := by
                intro sort hMember
                exact hFresh sort <| by
                  simp [Term.freeSupportList, hMember]
              intro piece hPiece
              simp only [List.mem_cons] at hPiece
              rcases hPiece with rfl | hPiece
              · exact
                  quote_term_tokens_with?_free_name_not_mem
                    entryDepth target hHeadFresh hHead
              · exact ih hTailFresh hTail piece hPiece

/--
Hilbert 核公式不含指定自由编号时，其规范 quotation 不含对应偶数变量 token。
-/
theorem quote_hilbert_tokens_with?_free_name_not_mem
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol]
    (entryDepth target : Nat)
    {formula : Formula σ} {tokens : List Nat}
    (hFresh :
      ∀ sort,
        (sort, target) ∉ Formula.freeSupport formula)
    (hQuote :
      Numbered.quote_hilbert_tokens_with?
          free_name bound_name
          (canonical_bound_names entryDepth)
          entryDepth formula =
        some tokens) :
    Numbered.variable_token (free_name target) ∉ tokens := by
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
                            free_name
                            (canonical_bound_names entryDepth)
                            left with
                      | none =>
                          simp [
                            Numbered.quote_hilbert_tokens_with?,
                            Numbered.quote_relation_tokens_with?,
                            hKind, hLeft] at hQuote
                      | some leftTokens =>
                          cases hRight :
                              Numbered.quote_term_tokens_with?
                                free_name
                                (canonical_bound_names entryDepth)
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
                              have hLeftFresh :
                                  ∀ sort,
                                    (sort, target) ∉
                                      Term.freeSupport left := by
                                intro sort hMember
                                exact hFresh sort <| by
                                  simp [Formula.freeSupport,
                                    Term.freeSupportList,
                                    hMember]
                              have hRightFresh :
                                  ∀ sort,
                                    (sort, target) ∉
                                      Term.freeSupport right := by
                                intro sort hMember
                                exact hFresh sort <| by
                                  simp [Formula.freeSupport,
                                    Term.freeSupportList,
                                    hMember]
                              have hLeftToken :=
                                quote_term_tokens_with?_free_name_not_mem
                                  entryDepth target
                                  hLeftFresh hLeft
                              have hRightToken :=
                                quote_term_tokens_with?_free_name_not_mem
                                  entryDepth target
                                  hRightFresh hRight
                              simp [Numbered.membership_tokens,
                                (logical_token_ne_variable_token
                                  .leftParenthesis
                                  (free_name target)).symm,
                                (membership_token_ne_variable_token
                                  (free_name target)).symm,
                                (logical_token_ne_variable_token
                                  .rightParenthesis
                                  (free_name target)).symm,
                                hLeftToken, hRightToken]
      | predicate =>
          cases arguments with
          | nil =>
              simp [Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?,
                hKind] at hQuote
          | cons head tail =>
              cases hArgumentTokens :
                  (head :: tail).mapM
                    (Numbered.quote_term_tokens_with?
                      free_name
                      (canonical_bound_names entryDepth)) with
              | none =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?,
                    hKind, hArgumentTokens] at hQuote
              | some argumentTokens =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?,
                    hKind, hArgumentTokens] at hQuote
                  subst tokens
                  have hArgumentsFresh :
                      ∀ sort,
                        (sort, target) ∉
                          Term.freeSupportList
                            (head :: tail) := by
                    simpa [Formula.freeSupport] using hFresh
                  have hPieces :=
                    quote_terms_tokens_with?_free_name_not_mem
                      entryDepth target
                      hArgumentsFresh hArgumentTokens
                  have hFlatten :
                      Numbered.variable_token (free_name target) ∉
                        argumentTokens.flatten := by
                    intro hMember
                    rcases List.mem_flatten.mp hMember with
                      ⟨piece, hPiece, hToken⟩
                    exact hPieces piece hPiece hToken
                  simpa [
                    Numbered.predicate_application_tokens,
                    (predicate_token_ne_variable_token
                      tail.length
                      (QuotationNumbering.relation_number relation)
                      (free_name target)).symm,
                    (logical_token_ne_variable_token
                      .leftParenthesis
                      (free_name target)).symm,
                    (logical_token_ne_variable_token
                      .rightParenthesis
                      (free_name target)).symm] using
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
                free_name
                (canonical_bound_names entryDepth) right with
          | none =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeft, hRight] at hQuote
          | some rightTokens =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeft, hRight] at hQuote
              subst tokens
              have hLeftFresh :
                  ∀ sort,
                    (sort, target) ∉
                      Term.freeSupport left := by
                intro sort hMember
                exact hFresh sort <| by
                  simp [Formula.freeSupport, hMember]
              have hRightFresh :
                  ∀ sort,
                    (sort, target) ∉
                      Term.freeSupport right := by
                intro sort hMember
                exact hFresh sort <| by
                  simp [Formula.freeSupport, hMember]
              have hLeftToken :=
                quote_term_tokens_with?_free_name_not_mem
                  entryDepth target hLeftFresh hLeft
              have hRightToken :=
                quote_term_tokens_with?_free_name_not_mem
                  entryDepth target hRightFresh hRight
              simp [Numbered.equality_tokens,
                (logical_token_ne_variable_token
                  .leftParenthesis (free_name target)).symm,
                (logical_token_ne_variable_token
                  .equality (free_name target)).symm,
                (logical_token_ne_variable_token
                  .rightParenthesis (free_name target)).symm,
                hLeftToken, hRightToken]
  | neg body ih =>
      cases hBody :
          Numbered.quote_hilbert_tokens_with?
            free_name bound_name
            (canonical_bound_names entryDepth)
            entryDepth body with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hBody] at hQuote
      | some bodyTokens =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hBody] at hQuote
          subst tokens
          have hBodyFresh :
              ∀ sort,
                (sort, target) ∉
                  Formula.freeSupport body := by
            simpa [Formula.freeSupport] using hFresh
          have hBodyToken :=
            ih entryDepth hBodyFresh hBody
          simp [Numbered.negation_tokens,
            (logical_token_ne_variable_token
              .leftParenthesis (free_name target)).symm,
            (logical_token_ne_variable_token
              .negation (free_name target)).symm,
            (logical_token_ne_variable_token
              .rightParenthesis (free_name target)).symm,
            hBodyToken]
  | conj left right =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | disj left right =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | imp left right ihLeft ihRight =>
      cases hLeft :
          Numbered.quote_hilbert_tokens_with?
            free_name bound_name
            (canonical_bound_names entryDepth)
            entryDepth left with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hLeft] at hQuote
      | some leftTokens =>
          cases hRight :
              Numbered.quote_hilbert_tokens_with?
                free_name bound_name
                (canonical_bound_names entryDepth)
                entryDepth right with
          | none =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeft, hRight] at hQuote
          | some rightTokens =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeft, hRight] at hQuote
              subst tokens
              have hLeftFresh :
                  ∀ sort,
                    (sort, target) ∉
                      Formula.freeSupport left := by
                intro sort hMember
                exact hFresh sort <| by
                  simp [Formula.freeSupport, hMember]
              have hRightFresh :
                  ∀ sort,
                    (sort, target) ∉
                      Formula.freeSupport right := by
                intro sort hMember
                exact hFresh sort <| by
                  simp [Formula.freeSupport, hMember]
              have hLeftToken :=
                ihLeft entryDepth hLeftFresh hLeft
              have hRightToken :=
                ihRight entryDepth hRightFresh hRight
              simp [Numbered.implication_tokens,
                (logical_token_ne_variable_token
                  .leftParenthesis (free_name target)).symm,
                (logical_token_ne_variable_token
                  .implication (free_name target)).symm,
                (logical_token_ne_variable_token
                  .rightParenthesis (free_name target)).symm,
                hLeftToken, hRightToken]
  | iff left right =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | forallE sort body ih =>
      let binderName := bound_name entryDepth
      cases hBody :
          Numbered.quote_hilbert_tokens_with?
            free_name bound_name
            (binderName ::
              canonical_bound_names entryDepth)
            (entryDepth + 1) body with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            binderName, hBody] at hQuote
      | some bodyTokens =>
          simp [Numbered.quote_hilbert_tokens_with?,
            binderName, hBody] at hQuote
          subst tokens
          have hBodyFresh :
              ∀ sort,
                (sort, target) ∉
                  Formula.freeSupport body := by
            simpa [Formula.freeSupport] using hFresh
          have hBodyCanonical :
              Numbered.quote_hilbert_tokens_with?
                  free_name bound_name
                  (canonical_bound_names
                    (entryDepth + 1))
                  (entryDepth + 1) body =
                some bodyTokens := by
            simpa [binderName, canonical_bound_names] using
              hBody
          have hBodyToken :=
            ih (entryDepth + 1)
              hBodyFresh hBodyCanonical
          simp [Numbered.universal_tokens,
            (logical_token_ne_variable_token
              .leftParenthesis (free_name target)).symm,
            (logical_token_ne_variable_token
              .universal (free_name target)).symm,
            (variable_token_ne_variable_token
              (free_name_ne_bound_name
                target entryDepth)),
            (logical_token_ne_variable_token
              .rightParenthesis (free_name target)).symm,
            hBodyToken]
  | existsE sort body =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote

/-- 原公式的新鲜性直接推出规范 token quotation 的偶数自由变量标签避让。 -/
theorem quote_tokens?_free_name_not_mem
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol]
    (target : Nat)
    {formula : Formula σ} {tokens : List Nat}
    (hFresh :
      (numbering.objectSort, target) ∉
        Formula.freeSupport formula)
    (hQuote :
      Numbered.quote_tokens? formula = some tokens) :
    Numbered.variable_token (free_name target) ∉ tokens := by
  have hHilbertFresh :
      ∀ sort,
        (sort, target) ∉
          Formula.freeSupport
            (Formula.hilbertize
              numbering.objectSort formula) := by
    intro sort hMember
    have hSort : sort = numbering.objectSort :=
      numbering.sort_eq_object sort
    subst sort
    exact hFresh <|
      (Formula.mem_freeSupport_hilbertize_iff
        numbering.objectSort
        (numbering.objectSort, target) formula).mp hMember
  apply quote_hilbert_tokens_with?_free_name_not_mem
    0 target hHilbertFresh
  simpa [Numbered.quote_tokens?,
    Numbered.quote_tokens_with?,
    canonical_bound_names] using hQuote

/-! ## 对象层变量出现否定 -/

/--
闭代码等式可运输变量符号出现条件。该结论只使用一阶等词替换，不依赖任何
quotation 专用理论公理。
-/
theorem variable_symbol_occurs_iff_of_code_equality
    {T : Theory signature} {Γ : Context signature}
    (boundVariable left right : SetTerm)
    (hBoundVariable : Numbered.CodeBoundary boundVariable)
    (hLeft : Numbered.CodeBoundary left)
    (hRight : Numbered.CodeBoundary right)
    (hEquality :
      Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      variable_symbol_occurs_condition boundVariable left ↔ₘ
        variable_symbol_occurs_condition boundVariable right := by
  let body : SetFormula :=
    variable_symbol_occurs_condition
      boundVariable (x#490)
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ)
      (sort := SetSort.set) (eigen := 490)
      (left := left) (right := right)
      (body := body) hEquality
  have hBoundVariableFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 490 replacement
          boundVariable =
        boundVariable :=
    Numbered.CodeBoundary.substituteFree_eq
      hBoundVariable 490 replacement
  have hBoundVariableClose :
      Term.closeFreeAt SetSort.set 312 0 boundVariable =
        boundVariable :=
    Numbered.CodeBoundary.closeFreeAt_eq
      hBoundVariable 312 0
  have hLeftClose :
      Term.closeFreeAt SetSort.set 312 0 left = left :=
    Numbered.CodeBoundary.closeFreeAt_eq hLeft 312 0
  have hRightClose :
      Term.closeFreeAt SetSort.set 312 0 right = right :=
    Numbered.CodeBoundary.closeFreeAt_eq hRight 312 0
  have hNumeralClose :
      Term.closeFreeAt SetSort.set 312 0 (numₘ(0)) =
        numₘ(0) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 312 0 (numₘ(0))
      (finite_numeral_term_admissible 0).2 (by
        simp [finite_numeral_term_freeSupport])
  have hNumeralSubstitute (replacement : SetTerm) :
      Term.substituteFree SetSort.set 490 replacement
          (numₘ(0)) =
        numₘ(0) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 490 replacement (numₘ(0)) (by
        simp [finite_numeral_term_freeSupport])
  have hVariableFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 490 replacement
          (x#490) =
        replacement := by
    simp [Term.substituteFree, set_variable]
  simpa [body, variable_symbol_occurs_condition,
    Formula.substituteFree,
    Formula.closeFreeAt, Formula.next_depth,
    Term.substituteFree, set_variable,
    Term.closeFreeAt,
    hBoundVariableFixed, hVariableFixed,
    hBoundVariableClose, hLeftClose, hRightClose,
    hNumeralClose, hNumeralSubstitute] using
      hCongruence

/--
变量符号出现条件可同时沿变量码等式与公式码等式运输。

四个项均为闭代码，因此运输只使用一阶等词替换，不增加 occurrence 理论前提。
-/
theorem variable_symbol_occurs_iff_of_equalities
    {T : Theory signature} {Γ : Context signature}
    (leftVariable rightVariable left right : SetTerm)
    (hLeftVariable : Numbered.CodeBoundary leftVariable)
    (hRightVariable : Numbered.CodeBoundary rightVariable)
    (hLeft : Numbered.CodeBoundary left)
    (hRight : Numbered.CodeBoundary right)
    (hVariableEquality :
      Γ ⊢ₘ[T] leftVariable ≐ₘ rightVariable)
    (hCodeEquality :
      Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      variable_symbol_occurs_condition leftVariable left ↔ₘ
        variable_symbol_occurs_condition rightVariable right := by
  have hCodeIff :=
    variable_symbol_occurs_iff_of_code_equality
      leftVariable left right hLeftVariable hLeft hRight hCodeEquality
  let body : SetFormula :=
    variable_symbol_occurs_condition (x#493) right
  have hNormalize
      (replacement : SetTerm)
      (hReplacement : Numbered.CodeBoundary replacement) :
      Formula.substituteFree SetSort.set 493 replacement body =
        variable_symbol_occurs_condition replacement right := by
    exact variable_symbol_occurs_condition_substituteFree
      493 replacement (x#493) right replacement right
      (by native_decide) hReplacement.1
      (by
        rw [hReplacement.2]
        exact List.not_mem_nil)
      (by simp [Term.substituteFree, set_variable])
      (Numbered.CodeBoundary.substituteFree_eq
        hRight 493 replacement)
  have hVariableIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ)
      (sort := SetSort.set) (eigen := 493)
      (left := leftVariable) (right := rightVariable)
      (body := body) hVariableEquality
      (hLeftCheck := hLeftVariable.check_certificate)
      (hRightCheck := hRightVariable.check_certificate)
      (hBodyCheck := Formula.check_certificate_of_admissible <| by
        exact variable_symbol_occurs_condition_admissible
          (x#493) right
          (set_variable_admissible 493) hRight.1)
  have hVariableIff :
      Γ ⊢ₘ[T]
        variable_symbol_occurs_condition leftVariable right ↔ₘ
          variable_symbol_occurs_condition rightVariable right := by
    simpa only [
      hNormalize leftVariable hLeftVariable,
      hNormalize rightVariable hRightVariable] using
      hVariableIffRaw
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.impElim
      (Metatheory.Derives.iff_trans_m
        (φ := variable_symbol_occurs_condition
          leftVariable right)
        (ψ := variable_symbol_occurs_condition
          leftVariable left)
        (θ := variable_symbol_occurs_condition
          rightVariable right)
        (variable_symbol_occurs_condition_admissible
          leftVariable right hLeftVariable.1 hRight.1)
        (variable_symbol_occurs_condition_admissible
          leftVariable left hLeftVariable.1 hLeft.1)
        (variable_symbol_occurs_condition_admissible
          rightVariable right hRightVariable.1 hRight.1))
      hCodeIff)
    hVariableIff

/--
若变量 token 不在标准串中，则对应具名变量不满足该串上的变量符号出现条件。
-/
theorem standard_token_sequence_not_variable_symbol_occurs
    (tokens : List Nat) (name : Nat)
    (hToken :
      Numbered.variable_token name ∉ tokens) :
    ⊢ₘ[quotation_occurrence_theory]
      ¬ₘ variable_symbol_occurs_condition
        (Numbered.named_variable_code name)
        (standard_token_sequence tokens) := by
  let variableCode :=
    Numbered.named_variable_code name
  let formulaCode :=
    standard_token_sequence tokens
  let occurrence : SetFormula :=
    variable_symbol_occurs_condition
      variableCode formulaCode
  let Γ : Context signature := [occurrence]
  have hVariableBoundary :
      Numbered.CodeBoundary variableCode :=
    ⟨variable_code_term_admissible
        (numₘ(name))
        (finite_numeral_term_admissible name),
      named_variable_code_freeSupport name⟩
  have hFormulaBoundary :
      Numbered.CodeBoundary formulaCode :=
    ⟨standard_token_sequence_admissible tokens,
      standard_token_sequence_freeSupport_nil tokens⟩
  nd_apply FirstOrder.Derives.negIntro
  have hOccurrence :
      Γ ⊢ₘ[quotation_occurrence_theory]
        occurrence :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hExists :
      Γ ⊢ₘ[quotation_occurrence_theory]
        ∃ₘ[SetSort.set, 312],
          ((x#312 ∈ₘ domₘ(formulaCode)) ∧ₘ
            ((formulaCode ·ₘ x#312) ≐ₘ
              (variableCode ·ₘ numₘ(0)))) := by
    simpa [occurrence,
      variable_symbol_occurs_condition] using
      FirstOrder.Derives.conjElimRight hOccurrence
  nd_apply FirstOrder.Derives.exists_elim
      (T := quotation_occurrence_theory)
      (Γ := Γ) (sort := SetSort.set)
      (eigen := 312)
      (body :=
        (x#312 ∈ₘ domₘ(formulaCode)) ∧ₘ
          ((formulaCode ·ₘ x#312) ≐ₘ
            (variableCode ·ₘ numₘ(0))))
      (conclusion := Formula.falsum)
  · intro formula hFormula
    rw [(quotation_occurrence_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simp [occurrence,
      variable_symbol_occurs_condition,
      Formula.freeSupport,
      Term.freeSupport, Term.freeSupportList,
      hVariableBoundary.2,
      Formula.not_mem_freeSupport_closeFreeAt]
  · exact List.not_mem_nil
  · exact hExists
  · let position : SetTerm := x#312
    let positionCondition : SetFormula :=
      (position ∈ₘ domₘ(formulaCode)) ∧ₘ
        ((formulaCode ·ₘ position) ≐ₘ
          (variableCode ·ₘ numₘ(0)))
    let Δ : Context signature :=
      [positionCondition, occurrence]
    have hPositionCondition :
        Δ ⊢ₘ[quotation_occurrence_theory]
          positionCondition :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hPositionMember :
        Δ ⊢ₘ[quotation_occurrence_theory]
          position ∈ₘ domₘ(formulaCode) :=
      FirstOrder.Derives.conjElimLeft
        hPositionCondition
    have hValueEquality :
        Δ ⊢ₘ[quotation_occurrence_theory]
          (formulaCode ·ₘ position) ≐ₘ
            (variableCode ·ₘ numₘ(0)) :=
      FirstOrder.Derives.conjElimRight
        hPositionCondition
    have hAvoidanceUniversal :=
      standard_token_sequence_avoids_token
        tokens (Numbered.variable_token name) hToken
    have hAvoidanceAtRaw :=
      FirstOrder.Derives.forall_elim
        (term := position)
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ])
          hAvoidanceUniversal)
    have hTokenBoundary :
        Numbered.CodeBoundary
          (numₘ(Numbered.variable_token name)) :=
      ⟨finite_numeral_term_admissible
          (Numbered.variable_token name),
        finite_numeral_term_freeSupport
          (Numbered.variable_token name)⟩
    have hAvoidanceAt :
        Δ ⊢ₘ[quotation_occurrence_theory]
          (position ∈ₘ domₘ(formulaCode)) ⟶ₘ
            ¬ₘ ((formulaCode ·ₘ position) ≐ₘ
              numₘ(Numbered.variable_token name)) := by
      simpa [position, formulaCode,
        Formula.openAt_closeFreeAt_eq_substituteFree,
        Formula.openAt, Formula.substituteFree,
        Term.openAt, Term.substituteFree,
        set_variable,
        Numbered.CodeBoundary.substituteFree_eq
          hFormulaBoundary,
        Numbered.CodeBoundary.substituteFree_eq
          hTokenBoundary] using hAvoidanceAtRaw
    have hNotTokenValue :
        Δ ⊢ₘ[quotation_occurrence_theory]
          ¬ₘ ((formulaCode ·ₘ position) ≐ₘ
            numₘ(Numbered.variable_token name)) :=
      FirstOrder.Derives.impElim
        hAvoidanceAt hPositionMember
    have hVariableValue :
        Δ ⊢ₘ[quotation_occurrence_theory]
          (variableCode ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.variable_token name) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp [Δ]) <| by
          simpa [variableCode] using
            named_variable_code_apply_zero name
    have hTokenValue :
        Δ ⊢ₘ[quotation_occurrence_theory]
          (formulaCode ·ₘ position) ≐ₘ
            numₘ(Numbered.variable_token name) :=
      Metatheory.Derives.equality_trans
        hValueEquality hVariableValue
    exact FirstOrder.Derives.negElim
      hTokenValue hNotTokenValue

/--
规范 quotation 的元层自由变量新鲜性推出对象公式码上的变量符号出现否定。
-/
theorem quote?_not_variable_symbol_occurs_of_fresh
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol]
    (target : Nat)
    {formula : Formula σ} {code : SetTerm}
    (hFormula : Formula.Admissible formula)
    (hFresh :
      (numbering.objectSort, target) ∉
        Formula.freeSupport formula)
    (hQuote :
      Numbered.quote? formula = some code) :
    ⊢ₘ[quotation_occurrence_theory]
      ¬ₘ variable_symbol_occurs_condition
        (Numbered.named_variable_code
          (free_name target))
        code := by
  rcases Numbered.quote_tokens?_exists hFormula with
    ⟨tokens, hTokens⟩
  let variableCode :=
    Numbered.named_variable_code (free_name target)
  let standardCode :=
    standard_token_sequence tokens
  have hVariableBoundary :
      Numbered.CodeBoundary variableCode :=
    ⟨variable_code_term_admissible
        (numₘ(free_name target))
        (finite_numeral_term_admissible
          (free_name target)),
      named_variable_code_freeSupport
        (free_name target)⟩
  have hCodeBoundary :
      Numbered.CodeBoundary code :=
    Numbered.quote?_code_boundary hQuote
  have hStandardBoundary :
      Numbered.CodeBoundary standardCode :=
    ⟨standard_token_sequence_admissible tokens,
      standard_token_sequence_freeSupport_nil tokens⟩
  have hToken :
      Numbered.variable_token (free_name target) ∉ tokens :=
    quote_tokens?_free_name_not_mem
      target hFresh hTokens
  have hCodeEquality :
      ⊢ₘ[quotation_occurrence_theory]
        code ≐ₘ standardCode := by
    simpa [standardCode] using
      qo_weaken_godel_quotation <|
        quote?_eq_standard_token_sequence
          hTokens hQuote
  have hOccurrenceIff :
      ⊢ₘ[quotation_occurrence_theory]
        variable_symbol_occurs_condition
            variableCode code ↔ₘ
          variable_symbol_occurs_condition
            variableCode standardCode :=
    variable_symbol_occurs_iff_of_code_equality
      variableCode code standardCode
      hVariableBoundary hCodeBoundary
      hStandardBoundary hCodeEquality
  have hNotStandard :
      ⊢ₘ[quotation_occurrence_theory]
        ¬ₘ variable_symbol_occurs_condition
          variableCode standardCode := by
    simpa [variableCode, standardCode] using
      standard_token_sequence_not_variable_symbol_occurs
        tokens (free_name target) hToken
  let occurrence : SetFormula :=
    variable_symbol_occurs_condition
      variableCode code
  let Γ : Context signature := [occurrence]
  nd_apply FirstOrder.Derives.negIntro
  have hOccurrence :
      Γ ⊢ₘ[quotation_occurrence_theory]
        variable_symbol_occurs_condition
          variableCode code := by
    simpa [Γ, occurrence] using
      (FirstOrder.Derives.assumption
        (T := quotation_occurrence_theory)
        (Γ := Γ) (φ := occurrence) (by simp [Γ]))
  have hStandardOccurrence :
      Γ ⊢ₘ[quotation_occurrence_theory]
        variable_symbol_occurs_condition
          variableCode standardCode :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken_cons
        hOccurrenceIff)
      hOccurrence
  exact FirstOrder.Derives.negElim
    hStandardOccurrence
    (FirstOrder.Derives.context_weaken_cons
      hNotStandard)

/--
规范 quotation 中，偶数自由变量名不会作为全称量词 binder 出现。
该结论只使用自由名/约束名分离，不要求该自由变量在公式中本身新鲜。
-/
theorem quote?_not_quantifier_occurs_free_name
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol]
    (target : Nat)
    {formula : Formula σ} {code : SetTerm}
    (hFormula : Formula.Admissible formula)
    (hQuote : Numbered.quote? formula = some code) :
    ⊢ₘ[quotation_occurrence_theory]
      ¬ₘ quantifier_occurs_condition
        (Numbered.named_variable_code (free_name target)) code := by
  rcases Numbered.quote_tokens?_exists hFormula with
    ⟨tokens, hTokens⟩
  let variableCode :=
    Numbered.named_variable_code (free_name target)
  let standardCode := standard_token_sequence tokens
  let variableTokens := [Numbered.variable_token (free_name target)]
  have hVariableTokens :
      quote_term_tokens?
          (Term.var (.fvar numbering.objectSort target) : Term σ) =
        some variableTokens := by
    simp [variableTokens, quote_term_tokens?,
      Numbered.quote_term_tokens_with?]
  have hFollower :
      gq_universal_follower_condition
        (fun token => token ∉ variableTokens) tokens :=
    quote_tokens?_universal_followers_avoid_term
      hTokens hVariableTokens
  have hSeparation :
      ⊢ₘ[quotation_occurrence_theory]
        universal_binder_at_condition
            variableCode standardCode (x#321) (x#322) ⟶ₘ
          ¬ₘ variable_symbol_occurs_condition
            variableCode (standard_token_sequence variableTokens) := by
    simpa [variableCode, standardCode] using
      standard_token_sequences_universal_binder_separation
        tokens variableTokens hFollower
        variableCode (x#321) (x#322) (by
          apply reserved_ids_fresh_cons_closed
            (named_variable_code_freeSupport (free_name target))
          apply reserved_ids_fresh_cons_variable 321
          · intro id hId
            simp only [List.mem_cons, List.not_mem_nil,
              or_false] at hId
            rcases hId with rfl | rfl | rfl <;> decide
          apply reserved_ids_fresh_cons_variable 322
          · intro id hId
            simp only [List.mem_cons, List.not_mem_nil,
              or_false] at hId
            rcases hId with rfl | rfl | rfl <;> decide
          exact reserved_ids_fresh_nil _)
        (Term.check_admissible_complete <|
          variable_code_term_admissible
            (numₘ(free_name target))
            (finite_numeral_term_admissible (free_name target)))
        (by prove_term_check) (by prove_term_check)
  have hVariableOccurrence :
      ⊢ₘ[quotation_occurrence_theory]
        variable_symbol_occurs_condition
          variableCode (standard_token_sequence variableTokens) := by
    simpa [variableCode, variableTokens] using
      standard_token_sequence_variable_symbol_occurs
        variableTokens (free_name target) (by simp [variableTokens])
  have hNotStandard :
      ⊢ₘ[quotation_occurrence_theory]
        ¬ₘ quantifier_occurs_condition variableCode standardCode := by
    let binder : SetFormula :=
      universal_binder_at_condition
        variableCode standardCode (x#321) (x#322)
    have hBinderImp :
        ⊢ₘ[quotation_occurrence_theory]
          binder ⟶ₘ Formula.falsum := by
      nd_apply FirstOrder.Derives.impIntro
      exact FirstOrder.Derives.negElim
        (FirstOrder.Derives.context_weaken_cons hVariableOccurrence)
        (FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken_cons hSeparation)
          (FirstOrder.Derives.assumption (by simp [binder])))
    have hTheoryFresh (id : FreeVarId) :
        ∀ φ, quotation_occurrence_theory φ →
          (SetSort.set, id) ∉ Formula.freeSupport φ := by
      intro φ hφ
      rw [(quotation_occurrence_theory_sentence hφ).2]
      exact List.not_mem_nil
    have hEmptyFresh (id : FreeVarId) :
        ∀ φ, φ ∈ ([] : Context signature) →
          (SetSort.set, id) ∉ Formula.freeSupport φ := by
      intro φ hφ
      exact False.elim (List.not_mem_nil hφ)
    have hStartImp :=
      FirstOrder.Derives.exists_imp_of_imp
        (T := quotation_occurrence_theory)
        (Γ := ([] : Context signature))
        (sort := SetSort.set) (eigen := 322)
        (body := binder) (conclusion := Formula.falsum)
        (hTheoryFresh 322) (hEmptyFresh 322)
        List.not_mem_nil hBinderImp
    have hBodyImp :=
      FirstOrder.Derives.exists_imp_of_imp
        (T := quotation_occurrence_theory)
        (Γ := ([] : Context signature))
        (sort := SetSort.set) (eigen := 321)
        (body := ∃ₘ[SetSort.set, 322], binder)
        (conclusion := Formula.falsum)
        (hTheoryFresh 321) (hEmptyFresh 321)
        List.not_mem_nil hStartImp
    nd_apply FirstOrder.Derives.negIntro
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken_cons hBodyImp)
      (FirstOrder.Derives.assumption (by
        simp [quantifier_occurs_condition, binder]))
  have hCodeEquality :
      ⊢ₘ[quotation_occurrence_theory] code ≐ₘ standardCode := by
    simpa [standardCode] using
      qo_weaken_godel_quotation
        (quote?_eq_standard_token_sequence hTokens hQuote)
  let body : SetFormula :=
    quantifier_occurs_condition variableCode (x#492)
  have hSubstitute
      (replacement : SetTerm)
      (hReplacement : Numbered.CodeBoundary replacement) :
      Formula.substituteFree SetSort.set 492 replacement body =
        quantifier_occurs_condition variableCode replacement := by
    dsimp only [body, quantifier_occurs_condition]
    simp only [Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 492 321 0 replacement _ (by decide)
      hReplacement.1.2 (by rw [hReplacement.2]; exact List.not_mem_nil)]
    simp only [Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 492 322 0 replacement _ (by decide)
      hReplacement.1.2 (by rw [hReplacement.2]; exact List.not_mem_nil)]
    simp only [universal_binder_at_condition,
      code_substring_at_condition,
      Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 492 320 0 replacement _ (by decide)
      hReplacement.1.2 (by rw [hReplacement.2]; exact List.not_mem_nil)]
    simp [Formula.substituteFree, Term.substituteFree,
      set_variable, variableCode,
      Numbered.CodeBoundary.substituteFree_eq
        ⟨variable_code_term_admissible
            (numₘ(free_name target))
            (finite_numeral_term_admissible (free_name target)),
          named_variable_code_freeSupport (free_name target)⟩
      ]
  have hOccurrenceIff :=
    Metatheory.Derives.equality_iff_of_equality
      (T := quotation_occurrence_theory) (Γ := [])
      (sort := SetSort.set) (eigen := 492)
      (left := code) (right := standardCode)
      (body := body) hCodeEquality
      (hLeftCheck := Term.check_admissible_complete
        (Numbered.quote?_code_boundary hQuote).1)
      (hRightCheck := Term.check_admissible_complete
        (standard_token_sequence_admissible tokens))
      (hBodyCheck := Formula.check_admissible_complete <| by
        simpa [body] using
          quantifier_occurs_condition_admissible
            variableCode (x#492)
            (variable_code_term_admissible
              (numₘ(free_name target))
              (finite_numeral_term_admissible (free_name target)))
            (set_variable_admissible 492))
  rw [hSubstitute code (Numbered.quote?_code_boundary hQuote),
    hSubstitute standardCode
      ⟨standard_token_sequence_admissible tokens,
        standard_token_sequence_freeSupport_nil tokens⟩] at hOccurrenceIff
  have hNotCode :
      ⊢ₘ[quotation_occurrence_theory]
        ¬ₘ quantifier_occurs_condition variableCode code := by
    nd_apply FirstOrder.Derives.negIntro
    exact FirstOrder.Derives.negElim
      (FirstOrder.Derives.iffElimRight
        (FirstOrder.Derives.context_weaken_cons hOccurrenceIff)
        (FirstOrder.Derives.assumption (by simp)))
      (FirstOrder.Derives.context_weaken_cons hNotStandard)
  simpa [variableCode] using hNotCode

/-- 变量代码等式从右向左运输量词出现谓词的否定。 -/
theorem not_quantifier_occurs_congr_variable_code
    {T : Theory signature}
    (left right formula : SetTerm)
    (hLeft : Numbered.CodeBoundary left)
    (hRight : Numbered.CodeBoundary right)
    (hFormula : Numbered.CodeBoundary formula)
    (hEquality : ⊢ₘ[T] left ≐ₘ right)
    (hNotRight :
      ⊢ₘ[T] ¬ₘ quantifier_occurs_condition right formula) :
    ⊢ₘ[T] ¬ₘ quantifier_occurs_condition left formula := by
  let body : SetFormula :=
    ¬ₘ quantifier_occurs_condition (x#492) formula
  have hRightQuantifier :
      Formula.substituteFree SetSort.set 492 right
          (quantifier_occurs_condition (x#492) formula) =
        quantifier_occurs_condition right formula :=
    quantifier_occurs_condition_substituteFree
      (sourceId := 492) (replacement := right)
      (boundVariable := x#492) (formula := formula)
      (boundVariableResult := right) (formulaResult := formula)
      (by native_decide) hRight.1
      (fun id _ => by
        rw [hRight.2]
        exact List.not_mem_nil)
      (by simp [Term.substituteFree, set_variable])
      (Numbered.CodeBoundary.substituteFree_eq hFormula 492 right)
  have hLeftQuantifier :
      Formula.substituteFree SetSort.set 492 left
          (quantifier_occurs_condition (x#492) formula) =
        quantifier_occurs_condition left formula :=
    quantifier_occurs_condition_substituteFree
      (sourceId := 492) (replacement := left)
      (boundVariable := x#492) (formula := formula)
      (boundVariableResult := left) (formulaResult := formula)
      (by native_decide) hLeft.1
      (fun id _ => by
        rw [hLeft.2]
        exact List.not_mem_nil)
      (by simp [Term.substituteFree, set_variable])
      (Numbered.CodeBoundary.substituteFree_eq hFormula 492 left)
  have hTransport :=
    FirstOrder.Derives.eq_subst_m
      (T := T) (Γ := []) (sort := SetSort.set) (eigen := 492)
      (left := right) (right := left) (body := body)
      (Metatheory.Derives.equality_symm hEquality)
      (by
        rw [show Formula.substituteFree SetSort.set 492 right body =
            ¬ₘ quantifier_occurs_condition right formula by
          dsimp only [body]
          simp only [Formula.substituteFree]
          rw [hRightQuantifier]]
        exact hNotRight)
  rw [show Formula.substituteFree SetSort.set 492 left body =
      ¬ₘ quantifier_occurs_condition left formula by
    dsimp only [body]
    simp only [Formula.substituteFree]
    rw [hLeftQuantifier]] at hTransport
  exact hTransport

/--
规范 quotation 的自由变量新鲜性最终给出对象变量集合的非成员证书。
-/
theorem quote?_variable_collection_not_mem_of_fresh
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol]
    (target : Nat)
    {formula : Formula σ} {code : SetTerm}
    (hFormula : Formula.Admissible formula)
    (hFresh :
      (numbering.objectSort, target) ∉
        Formula.freeSupport formula)
    (hQuote :
      Numbered.quote? formula = some code) :
    ⊢ₘ[quotation_occurrence_theory]
      ¬ₘ (Numbered.named_variable_code
          (free_name target) ∈ₘ varsₘ(code)) := by
  let variableCode :=
    Numbered.named_variable_code (free_name target)
  have hVariableBoundary :
      Numbered.CodeBoundary variableCode :=
    ⟨variable_code_term_admissible
        (numₘ(free_name target))
        (finite_numeral_term_admissible
          (free_name target)),
      named_variable_code_freeSupport
        (free_name target)⟩
  have hCodeBoundary :
      Numbered.CodeBoundary code :=
    Numbered.quote?_code_boundary hQuote
  have hFormulaUnion :
      ⊢ₘ[godel_quotation_theory]
        code ∈ₘ (TermCodeₘ ∪ₘ FormulaCodeₘ) :=
    gq_mem_binary_union_right
      TermCodeₘ FormulaCodeₘ code
      term_code_set_term_admissible
      formula_code_set_term_admissible
      hCodeBoundary.1
      (Numbered.quote?_formula_code_mem hQuote)
  have hInversion :=
    qo_weaken_godel_quotation <|
      gq_variable_collection_member_inversion
        code hCodeBoundary hFormulaUnion
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := variableCode) hInversion
  have hNumeralClose (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth (numₘ(0)) =
        numₘ(0) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth (numₘ(0))
      (finite_numeral_term_admissible 0).2 (by
        simp [finite_numeral_term_freeSupport])
  have hNumeralOpen (depth : Nat)
      (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement
          (numₘ(0)) =
        numₘ(0) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(0))
      (finite_numeral_term_admissible 0).2
  have hAt :
      ⊢ₘ[quotation_occurrence_theory]
        (variableCode ∈ₘ varsₘ(code)) ⟶ₘ
          ((variableCode ∈ₘ VarSymₘ) ∧ₘ
            variable_symbol_occurs_condition
              variableCode code) := by
    simpa [
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable,
      variable_symbol_occurs_condition,
      hNumeralClose, hNumeralOpen,
      Numbered.CodeBoundary.openAt_eq hCodeBoundary,
      Numbered.CodeBoundary.substituteFree_eq
        hCodeBoundary,
      Numbered.CodeBoundary.closeFreeAt_eq
        hCodeBoundary,
      Numbered.CodeBoundary.openAt_eq
        hVariableBoundary,
      Numbered.CodeBoundary.substituteFree_eq
        hVariableBoundary,
      Numbered.CodeBoundary.closeFreeAt_eq
        hVariableBoundary] using hAtRaw
  have hNotOccurs :
      ⊢ₘ[quotation_occurrence_theory]
        ¬ₘ variable_symbol_occurs_condition
          variableCode code := by
    simpa [variableCode] using
      quote?_not_variable_symbol_occurs_of_fresh
        target hFormula hFresh hQuote
  let membership : SetFormula :=
    variableCode ∈ₘ varsₘ(code)
  let Γ : Context signature := [membership]
  nd_apply FirstOrder.Derives.negIntro
  have hMembership :
      Γ ⊢ₘ[quotation_occurrence_theory]
        variableCode ∈ₘ varsₘ(code) := by
    simpa [Γ, membership] using
      (FirstOrder.Derives.assumption
        (T := quotation_occurrence_theory)
        (Γ := Γ) (φ := membership) (by simp [Γ]))
  have hOccurs :
      Γ ⊢ₘ[quotation_occurrence_theory]
        variable_symbol_occurs_condition
          variableCode code :=
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken_cons hAt)
        hMembership
  exact FirstOrder.Derives.negElim
    hOccurs
    (FirstOrder.Derives.context_weaken_cons hNotOccurs)

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
