import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.Symbol

/-!
# FormalSystem 有限签名公式条件的正向回放

本模块把宿主 quotation 的实际 token 分类翻译为对象层
`fs_formula_token_condition`。证明只使用有限签名枚举与标准 singleton token
语义，不改变公共 `FormulaCodeₘ` 的可数签名强度。
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

/-! ## 宿主 token 分类 -/

/-- 当前 `FormalSystem` 公式 quotation 中允许出现的 token。 -/
inductive FSFormulaToken : Nat → Prop where
  | logical (symbol : LogicalSymbolKind) :
      FSFormulaToken (Numbered.logical_token symbol)
  | membership :
      FSFormulaToken Numbered.membership_token
  | var (name : Nat) :
      FSFormulaToken (Numbered.variable_token name)
  | func (symbol : FunctionSymbol) :
      FSFormulaToken (fs_function_symbol_token symbol)
  | pred (symbol : RelationSymbol)
      (hSymbol : symbol ≠ RelationSymbol.membership) :
      FSFormulaToken (fs_predicate_symbol_token symbol)

/-- 一列 token 全部落在当前有限签名中。 -/
def FSFormulaTokens (tokens : List Nat) : Prop :=
  ∀ token, token ∈ tokens → FSFormulaToken token

theorem fs_formula_tokens_nil :
    FSFormulaTokens [] := by
  intro token hToken
  simp at hToken

theorem fs_formula_tokens_singleton
    {token : Nat} (hToken : FSFormulaToken token) :
    FSFormulaTokens [token] := by
  intro candidate hCandidate
  have hEquality : candidate = token := by
    simpa using hCandidate
  subst candidate
  exact hToken

theorem fs_formula_tokens_append
    {left right : List Nat}
    (hLeft : FSFormulaTokens left)
    (hRight : FSFormulaTokens right) :
    FSFormulaTokens (left ++ right) := by
  intro token hToken
  rcases List.mem_append.mp hToken with hToken | hToken
  · exact hLeft token hToken
  · exact hRight token hToken

theorem fs_formula_tokens_cons
    {head : Nat} {tail : List Nat}
    (hHead : FSFormulaToken head)
    (hTail : FSFormulaTokens tail) :
    FSFormulaTokens (head :: tail) := by
  simpa using fs_formula_tokens_append
    (fs_formula_tokens_singleton hHead) hTail

theorem fs_formula_tokens_flatten
    {pieces : List (List Nat)}
    (hPieces :
      ∀ piece, piece ∈ pieces →
        FSFormulaTokens piece) :
    FSFormulaTokens pieces.flatten := by
  intro token hToken
  rcases List.mem_flatten.mp hToken with
    ⟨piece, hPiece, hToken⟩
  exact hPieces piece hPiece token hToken

/-! ## quotation 的宿主分类 -/

mutual
  /-- sort 正确的项 quotation 只产生当前有限签名允许的 token。 -/
  theorem fs_quote_term_tokens_formula_tokens
      (freeNaming : FreeVarId → Nat)
      (boundNames : List Nat)
      {term : SetTerm} {sort : SetSort}
      {tokens : List Nat}
      (hTerm : TermWellSorted term sort)
      (hQuote :
        Numbered.quote_term_tokens_with?
            freeNaming boundNames term =
          some tokens) :
      FSFormulaTokens tokens := by
    cases hTerm with
    | bvar variableSort index =>
        cases hName : boundNames[index]? with
        | none =>
            simp [Numbered.quote_term_tokens_with?,
              hName] at hQuote
        | some name =>
            simp [Numbered.quote_term_tokens_with?,
              hName] at hQuote
            subst tokens
            exact fs_formula_tokens_singleton
              (.var name)
    | fvar variableSort id =>
        simp [Numbered.quote_term_tokens_with?] at hQuote
        subst tokens
        exact fs_formula_tokens_singleton
          (.var (freeNaming id))
    | @app function arguments hArguments =>
        cases hCodes :
            arguments.mapM
              (Numbered.quote_term_tokens_with?
                freeNaming boundNames) with
        | none =>
            simp [Numbered.quote_term_tokens_with?,
              hCodes] at hQuote
        | some pieces =>
            have hPieces :=
              fs_quote_term_token_lists_formula_tokens
                freeNaming boundNames hArguments hCodes
            have hLength :=
              fs_option_mapM_length hCodes
            cases pieces with
            | nil =>
                simp [Numbered.quote_term_tokens_with?,
                  hCodes] at hQuote
                subst tokens
                have hArgumentsLength :
                    arguments.length = 0 := by
                  simpa using hLength.symm
                have hDomainLength :
                    (signature.funcDomain
                      function).length = 0 := by
                  rw [← Numbered.args_well_sorted_length_eq
                    hArguments]
                  exact hArgumentsLength
                have hDomain :
                    signature.funcDomain function = [] :=
                  List.eq_nil_of_length_eq_zero
                    hDomainLength
                apply fs_formula_tokens_singleton
                simpa [fs_function_symbol_token,
                  hDomain] using
                  (FSFormulaToken.func function)
            | cons first rest =>
                simp [Numbered.quote_term_tokens_with?,
                  hCodes] at hQuote
                subst tokens
                have hArgumentsLength :
                    arguments.length =
                      (first :: rest).length :=
                  hLength.symm
                cases hDomain :
                    signature.funcDomain function with
                | nil =>
                    have hWellSortedLength :=
                      Numbered.args_well_sorted_length_eq
                        hArguments
                    rw [hDomain] at hWellSortedLength
                    simp [hArgumentsLength] at hWellSortedLength
                | cons domainHead domainTail =>
                    have hWellSortedLength :=
                      Numbered.args_well_sorted_length_eq
                        hArguments
                    rw [hDomain] at hWellSortedLength
                    simp only [List.length_cons] at hWellSortedLength
                    have hArity :
                        arguments.length - 1 =
                          domainTail.length := by
                      omega
                    have hFunction :
                        FSFormulaToken
                          (Numbered.function_token
                            (arguments.length - 1)
                            function.ctorIdx) := by
                      simpa [fs_function_symbol_token,
                        hDomain, hArity] using
                        (FSFormulaToken.func function)
                    have hPrefix :
                        FSFormulaTokens
                          [Numbered.function_token
                              (arguments.length - 1)
                              function.ctorIdx,
                            Numbered.logical_token
                              .leftParenthesis] :=
                      fs_formula_tokens_cons hFunction
                        (fs_formula_tokens_singleton
                          (.logical .leftParenthesis))
                    have hArguments :
                        FSFormulaTokens
                          (first :: rest).flatten :=
                      fs_formula_tokens_flatten hPieces
                    have hSuffix :
                        FSFormulaTokens
                          [Numbered.logical_token
                            .rightParenthesis] :=
                      fs_formula_tokens_singleton
                        (.logical .rightParenthesis)
                    simpa [Numbered.function_application_tokens,
                      List.append_assoc] using
                      fs_formula_tokens_append hPrefix
                        (fs_formula_tokens_append
                          hArguments hSuffix)

  /-- 一列 sort 正确实参的 quotation 逐段满足有限签名分类。 -/
  theorem fs_quote_term_token_lists_formula_tokens
      (freeNaming : FreeVarId → Nat)
      (boundNames : List Nat)
      {terms : List SetTerm} {sorts : List SetSort}
      {pieces : List (List Nat)}
      (hTerms : ArgsWellSorted terms sorts)
      (hQuote :
        terms.mapM
            (Numbered.quote_term_tokens_with?
              freeNaming boundNames) =
          some pieces) :
      ∀ piece, piece ∈ pieces →
        FSFormulaTokens piece := by
    cases hTerms with
    | nil =>
        have hPieces : pieces = [] := by
          simpa using Option.some.inj hQuote.symm
        subst pieces
        simp
    | @cons head tail sort sorts hHead hTail =>
        cases hHeadQuote :
            Numbered.quote_term_tokens_with?
              freeNaming boundNames head with
        | none =>
            simp [List.mapM_cons, hHeadQuote] at hQuote
        | some headTokens =>
            cases hTailQuote :
                tail.mapM
                  (Numbered.quote_term_tokens_with?
                    freeNaming boundNames) with
            | none =>
                simp [List.mapM_cons, hHeadQuote,
                  hTailQuote] at hQuote
            | some tailPieces =>
                simp [List.mapM_cons, hHeadQuote,
                  hTailQuote] at hQuote
                subst pieces
                intro piece hPiece
                rcases List.mem_cons.mp hPiece with
                  rfl | hPiece
                · exact
                    fs_quote_term_tokens_formula_tokens
                      freeNaming boundNames
                      hHead hHeadQuote
                · exact
                    fs_quote_term_token_lists_formula_tokens
                      freeNaming boundNames
                      hTail hTailQuote piece hPiece
end

/-- Hilbert 核 quotation 只产生当前有限签名允许的 token。 -/
theorem fs_quote_hilbert_tokens_formula_tokens
    (freeNaming binderNaming : Nat → Nat)
    (boundNames : List Nat) (depth : Nat)
    {formula : SetFormula} {tokens : List Nat}
    (hFormula : FormulaWellFormed formula)
    (hQuote :
      Numbered.quote_hilbert_tokens_with?
          freeNaming binderNaming
          boundNames depth formula =
        some tokens) :
    FSFormulaTokens tokens := by
  induction hFormula generalizing
      boundNames depth tokens with
  | falsum =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | truth =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | @rel relation arguments hArguments =>
      cases hKind :
          QuotationNumbering.relation_kind relation with
      | membership =>
          cases arguments with
          | nil =>
              simp [Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?,
                hKind] at hQuote
          | cons left tail =>
              cases tail with
              | nil =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?,
                    hKind] at hQuote
              | cons right extra =>
                  cases extra with
                  | cons third rest =>
                      simp [Numbered.quote_hilbert_tokens_with?,
                        Numbered.quote_relation_tokens_with?,
                        hKind] at hQuote
                  | nil =>
                      have hDomain :=
                        fs_quotation_numbering.membership_domain
                          relation hKind
                      rw [hDomain] at hArguments
                      cases hArguments with
                      | cons hLeft hTail =>
                          cases hTail with
                          | cons hRight hNil =>
                              cases hLeftQuote :
                                  Numbered.quote_term_tokens_with?
                                    freeNaming boundNames left with
                              | none =>
                                  simp [Numbered.quote_hilbert_tokens_with?,
                                    Numbered.quote_relation_tokens_with?,
                                    hKind, hLeftQuote] at hQuote
                              | some leftTokens =>
                                  cases hRightQuote :
                                      Numbered.quote_term_tokens_with?
                                        freeNaming boundNames right with
                                  | none =>
                                      simp [Numbered.quote_hilbert_tokens_with?,
                                        Numbered.quote_relation_tokens_with?,
                                        hKind, hLeftQuote,
                                        hRightQuote] at hQuote
                                  | some rightTokens =>
                                      simp [Numbered.quote_hilbert_tokens_with?,
                                        Numbered.quote_relation_tokens_with?,
                                        hKind, hLeftQuote,
                                        hRightQuote] at hQuote
                                      subst tokens
                                      have hLeftTokens :=
                                        fs_quote_term_tokens_formula_tokens
                                          freeNaming boundNames
                                          hLeft hLeftQuote
                                      have hRightTokens :=
                                        fs_quote_term_tokens_formula_tokens
                                          freeNaming boundNames
                                          hRight hRightQuote
                                      have hLeftParenthesis :=
                                        fs_formula_tokens_singleton
                                          (FSFormulaToken.logical
                                            .leftParenthesis)
                                      have hMembership :=
                                        fs_formula_tokens_singleton
                                          FSFormulaToken.membership
                                      have hRightParenthesis :=
                                        fs_formula_tokens_singleton
                                          (FSFormulaToken.logical
                                            .rightParenthesis)
                                      simpa [Numbered.membership_tokens,
                                        List.append_assoc] using
                                        fs_formula_tokens_append
                                          hLeftParenthesis
                                          (fs_formula_tokens_append
                                            hLeftTokens
                                            (fs_formula_tokens_append
                                              hMembership
                                              (fs_formula_tokens_append
                                                hRightTokens
                                                hRightParenthesis)))
      | predicate =>
          cases arguments with
          | nil =>
              simp [Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?,
                hKind] at hQuote
          | cons head tail =>
              cases hPieces :
                  (head :: tail).mapM
                    (Numbered.quote_term_tokens_with?
                      freeNaming boundNames) with
              | none =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?,
                    hKind, hPieces] at hQuote
              | some pieces =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?,
                    hKind, hPieces] at hQuote
                  subst tokens
                  have hPieceTokens :=
                    fs_quote_term_token_lists_formula_tokens
                      freeNaming boundNames
                      hArguments hPieces
                  have hRelation :
                      relation ≠ RelationSymbol.membership := by
                    intro hRelation
                    subst relation
                    simp [fs_membership_relation_kind] at hKind
                  have hLength :=
                    Numbered.args_well_sorted_length_eq
                      hArguments
                  have hPredicate :
                      FSFormulaToken
                        (Numbered.predicate_token
                          ((head :: tail).length - 1)
                          relation.ctorIdx) := by
                    simpa [fs_predicate_symbol_token,
                      hLength, Nat.pred_eq_sub_one] using
                      (FSFormulaToken.pred
                        relation hRelation)
                  have hPrefix :
                      FSFormulaTokens
                        [Numbered.predicate_token
                            ((head :: tail).length - 1)
                            relation.ctorIdx,
                          Numbered.logical_token
                            .leftParenthesis] :=
                    fs_formula_tokens_cons hPredicate
                      (fs_formula_tokens_singleton
                        (.logical .leftParenthesis))
                  have hArguments :
                      FSFormulaTokens pieces.flatten :=
                    fs_formula_tokens_flatten hPieceTokens
                  have hSuffix :
                      FSFormulaTokens
                        [Numbered.logical_token
                          .rightParenthesis] :=
                    fs_formula_tokens_singleton
                      (.logical .rightParenthesis)
                  simpa [Numbered.predicate_application_tokens,
                    List.append_assoc] using
                    fs_formula_tokens_append hPrefix
                      (fs_formula_tokens_append
                        hArguments hSuffix)
  | @equal left right sort hLeft hRight =>
      cases hLeftQuote :
          Numbered.quote_term_tokens_with?
            freeNaming boundNames left with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hLeftQuote] at hQuote
      | some leftTokens =>
          cases hRightQuote :
              Numbered.quote_term_tokens_with?
                freeNaming boundNames right with
          | none =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeftQuote, hRightQuote] at hQuote
          | some rightTokens =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeftQuote, hRightQuote] at hQuote
              subst tokens
              have hLeftTokens :=
                fs_quote_term_tokens_formula_tokens
                  freeNaming boundNames hLeft hLeftQuote
              have hRightTokens :=
                fs_quote_term_tokens_formula_tokens
                  freeNaming boundNames hRight hRightQuote
              have hLeftParenthesis :=
                fs_formula_tokens_singleton
                  (FSFormulaToken.logical .leftParenthesis)
              have hEquality :=
                fs_formula_tokens_singleton
                  (FSFormulaToken.logical .equality)
              have hRightParenthesis :=
                fs_formula_tokens_singleton
                  (FSFormulaToken.logical .rightParenthesis)
              simpa [Numbered.equality_tokens,
                List.append_assoc] using
                fs_formula_tokens_append hLeftParenthesis
                  (fs_formula_tokens_append hLeftTokens
                    (fs_formula_tokens_append hEquality
                      (fs_formula_tokens_append
                        hRightTokens hRightParenthesis)))
  | @neg body hBody ih =>
      cases hBodyQuote :
          Numbered.quote_hilbert_tokens_with?
            freeNaming binderNaming
            boundNames depth body with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hBodyQuote] at hQuote
      | some bodyTokens =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hBodyQuote] at hQuote
          subst tokens
          have hBodyTokens :=
            ih boundNames depth hBodyQuote
          have hPrefix :
              FSFormulaTokens
                [Numbered.logical_token .leftParenthesis,
                  Numbered.logical_token .negation] :=
            fs_formula_tokens_cons
              (.logical .leftParenthesis)
              (fs_formula_tokens_singleton
                (.logical .negation))
          have hSuffix :=
            fs_formula_tokens_singleton
              (FSFormulaToken.logical .rightParenthesis)
          simpa [Numbered.negation_tokens,
            List.append_assoc] using
            fs_formula_tokens_append hPrefix
              (fs_formula_tokens_append
                hBodyTokens hSuffix)
  | @conj left right hLeft hRight ihLeft ihRight =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | @disj left right hLeft hRight ihLeft ihRight =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | @imp left right hLeft hRight ihLeft ihRight =>
      cases hLeftQuote :
          Numbered.quote_hilbert_tokens_with?
            freeNaming binderNaming
            boundNames depth left with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hLeftQuote] at hQuote
      | some leftTokens =>
          cases hRightQuote :
              Numbered.quote_hilbert_tokens_with?
                freeNaming binderNaming
                boundNames depth right with
          | none =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeftQuote, hRightQuote] at hQuote
          | some rightTokens =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeftQuote, hRightQuote] at hQuote
              subst tokens
              have hLeftTokens :=
                ihLeft boundNames depth hLeftQuote
              have hRightTokens :=
                ihRight boundNames depth hRightQuote
              have hLeftParenthesis :=
                fs_formula_tokens_singleton
                  (FSFormulaToken.logical .leftParenthesis)
              have hImplication :=
                fs_formula_tokens_singleton
                  (FSFormulaToken.logical .implication)
              have hRightParenthesis :=
                fs_formula_tokens_singleton
                  (FSFormulaToken.logical .rightParenthesis)
              simpa [Numbered.implication_tokens,
                List.append_assoc] using
                fs_formula_tokens_append hLeftParenthesis
                  (fs_formula_tokens_append hLeftTokens
                    (fs_formula_tokens_append hImplication
                      (fs_formula_tokens_append
                        hRightTokens hRightParenthesis)))
  | @iff left right hLeft hRight ihLeft ihRight =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote
  | @forallE sort body hBody ih =>
      let name := binderNaming depth
      cases hBodyQuote :
          Numbered.quote_hilbert_tokens_with?
            freeNaming binderNaming
            (name :: boundNames) (depth + 1) body with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            name, hBodyQuote] at hQuote
      | some bodyTokens =>
          simp [Numbered.quote_hilbert_tokens_with?,
            name, hBodyQuote] at hQuote
          subst tokens
          have hBodyTokens :=
            ih (name :: boundNames) (depth + 1)
              hBodyQuote
          have hPrefix :
              FSFormulaTokens
                [Numbered.logical_token .leftParenthesis,
                  Numbered.logical_token .universal,
                  Numbered.variable_token name] :=
            fs_formula_tokens_cons
              (.logical .leftParenthesis)
              (fs_formula_tokens_cons
                (.logical .universal)
                (fs_formula_tokens_singleton
                  (.var name)))
          have hSuffix :=
            fs_formula_tokens_singleton
              (FSFormulaToken.logical .rightParenthesis)
          simpa [Numbered.universal_tokens,
            List.append_assoc] using
            fs_formula_tokens_append hPrefix
              (fs_formula_tokens_append
                hBodyTokens hSuffix)
  | @existsE sort body hBody ih =>
      simp [Numbered.quote_hilbert_tokens_with?] at hQuote

/-- 任意 admissible 公式的规范 quotation 都满足当前有限签名分类。 -/
theorem fs_quote_tokens_formula_tokens
    {formula : SetFormula} {tokens : List Nat}
    (hFormula : Formula.Admissible formula)
    (hQuote :
      Numbered.quote_tokens? formula =
        some tokens) :
    FSFormulaTokens tokens := by
  unfold Numbered.quote_tokens?
    Numbered.quote_tokens_with? at hQuote
  exact fs_quote_hilbert_tokens_formula_tokens
    free_name bound_name [] 0
    (Numbered.hilbertize_well_formed
      SetSort.set hFormula.1)
    hQuote

/-! ## 有限集合字面量的成员刻画 -/

/-- 二元并项的成员关系在 quotation 理论中可消去为左右成员析取。 -/
theorem gq_binary_union_member_iff
    (left right member : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hMember : Term.Admissible member SetSort.set) :
    Derives godel_quotation_theory [] (
      (member ∈ₘ (left ∪ₘ right)) ↔ₘ
        ((member ∈ₘ left) ∨ₘ (member ∈ₘ right))) := by
  have hSpec :
      Derives godel_quotation_theory [] (
        binary_union_spec left right (left ∪ₘ right)) :=
    gq_weaken_relation_plane <|
      FirstOrder.Derives.theory_weaken
        (fun _ hFormula =>
          binary_union_operator_theory_subset_relation_plane_theory
            hFormula)
        (binary_union_term_spec_derives
          left right hLeft hRight)
  have hLeftOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement left hLeft.2
  have hRightOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement right hRight.2
  have hMemberOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement member = member :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement member hMember.2
  simpa [binary_union_spec,
    Formula.openAt, Term.openAt,
    hLeftOpen, hRightOpen, hMemberOpen] using
    (FirstOrder.Derives.forall_elim
      (term := member) hSpec)

/-- 宿主列表成员可回放为对象有限集合字面量的成员。 -/
theorem gq_finite_set_literal_mem_of_mem
    (elements : List SetTerm) (element : SetTerm)
    (hElements :
      ∀ member, member ∈ elements →
        Term.Admissible member SetSort.set)
    (hElement : element ∈ elements) :
    Derives godel_quotation_theory [] (
      element ∈ₘ finite_set_literal_term elements) := by
  induction elements with
  | nil =>
      simp at hElement
  | cons head tail ih =>
      have hHead :
          Term.Admissible head SetSort.set :=
        hElements head (by simp)
      have hTail :
          ∀ member, member ∈ tail →
            Term.Admissible member SetSort.set := by
        intro member hMember
        exact hElements member (by simp [hMember])
      have hTailSet :
          Term.Admissible
            (finite_set_literal_term tail) SetSort.set :=
        finite_set_literal_term_admissible tail hTail
      rcases List.mem_cons.mp hElement with
        hElement | hElement
      · have hSingletonSpec :
            Derives godel_quotation_theory [] (
              singleton_spec head {head}ₘ) :=
          gq_weaken_singleton
            (singleton_term_spec_derives head hHead)
        have hSingletonMember :
            Derives godel_quotation_theory [] (
              head ∈ₘ {head}ₘ) :=
          FirstOrder.Derives.iffElimLeft
            (singleton_spec_membership_iff
              head {head}ₘ head
              hHead
              (singleton_term_admissible head hHead)
              hHead hSingletonSpec)
            (FirstOrder.Derives.eq_refl_m head)
        have hResult := gq_mem_binary_union_left
          {head}ₘ (finite_set_literal_term tail) head
          (singleton_term_admissible head hHead)
          hTailSet hHead hSingletonMember
        simpa [hElement] using hResult
      · exact gq_mem_binary_union_right
          {head}ₘ (finite_set_literal_term tail) element
          (singleton_term_admissible head hHead)
          hTailSet
          (hTail element hElement)
          (ih hTail hElement)

/--
若一个 admissible 项与宿主列表中的每个项都对象层互异，则它不属于对应的
有限集合字面量。该接口把后续有限签名拒绝压缩为有限个闭项不等式。
-/
theorem gq_finite_set_literal_not_mem_of_forall_ne
    (elements : List SetTerm) (element : SetTerm)
    (hElements :
      ∀ member, member ∈ elements →
        Term.Admissible member SetSort.set)
    (hElement : Term.Admissible element SetSort.set)
    (hNe :
      ∀ member, member ∈ elements →
        Derives godel_quotation_theory [] (
          ¬ₘ (element ≐ₘ member))) :
    Derives godel_quotation_theory [] (
      ¬ₘ (element ∈ₘ finite_set_literal_term elements)) := by
  induction elements with
  | nil =>
      simpa [finite_set_literal_term] using
        (gq_weaken_standard_sequence
          (stdseq_empty element hElement))
  | cons head tail ih =>
      have hHead :
          Term.Admissible head SetSort.set :=
        hElements head (by simp)
      have hTail :
          ∀ member, member ∈ tail →
            Term.Admissible member SetSort.set := by
        intro member hMember
        exact hElements member (by simp [hMember])
      have hTailSet :
          Term.Admissible
            (finite_set_literal_term tail) SetSort.set :=
        finite_set_literal_term_admissible tail hTail
      have hHeadNe :
          Derives godel_quotation_theory [] (
            ¬ₘ (element ≐ₘ head)) :=
        hNe head (by simp)
      have hTailNe :
          ∀ member, member ∈ tail →
            Derives godel_quotation_theory [] (
              ¬ₘ (element ≐ₘ member)) := by
        intro member hMember
        exact hNe member (by simp [hMember])
      have hTailNot :
          Derives godel_quotation_theory [] (
            ¬ₘ (element ∈ₘ
              finite_set_literal_term tail)) :=
        ih hTail hTailNe
      nd_apply FirstOrder.Derives.negIntro
      have hMembership :
          [element ∈ₘ
            ({head}ₘ ∪ₘ finite_set_literal_term tail)]
              ⊢ₘ[godel_quotation_theory]
            element ∈ₘ
              ({head}ₘ ∪ₘ finite_set_literal_term tail) := by
        exact FirstOrder.Derives.assumption (by simp)
      have hCases :
          [element ∈ₘ
            ({head}ₘ ∪ₘ finite_set_literal_term tail)]
              ⊢ₘ[godel_quotation_theory]
            (element ∈ₘ {head}ₘ) ∨ₘ
              (element ∈ₘ finite_set_literal_term tail) :=
        FirstOrder.Derives.iffElimRight
          (FirstOrder.Derives.context_weaken_cons
            (gq_binary_union_member_iff
              {head}ₘ
              (finite_set_literal_term tail)
              element
              (singleton_term_admissible head hHead)
              hTailSet hElement))
          hMembership
      apply FirstOrder.Derives.disjElim hCases
      · have hSingletonSpec :
            (element ∈ₘ {head}ₘ) ::
              [element ∈ₘ
                ({head}ₘ ∪ₘ finite_set_literal_term tail)]
              ⊢ₘ[godel_quotation_theory]
                singleton_spec head {head}ₘ :=
          FirstOrder.Derives.context_weaken
            (Γ := [])
            (Δ :=
              (element ∈ₘ {head}ₘ) ::
                [element ∈ₘ
                  ({head}ₘ ∪ₘ finite_set_literal_term tail)])
            (by simp)
            (gq_weaken_singleton
              (singleton_term_spec_derives head hHead))
        have hEquality :
            (element ∈ₘ {head}ₘ) ::
              [element ∈ₘ
                ({head}ₘ ∪ₘ finite_set_literal_term tail)]
              ⊢ₘ[godel_quotation_theory]
                element ≐ₘ head :=
          FirstOrder.Derives.iffElimRight
            (singleton_spec_membership_iff
              head {head}ₘ element
              hHead
              (singleton_term_admissible head hHead)
              hElement hSingletonSpec)
            (FirstOrder.Derives.assumption
              (by simp))
        exact FirstOrder.Derives.negElim
          hEquality
          (FirstOrder.Derives.context_weaken
            (Γ := [])
            (Δ :=
              (element ∈ₘ {head}ₘ) ::
                [element ∈ₘ
                  ({head}ₘ ∪ₘ finite_set_literal_term tail)])
            (by simp) hHeadNe)
      · exact FirstOrder.Derives.negElim
          (FirstOrder.Derives.assumption
            (by simp))
          (FirstOrder.Derives.context_weaken
            (Γ := [])
            (Δ :=
              (element ∈ₘ finite_set_literal_term tail) ::
                [element ∈ₘ
                  ({head}ₘ ∪ₘ finite_set_literal_term tail)])
            (by simp) hTailNot)

/-! ## 有限 numeral 的上下文消去 -/

/-- 在 quotation 理论的任意局部上下文中消去一个有限 numeral 成员见证。 -/
theorem gq_finite_numeral_member_elim_context
    {Γ : Context signature}
    (bound : Nat)
    (point : SetTerm)
    (conclusion : SetFormula)
    (hPoint : Term.Admissible point SetSort.set)
    (hConclusion : Formula.Admissible conclusion)
    (hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        point ∈ₘ numₘ(bound))
    (hBranch :
      ∀ index, index < bound →
        (point ≐ₘ numₘ(index)) :: Γ
          ⊢ₘ[godel_quotation_theory] conclusion) :
    Γ ⊢ₘ[godel_quotation_theory] conclusion := by
  have hIff :
      Γ ⊢ₘ[godel_quotation_theory]
        (point ∈ₘ numₘ(bound)) ↔ₘ
          stdseq_numeral_member_condition
            bound point :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
      gq_weaken_standard_sequence
        (stdseq_numeral_member_iff
          bound point hPoint)
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        stdseq_numeral_member_condition
          bound point :=
    FirstOrder.Derives.iffElimRight
      hIff hMember
  have hCases :
      stdseq_numeral_member_condition bound point :: Γ
        ⊢ₘ[godel_quotation_theory] conclusion :=
    stdseq_numeral_member_condition_elim_context
      bound point conclusion hBranch
      (hPointCheck :=
        Term.check_admissible_complete hPoint)
      (hConclusionCheck :=
        Formula.check_admissible_complete hConclusion)
  exact FirstOrder.Derives.cut hCondition hCases

/-! ## 公共符号集合成员 -/

/-- 逻辑符号编码理论的证明可提升到完整 quotation 理论。 -/
theorem gq_weaken_logical_symbol
    {formula : SetFormula}
    (hDerives :
      Derives logical_symbol_encoding_theory [] formula) :
    Derives godel_quotation_theory [] formula := by
  apply gq_weaken_symbol_operator
  exact FirstOrder.Derives.theory_weaken
    (fun _ hFormula =>
      formal_language_encoding_theory_subset_symbol_code_operator_theory <|
        term_sequence_encoding_theory_subset_formal_language_encoding_theory <|
          term_code_predicate_theory_subset_term_sequence_encoding_theory <|
            term_code_set_theory_subset_term_code_predicate_theory <|
              formal_language_symbol_theory_subset_term_code_set_theory <|
                function_symbol_encoding_theory_subset_formal_language_symbol_theory <|
                  constant_symbol_encoding_theory_subset_function_symbol_encoding_theory <|
                    variable_symbol_encoding_theory_subset_constant_symbol_encoding_theory <|
                      membership_symbol_encoding_theory_subset_variable_symbol_encoding_theory <|
                        logical_symbol_encoding_theory_subset_membership_symbol_encoding_theory
                          hFormula)
    hDerives

/-- 隶属符号编码理论的证明可提升到完整 quotation 理论。 -/
theorem gq_weaken_membership_symbol
    {formula : SetFormula}
    (hDerives :
      Derives membership_symbol_encoding_theory [] formula) :
    Derives godel_quotation_theory [] formula := by
  apply gq_weaken_symbol_operator
  exact FirstOrder.Derives.theory_weaken
    (fun _ hFormula =>
      formal_language_encoding_theory_subset_symbol_code_operator_theory <|
        term_sequence_encoding_theory_subset_formal_language_encoding_theory <|
          term_code_predicate_theory_subset_term_sequence_encoding_theory <|
            term_code_set_theory_subset_term_code_predicate_theory <|
              formal_language_symbol_theory_subset_term_code_set_theory <|
                function_symbol_encoding_theory_subset_formal_language_symbol_theory <|
                  constant_symbol_encoding_theory_subset_function_symbol_encoding_theory <|
                    variable_symbol_encoding_theory_subset_constant_symbol_encoding_theory <|
                      membership_symbol_encoding_theory_subset_variable_symbol_encoding_theory
                        hFormula)
    hDerives

theorem logical_symbol_code_mem_logical_symbols
    (symbol : LogicalSymbolKind) :
    Derives godel_quotation_theory [] (
      logical_symbol_code_term symbol ∈ₘ LogicSymₘ) := by
  have hLiteral :
      Derives godel_quotation_theory [] (
        logical_symbol_code_term symbol ∈ₘ
          finite_set_literal_term
            logical_symbol_code_terms) := by
    apply gq_finite_set_literal_mem_of_mem
      logical_symbol_code_terms
      (logical_symbol_code_term symbol)
    · intro member hMember
      rcases List.mem_map.mp hMember with
        ⟨kind, _, rfl⟩
      exact logical_symbol_code_term_admissible kind
    · apply List.mem_map.mpr
      refine ⟨symbol, ?_, rfl⟩
      cases symbol <;>
        simp [logical_symbol_kinds]
  have hDefinition :
      Derives godel_quotation_theory [] (
        LogicSymₘ ≐ₘ
          finite_set_literal_term
            logical_symbol_code_terms) := by
    apply gq_weaken_logical_symbol
    exact FirstOrder.Derives.theoryAxiom
      (Or.inl rfl)
  exact FirstOrder.Derives.iffElimLeft
    (membership_right_iff_of_equality
      (logical_symbol_code_term symbol)
      LogicSymₘ
      (finite_set_literal_term
        logical_symbol_code_terms)
      (logical_symbol_code_term_admissible symbol)
      logical_symbol_set_term_admissible
      (finite_set_literal_term_admissible
        logical_symbol_code_terms
        (by
          intro member hMember
          rcases List.mem_map.mp hMember with
            ⟨kind, _, rfl⟩
          exact logical_symbol_code_term_admissible kind))
      hDefinition)
    hLiteral

theorem membership_symbol_code_mem_membership_symbols :
    Derives godel_quotation_theory [] (
      membership_symbol_code_term ∈ₘ
        MembershipSymₘ) := by
  have hSingletonSpec :
      Derives godel_quotation_theory [] (
        singleton_spec
          membership_symbol_code_term
          {membership_symbol_code_term}ₘ) :=
    gq_weaken_singleton
      (singleton_term_spec_derives
        membership_symbol_code_term
        membership_symbol_code_term_admissible)
  have hSingletonMember :
      Derives godel_quotation_theory [] (
        membership_symbol_code_term ∈ₘ
          {membership_symbol_code_term}ₘ) :=
    FirstOrder.Derives.iffElimLeft
      (singleton_spec_membership_iff
        membership_symbol_code_term
        {membership_symbol_code_term}ₘ
        membership_symbol_code_term
        membership_symbol_code_term_admissible
        (singleton_term_admissible
          membership_symbol_code_term
          membership_symbol_code_term_admissible)
        membership_symbol_code_term_admissible
        hSingletonSpec)
      (FirstOrder.Derives.eq_refl_m
        membership_symbol_code_term)
  have hDefinition :
      Derives godel_quotation_theory [] (
        MembershipSymₘ ≐ₘ
          {membership_symbol_code_term}ₘ) := by
    apply gq_weaken_membership_symbol
    exact FirstOrder.Derives.theoryAxiom
      (Or.inl rfl)
  exact FirstOrder.Derives.iffElimLeft
    (membership_right_iff_of_equality
      membership_symbol_code_term
      MembershipSymₘ
      {membership_symbol_code_term}ₘ
      membership_symbol_code_term_admissible
      membership_symbol_set_term_admissible
      (singleton_term_admissible
        membership_symbol_code_term
        membership_symbol_code_term_admissible)
      hDefinition)
    hSingletonMember

/-! ## 标准 singleton token 的对象层分类 -/

theorem gq_standard_token_singleton_eq_symbol_code
    (token : Nat) :
    Derives godel_quotation_theory [] (
      standard_token_sequence [token] ≐ₘ
        sym_codeₘ(numₘ(token))) := by
  apply gq_weaken_standard_sequence
  simpa [standard_token_sequence] using
    standard_singleton_sequence_eq_symbol_code
      (numₘ(token))
      (finite_numeral_term_admissible token)

/--
不同 token 的标准 singleton 序列不等式可沿一个已知符号码值运输回当前
规范符号码。
-/
theorem gq_symbol_code_ne_of_token_ne
    (code : SetTerm) (token codeToken : Nat)
    (hCode : Term.Admissible code SetSort.set)
    (hCodeValue :
      Derives godel_quotation_theory [] (
        code ≐ₘ standard_token_sequence [codeToken]))
    (hNe : token ≠ codeToken) :
    Derives godel_quotation_theory [] (
      ¬ₘ (sym_codeₘ(numₘ(token)) ≐ₘ code)) := by
  have hCodeBack :
      Derives godel_quotation_theory [] (
        standard_token_sequence [codeToken] ≐ₘ code) :=
    Metatheory.Derives.equality_symm hCodeValue
  have hStandardNe :
      Derives godel_quotation_theory [] (
        ¬ₘ (standard_token_sequence [token] ≐ₘ
          standard_token_sequence [codeToken])) :=
    gq_weaken_standard_sequence <|
      standard_token_sequence_ne (by
        simpa using hNe)
  nd_apply FirstOrder.Derives.negIntro
  have hEquality :
      [sym_codeₘ(numₘ(token)) ≐ₘ code]
        ⊢ₘ[godel_quotation_theory]
          sym_codeₘ(numₘ(token)) ≐ₘ code :=
    FirstOrder.Derives.assumption (by simp)
  have hStandardEquality :
      [sym_codeₘ(numₘ(token)) ≐ₘ code]
        ⊢ₘ[godel_quotation_theory]
          standard_token_sequence [token] ≐ₘ
            standard_token_sequence [codeToken] :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_trans
        (FirstOrder.Derives.context_weaken_cons
          (gq_standard_token_singleton_eq_symbol_code token))
        hEquality)
      (FirstOrder.Derives.context_weaken_cons hCodeValue)
  exact FirstOrder.Derives.negElim
    hStandardEquality
    (FirstOrder.Derives.context_weaken_cons hStandardNe)

/-- 当前函数符号闭项等于其实际 arity 编码的标准 singleton token 序列。 -/
theorem gq_fs_function_symbol_code_eq_standard_token_sequence
    (symbol : FunctionSymbol) :
    Derives godel_quotation_theory [] (
      fs_function_symbol_code_term symbol ≐ₘ
        standard_token_sequence
          [fs_function_symbol_token symbol]) := by
  cases hDomain : signature.funcDomain symbol with
  | nil =>
      simpa [fs_function_symbol_code_term,
        fs_function_symbol_token, hDomain] using
        constant_symbol_code_eq_standard_token_sequence
          symbol.ctorIdx
  | cons head tail =>
      simpa [fs_function_symbol_code_term,
        fs_function_symbol_token, hDomain] using
        coded_function_symbol_code_eq_standard_token_sequence
          tail.length symbol.ctorIdx

/-- 变量符号闭项等于对应名字编码的标准 singleton token 序列。 -/
theorem gq_fs_variable_symbol_code_eq_standard_token_sequence
    (name : Nat) :
    Derives godel_quotation_theory [] (
      variable_symbol_code_term (numₘ(name)) ≐ₘ
        standard_token_sequence
          [Numbered.variable_token name]) := by
  simpa [variable_symbol_code_term,
    variable_symbol_number_term,
    indexed_prime_power_code_term,
    Numbered.variable_token,
    finite_numeral_term] using
    prime_power_symbol_code_eq_standard_token_sequence
      3 (name + 1)

/-- 变量符号码沿任意已证名字等式保持相等。 -/
theorem gq_variable_symbol_code_term_congr_of_equality
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        left ≐ₘ right) :
    Γ ⊢ₘ[godel_quotation_theory]
      variable_symbol_code_term left ≐ₘ
        variable_symbol_code_term right := by
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [left ≐ₘ right]
  let context :=
    variable_symbol_code_term (x#parameter)
  have hContext :
      Term.CheckCertificate context SetSort.set := by
    prove_term_check
  have hRaw :=
    gq_term_context_congr_of_equality
      parameter left right context
      (Term.check_admissible_complete hLeft)
      (Term.check_admissible_complete hRight)
      hContext
      (by
        have hFormulaFresh :
            (SetSort.set, parameter) ∉
              Formula.freeSupport (left ≐ₘ right) := by
          dsimp [parameter]
          exact FreshVariable.fresh_id_not_mem_m
            (sort := SetSort.set)
            (formulas := [left ≐ₘ right])
            (formula := left ≐ₘ right)
            (by simp)
        intro hMember
        apply hFormulaFresh
        exact List.mem_append_left
          (Term.freeSupport right)
          hMember)
      hEquality
  have hZeroFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement
          (numₘ(0)) =
        numₘ(0) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    simp
  have hThreeFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement
          (numₘ(3)) =
        numₘ(3) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    simp
  simpa [context, variable_symbol_code_term,
    variable_symbol_number_term,
    indexed_prime_power_code_term,
    prime_power_code_term,
    Formula.substituteFree, Term.substituteFree,
    set_variable, hZeroFixed, hThreeFixed] using hRaw

/--
宿主有界变量解码失败时，对象层有界变量 token 条件为假。
证明只枚举 `0, ..., token`，每支以标准 singleton 序列互异性结束。
-/
theorem gq_fs_variable_token_condition_not
    (token : Nat)
    (hDecode :
      fs_variable_name_decode token = none) :
    Derives godel_quotation_theory [] (
      ¬ₘ fs_variable_token_condition
        (numₘ(token))) := by
  let condition : SetFormula :=
    fs_variable_token_condition (numₘ(token))
  let Γ : Context signature := [condition]
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete
        (fs_variable_token_condition_admissible
          (numₘ(token))
          (finite_numeral_term_admissible token)))
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete <| by
        simpa [condition] using
          fs_variable_token_condition_admissible
            (numₘ(token))
            (finite_numeral_term_admissible token))
  let witness : SetTerm := x#700
  let witnessCondition : SetFormula :=
    (witness ∈ₘ Sₘ(numₘ(token))) ∧ₘ
      (sym_codeₘ(numₘ(token)) ≐ₘ
        variable_symbol_code_term witness)
  have hWitnessConditionAdmissible :
      Formula.Admissible witnessCondition := by
    dsimp [witnessCondition, witness]
    exact Formula.Admissible.conj
      (membership_formula_admissible
        (set_variable_admissible 700)
        (successor_term_admissible
          (numₘ(token))
          (finite_numeral_term_admissible token)))
      (Formula.Admissible.equal
        (singleton_symbol_code_term_admissible
          (numₘ(token))
          (finite_numeral_term_admissible token))
        (variable_symbol_code_term_admissible
          (x#700)
          (set_variable_admissible 700)))
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 700], witnessCondition := by
    have hTokenClose :
        Term.closeFreeAt SetSort.set 700 0
            (numₘ(token)) =
          numₘ(token) :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 700 0 (numₘ(token))
        (finite_numeral_term_admissible token).2 (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
    have hZeroClose :
        Term.closeFreeAt SetSort.set 700 0
            (numₘ(0)) =
          numₘ(0) :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 700 0 (numₘ(0))
        (finite_numeral_term_admissible 0).2 (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
    have hThreeClose :
        Term.closeFreeAt SetSort.set 700 0
            (numₘ(3)) =
          numₘ(3) :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 700 0 (numₘ(3))
        (finite_numeral_term_admissible 3).2 (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
    simpa [condition, fs_variable_token_condition,
      witnessCondition, witness,
      Formula.closeFreeAt, Term.closeFreeAt,
      set_variable, set_bound_variable,
      hTokenClose, hZeroClose, hThreeClose] using
      hCondition
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 700)
    (body := witnessCondition)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete
        hWitnessConditionAdmissible)
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simp [condition, fs_variable_token_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport]
  · simp [Formula.freeSupport]
  · exact hExists
  · let Δ : Context signature :=
      witnessCondition :: Γ
    have hWitness :
        Term.Admissible witness SetSort.set := by
      simpa [witness] using
        set_variable_admissible 700
    have hWitnessCondition :
        Δ ⊢ₘ[godel_quotation_theory]
          witnessCondition :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hWitnessMember :
        Δ ⊢ₘ[godel_quotation_theory]
          witness ∈ₘ numₘ(token + 1) := by
      simpa [witnessCondition,
        finite_numeral_term] using
        FirstOrder.Derives.conjElimLeft
          hWitnessCondition
    have hSymbolEquality :
        Δ ⊢ₘ[godel_quotation_theory]
          sym_codeₘ(numₘ(token)) ≐ₘ
            variable_symbol_code_term witness := by
      simpa [witnessCondition] using
        FirstOrder.Derives.conjElimRight
          hWitnessCondition
    apply gq_finite_numeral_member_elim_context
      (Γ := Δ)
      (token + 1) witness Formula.falsum
      hWitness Formula.Admissible.falsum
      hWitnessMember
    intro index hIndex
    let Ξ : Context signature :=
      (witness ≐ₘ numₘ(index)) :: Δ
    have hWitnessEquality :
        Ξ ⊢ₘ[godel_quotation_theory]
          witness ≐ₘ numₘ(index) :=
      FirstOrder.Derives.assumption (by simp [Ξ])
    have hVariableCodeEquality :
        Ξ ⊢ₘ[godel_quotation_theory]
          variable_symbol_code_term witness ≐ₘ
            variable_symbol_code_term
              (numₘ(index)) :=
      gq_variable_symbol_code_term_congr_of_equality
        witness (numₘ(index))
        hWitness
        (finite_numeral_term_admissible index)
        hWitnessEquality
    have hConcreteEquality :
        Ξ ⊢ₘ[godel_quotation_theory]
          sym_codeₘ(numₘ(token)) ≐ₘ
            variable_symbol_code_term
              (numₘ(index)) :=
      Metatheory.Derives.equality_trans
        (FirstOrder.Derives.context_weaken
          (Γ := Δ) (Δ := Ξ)
          (by
            intro formula hFormula
            simpa [Ξ] using
              List.mem_cons_of_mem
                (witness ≐ₘ numₘ(index))
                hFormula)
          hSymbolEquality)
        hVariableCodeEquality
    have hTokenNe :
        token ≠ Numbered.variable_token index := by
      intro hEquality
      have hSome :
          fs_variable_name_decode token =
            some index := by
        rw [hEquality]
        exact fs_variable_name_decode_encode index
      rw [hDecode] at hSome
      cases hSome
    exact FirstOrder.Derives.negElim
      hConcreteEquality
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Ξ)
        (by simp)
        (gq_symbol_code_ne_of_token_ne
          (variable_symbol_code_term
            (numₘ(index)))
          token (Numbered.variable_token index)
          (variable_symbol_code_term_admissible
            (numₘ(index))
            (finite_numeral_term_admissible index))
          (gq_fs_variable_symbol_code_eq_standard_token_sequence
            index)
          hTokenNe))

/-- 当前一般谓词闭项等于其实际 arity 编码的标准 singleton token 序列。 -/
theorem gq_fs_predicate_symbol_code_eq_standard_token_sequence
    (symbol : RelationSymbol) :
    Derives godel_quotation_theory [] (
      fs_predicate_symbol_code_term symbol ≐ₘ
        standard_token_sequence
          [fs_predicate_symbol_token symbol]) := by
  simpa [fs_predicate_symbol_code_term,
    fs_predicate_symbol_token] using
    coded_predicate_symbol_code_eq_standard_token_sequence
      (signature.relDomain symbol).length.pred
      symbol.ctorIdx

private theorem gq_symbol_member_of_standard_equality
    (source space : SetTerm) (token : Nat)
    (hSource : Term.Admissible source SetSort.set)
    (hSpace : Term.Admissible space SetSort.set)
    (hEquality :
      Derives godel_quotation_theory [] (
        source ≐ₘ standard_token_sequence [token]))
    (hMember :
      Derives godel_quotation_theory [] (
        source ∈ₘ space)) :
    Derives godel_quotation_theory [] (
      sym_codeₘ(numₘ(token)) ∈ₘ space) := by
  have hToSymbol :
      Derives godel_quotation_theory [] (
        source ≐ₘ sym_codeₘ(numₘ(token))) :=
    Metatheory.Derives.equality_trans hEquality
      (gq_standard_token_singleton_eq_symbol_code token)
  exact FirstOrder.Derives.iffElimRight
    (membership_left_iff_of_equality
      source (sym_codeₘ(numₘ(token))) space
      hSource
      (singleton_symbol_code_term_admissible
        (numₘ(token))
        (finite_numeral_term_admissible token))
      hSpace hToSymbol)
    hMember

theorem gq_fs_nonlogical_symbol_code_mem
    (code : SetTerm)
    (hCode : code ∈
      fs_nonlogical_symbol_code_terms) :
    Derives godel_quotation_theory [] (
      code ∈ₘ fs_nonlogical_symbol_code_set_term) := by
  exact gq_finite_set_literal_mem_of_mem
    fs_nonlogical_symbol_code_terms code
    fs_nonlogical_symbol_code_terms_admissible
    hCode

/--
不在当前有限非逻辑 token 表中的自然数，其规范 singleton 符号码不属于对象层
非逻辑符号有限集。
-/
theorem gq_fs_nonlogical_symbol_code_not_mem
    (token : Nat)
    (hToken : token ∉ fs_nonlogical_symbol_tokens) :
    Derives godel_quotation_theory [] (
      ¬ₘ (sym_codeₘ(numₘ(token)) ∈ₘ
        fs_nonlogical_symbol_code_set_term)) := by
  apply gq_finite_set_literal_not_mem_of_forall_ne
    fs_nonlogical_symbol_code_terms
    (sym_codeₘ(numₘ(token)))
    fs_nonlogical_symbol_code_terms_admissible
    (singleton_symbol_code_term_admissible
      (numₘ(token))
      (finite_numeral_term_admissible token))
  intro code hCode
  rcases List.mem_append.mp hCode with
    hFunction | hPredicate
  · rcases List.mem_map.mp hFunction with
      ⟨symbol, hSymbol, rfl⟩
    have hNe :
        token ≠ fs_function_symbol_token symbol := by
      intro hEquality
      apply hToken
      rw [hEquality]
      apply List.mem_append.mpr
      exact Or.inl <|
        List.mem_map.mpr
          ⟨symbol, hSymbol, rfl⟩
    exact gq_symbol_code_ne_of_token_ne
      (fs_function_symbol_code_term symbol)
      token (fs_function_symbol_token symbol)
      (fs_function_symbol_code_term_admissible symbol)
      (gq_fs_function_symbol_code_eq_standard_token_sequence
        symbol)
      hNe
  · rcases List.mem_map.mp hPredicate with
      ⟨symbol, hSymbol, rfl⟩
    have hNe :
        token ≠ fs_predicate_symbol_token symbol := by
      intro hEquality
      apply hToken
      rw [hEquality]
      apply List.mem_append.mpr
      exact Or.inr <|
        List.mem_map.mpr
          ⟨symbol, hSymbol, rfl⟩
    exact gq_symbol_code_ne_of_token_ne
      (fs_predicate_symbol_code_term symbol)
      token (fs_predicate_symbol_token symbol)
      (fs_predicate_symbol_code_term_admissible symbol)
      (gq_fs_predicate_symbol_code_eq_standard_token_sequence
        symbol)
      hNe

theorem gq_fs_formula_token_condition
    {token : Nat} (hToken : FSFormulaToken token) :
    Derives godel_quotation_theory [] (
      fs_formula_token_condition (numₘ(token))) := by
  have hCode :
      Term.Admissible
        (sym_codeₘ(numₘ(token))) SetSort.set :=
    singleton_symbol_code_term_admissible
      (numₘ(token))
      (finite_numeral_term_admissible token)
  have hLogicalCheck :
      Formula.CheckCertificate
        (sym_codeₘ(numₘ(token)) ∈ₘ LogicSymₘ) :=
    Formula.check_admissible_complete
      (membership_formula_admissible
        hCode logical_symbol_set_term_admissible)
  have hMembershipCheck :
      Formula.CheckCertificate
        (sym_codeₘ(numₘ(token)) ∈ₘ MembershipSymₘ) :=
    Formula.check_admissible_complete
      (membership_formula_admissible
        hCode membership_symbol_set_term_admissible)
  have hVariableCheck :
      Formula.CheckCertificate
        (fs_variable_token_condition
          (numₘ(token))) :=
    Formula.check_admissible_complete
      (fs_variable_token_condition_admissible
        (numₘ(token))
        (finite_numeral_term_admissible token))
  have hNonlogicalCheck :
      Formula.CheckCertificate
        (sym_codeₘ(numₘ(token)) ∈ₘ
          fs_nonlogical_symbol_code_set_term) :=
    Formula.check_admissible_complete
      (membership_formula_admissible
        hCode
        fs_nonlogical_symbol_code_set_term_admissible)
  have hLeftCheck :
      Formula.CheckCertificate
        ((sym_codeₘ(numₘ(token)) ∈ₘ LogicSymₘ) ∨ₘ
          (sym_codeₘ(numₘ(token)) ∈ₘ MembershipSymₘ)) :=
    Formula.check_admissible_complete
      (Formula.Admissible.disj
        hLogicalCheck.admissible
        hMembershipCheck.admissible)
  have hRightCheck :
      Formula.CheckCertificate
        (fs_variable_token_condition
            (numₘ(token)) ∨ₘ
          (sym_codeₘ(numₘ(token)) ∈ₘ
            fs_nonlogical_symbol_code_set_term)) :=
    Formula.check_admissible_complete
      (Formula.Admissible.disj
        hVariableCheck.admissible
        hNonlogicalCheck.admissible)
  cases hToken with
  | logical symbol =>
      have hMember :=
        gq_symbol_member_of_standard_equality
          (logical_symbol_code_term symbol)
          LogicSymₘ
          (Numbered.logical_token symbol)
          (logical_symbol_code_term_admissible symbol)
          logical_symbol_set_term_admissible
          (logical_symbol_code_eq_standard_token_sequence
            symbol)
          (logical_symbol_code_mem_logical_symbols symbol)
      exact FirstOrder.Derives.disjIntroLeft
        (FirstOrder.Derives.disjIntroLeft
          hMember hMembershipCheck)
        hRightCheck
  | membership =>
      have hMember :=
        gq_symbol_member_of_standard_equality
          membership_symbol_code_term
          MembershipSymₘ
          Numbered.membership_token
          membership_symbol_code_term_admissible
          membership_symbol_set_term_admissible
          membership_symbol_code_eq_standard_token_sequence
          membership_symbol_code_mem_membership_symbols
      exact FirstOrder.Derives.disjIntroLeft
        (FirstOrder.Derives.disjIntroRight
          hMember hLogicalCheck)
        hRightCheck
  | var name =>
      have hNameMember :
          Derives godel_quotation_theory [] (
            numₘ(name) ∈ₘ
              Sₘ(numₘ(Numbered.variable_token name))) :=
        gq_weaken_standard_sequence <| by
          simpa [finite_numeral_term] using
            standard_sequence_finite_numeral_mem_of_lt
              name
              (Numbered.variable_token name + 1)
              (fs_name_lt_variable_token_succ name)
      have hCodeEquality :
          Derives godel_quotation_theory [] (
            sym_codeₘ(numₘ(Numbered.variable_token name)) ≐ₘ
              variable_symbol_code_term
                (numₘ(name))) :=
        Metatheory.Derives.equality_trans
          (Metatheory.Derives.equality_symm
            (gq_standard_token_singleton_eq_symbol_code
              (Numbered.variable_token name)))
          (Metatheory.Derives.equality_symm
            (gq_fs_variable_symbol_code_eq_standard_token_sequence
              name))
      have hMember :
          Derives godel_quotation_theory [] (
            fs_variable_token_condition
              (numₘ(Numbered.variable_token name))) := by
        have hTokenOpen :
            Term.openAt SetSort.set 0 (numₘ(name))
                (numₘ(Numbered.variable_token name)) =
              numₘ(Numbered.variable_token name) :=
          Term.openAt_eq_self_of_boundClosed
            SetSort.set 0 (numₘ(name))
            (numₘ(Numbered.variable_token name))
            (finite_numeral_term_admissible
              (Numbered.variable_token name)).2
        have hZeroOpen :
            Term.openAt SetSort.set 0 (numₘ(name))
                (numₘ(0)) =
              numₘ(0) :=
          Term.openAt_eq_self_of_boundClosed
            SetSort.set 0 (numₘ(name)) (numₘ(0))
            (finite_numeral_term_admissible 0).2
        have hThreeOpen :
            Term.openAt SetSort.set 0 (numₘ(name))
                (numₘ(3)) =
              numₘ(3) :=
          Term.openAt_eq_self_of_boundClosed
            SetSort.set 0 (numₘ(name)) (numₘ(3))
            (finite_numeral_term_admissible 3).2
        unfold fs_variable_token_condition
        nd_apply FirstOrder.Derives.exists_intro
          (term := numₘ(name))
        simpa [Formula.openAt, Term.openAt,
          hTokenOpen, hZeroOpen, hThreeOpen] using
          FirstOrder.Derives.conjIntro
            hNameMember hCodeEquality
      exact FirstOrder.Derives.disjIntroRight
        (FirstOrder.Derives.disjIntroLeft
          hMember hNonlogicalCheck)
        hLeftCheck
  | func symbol =>
      have hCodeMember :
          fs_function_symbol_code_term symbol ∈
            fs_nonlogical_symbol_code_terms := by
        apply List.mem_append_left
        apply List.mem_map.mpr
        exact ⟨symbol,
          fs_function_symbols_complete symbol, rfl⟩
      have hMember :=
        gq_fs_nonlogical_symbol_code_mem
          (fs_function_symbol_code_term symbol)
          hCodeMember
      have hTransported :=
        gq_symbol_member_of_standard_equality
          (fs_function_symbol_code_term symbol)
          fs_nonlogical_symbol_code_set_term
          (fs_function_symbol_token symbol)
          (fs_function_symbol_code_term_admissible symbol)
          fs_nonlogical_symbol_code_set_term_admissible
          (gq_fs_function_symbol_code_eq_standard_token_sequence
            symbol)
          hMember
      exact FirstOrder.Derives.disjIntroRight
        (FirstOrder.Derives.disjIntroRight
          hTransported hVariableCheck)
        hLeftCheck
  | pred symbol hSymbol =>
      have hPredicate :
          symbol ∈ fs_predicate_symbols := by
        simp [fs_predicate_symbols,
          fs_relation_symbols_complete symbol,
          hSymbol]
      have hCodeMember :
          fs_predicate_symbol_code_term symbol ∈
            fs_nonlogical_symbol_code_terms := by
        apply List.mem_append_right
        apply List.mem_map.mpr
        exact ⟨symbol, hPredicate, rfl⟩
      have hMember :=
        gq_fs_nonlogical_symbol_code_mem
          (fs_predicate_symbol_code_term symbol)
          hCodeMember
      have hTransported :=
        gq_symbol_member_of_standard_equality
          (fs_predicate_symbol_code_term symbol)
          fs_nonlogical_symbol_code_set_term
          (fs_predicate_symbol_token symbol)
          (fs_predicate_symbol_code_term_admissible symbol)
          fs_nonlogical_symbol_code_set_term_admissible
          (gq_fs_predicate_symbol_code_eq_standard_token_sequence
            symbol)
          hMember
      exact FirstOrder.Derives.disjIntroRight
        (FirstOrder.Derives.disjIntroRight
          hTransported hVariableCheck)
        hLeftCheck

/-- `fs_formula_token_condition` 沿任意已证对象项等式双向运输。 -/
theorem fs_formula_token_condition_iff_of_equality
    {T : SetTheory} {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEquality : Derives T Γ (left ≐ₘ right)) :
    Derives T Γ (
      fs_formula_token_condition left ↔ₘ
        fs_formula_token_condition right) := by
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [left ≐ₘ right]
  let body : SetFormula :=
    fs_formula_token_condition (x#parameter)
  have hBody :
      Formula.Admissible body :=
    fs_formula_token_condition_admissible
      (x#parameter)
      (set_variable_admissible parameter)
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ)
      (sort := SetSort.set)
      (eigen := parameter)
      (left := left) (right := right)
      (body := body)
      hEquality
  have hZeroFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement
          (numₘ(0)) =
        numₘ(0) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    simp
  have hThreeFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement
          (numₘ(3)) =
        numₘ(3) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    simp
  have hSignatureFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement
          fs_nonlogical_symbol_code_set_term =
        fs_nonlogical_symbol_code_set_term := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [fs_nonlogical_symbol_code_set_term_freeSupport]
    simp
  simpa [body, fs_formula_token_condition,
    fs_formula_token_condition_lifted,
    fs_variable_token_condition,
    Formula.substituteFree, Term.substituteFree,
    set_variable, hZeroFixed, hThreeFixed,
    hSignatureFixed] using hCongruence

/--
同一显式 token binder 下，有限签名全称条件沿代码等式运输。

`tokenIndexId` 必须对两端代码新鲜；这正是自动接口选择 binder 时保证的条件。
-/
theorem fs_formula_signature_condition_with_id_iff_of_equality
    {T : SetTheory} {Γ : Context signature}
    (left right : SetTerm)
    (tokenIndexId : FreeVarId)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hLeftFresh :
      (SetSort.set, tokenIndexId) ∉
        Term.freeSupport left)
    (hRightFresh :
      (SetSort.set, tokenIndexId) ∉
        Term.freeSupport right)
    (hEquality : Derives T Γ (left ≐ₘ right)) :
    Derives T Γ (
      fs_formula_signature_condition_with_id
          left tokenIndexId ↔ₘ
        fs_formula_signature_condition_with_id
          right tokenIndexId) := by
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [left ≐ₘ right,
        x#tokenIndexId ≐ₘ x#tokenIndexId]
  let body : SetFormula :=
    fs_formula_signature_condition_with_id
      (x#parameter) tokenIndexId
  have hParameterFresh :
      (SetSort.set, parameter) ∉
        Formula.freeSupport
          (x#tokenIndexId ≐ₘ
            x#tokenIndexId) := by
    exact FreshVariable.fresh_id_not_mem_m
      (sort := SetSort.set)
      (formulas :=
        [left ≐ₘ right,
          x#tokenIndexId ≐ₘ x#tokenIndexId])
      (formula :=
        x#tokenIndexId ≐ₘ x#tokenIndexId)
      (by simp)
  have hParameterNe :
      parameter ≠ tokenIndexId := by
    intro hEqual
    rw [hEqual] at hParameterFresh
    apply hParameterFresh
    exact List.mem_cons_self
  have hBody :
      Formula.Admissible body :=
    fs_formula_signature_condition_with_id_admissible
      (x#parameter) tokenIndexId
      (set_variable_admissible parameter)
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ)
      (sort := SetSort.set)
      (eigen := parameter)
      (left := left) (right := right)
      (body := body)
      hEquality
  have hLeftClose (depth : Nat) :
      Term.closeFreeAt SetSort.set tokenIndexId
          depth left =
        left :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set tokenIndexId depth left
      hLeft.2 hLeftFresh
  have hRightClose (depth : Nat) :
      Term.closeFreeAt SetSort.set tokenIndexId
          depth right =
        right :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set tokenIndexId depth right
      hRight.2 hRightFresh
  have hZeroFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement
          (numₘ(0)) =
        numₘ(0) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    simp
  have hZeroClose (depth : Nat) :
      Term.closeFreeAt SetSort.set tokenIndexId depth
          (numₘ(0)) =
        numₘ(0) := by
    apply
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
    · exact (finite_numeral_term_admissible 0).2
    · rw [finite_numeral_term_freeSupport]
      simp
  have hThreeFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement
          (numₘ(3)) =
        numₘ(3) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    simp
  have hThreeClose (depth : Nat) :
      Term.closeFreeAt SetSort.set tokenIndexId depth
          (numₘ(3)) =
        numₘ(3) := by
    apply
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
    · exact (finite_numeral_term_admissible 3).2
    · rw [finite_numeral_term_freeSupport]
      simp
  have hSignatureFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement
          fs_nonlogical_symbol_code_set_term =
        fs_nonlogical_symbol_code_set_term := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [fs_nonlogical_symbol_code_set_term_freeSupport]
    simp
  have hSignatureClose (depth : Nat) :
      Term.closeFreeAt SetSort.set tokenIndexId depth
          fs_nonlogical_symbol_code_set_term =
        fs_nonlogical_symbol_code_set_term := by
    apply
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
    · exact
        fs_nonlogical_symbol_code_set_term_admissible.2
    · rw [fs_nonlogical_symbol_code_set_term_freeSupport]
      simp
  simpa [body,
    fs_formula_signature_condition_with_id,
    fs_formula_token_condition,
    fs_formula_token_condition_lifted,
    fs_variable_token_condition,
    Formula.substituteFree, Formula.closeFreeAt,
    Formula.next_depth,
    Term.substituteFree, Term.closeFreeAt,
    set_variable, set_bound_variable,
    hParameterNe, hLeftClose, hRightClose,
    hZeroFixed, hZeroClose,
    hThreeFixed, hThreeClose,
    hSignatureFixed, hSignatureClose] using
    hCongruence

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
