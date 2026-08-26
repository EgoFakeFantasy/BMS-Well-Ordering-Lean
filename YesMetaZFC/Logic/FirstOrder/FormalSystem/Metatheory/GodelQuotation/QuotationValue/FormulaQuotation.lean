import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.TermQuotation
/-!
# Gödel quotation 的公式 quotation 值
本模块证明 Hilbert 公式 quotation 的标准 token 值与对象公式编码证书。
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
/--
任意可编号单排序签名的显式 Hilbert quotation，其对象编码值等于同步 token
quotation 的标准序列。
-/
theorem quote_hilbert_with?_eq_standard_token_sequence
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] (freeNaming binderNaming : Nat → Nat)
    {boundNames : List Nat} {depth : Nat}
    {formula : Formula σ} {tokens : List Nat} {code : SetTerm} (hTokens :
      Numbered.quote_hilbert_tokens_with?
        freeNaming binderNaming boundNames depth formula =
          some tokens) (hCode :
      Numbered.quote_hilbert_with?
        freeNaming binderNaming boundNames depth formula =
          some code) :
    ⊢ₘ[godel_quotation_theory]
      code ≐ₘ standard_token_sequence tokens := by
  induction formula generalizing boundNames depth tokens code with
  | falsum =>
      simp [Numbered.quote_hilbert_tokens_with?] at hTokens
  | truth =>
      simp [Numbered.quote_hilbert_tokens_with?] at hTokens
  | rel relation arguments =>
      cases hKind : numbering.relation_kind relation with
      | membership =>
          cases arguments with
          | nil =>
              simp [Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?, hKind] at hTokens
          | cons left rest =>
              cases rest with
              | nil =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?, hKind] at hTokens
              | cons right tail =>
                  cases tail with
                  | cons extra tail =>
                      simp [Numbered.quote_hilbert_tokens_with?,
                        Numbered.quote_relation_tokens_with?,
                        hKind] at hTokens
                  | nil =>
                      cases hLeftTokens :
                          Numbered.quote_term_tokens_with?
                            freeNaming boundNames left with
                      | none =>
                          simp [Numbered.quote_hilbert_tokens_with?,
                            Numbered.quote_relation_tokens_with?,
                            hKind, hLeftTokens] at hTokens
                      | some leftTokens =>
                          cases hRightTokens :
                              Numbered.quote_term_tokens_with?
                                freeNaming boundNames right with
                          | none =>
                              simp [Numbered.quote_hilbert_tokens_with?,
                                Numbered.quote_relation_tokens_with?,
                                hKind, hLeftTokens,
                                hRightTokens] at hTokens
                          | some rightTokens =>
                              cases hLeftCode :
                                  Numbered.quote_term_with?
                                    freeNaming boundNames left with
                              | none =>
                                  simp [Numbered.quote_hilbert_with?,
                                    Numbered.quote_relation_with?,
                                    hKind, hLeftCode] at hCode
                              | some leftCode =>
                                  cases hRightCode :
                                      Numbered.quote_term_with?
                                        freeNaming boundNames right with
                                  | none =>
                                      simp [Numbered.quote_hilbert_with?,
                                        Numbered.quote_relation_with?,
                                        hKind, hLeftCode,
                                        hRightCode] at hCode
                                  | some rightCode =>
                                      simp [Numbered.quote_hilbert_tokens_with?,
                                        Numbered.quote_relation_tokens_with?,
                                        hKind, hLeftTokens,
                                        hRightTokens] at hTokens
                                      simp [Numbered.quote_hilbert_with?,
                                        Numbered.quote_relation_with?,
                                        hKind, hLeftCode,
                                        hRightCode] at hCode
                                      subst tokens
                                      subst code
                                      have hLeftCheck :
                                          Term.CheckCertificate leftCode SetSort.set :=
                                        (Numbered.quote_term_with?_code_boundary
                                          freeNaming boundNames hLeftCode).check_certificate
                                      have hRightCheck :
                                          Term.CheckCertificate rightCode SetSort.set :=
                                        (Numbered.quote_term_with?_code_boundary
                                          freeNaming boundNames hRightCode).check_certificate
                                      exact
                                        membership_formula_string_eq_standard_token_sequence
                                          leftTokens rightTokens
                                          leftCode rightCode
                                          (quote_term_with?_eq_standard_token_sequence
                                            freeNaming boundNames
                                            hLeftTokens hLeftCode) (quote_term_with?_eq_standard_token_sequence
                                            freeNaming boundNames
                                            hRightTokens hRightCode)
      | predicate =>
          cases arguments with
          | nil =>
              simp [Numbered.quote_hilbert_tokens_with?,
                Numbered.quote_relation_tokens_with?, hKind] at hTokens
          | cons head tail =>
              cases hArgumentTokens : (head :: tail).mapM (Numbered.quote_term_tokens_with?
                      freeNaming boundNames) with
              | none =>
                  simp [Numbered.quote_hilbert_tokens_with?,
                    Numbered.quote_relation_tokens_with?,
                    hKind, hArgumentTokens] at hTokens
              | some pieces =>
                  cases hArgumentCodes : (head :: tail).mapM (Numbered.quote_term_with?
                          freeNaming boundNames) with
                  | none =>
                      simp [Numbered.quote_hilbert_with?,
                        Numbered.quote_relation_with?,
                        Numbered.quote_terms_with?,
                        hKind, hArgumentCodes] at hCode
                  | some codes =>
                      simp [Numbered.quote_hilbert_tokens_with?,
                        Numbered.quote_relation_tokens_with?,
                        hKind, hArgumentTokens] at hTokens
                      simp [Numbered.quote_hilbert_with?,
                        Numbered.quote_relation_with?,
                        Numbered.quote_terms_with?,
                        hKind, hArgumentCodes] at hCode
                      subst tokens
                      subst code
                      rcases gq_quote_terms_with?_certificate
                          freeNaming boundNames hArgumentCodes with
                        ⟨certificatePieces, hCertificatePieces,
                          hCorrect, hLength⟩
                      rw [hArgumentTokens] at hCertificatePieces
                      simp at hCertificatePieces
                      subst certificatePieces
                      exact
                        gq_predicate_application_code_eq_standard_token_sequence ((head :: tail).length - 1) (numbering.relation_number relation)
                          hCorrect.1
  | equal left right =>
      cases hLeftTokens :
          Numbered.quote_term_tokens_with?
            freeNaming boundNames left with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hLeftTokens] at hTokens
      | some leftTokens =>
          cases hRightTokens :
              Numbered.quote_term_tokens_with?
                freeNaming boundNames right with
          | none =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeftTokens, hRightTokens] at hTokens
          | some rightTokens =>
              cases hLeftCode :
                  Numbered.quote_term_with?
                    freeNaming boundNames left with
              | none =>
                  simp [Numbered.quote_hilbert_with?,
                    hLeftCode] at hCode
              | some leftCode =>
                  cases hRightCode :
                      Numbered.quote_term_with?
                        freeNaming boundNames right with
                  | none =>
                      simp [Numbered.quote_hilbert_with?,
                        hLeftCode, hRightCode] at hCode
                  | some rightCode =>
                      simp [Numbered.quote_hilbert_tokens_with?,
                        hLeftTokens, hRightTokens] at hTokens
                      simp [Numbered.quote_hilbert_with?,
                        hLeftCode, hRightCode] at hCode
                      subst tokens
                      subst code
                      have hLeftCheck :
                          Term.CheckCertificate leftCode SetSort.set :=
                        (Numbered.quote_term_with?_code_boundary
                          freeNaming boundNames hLeftCode).check_certificate
                      have hRightCheck :
                          Term.CheckCertificate rightCode SetSort.set :=
                        (Numbered.quote_term_with?_code_boundary
                          freeNaming boundNames hRightCode).check_certificate
                      exact
                        equality_formula_code_eq_standard_token_sequence
                          leftTokens rightTokens leftCode rightCode
                          (Numbered.quote_term_with?_is_term_code
                            freeNaming boundNames hLeftCode) (Numbered.quote_term_with?_is_term_code
                            freeNaming boundNames hRightCode) (quote_term_with?_eq_standard_token_sequence
                            freeNaming boundNames hLeftTokens hLeftCode) (quote_term_with?_eq_standard_token_sequence
                            freeNaming boundNames hRightTokens hRightCode)
  | neg body ih =>
      cases hBodyTokens :
          Numbered.quote_hilbert_tokens_with?
            freeNaming binderNaming boundNames depth body with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hBodyTokens] at hTokens
      | some bodyTokens =>
          cases hBodyCode :
              Numbered.quote_hilbert_with?
                freeNaming binderNaming boundNames depth body with
          | none =>
              simp [Numbered.quote_hilbert_with?,
                hBodyCode] at hCode
          | some bodyCode =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hBodyTokens] at hTokens
              simp [Numbered.quote_hilbert_with?,
                hBodyCode] at hCode
              subst tokens
              subst code
              have hBodyCheck :
                  Term.CheckCertificate bodyCode SetSort.set :=
                (Numbered.quote_hilbert_with?_code_boundary
                  freeNaming binderNaming hBodyCode).check_certificate
              exact negation_formula_code_eq_standard_token_sequence
                bodyTokens bodyCode (ih hBodyTokens hBodyCode)
  | conj left right =>
      simp [Numbered.quote_hilbert_tokens_with?] at hTokens
  | disj left right =>
      simp [Numbered.quote_hilbert_tokens_with?] at hTokens
  | imp left right ihLeft ihRight =>
      cases hLeftTokens :
          Numbered.quote_hilbert_tokens_with?
            freeNaming binderNaming boundNames depth left with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            hLeftTokens] at hTokens
      | some leftTokens =>
          cases hRightTokens :
              Numbered.quote_hilbert_tokens_with?
                freeNaming binderNaming boundNames depth right with
          | none =>
              simp [Numbered.quote_hilbert_tokens_with?,
                hLeftTokens, hRightTokens] at hTokens
          | some rightTokens =>
              cases hLeftCode :
                  Numbered.quote_hilbert_with?
                    freeNaming binderNaming boundNames depth left with
              | none =>
                  simp [Numbered.quote_hilbert_with?,
                    hLeftCode] at hCode
              | some leftCode =>
                  cases hRightCode :
                      Numbered.quote_hilbert_with?
                        freeNaming binderNaming boundNames depth right with
                  | none =>
                      simp [Numbered.quote_hilbert_with?,
                        hLeftCode, hRightCode] at hCode
                  | some rightCode =>
                      simp [Numbered.quote_hilbert_tokens_with?,
                        hLeftTokens, hRightTokens] at hTokens
                      simp [Numbered.quote_hilbert_with?,
                        hLeftCode, hRightCode] at hCode
                      subst tokens
                      subst code
                      have hLeftCheck :
                          Term.CheckCertificate leftCode SetSort.set :=
                        (Numbered.quote_hilbert_with?_code_boundary
                          freeNaming binderNaming hLeftCode).check_certificate
                      have hRightCheck :
                          Term.CheckCertificate rightCode SetSort.set :=
                        (Numbered.quote_hilbert_with?_code_boundary
                          freeNaming binderNaming hRightCode).check_certificate
                      exact
                        implication_formula_code_eq_standard_token_sequence
                          leftTokens rightTokens leftCode rightCode
                          (ihLeft hLeftTokens hLeftCode)
                          (ihRight hRightTokens hRightCode)
  | iff left right =>
      simp [Numbered.quote_hilbert_tokens_with?] at hTokens
  | forallE sort body ih =>
      let name := binderNaming depth
      cases hBodyTokens :
          Numbered.quote_hilbert_tokens_with?
            freeNaming binderNaming (name :: boundNames) (depth + 1) body with
      | none =>
          simp [Numbered.quote_hilbert_tokens_with?,
            name, hBodyTokens] at hTokens
      | some bodyTokens =>
          cases hBodyCode :
              Numbered.quote_hilbert_with?
                freeNaming binderNaming (name :: boundNames) (depth + 1) body with
          | none =>
              simp [Numbered.quote_hilbert_with?,
                name, hBodyCode] at hCode
          | some bodyCode =>
              simp [Numbered.quote_hilbert_tokens_with?,
                name, hBodyTokens] at hTokens
              simp [Numbered.quote_hilbert_with?,
                name, hBodyCode] at hCode
              subst tokens
              subst code
              have hBodyCheck :
                  Term.CheckCertificate bodyCode SetSort.set :=
                (Numbered.quote_hilbert_with?_code_boundary
                  freeNaming binderNaming hBodyCode).check_certificate
              exact universal_formula_code_eq_standard_token_sequence
                name bodyTokens bodyCode (ih hBodyTokens hBodyCode)
  | existsE sort body =>
      simp [Numbered.quote_hilbert_tokens_with?] at hTokens
/--
任意可编号单排序签名的规范公式 quotation，其对象值等于规范 token quotation
的标准序列。
-/
theorem quote?_eq_standard_token_sequence
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {formula : Formula σ} {tokens : List Nat} {code : SetTerm} (hTokens : Numbered.quote_tokens? formula = some tokens)
    (hCode : Numbered.quote? formula = some code) :
    ⊢ₘ[godel_quotation_theory]
      code ≐ₘ standard_token_sequence tokens := by
  exact quote_hilbert_with?_eq_standard_token_sequence
    free_name bound_name hTokens hCode
/--
任意可编号单排序签名的成功 Hilbert quotation 都属于对象集合 `FormulaCodeₘ`。
普通谓词分支经由同步参数证书建立 `TermSeqₘ`，不保留额外编码前置条件。
-/
theorem Numbered.quote_hilbert_with?_formula_code_mem
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] (freeNaming binderNaming : Nat → Nat)
    {boundNames : List Nat} {depth : Nat}
    {formula : Formula σ} {code : SetTerm} (hQuote :
      Numbered.quote_hilbert_with?
        freeNaming binderNaming boundNames depth formula =
          some code) :
    ⊢ₘ[godel_quotation_theory] code ∈ₘ FormulaCodeₘ := by
  induction formula generalizing boundNames depth code with
  | falsum =>
      simp [Numbered.quote_hilbert_with?] at hQuote
  | truth =>
      simp [Numbered.quote_hilbert_with?] at hQuote
  | rel relation arguments =>
      cases hKind : numbering.relation_kind relation with
      | membership =>
          cases arguments with
          | nil =>
              simp [Numbered.quote_hilbert_with?,
                Numbered.quote_relation_with?, hKind] at hQuote
          | cons left rest =>
              cases rest with
              | nil =>
                  simp [Numbered.quote_hilbert_with?,
                    Numbered.quote_relation_with?, hKind] at hQuote
              | cons right tail =>
                  cases tail with
                  | cons extra tail =>
                      simp [Numbered.quote_hilbert_with?,
                        Numbered.quote_relation_with?, hKind] at hQuote
                  | nil =>
                      cases hLeftCode :
                          Numbered.quote_term_with?
                            freeNaming boundNames left with
                      | none =>
                          simp [Numbered.quote_hilbert_with?,
                            Numbered.quote_relation_with?,
                            hKind, hLeftCode] at hQuote
                      | some leftCode =>
                          cases hRightCode :
                              Numbered.quote_term_with?
                                freeNaming boundNames right with
                          | none =>
                              simp [Numbered.quote_hilbert_with?,
                                Numbered.quote_relation_with?,
                                hKind, hLeftCode,
                                hRightCode] at hQuote
                          | some rightCode =>
                              simp [Numbered.quote_hilbert_with?,
                                Numbered.quote_relation_with?,
                                hKind, hLeftCode,
                                hRightCode] at hQuote
                              subst code
                              have hLeftBoundary :=
                                Numbered.quote_term_with?_code_boundary
                                  freeNaming boundNames hLeftCode
                              have hRightBoundary :=
                                Numbered.quote_term_with?_code_boundary
                                  freeNaming boundNames hRightCode
                              exact gq_membership_formula_code_mem
                                leftCode rightCode
                                hLeftBoundary.check_certificate.admissible
                                hRightBoundary.check_certificate.admissible
                                hLeftBoundary.2 hRightBoundary.2 (Numbered.quote_term_with?_is_term_code
                                  freeNaming boundNames hLeftCode) (Numbered.quote_term_with?_is_term_code
                                  freeNaming boundNames hRightCode)
      | predicate =>
          cases arguments with
          | nil =>
              simp [Numbered.quote_hilbert_with?,
                Numbered.quote_relation_with?, hKind] at hQuote
          | cons head tail =>
              cases hArgumentCodes : (head :: tail).mapM (Numbered.quote_term_with?
                      freeNaming boundNames) with
              | none =>
                  simp [Numbered.quote_hilbert_with?,
                    Numbered.quote_relation_with?,
                    Numbered.quote_terms_with?,
                    hKind, hArgumentCodes] at hQuote
              | some argumentCodes =>
                  simp [Numbered.quote_hilbert_with?,
                    Numbered.quote_relation_with?,
                    Numbered.quote_terms_with?,
                    hKind, hArgumentCodes] at hQuote
                  subst code
                  rcases gq_quote_terms_with?_certificate
                      freeNaming boundNames hArgumentCodes with
                    ⟨pieces, hPieces, hCorrect, hLength⟩
                  rcases hCorrect with
                    ⟨hAligned, hTermCodes⟩
                  cases hAligned with
                  | nil =>
                      simp at hLength
                  | @cons headCode headTokens tailCodes tailPieces
                      hHead hTail =>
                      let family :=
                        standard_sequence (headCode :: tailCodes)
                      have hElements :
                          ∀ element, element ∈ headCode :: tailCodes →
                            Term.CheckCertificate element SetSort.set := by
                        intro element hElement
                        exact
                          (gq_aligned_codes_boundary
                            (.cons hHead hTail)
                            element hElement).check_certificate
                      have hElementsClosed :
                          ∀ element, element ∈ headCode :: tailCodes →
                            Term.freeSupport element = [] := by
                        intro element hElement
                        exact (gq_aligned_codes_boundary (.cons hHead hTail)
                            element hElement).2
                      have hFamily :
                          Term.CheckCertificate family SetSort.set := by
                        apply standard_sequence_from_check
                        exact hElements
                      have hFamilyClosed :
                          Term.freeSupport family = [] :=
                        seq_support_nil_m
                          0 hElementsClosed
                      have hTermSequence :
                          ⊢ₘ[godel_quotation_theory]
                            family ∈ₘ TermSeqₘ := by
                        simpa [family] using
                          gq_aligned_term_code_family_mem_term_sequence (.cons hHead hTail) hTermCodes
                      have hArgumentsLength : (head :: tail).length =
                            tailCodes.length + 1 := by
                        simpa using hLength.symm
                      have hDomain :
                          ⊢ₘ[godel_quotation_theory]
                            domₘ(family) ≐ₘ
                              Sₘ(numₘ((head :: tail).length - 1)) := by
                        have hDomainRaw :=
                          gq_weaken_standard_sequence <|
                            standard_sequence_domain_eq_numeral_length
                              (fun element hElement =>
                                (hElements element hElement).admissible)
                                (stdseq_element_fresh_of_support_nil
                                  hElementsClosed 0)
                                (stdseq_element_fresh_of_support_nil
                                  hElementsClosed 1)
                        simpa [family, hArgumentsLength,
                          finite_numeral_term] using hDomainRaw
                      simpa [family] using
                        gq_predicate_application_formula_code_mem ((head :: tail).length - 1) (numbering.relation_number relation)
                          family hFamily.admissible hFamilyClosed
                          hTermSequence hDomain
  | equal left right =>
      cases hLeftCode :
          Numbered.quote_term_with?
            freeNaming boundNames left with
      | none =>
          simp [Numbered.quote_hilbert_with?,
            hLeftCode] at hQuote
      | some leftCode =>
          cases hRightCode :
              Numbered.quote_term_with?
                freeNaming boundNames right with
          | none =>
              simp [Numbered.quote_hilbert_with?,
                hLeftCode, hRightCode] at hQuote
          | some rightCode =>
              simp [Numbered.quote_hilbert_with?,
                hLeftCode, hRightCode] at hQuote
              subst code
              have hLeftBoundary :=
                Numbered.quote_term_with?_code_boundary
                  freeNaming boundNames hLeftCode
              have hRightBoundary :=
                Numbered.quote_term_with?_code_boundary
                  freeNaming boundNames hRightCode
              exact gq_equality_formula_code_mem
                leftCode rightCode
                hLeftBoundary.check_certificate.admissible
                hRightBoundary.check_certificate.admissible
                hLeftBoundary.2 hRightBoundary.2 (Numbered.quote_term_with?_is_term_code
                  freeNaming boundNames hLeftCode) (Numbered.quote_term_with?_is_term_code
                  freeNaming boundNames hRightCode)
  | neg body ih =>
      cases hBodyCode :
          Numbered.quote_hilbert_with?
            freeNaming binderNaming boundNames depth body with
      | none =>
          simp [Numbered.quote_hilbert_with?,
            hBodyCode] at hQuote
      | some bodyCode =>
          simp [Numbered.quote_hilbert_with?,
            hBodyCode] at hQuote
          subst code
          exact gq_formula_code_mem_negation bodyCode
            (Numbered.quote_hilbert_with?_code_boundary
              freeNaming binderNaming hBodyCode).check_certificate.admissible
            (ih hBodyCode)
  | conj left right =>
      simp [Numbered.quote_hilbert_with?] at hQuote
  | disj left right =>
      simp [Numbered.quote_hilbert_with?] at hQuote
  | imp left right ihLeft ihRight =>
      cases hLeftCode :
          Numbered.quote_hilbert_with?
            freeNaming binderNaming boundNames depth left with
      | none =>
          simp [Numbered.quote_hilbert_with?,
            hLeftCode] at hQuote
      | some leftCode =>
          cases hRightCode :
              Numbered.quote_hilbert_with?
                freeNaming binderNaming boundNames depth right with
          | none =>
              simp [Numbered.quote_hilbert_with?,
                hLeftCode, hRightCode] at hQuote
          | some rightCode =>
              simp [Numbered.quote_hilbert_with?,
                hLeftCode, hRightCode] at hQuote
              subst code
              exact gq_formula_code_mem_implication
                leftCode rightCode
                (Numbered.quote_hilbert_with?_code_boundary
                  freeNaming binderNaming hLeftCode).check_certificate.admissible
                (Numbered.quote_hilbert_with?_code_boundary
                  freeNaming binderNaming hRightCode).check_certificate.admissible
                (ihLeft hLeftCode) (ihRight hRightCode)
  | iff left right =>
      simp [Numbered.quote_hilbert_with?] at hQuote
  | forallE sort body ih =>
      let name := binderNaming depth
      cases hBodyCode :
          Numbered.quote_hilbert_with?
            freeNaming binderNaming (name :: boundNames) (depth + 1) body with
      | none =>
          simp [Numbered.quote_hilbert_with?,
            name, hBodyCode] at hQuote
      | some bodyCode =>
          simp [Numbered.quote_hilbert_with?,
            name, hBodyCode] at hQuote
          subst code
          have hVariableCheck :
              Term.CheckCertificate
                (Numbered.named_variable_code name) SetSort.set := by
            prove_term_check
          exact gq_formula_code_mem_universal
            (Numbered.named_variable_code name) bodyCode
            hVariableCheck.admissible
            (Numbered.quote_hilbert_with?_code_boundary
              freeNaming binderNaming hBodyCode).check_certificate.admissible
            (named_variable_code_mem_variable_symbols name)
            (ih hBodyCode)
  | existsE sort body =>
      simp [Numbered.quote_hilbert_with?] at hQuote
/-- 成功 Hilbert quotation 自动满足对象谓词 `formula_codeₘ`。 -/
theorem Numbered.quote_hilbert_with?_is_formula_code
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] (freeNaming binderNaming : Nat → Nat)
    {boundNames : List Nat} {depth : Nat}
    {formula : Formula σ} {code : SetTerm} (hQuote :
      Numbered.quote_hilbert_with?
        freeNaming binderNaming boundNames depth formula =
          some code) :
    ⊢ₘ[godel_quotation_theory] formula_codeₘ(code) :=
  gq_is_formula_code_of_mem code (Numbered.quote_hilbert_with?_code_boundary
      freeNaming binderNaming hQuote).check_certificate.admissible
    (Numbered.quote_hilbert_with?_formula_code_mem
      freeNaming binderNaming hQuote)
/-- 规范 quotation 的结果自动属于 `FormulaCodeₘ`。 -/
theorem Numbered.quote?_formula_code_mem
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {formula : Formula σ} {code : SetTerm} (hQuote : Numbered.quote? formula = some code) :
    ⊢ₘ[godel_quotation_theory] code ∈ₘ FormulaCodeₘ :=
  Numbered.quote_hilbert_with?_formula_code_mem
    free_name bound_name hQuote
/-- 规范 quotation 的结果自动满足对象谓词 `formula_codeₘ`。 -/
theorem Numbered.quote?_is_formula_code
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {formula : Formula σ} {code : SetTerm} (hQuote : Numbered.quote? formula = some code) :
    ⊢ₘ[godel_quotation_theory] formula_codeₘ(code) :=
  Numbered.quote_hilbert_with?_is_formula_code
    free_name bound_name hQuote
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
