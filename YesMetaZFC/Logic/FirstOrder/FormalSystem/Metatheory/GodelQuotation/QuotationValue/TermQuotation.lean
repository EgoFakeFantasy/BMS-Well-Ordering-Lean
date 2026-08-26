import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.FormulaConstruction
/-!
# Gödel quotation 的项 quotation 值
本模块证明项 quotation 的标准 token 值及其对象项编码证书。
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
任意可编号单排序签名的项 quotation，其对象值等于同步 token quotation 的标准序列。
项与参数列使用同一个结构递归：参数列分支同时记录逐项代码边界和值对齐证书，
因此正元函数应用可以直接消费公共 `flattenₘ` 正确性，而不需要签名特化接口。
-/
theorem quote_term_with?_eq_standard_token_sequence
    {σ : Signature.{u, v, w}} [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    {term : Term σ} {tokens : List Nat} {code : SetTerm} (hTokens :
      Numbered.quote_term_tokens_with?
        freeNaming boundNames term = some tokens) (hCode :
      Numbered.quote_term_with?
        freeNaming boundNames term = some code) :
    ⊢ₘ[godel_quotation_theory]
      code ≐ₘ standard_token_sequence tokens := by
  refine Term.rec (motive_1 := fun term =>
      ∀ tokens code,
        Numbered.quote_term_tokens_with? freeNaming boundNames term =
            some tokens →
          Numbered.quote_term_with? freeNaming boundNames term =
              some code →
            ⊢ₘ[godel_quotation_theory]
              code ≐ₘ standard_token_sequence tokens) (motive_2 := fun terms =>
      ∀ pieces codes,
        terms.mapM (Numbered.quote_term_tokens_with?
                freeNaming boundNames) =
            some pieces →
          terms.mapM (Numbered.quote_term_with? freeNaming boundNames) =
              some codes →
            gq_code_token_aligned_list codes pieces)
    ?_ ?_ ?_ ?_ term tokens code hTokens hCode
  · intro sourceVar sourceTokens sourceCode
      hSourceTokens hSourceCode
    cases sourceVar with
    | bvar sort index =>
        cases hName : boundNames[index]? with
        | none =>
            simp [Numbered.quote_term_tokens_with?,
              hName] at hSourceTokens
        | some name =>
            simp [Numbered.quote_term_tokens_with?,
              Numbered.quote_term_with?,
              hName] at hSourceTokens hSourceCode
            subst sourceTokens
            subst sourceCode
            exact named_variable_code_eq_standard_token_sequence name
    | fvar sort id =>
        simp [Numbered.quote_term_tokens_with?,
          Numbered.quote_term_with?]
          at hSourceTokens hSourceCode
        subst sourceTokens
        subst sourceCode
        exact named_variable_code_eq_standard_token_sequence (freeNaming id)
  · intro function arguments ih argumentTokens resultCode
      hResultTokens hResultCode
    cases hArgumentTokens :
        arguments.mapM (Numbered.quote_term_tokens_with?
            freeNaming boundNames) with
    | none =>
        simp [Numbered.quote_term_tokens_with?, hArgumentTokens]
          at hResultTokens
    | some tokenPieces =>
        cases hArgumentCodes :
            arguments.mapM (Numbered.quote_term_with? freeNaming boundNames) with
        | none =>
            simp [Numbered.quote_term_with?, hArgumentCodes]
              at hResultCode
        | some argumentCodes =>
            have hAligned :=
              ih tokenPieces argumentCodes
                hArgumentTokens hArgumentCodes
            cases hAligned with
            | nil =>
                simp [Numbered.quote_term_tokens_with?,
                  Numbered.quote_term_with?,
                  hArgumentTokens, hArgumentCodes]
                    at hResultTokens hResultCode
                subst argumentTokens
                subst resultCode
                exact constant_code_eq_standard_token_sequence (QuotationNumbering.function_number function)
            | @cons headCode headTokens tailCodes tailPieces
                hHead hTail =>
                simp [Numbered.quote_term_tokens_with?,
                  Numbered.quote_term_with?,
                  hArgumentTokens, hArgumentCodes]
                    at hResultTokens hResultCode
                subst argumentTokens
                subst resultCode
                exact
                  gq_term_application_code_eq_standard_token_sequence (arguments.length - 1) (QuotationNumbering.function_number function) (.cons hHead hTail)
  · intro pieces codes hPieces hCodes
    simp at hPieces hCodes
    subst pieces
    subst codes
    exact .nil
  · intro head tail ihHead ihTail pieces codes hPieces hCodes
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
        | some tailPieces =>
            cases hHeadCode :
                Numbered.quote_term_with?
                  freeNaming boundNames head with
            | none =>
                simp [hHeadCode] at hCodes
            | some headCode =>
                cases hTailCodes :
                    tail.mapM (Numbered.quote_term_with?
                        freeNaming boundNames) with
                | none =>
                    simp [hHeadCode, hTailCodes] at hCodes
                | some tailCodes =>
                    simp [hHeadTokens, hTailTokens] at hPieces
                    simp [hHeadCode, hTailCodes] at hCodes
                    subst pieces
                    subst codes
                    exact .cons
                      ⟨Numbered.quote_term_with?_code_boundary
                          freeNaming boundNames hHeadCode,
                        ihHead headTokens headCode
                          hHeadTokens hHeadCode⟩ (ihTail tailPieces tailCodes
                        hTailTokens hTailCodes)
/-- 代码值对齐并逐项满足“是项编码”的参数列证书。 -/
def gq_term_code_token_aligned_list
    (codes : List SetTerm) (pieces : List (List Nat)) : Prop :=
  gq_code_token_aligned_list codes pieces ∧
    ∀ code, code ∈ codes →
      ⊢ₘ[godel_quotation_theory] term_codeₘ(code)
/--
在 Gödel quotation 联合理论中，标准序列的每个列表元素属于目标集时，序列在
定义域内的规范求值也属于目标集。
-/
private theorem gq_standard_sequence_values_mem (binder : FreeVarId)
    {elements : List SetTerm} (target : SetTerm) (hElements : ∀ element, element ∈ elements →
      Term.CheckCertificate element SetSort.set) (hElementsClosed : ∀ element, element ∈ elements →
      Term.freeSupport element = []) (hTargetClosed : Term.freeSupport target = [])
    (hTargetMember : ∀ element, element ∈ elements →
      ⊢ₘ[godel_quotation_theory] element ∈ₘ target)
    (hTarget : Term.CheckCertificate target SetSort.set := by
      prove_term_check) :
    ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, binder], (x#binder ∈ₘ domₘ(standard_sequence elements)) ⟶ₘ ((standard_sequence elements ·ₘ x#binder) ∈ₘ target) := by
  let sequence := standard_sequence elements
  let index : SetTerm := x#binder
  have hSequence :
      Term.CheckCertificate sequence SetSort.set := by
    apply standard_sequence_from_check
    exact hElements
  have hSequenceSupport : Term.freeSupport sequence = [] :=
    seq_support_nil_m 0 hElementsClosed
  have hIndex :
      Term.CheckCertificate index SetSort.set := by
    prove_term_check
  have hValue :
      Term.CheckCertificate (sequence ·ₘ index) SetSort.set := by
    prove_term_check
  have hFunction :
      ⊢ₘ[godel_quotation_theory]
        is_function_formula sequence :=
    gq_weaken_standard_sequence <| by
      simpa [sequence] using
        standard_sequence_from_is_function
          0 (fun element hElement =>
            (hElements element hElement).admissible)
            (stdseq_element_fresh_of_support_nil hElementsClosed 0)
            (stdseq_element_fresh_of_support_nil hElementsClosed 1)
            (stdseq_element_fresh_of_support_nil hElementsClosed 2)
  have hGraphContract :
      ⊢ₘ[godel_quotation_theory] (is_function_formula sequence ∧ₘ (index ∈ₘ domₘ(sequence))) ⟶ₘ (⟨index, sequence ·ₘ index⟩ₘ ∈ₘ sequence) :=
    gq_weaken_standard_sequence <|
      standard_sequence_weaken_function_application <|
        function_application_graph_mem
          sequence index
            hSequence.admissible hIndex.admissible
  have hGraphValue :=
    standard_sequence_from_graph_value_mem_of_theory (T := godel_quotation_theory) (fun _ hFormula => Or.inl hFormula)
      0 target index (sequence ·ₘ index)
      (fun element hElement =>
        (hElements element hElement).admissible)
      hTarget.admissible hTargetMember
      hIndex.admissible hValue.admissible
  have hDomainMembershipCheck :
      Formula.CheckCertificate (index ∈ₘ domₘ(sequence)) := by
    prove_formula_check
  have hPoint :
      ⊢ₘ[godel_quotation_theory] (index ∈ₘ domₘ(sequence)) ⟶ₘ ((sequence ·ₘ index) ∈ₘ target) := by
    nd_apply FirstOrder.Derives.impIntro
    let domainMembership : SetFormula :=
      index ∈ₘ domₘ(sequence)
    let Γ : Context signature := [domainMembership]
    have hDomain :
        Γ ⊢ₘ[godel_quotation_theory]
          index ∈ₘ domₘ(sequence) := by
      simpa [Γ, domainMembership] using (show Γ ⊢ₘ[godel_quotation_theory]
            domainMembership from
          .assumption (by simp [Γ]))
    have hGraph :
        Γ ⊢ₘ[godel_quotation_theory]
          ⟨index, sequence ·ₘ index⟩ₘ ∈ₘ sequence :=
      FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ])
          hGraphContract) (FirstOrder.Derives.conjIntro (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hFunction)
          hDomain)
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hGraphValue)
      hGraph
  have hSequenceClose :
      Term.closeFreeAt SetSort.set binder 0 sequence = sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set binder 0 sequence hSequence.admissible.2
        (by rw [hSequenceSupport]; exact List.not_mem_nil)
  have hTargetClose :
      Term.closeFreeAt SetSort.set binder 0 target = target :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set binder 0 target hTarget.admissible.2
        (by rw [hTargetClosed]; exact List.not_mem_nil)
  have hGeneralized :
      ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, binder], ((x#binder ∈ₘ domₘ(sequence)) ⟶ₘ ((sequence ·ₘ x#binder) ∈ₘ target)) := by
    derive_close (binder) using hPoint
  simpa [sequence, index,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt, set_variable,
    domain_term, function_application_term,
    hSequenceClose, hTargetClose] using hGeneralized
/--
标准序列的列表元素逐项满足 `term_codeₘ` 时，其定义域内的规范求值也逐点满足
`term_codeₘ`。证明先经 `TermCodeₘ` 集合成员语义传递，再由定义合同返回谓词。
-/
theorem gq_standard_sequence_term_code_values (binder : FreeVarId)
    {elements : List SetTerm} (hElements : ∀ element, element ∈ elements →
      Term.CheckCertificate element SetSort.set) (hElementsClosed : ∀ element, element ∈ elements →
      Term.freeSupport element = []) (hTermCodes : ∀ element, element ∈ elements →
      ⊢ₘ[godel_quotation_theory] term_codeₘ(element)) :
    ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, binder], (x#binder ∈ₘ domₘ(standard_sequence elements)) ⟶ₘ
          term_codeₘ(standard_sequence elements ·ₘ x#binder) := by
  let sequence := standard_sequence elements
  let index : SetTerm := x#binder
  let value : SetTerm := sequence ·ₘ index
  have hSequence :
      Term.CheckCertificate sequence SetSort.set := by
    apply standard_sequence_from_check
    exact hElements
  have hIndex :
      Term.CheckCertificate index SetSort.set := by
    prove_term_check
  have hValue :
      Term.CheckCertificate value SetSort.set := by
    prove_term_check
  have hMembers :
      ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, binder], (x#binder ∈ₘ domₘ(sequence)) ⟶ₘ ((sequence ·ₘ x#binder) ∈ₘ TermCodeₘ) := by
    simpa [sequence] using
      gq_standard_sequence_values_mem
        binder TermCodeₘ hElements hElementsClosed
        rfl (by
          intro element hElement
          exact FirstOrder.Derives.iffElimRight (gq_term_code_definition_instance
              element (hElements element hElement).admissible)
            (hTermCodes element hElement))
  have hMembersAt :=
    FirstOrder.Derives.forall_elim hMembers
      (hTermCheck := hIndex)
  have hSequenceOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term sequence = sequence :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term sequence hSequence.admissible.2
  have hSequenceClose (depth : Nat) :
      Term.closeFreeAt SetSort.set binder depth sequence = sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set binder depth sequence hSequence.admissible.2 (by
        rw [seq_support_nil_m
          0 hElementsClosed]
        exact List.not_mem_nil)
  have hMemberPoint :
      ⊢ₘ[godel_quotation_theory] (index ∈ₘ domₘ(sequence)) ⟶ₘ (value ∈ₘ TermCodeₘ) := by
    simpa [sequence, index, value,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, domain_term,
      function_application_term,
      hSequenceOpen, hSequenceClose] using hMembersAt
  have hDefinition :
      ⊢ₘ[godel_quotation_theory]
        term_codeₘ(value) ↔ₘ (value ∈ₘ TermCodeₘ) :=
    gq_term_code_definition_instance value hValue.admissible
  have hDomainMembershipCheck :
      Formula.CheckCertificate (index ∈ₘ domₘ(sequence)) := by
    prove_formula_check
  have hPoint :
      ⊢ₘ[godel_quotation_theory] (index ∈ₘ domₘ(sequence)) ⟶ₘ term_codeₘ(value) := by
    nd_apply FirstOrder.Derives.impIntro
    let domainMembership : SetFormula :=
      index ∈ₘ domₘ(sequence)
    let Γ : Context signature := [domainMembership]
    have hDomain :
        Γ ⊢ₘ[godel_quotation_theory]
          index ∈ₘ domₘ(sequence) := by
      simpa [Γ, domainMembership] using (show Γ ⊢ₘ[godel_quotation_theory]
            domainMembership from
          .assumption (by simp [Γ]))
    have hMember :
        Γ ⊢ₘ[godel_quotation_theory] value ∈ₘ TermCodeₘ :=
      FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hMemberPoint)
        hDomain
    exact FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) hDefinition)
      hMember
  have hGeneralized :
      ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, binder], ((x#binder ∈ₘ domₘ(sequence)) ⟶ₘ
            term_codeₘ(sequence ·ₘ x#binder)) := by
    derive_close (binder) using hPoint
  simpa [sequence, index, value,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt, set_variable,
    domain_term, function_application_term,
    hSequenceClose] using hGeneralized
/--
非空对齐代码族的标准序列属于非空代码字符串序列空间。
正性只依赖 token 对齐，不额外要求这些代码已经属于 `TermCodeₘ`。
-/
theorem gq_aligned_code_family_mem_positive_code_strings
    {headCode : SetTerm} {headTokens : List Nat}
    {tailCodes : List SetTerm} {tailPieces : List (List Nat)}
    (hAligned :
      gq_code_token_aligned_list
        (headCode :: tailCodes) (headTokens :: tailPieces)) :
    ⊢ₘ[godel_quotation_theory]
      standard_sequence (headCode :: tailCodes) ∈ₘ
        seq₊_spaceₘ(CodeStrₘ) := by
  let family := standard_sequence (headCode :: tailCodes)
  let rightFamily :=
    standard_sequence ((headTokens :: tailPieces).map standard_token_sequence)
  have hElements :
      ∀ element, element ∈ headCode :: tailCodes →
        Term.CheckCertificate element SetSort.set := by
    intro element hElement
    exact
      (gq_aligned_codes_boundary
        hAligned element hElement).check_certificate
  have hElementsClosed :
      ∀ element, element ∈ headCode :: tailCodes →
        Term.freeSupport element = [] := by
    intro element hElement
    exact (gq_aligned_codes_boundary
      hAligned element hElement).2
  have hFamily :
      Term.CheckCertificate family SetSort.set := by
    apply standard_sequence_from_check
    exact hElements
  have hFamilyClosed : Term.freeSupport family = [] :=
    seq_support_nil_m 0 hElementsClosed
  have hRightFamily :
      Term.CheckCertificate rightFamily SetSort.set := by
    apply standard_sequence_from_check
    intro element hElement
    rcases List.mem_cons.mp hElement with hHead | hElement
    · subst element
      prove_term_check
    · rcases List.mem_map.mp hElement with
        ⟨tokens, _, rfl⟩
      prove_term_check
  have hRightPositive :
      ⊢ₘ[godel_quotation_theory]
        rightFamily ∈ₘ seq₊_spaceₘ(CodeStrₘ) :=
    gq_weaken_standard_sequence <| by
      simpa [rightFamily] using
        standard_sequence_mem_nonempty_sequence_space
          CodeStrₘ (by
            intro element hElement
            rcases List.mem_cons.mp hElement with hHead | hElement
            · subst element
              exact standard_token_sequence_admissible headTokens
            · rcases List.mem_map.mp hElement with
                ⟨tokens, _, rfl⟩
              exact standard_token_sequence_admissible tokens) (by
            intro element hElement
            rcases List.mem_cons.mp hElement with hHead | hElement
            · subst element
              exact standard_token_sequence_freeSupport_nil headTokens
            · rcases List.mem_map.mp hElement with
                ⟨tokens, _, rfl⟩
              exact standard_token_sequence_freeSupport_nil tokens)
          code_string_space_term_admissible rfl
          standard_token_sequence_code_string_ne_empty (by
            intro element hElement
            rcases List.mem_cons.mp hElement with hHead | hElement
            · subst element
              exact standard_token_sequence_mem_code_string headTokens
            · rcases List.mem_map.mp hElement with
                ⟨tokens, _, rfl⟩
              exact standard_token_sequence_mem_code_string tokens) (by simp)
  have hFamilyEquality :
      ⊢ₘ[godel_quotation_theory]
        family ≐ₘ rightFamily := by
    simpa [family, rightFamily] using
      gq_standard_sequence_eq_token_family hAligned
  have hPositive :
      ⊢ₘ[godel_quotation_theory]
        family ∈ₘ seq₊_spaceₘ(CodeStrₘ) :=
    FirstOrder.Derives.iffElimLeft (membership_left_iff_of_equality
        family rightFamily (seq₊_spaceₘ(CodeStrₘ))
        hFamily.admissible hRightFamily.admissible
        (nonempty_finite_sequence_space_term_admissible
          CodeStrₘ code_string_space_term_admissible)
        hFamilyEquality)
      hRightPositive
  simpa [family] using hPositive

/--
非空、逐项对齐且逐项满足 `term_codeₘ` 的代码族，其标准序列属于对象集合
`TermSeqₘ`。
-/
theorem gq_aligned_term_code_family_mem_term_sequence
    {headCode : SetTerm} {headTokens : List Nat}
    {tailCodes : List SetTerm} {tailPieces : List (List Nat)} (hAligned :
      gq_code_token_aligned_list (headCode :: tailCodes) (headTokens :: tailPieces)) (hTermCodes : ∀ code, code ∈ headCode :: tailCodes →
      ⊢ₘ[godel_quotation_theory] term_codeₘ(code)) :
    ⊢ₘ[godel_quotation_theory]
      standard_sequence (headCode :: tailCodes) ∈ₘ TermSeqₘ := by
  let family := standard_sequence (headCode :: tailCodes)
  have hElements :
      ∀ element, element ∈ headCode :: tailCodes →
        Term.CheckCertificate element SetSort.set := by
    intro element hElement
    exact
      (gq_aligned_codes_boundary
        hAligned element hElement).check_certificate
  have hElementsClosed :
      ∀ element, element ∈ headCode :: tailCodes →
        Term.freeSupport element = [] := by
    intro element hElement
    exact (gq_aligned_codes_boundary
      hAligned element hElement).2
  have hFamily :
      Term.CheckCertificate family SetSort.set := by
    apply standard_sequence_from_check
    exact hElements
  have hFamilyClosed : Term.freeSupport family = [] :=
    seq_support_nil_m 0 hElementsClosed
  have hPositive :
      ⊢ₘ[godel_quotation_theory]
        family ∈ₘ seq₊_spaceₘ(CodeStrₘ) := by
    simpa [family] using
      gq_aligned_code_family_mem_positive_code_strings hAligned
  have hValues :
      ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, 220], (x#220 ∈ₘ domₘ(family)) ⟶ₘ
            term_codeₘ(family ·ₘ x#220) := by
    simpa [family] using
      gq_standard_sequence_term_code_values
        220 hElements hElementsClosed hTermCodes
  exact gq_term_sequence_mem
    family hFamily.admissible
      (by rw [hFamilyClosed]; exact List.not_mem_nil)
      hPositive hValues

/--
非空、逐项对齐且逐项满足 `term_codeₘ` 的代码族，可直接组成正元函数应用项码。
该接口把 quotation 与 checked decoder 共用的有限序列闭包集中在一处。
-/
theorem gq_term_application_code_is_term_code_of_aligned
    (index : Nat)
    {headCode : SetTerm} {headTokens : List Nat}
    {tailCodes : List SetTerm} {tailPieces : List (List Nat)}
    (hAligned :
      gq_code_token_aligned_list
        (headCode :: tailCodes) (headTokens :: tailPieces))
    (hTermCodes :
      ∀ code, code ∈ headCode :: tailCodes →
        ⊢ₘ[godel_quotation_theory] term_codeₘ(code)) :
    ⊢ₘ[godel_quotation_theory]
      term_codeₘ(
        term_application_code_term
          (numₘ(tailCodes.length)) (numₘ(index))
          (standard_sequence (headCode :: tailCodes))) := by
  let codes := headCode :: tailCodes
  let family := standard_sequence codes
  have hElements :
      ∀ element, element ∈ codes →
        Term.CheckCertificate element SetSort.set := by
    intro element hElement
    exact
      (gq_aligned_codes_boundary
        hAligned element hElement).check_certificate
  have hElementsClosed :
      ∀ element, element ∈ codes →
        Term.freeSupport element = [] := by
    intro element hElement
    exact
      (gq_aligned_codes_boundary
        hAligned element hElement).2
  have hFamily :
      Term.CheckCertificate family SetSort.set := by
    apply standard_sequence_from_check
    exact hElements
  have hPositive :
      ⊢ₘ[godel_quotation_theory]
        family ∈ₘ seq₊_spaceₘ(CodeStrₘ) := by
    simpa [family, codes] using
      gq_aligned_code_family_mem_positive_code_strings hAligned
  have hDomain :
      ⊢ₘ[godel_quotation_theory]
        domₘ(family) ≐ₘ
          Sₘ(numₘ(tailCodes.length)) := by
    have hRaw :=
      gq_weaken_standard_sequence <|
        standard_sequence_domain_eq_numeral_length
          (fun element hElement =>
            (hElements element hElement).admissible)
          (stdseq_element_fresh_of_support_nil
            hElementsClosed 0)
          (stdseq_element_fresh_of_support_nil
            hElementsClosed 1)
    simpa [family, codes, finite_numeral_term] using hRaw
  have hValues :
      ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, 213],
          (x#213 ∈ₘ domₘ(family)) ⟶ₘ
            ((family ·ₘ x#213) ∈ₘ TermCodeₘ) := by
    simpa [family, codes] using
      gq_standard_sequence_values_mem
        213 TermCodeₘ hElements hElementsClosed
        rfl
        (by
          intro element hElement
          exact FirstOrder.Derives.iffElimRight
            (gq_term_code_definition_instance
              element
              (hElements element hElement).admissible)
            (hTermCodes element hElement))
  exact
    gq_term_application_code_is_term_code
      tailCodes.length index family
      hFamily.admissible
      (seq_support_nil_m 0 hElementsClosed)
      hPositive hDomain hValues
/--
成功项 quotation 的内部证书：同步 token quotation 与对象 `TermCodeₘ` 证明同时存在。
递归同时返回值对齐证书和逐项项编码证书；正元函数应用因此直接消费非空参数序列、
定义域与逐点求值三个公共接口。
-/
private theorem gq_quote_term_with?_certificate
    {σ : Signature.{u, v, w}} [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    {term : Term σ} {code : SetTerm} (hQuote :
      Numbered.quote_term_with?
        freeNaming boundNames term = some code) :
    ∃ tokens, (Numbered.quote_term_tokens_with?
          freeNaming boundNames term = some tokens) ∧ (⊢ₘ[godel_quotation_theory] term_codeₘ(code)) := by
  have hResult := Term.rec (motive_1 := fun term =>
      ∀ code,
        Numbered.quote_term_with? freeNaming boundNames term =
            some code →
          ∃ tokens, (Numbered.quote_term_tokens_with?
                  freeNaming boundNames term =
                some tokens) ∧ (⊢ₘ[godel_quotation_theory] term_codeₘ(code))) (motive_2 := fun terms =>
      ∀ codes,
        terms.mapM (Numbered.quote_term_with? freeNaming boundNames) =
            some codes →
          ∃ pieces, (terms.mapM (Numbered.quote_term_tokens_with?
                      freeNaming boundNames) =
                  some pieces) ∧ (gq_term_code_token_aligned_list codes pieces ∧
                codes.length = terms.length)) (by
      intro sourceVar sourceCode hSourceCode
      cases sourceVar with
      | bvar sort index =>
          cases hName : boundNames[index]? with
          | none =>
              simp [Numbered.quote_term_with?, hName] at hSourceCode
          | some name =>
              simp [Numbered.quote_term_with?, hName] at hSourceCode
              subst sourceCode
              let tokens := [Numbered.variable_token name]
              refine ⟨tokens, ?_, ?_⟩
              · simp [tokens, Numbered.quote_term_tokens_with?, hName]
              · exact named_variable_code_is_term_code name
      | fvar sort id =>
          simp [Numbered.quote_term_with?] at hSourceCode
          subst sourceCode
          let tokens := [Numbered.variable_token (freeNaming id)]
          refine ⟨tokens, ?_, ?_⟩
          · simp [tokens, Numbered.quote_term_tokens_with?]
          · exact named_variable_code_is_term_code (freeNaming id)) (by
      intro function arguments ih resultCode hResultCode
      simp only [Numbered.quote_term_with?] at hResultCode
      cases hArgumentCodes :
          arguments.mapM (Numbered.quote_term_with? freeNaming boundNames) with
      | none =>
          simp [hArgumentCodes] at hResultCode
      | some argumentCodes =>
          simp [hArgumentCodes] at hResultCode
          rcases ih argumentCodes hArgumentCodes with
            ⟨pieces, hPieces, hCorrect, hLength⟩
          rcases hCorrect with ⟨hAligned, hTermCodes⟩
          cases hAligned with
          | nil =>
              simp at hResultCode
              subst resultCode
              let tokens :=
                [Numbered.constant_token (QuotationNumbering.function_number function)]
              refine ⟨tokens, ?_, ?_⟩
              · simp [tokens, Numbered.quote_term_tokens_with?, hPieces]
              · exact constant_code_is_term_code (QuotationNumbering.function_number function)
          | @cons headCode headTokens tailCodes tailPieces
              hHead hTail =>
              simp at hResultCode
              subst resultCode
              let family := standard_sequence (headCode :: tailCodes)
              let rightFamily :=
                standard_sequence ((headTokens :: tailPieces).map
                    standard_token_sequence)
              have hElements :
                  ∀ element, element ∈ headCode :: tailCodes →
                    Term.CheckCertificate element SetSort.set := by
                intro element hElement
                exact
                  (gq_aligned_codes_boundary
                    (.cons hHead hTail) element hElement).check_certificate
              have hElementsClosed :
                  ∀ element, element ∈ headCode :: tailCodes →
                    Term.freeSupport element = [] := by
                intro element hElement
                exact (gq_aligned_codes_boundary (.cons hHead hTail) element hElement).2
              have hFamily :
                  Term.CheckCertificate family SetSort.set := by
                apply standard_sequence_from_check
                exact hElements
              have hRightFamily :
                  Term.CheckCertificate rightFamily SetSort.set := by
                apply standard_sequence_from_check
                intro element hElement
                simp only [List.map_cons, List.mem_cons] at hElement
                rcases hElement with rfl | hElement
                · prove_term_check
                · rcases List.mem_map.mp hElement with
                    ⟨tokens, _, rfl⟩
                  prove_term_check
              have hRightPositive :
                  ⊢ₘ[godel_quotation_theory]
                    rightFamily ∈ₘ seq₊_spaceₘ(CodeStrₘ) :=
                gq_weaken_standard_sequence <| by
                  simpa [rightFamily] using
                    standard_sequence_mem_nonempty_sequence_space
                      CodeStrₘ (by
                        intro element hElement
                        simp only [ List.mem_cons] at hElement
                        rcases hElement with rfl | hElement
                        · exact standard_token_sequence_admissible headTokens
                        · rcases List.mem_map.mp hElement with
                            ⟨tokens, _, rfl⟩
                          exact standard_token_sequence_admissible tokens) (by
                        intro element hElement
                        simp only [ List.mem_cons] at hElement
                        rcases hElement with rfl | hElement
                        · exact
                            standard_token_sequence_freeSupport_nil headTokens
                        · rcases List.mem_map.mp hElement with
                            ⟨tokens, _, rfl⟩
                          exact
                            standard_token_sequence_freeSupport_nil tokens)
                      code_string_space_term_admissible rfl
                      standard_token_sequence_code_string_ne_empty (by
                        intro element hElement
                        simp only [ List.mem_cons] at hElement
                        rcases hElement with rfl | hElement
                        · exact
                            standard_token_sequence_mem_code_string headTokens
                        · rcases List.mem_map.mp hElement with
                            ⟨tokens, _, rfl⟩
                          exact standard_token_sequence_mem_code_string tokens) (by simp)
              have hFamilyEquality :
                  ⊢ₘ[godel_quotation_theory]
                    family ≐ₘ rightFamily := by
                simpa [family, rightFamily] using
                  gq_standard_sequence_eq_token_family (.cons hHead hTail)
              have hPositive :
                  ⊢ₘ[godel_quotation_theory]
                    family ∈ₘ seq₊_spaceₘ(CodeStrₘ) :=
                FirstOrder.Derives.iffElimLeft (membership_left_iff_of_equality
                    family rightFamily (seq₊_spaceₘ(CodeStrₘ))
                    hFamily.admissible hRightFamily.admissible
                    (nonempty_finite_sequence_space_term_admissible
                      CodeStrₘ code_string_space_term_admissible)
                    hFamilyEquality)
                  hRightPositive
              have hArgumentsLength :
                  arguments.length = tailCodes.length + 1 := by
                simpa using hLength.symm
              have hDomain :
                  ⊢ₘ[godel_quotation_theory]
                    domₘ(family) ≐ₘ
                      Sₘ(numₘ(arguments.length - 1)) := by
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
              have hValues :
                  ⊢ₘ[godel_quotation_theory]
                    ∀ₘ[SetSort.set, 213], (x#213 ∈ₘ domₘ(family)) ⟶ₘ ((family ·ₘ x#213) ∈ₘ TermCodeₘ) := by
                apply gq_standard_sequence_values_mem
                  213 TermCodeₘ hElements hElementsClosed
                  rfl
                intro element hElement
                exact FirstOrder.Derives.iffElimRight (gq_term_code_definition_instance
                    element (hElements element hElement).admissible)
                  (hTermCodes element hElement)
              refine
                ⟨Numbered.function_application_tokens (arguments.length - 1) (QuotationNumbering.function_number function) (headTokens :: tailPieces),
                  ?_, ?_⟩
              · simp [Numbered.quote_term_tokens_with?, hPieces]
              · simpa [family] using
                  gq_term_application_code_is_term_code (arguments.length - 1) (QuotationNumbering.function_number function)
                    family hFamily.admissible (seq_support_nil_m
                      0 hElementsClosed)
                    hPositive hDomain hValues) (by
      intro codes hCodes
      simp at hCodes
      subst codes
      exact
        ⟨List.nil, by simp,
          ⟨gq_code_token_aligned_list.nil, by simp⟩, by simp⟩) (by
      intro head tail ihHead ihTail codes hCodes
      cases hHeadCode :
          Numbered.quote_term_with?
            freeNaming boundNames head with
      | none =>
          simp [hHeadCode] at hCodes
      | some headCode =>
          cases hTailCodes :
              tail.mapM (Numbered.quote_term_with?
                  freeNaming boundNames) with
          | none =>
              simp [hHeadCode, hTailCodes] at hCodes
          | some tailCodes =>
              simp [hHeadCode, hTailCodes] at hCodes
              subst codes
              rcases ihHead headCode hHeadCode with
                ⟨headTokens, hHeadTokens, hHeadTerm⟩
              rcases ihTail tailCodes hTailCodes with
                ⟨tailPieces, hTailPieces,
                  hTailCorrect, hTailLength⟩
              rcases hTailCorrect with
                ⟨hTailAligned, hTailTerms⟩
              refine
                ⟨headTokens :: tailPieces, ?_, ?_, ?_⟩
              · simp [hHeadTokens, hTailPieces]
              · refine ⟨.cons ?_ hTailAligned, ?_⟩
                · exact
                    ⟨Numbered.quote_term_with?_code_boundary
                        freeNaming boundNames hHeadCode,
                      quote_term_with?_eq_standard_token_sequence
                        freeNaming boundNames
                        hHeadTokens hHeadCode⟩
                · intro element hElement
                  simp only [List.mem_cons] at hElement
                  rcases hElement with rfl | hElement
                  · exact hHeadTerm
                  · exact hTailTerms element hElement
              · simp [hTailLength])
    term code hQuote
  exact hResult
/--
任意可编号单排序签名的成功项 quotation 都满足对象谓词 `term_codeₘ`。
-/
theorem Numbered.quote_term_with?_is_term_code
    {σ : Signature.{u, v, w}} [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    {term : Term σ} {code : SetTerm} (hQuote :
      Numbered.quote_term_with?
        freeNaming boundNames term = some code) :
    ⊢ₘ[godel_quotation_theory] term_codeₘ(code) := by
  rcases gq_quote_term_with?_certificate
      freeNaming boundNames hQuote with
    ⟨_, _, hTermCode⟩
  exact hTermCode
/--
一列成功项 quotation 的同步证书：token 分片逐项对齐，且每个编码都属于
`TermCodeₘ`。该接口供普通谓词应用同时复用 quotation 值证明和编码闭包证明。
-/
theorem gq_quote_terms_with?_certificate
    {σ : Signature.{u, v, w}} [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    {terms : List (Term σ)} {codes : List SetTerm} (hCodes :
      terms.mapM (Numbered.quote_term_with? freeNaming boundNames) =
        some codes) :
    ∃ pieces, (terms.mapM (Numbered.quote_term_tokens_with?
              freeNaming boundNames) =
          some pieces) ∧ (gq_term_code_token_aligned_list codes pieces ∧
          codes.length = terms.length) := by
  induction terms generalizing codes with
  | nil =>
      simp at hCodes
      subst codes
      exact
        ⟨List.nil, by simp,
          ⟨gq_code_token_aligned_list.nil, by simp⟩, by simp⟩
  | cons head tail ih =>
      cases hHeadCode :
          Numbered.quote_term_with?
            freeNaming boundNames head with
      | none =>
          simp [hHeadCode] at hCodes
      | some headCode =>
          cases hTailCodes :
              tail.mapM (Numbered.quote_term_with?
                  freeNaming boundNames) with
          | none =>
              simp [hHeadCode, hTailCodes] at hCodes
          | some tailCodes =>
              simp [hHeadCode, hTailCodes] at hCodes
              subst codes
              rcases gq_quote_term_with?_certificate
                  freeNaming boundNames hHeadCode with
                ⟨headTokens, hHeadTokens, hHeadTerm⟩
              rcases ih hTailCodes with
                ⟨tailPieces, hTailPieces,
                  hTailCorrect, hTailLength⟩
              rcases hTailCorrect with
                ⟨hTailAligned, hTailTerms⟩
              refine
                ⟨headTokens :: tailPieces, ?_, ?_, ?_⟩
              · simp [hHeadTokens, hTailPieces]
              · refine ⟨.cons ?_ hTailAligned, ?_⟩
                · exact
                    ⟨Numbered.quote_term_with?_code_boundary
                        freeNaming boundNames hHeadCode,
                      quote_term_with?_eq_standard_token_sequence
                        freeNaming boundNames
                        hHeadTokens hHeadCode⟩
                · intro element hElement
                  simp only [List.mem_cons] at hElement
                  rcases hElement with rfl | hElement
                  · exact hHeadTerm
                  · exact hTailTerms element hElement
              · simp [hTailLength]
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
