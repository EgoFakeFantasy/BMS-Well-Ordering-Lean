import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Substitution.Core
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.StandardTokenSequenceFlatten
/-!
# Gödel 替换的规范分片序列
本模块构造标准替换分片族，并证明其满足对象层 code_substitution_spec。
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
attribute [local simp] finite_numeral_term_freeSupport
/-! ## quotation 对象项的保留编号新鲜性 -/
/-- `code_substitution_spec` 使用的规范分片族对象。 -/
def standard_substitution_pieces_sequence (source : List Nat) (boundToken : Nat) (replacement : List Nat) :
    SetTerm :=
  standard_sequence ((substitution_pieces_tokens source boundToken replacement).map
      standard_token_sequence)
private theorem stdsubst_piece_elements_admissible (source : List Nat) (boundToken : Nat) (replacement : List Nat) :
    ∀ piece,
      piece ∈ (substitution_pieces_tokens source boundToken replacement).map
            standard_token_sequence →
        Term.Admissible piece SetSort.set := by
  intro piece hPiece
  rcases List.mem_map.mp hPiece with ⟨tokens, hTokens, rfl⟩
  exact standard_token_sequence_admissible tokens
private theorem stdsubst_piece_elements_closed (source : List Nat) (boundToken : Nat) (replacement : List Nat) :
    ∀ piece,
      piece ∈ (substitution_pieces_tokens source boundToken replacement).map
            standard_token_sequence →
        Term.freeSupport piece = [] := by
  intro piece hPiece
  rcases List.mem_map.mp hPiece with ⟨tokens, hTokens, rfl⟩
  exact standard_token_sequence_freeSupport_nil tokens
/-- 规范分片族对象满足 proof-carrying 项边界。 -/
theorem standard_substitution_pieces_sequence_admissible (source : List Nat) (boundToken : Nat) (replacement : List Nat) :
    Term.Admissible (standard_substitution_pieces_sequence
        source boundToken replacement)
      SetSort.set := by
  exact seq_admissible_m 0 (stdsubst_piece_elements_admissible
      source boundToken replacement)
/- 规范分片族项的合法性由纯函数检查直接给出。 -/
@[term_check]
theorem standard_substitution_pieces_sequence_check
    (source : List Nat) (boundToken : Nat) (replacement : List Nat) :
    Term.CheckCertificate
      (standard_substitution_pieces_sequence
        source boundToken replacement) SetSort.set :=
  Term.check_admissible_complete
    (standard_substitution_pieces_sequence_admissible
      source boundToken replacement)
/-- 规范分片族是 closed 对象项。 -/
@[simp]
theorem standard_substitution_pieces_sequence_freeSupport_nil (source : List Nat) (boundToken : Nat) (replacement : List Nat) :
    Term.freeSupport (standard_substitution_pieces_sequence
        source boundToken replacement) = [] := by
  exact seq_support_nil_m 0 (stdsubst_piece_elements_closed
      source boundToken replacement)
/-- 分片族定义域正好等于源 token 串长度。 -/
theorem standard_substitution_pieces_sequence_domain_eq_length (source : List Nat) (boundToken : Nat) (replacement : List Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      domₘ(standard_substitution_pieces_sequence
        source boundToken replacement) ≐ₘ
          numₘ(source.length) := by
  have hDomain := standard_sequence_domain_eq_numeral_length (stdsubst_piece_elements_admissible
      source boundToken replacement) (stdseq_element_fresh_of_support_nil
      (stdsubst_piece_elements_closed source boundToken replacement) 0)
      (stdseq_element_fresh_of_support_nil
        (stdsubst_piece_elements_closed source boundToken replacement) 1)
  simpa [standard_substitution_pieces_sequence,
    substitution_pieces_tokens] using hDomain
/-- 分片族在每个标准指标处求值为相应的标准 token 子串。 -/
theorem standard_substitution_pieces_sequence_apply_getElem? (source : List Nat) (boundToken : Nat) (replacement : List Nat)
    {index : Nat} {piece : List Nat} (hGet : (substitution_pieces_tokens source boundToken replacement)[index]? =
        some piece) :
    ⊢ₘ[standard_sequence_semantics_theory] (standard_substitution_pieces_sequence
          source boundToken replacement ·ₘ numₘ(index)) ≐ₘ
        standard_token_sequence piece := by
  have hMapped : ((substitution_pieces_tokens source boundToken replacement).map
          standard_token_sequence)[index]? =
        some (standard_token_sequence piece) := by
    simpa using congrArg (Option.map standard_token_sequence) hGet
  simpa [standard_substitution_pieces_sequence, standard_sequence] using (standard_sequence_from_apply_getElem?
      0 hMapped (stdsubst_piece_elements_admissible
        source boundToken replacement) (stdsubst_piece_elements_closed
        source boundToken replacement)
      (standard_token_sequence_check piece).admissible)
/--
标准替换结果正是规范分片族经 `flattenₘ` 折叠后的对象。
这里把通用标准序列 flatten 正确性专门实例化到替换分片族；后续
`code_substitution_spec` 只需处理逐点分支，不再接触递归折叠细节。
-/
theorem standard_substitution_pieces_sequence_flatten_eq (source : List Nat) (boundToken : Nat) (replacement : List Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      standard_token_sequence (substitute_tokens source boundToken replacement) ≐ₘ
        flattenₘ(standard_substitution_pieces_sequence
          source boundToken replacement) := by
  simpa [standard_substitution_pieces_sequence,
    substitute_tokens] using (standard_token_sequence_family_flatten (substitution_pieces_tokens source boundToken replacement))
/-- 编码字符串空间由空 token 串见证为非空。 -/
private theorem stdsubst_code_string_ne_empty :
    ⊢ₘ[standard_sequence_semantics_theory]
      CodeStrₘ ≠ₘ ∅ₘ := by
  have hNonempty :=
    member_implies_set_nonempty (standard_token_sequence [])
      CodeStrₘ (standard_token_sequence_check []).admissible
      code_string_space_term_admissible
  have hNonempty' :
      ⊢ₘ[standard_sequence_semantics_theory] (standard_token_sequence [] ∈ₘ CodeStrₘ) ⟶ₘ
          CodeStrₘ ≠ₘ ∅ₘ := by
    exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hFormula)))))
      hNonempty
  exact FirstOrder.Derives.impElim hNonempty' (standard_token_sequence_mem_code_string [])
/-- 规范替换分片族是一个以编码字符串为值的有限序列。 -/
theorem standard_substitution_pieces_sequence_mem_sequence_space (source : List Nat) (boundToken : Nat) (replacement : List Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      standard_substitution_pieces_sequence
          source boundToken replacement ∈ₘ
        seq_spaceₘ(CodeStrₘ) := by
  have hMembers :
      ∀ piece,
        piece ∈ (substitution_pieces_tokens source boundToken replacement).map
              standard_token_sequence →
          ⊢ₘ[standard_sequence_semantics_theory]
            piece ∈ₘ CodeStrₘ := by
    intro piece hPiece
    rcases List.mem_map.mp hPiece with ⟨tokens, _, rfl⟩
    exact standard_token_sequence_mem_code_string tokens
  simpa [standard_substitution_pieces_sequence] using (standard_sequence_mem_sequence_space
      CodeStrₘ (stdsubst_piece_elements_admissible
        source boundToken replacement) (stdsubst_piece_elements_closed
        source boundToken replacement)
      code_string_space_term_admissible
      rfl
      stdsubst_code_string_ne_empty
      hMembers)
/-- `substitution_piece_condition` 去掉定义域 guard 后的点态值条件。 -/
private def stdsubst_piece_value_condition (source boundVariable replacement pieces index : SetTerm) :
    SetFormula := ((((source ·ₘ index) ≐ₘ (boundVariable ·ₘ numₘ(0))) ∧ₘ ((pieces ·ₘ index) ≐ₘ replacement)) ∨ₘ (((source ·ₘ index) ≠ₘ
      (boundVariable ·ₘ numₘ(0))) ∧ₘ ((pieces ·ₘ index) ≐ₘ
        sym_codeₘ(source ·ₘ index))))
/- 点态替换二分的公式合法性由参数项的纯检查证书计算。 -/
@[formula_check]
private theorem stdsubst_piece_value_condition_check
    (source boundVariable replacement pieces index : SetTerm)
    (hSource : Term.CheckCertificate source SetSort.set)
    (hBoundVariable : Term.CheckCertificate boundVariable SetSort.set)
    (hReplacement : Term.CheckCertificate replacement SetSort.set)
    (hPieces : Term.CheckCertificate pieces SetSort.set)
    (hIndex : Term.CheckCertificate index SetSort.set) :
    Formula.CheckCertificate
      (stdsubst_piece_value_condition
        source boundVariable replacement pieces index) := by
  unfold stdsubst_piece_value_condition
  prove_formula_check
/-- 规范分片族在一个具体源位置满足替换规格的点态二分。 -/
private theorem stdsubst_piece_condition_at_numeral (source : List Nat) (boundToken : Nat) (replacement : List Nat)
    (index : Nat) (hIndex : index < source.length) :
    ⊢ₘ[standard_sequence_semantics_theory]
      stdsubst_piece_value_condition (standard_token_sequence source) (standard_token_sequence [boundToken]) (standard_token_sequence replacement)
        (standard_substitution_pieces_sequence
          source boundToken replacement) (numₘ(index)) := by
  let sourceSequence := standard_token_sequence source
  let boundSequence := standard_token_sequence [boundToken]
  let replacementSequence := standard_token_sequence replacement
  let piecesSequence :=
    standard_substitution_pieces_sequence
      source boundToken replacement
  let token := source[index]
  let sourceValue := sourceSequence ·ₘ numₘ(index)
  let boundValue := boundSequence ·ₘ numₘ(0)
  let piecesValue := piecesSequence ·ₘ numₘ(index)
  have hGetSource : source[index]? = some token := by
    simp [token]
  have hGetPieces : (substitution_pieces_tokens source boundToken replacement)[index]? =
        some (substitution_piece_tokens
          boundToken replacement token) := by
    rw [substitution_pieces_tokens_getElem?]
    simp [hGetSource]
  have hSourceValue :
      ⊢ₘ[standard_sequence_semantics_theory]
        sourceValue ≐ₘ numₘ(token) := by
    simpa [sourceValue, sourceSequence, token] using (standard_token_sequence_apply_getElem? source hGetSource)
  have hBoundValue :
      ⊢ₘ[standard_sequence_semantics_theory]
        boundValue ≐ₘ numₘ(boundToken) := by
    have hGet : ([boundToken] : List Nat)[0]? = some boundToken := by
      simp
    simpa [boundValue, boundSequence] using (standard_token_sequence_apply_getElem? [boundToken] hGet)
  have hPiecesValue :
      ⊢ₘ[standard_sequence_semantics_theory]
        piecesValue ≐ₘ
          standard_token_sequence (substitution_piece_tokens
              boundToken replacement token) := by
    simpa [piecesValue, piecesSequence] using (standard_substitution_pieces_sequence_apply_getElem?
        source boundToken replacement hGetPieces)
  have hSourceValueCheck :
      Term.CheckCertificate sourceValue SetSort.set := by
    prove_term_check
  by_cases hToken : token = boundToken
  · have hBoundBack :
        ⊢ₘ[standard_sequence_semantics_theory]
          numₘ(boundToken) ≐ₘ boundValue :=
      Metatheory.Derives.equality_symm hBoundValue
    have hSourceBound :
        ⊢ₘ[standard_sequence_semantics_theory]
          sourceValue ≐ₘ boundValue := by
      exact Metatheory.Derives.equality_trans
        (by simpa [hToken] using hSourceValue) hBoundBack
    have hPieceReplacement :
        ⊢ₘ[standard_sequence_semantics_theory]
          piecesValue ≐ₘ replacementSequence := by
      simpa [replacementSequence, hToken] using hPiecesValue
    exact FirstOrder.Derives.disjIntroLeft
      (FirstOrder.Derives.conjIntro
        hSourceBound hPieceReplacement)
  · have hNumeralNe :
        ⊢ₘ[standard_sequence_semantics_theory]
          ¬ₘ (numₘ(token) ≐ₘ numₘ(boundToken)) :=
      standard_sequence_finite_numeral_ne hToken
    have hSourceBoundNe :
        ⊢ₘ[standard_sequence_semantics_theory]
          ¬ₘ (sourceValue ≐ₘ boundValue) := by
      nd_apply FirstOrder.Derives.negIntro
      let equality : SetFormula := sourceValue ≐ₘ boundValue
      let Γ : Context signature := [equality]
      have hEquality :
          Γ ⊢ₘ[standard_sequence_semantics_theory]
            sourceValue ≐ₘ boundValue := by
        simpa [Γ, equality] using
          (FirstOrder.Derives.assumption
            (T := standard_sequence_semantics_theory)
            (Γ := Γ) (φ := equality) (by simp [Γ]))
      have hSourceBack :
          Γ ⊢ₘ[standard_sequence_semantics_theory]
            numₘ(token) ≐ₘ sourceValue :=
        FirstOrder.Derives.context_weaken_cons <|
          Metatheory.Derives.equality_symm hSourceValue
      have hTokenToBound :
          Γ ⊢ₘ[standard_sequence_semantics_theory]
            numₘ(token) ≐ₘ boundValue :=
        Metatheory.Derives.equality_trans hSourceBack hEquality
      have hNumeralEquality :
          Γ ⊢ₘ[standard_sequence_semantics_theory]
            numₘ(token) ≐ₘ numₘ(boundToken) :=
        Metatheory.Derives.equality_trans
          hTokenToBound (FirstOrder.Derives.context_weaken_cons hBoundValue)
      exact FirstOrder.Derives.negElim hNumeralEquality (FirstOrder.Derives.context_weaken_cons hNumeralNe)
    have hPieceSingleton :
        ⊢ₘ[standard_sequence_semantics_theory]
          piecesValue ≐ₘ standard_token_sequence [token] := by
      simpa [hToken] using hPiecesValue
    have hSingletonCode :
        ⊢ₘ[standard_sequence_semantics_theory]
          standard_token_sequence [token] ≐ₘ
            sym_codeₘ(numₘ(token)) := by
      simpa [standard_token_sequence] using
        (standard_singleton_sequence_eq_symbol_code
          (numₘ(token)) (finite_numeral_term_check token).admissible)
    have hTokenBack :
        ⊢ₘ[standard_sequence_semantics_theory]
          numₘ(token) ≐ₘ sourceValue :=
      Metatheory.Derives.equality_symm hSourceValue
    have hSymbolTransport :
        ⊢ₘ[standard_sequence_semantics_theory]
          sym_codeₘ(numₘ(token)) ≐ₘ
            sym_codeₘ(sourceValue) := by
      let parameter : FreeVarId := 396
      let context : SetTerm := sym_codeₘ(x#parameter)
      have hContextCheck :
          Term.CheckCertificate context SetSort.set := by
        prove_term_check
      have hZeroFixed (candidate : SetTerm) :
          Term.substituteFree SetSort.set parameter candidate (numₘ(0)) =
            numₘ(0) := by
        apply Term.substituteFree_eq_self_of_not_mem
        rw [finite_numeral_term_freeSupport]
        simp
      have hTransported :=
        Metatheory.Derives.term_substituteFree_congr_of_equality (T := standard_sequence_semantics_theory) (Γ := []) SetSort.set parameter
          (numₘ(token)) sourceValue context
          (finite_numeral_term_check token).admissible
          hSourceValueCheck.admissible hContextCheck.admissible (by
            rw [finite_numeral_term_freeSupport]
            simp)
          hTokenBack
      simpa [context, Term.substituteFree, set_variable,
        hZeroFixed] using
        hTransported
    have hPieceCode :
        ⊢ₘ[standard_sequence_semantics_theory]
          piecesValue ≐ₘ sym_codeₘ(sourceValue) := by
      have hPieceNumberCode :=
        Metatheory.Derives.equality_trans
          hPieceSingleton hSingletonCode
      exact Metatheory.Derives.equality_trans
        hPieceNumberCode hSymbolTransport
    exact FirstOrder.Derives.disjIntroRight <|
      FirstOrder.Derives.conjIntro hSourceBoundNe hPieceCode
/-- 点与具体标准下标相等时，点态替换二分可由该下标实例运输得到。 -/
private theorem stdsubst_piece_condition_at_equality (source : List Nat) (boundToken : Nat) (replacement : List Nat)
    (point : SetTerm) (hPoint : Term.CheckCertificate point SetSort.set)
    (index : Nat) (hIndex : index < source.length) :
    ⊢ₘ[standard_sequence_semantics_theory] (point ≐ₘ numₘ(index)) ⟶ₘ
        stdsubst_piece_value_condition (standard_token_sequence source) (standard_token_sequence [boundToken]) (standard_token_sequence replacement)
          (standard_substitution_pieces_sequence
            source boundToken replacement)
          point := by
  let sourceSequence := standard_token_sequence source
  let boundSequence := standard_token_sequence [boundToken]
  let replacementSequence := standard_token_sequence replacement
  let piecesSequence :=
    standard_substitution_pieces_sequence
      source boundToken replacement
  let parameter : FreeVarId := 398
  let body : SetFormula :=
    stdsubst_piece_value_condition
      sourceSequence boundSequence replacementSequence piecesSequence (x#parameter)
  let equality : SetFormula := point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        point ≐ₘ numₘ(index) := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := standard_sequence_semantics_theory)
        (Γ := Γ) (φ := equality) (by simp [Γ]))
  have hSourceFixed (candidate : SetTerm) :
      Term.substituteFree SetSort.set parameter candidate sourceSequence =
        sourceSequence := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport sourceSequence = [] by
      simp [sourceSequence]]
    simp
  have hBoundFixed (candidate : SetTerm) :
      Term.substituteFree SetSort.set parameter candidate boundSequence =
        boundSequence := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport boundSequence = [] by
      simp [boundSequence]]
    simp
  have hReplacementFixed (candidate : SetTerm) :
      Term.substituteFree SetSort.set parameter candidate
          replacementSequence =
        replacementSequence := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport replacementSequence = [] by
      simp [replacementSequence]]
    simp
  have hPiecesFixed (candidate : SetTerm) :
      Term.substituteFree SetSort.set parameter candidate piecesSequence =
        piecesSequence := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport piecesSequence = [] by
      simp [piecesSequence]]
    simp
  have hZeroFixed (candidate : SetTerm) :
      Term.substituteFree SetSort.set parameter candidate (numₘ(0)) =
        numₘ(0) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    simp
  have hBodyCheck : Formula.CheckCertificate body := by
    simpa [body] using
      (stdsubst_piece_value_condition_check
        sourceSequence boundSequence replacementSequence
        piecesSequence (x#parameter)
        (by prove_term_check) (by prove_term_check) (by prove_term_check)
        (by prove_term_check) (by prove_term_check))
  have hIff :=
    Metatheory.Derives.equality_iff_of_equality (T := standard_sequence_semantics_theory) (Γ := Γ) (sort := SetSort.set) (eigen := parameter)
      (left := point) (right := numₘ(index)) (body := body)
      hEquality
  have hTransport :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        stdsubst_piece_value_condition
            sourceSequence boundSequence replacementSequence
            piecesSequence point ↔ₘ
          stdsubst_piece_value_condition
            sourceSequence boundSequence replacementSequence
            piecesSequence (numₘ(index)) := by
    simpa [body, stdsubst_piece_value_condition,
      Formula.substituteFree, Term.substituteFree, set_variable,
      hSourceFixed, hBoundFixed, hReplacementFixed, hPiecesFixed,
      hZeroFixed] using hIff
  have hConcrete :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        stdsubst_piece_value_condition
          sourceSequence boundSequence replacementSequence piecesSequence (numₘ(index)) :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) (by
        simpa [sourceSequence, boundSequence, replacementSequence,
          piecesSequence] using
          stdsubst_piece_condition_at_numeral
            source boundToken replacement index hIndex)
  simpa [Γ, equality, sourceSequence, boundSequence,
    replacementSequence, piecesSequence] using
    FirstOrder.Derives.iffElimLeft hTransport hConcrete
/-- 规范分片族逐点满足 `code_substitution_spec` 要求的替换条件。 -/
theorem standard_substitution_pieces_sequence_pointwise (source : List Nat) (boundToken : Nat) (replacement : List Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      ∀ₘ[SetSort.set],
        substitution_piece_condition (standard_token_sequence source) (standard_token_sequence [boundToken]) (standard_token_sequence replacement)
          (standard_substitution_pieces_sequence
            source boundToken replacement)
          bₛ#0 := by
  let sourceSequence := standard_token_sequence source
  let boundSequence := standard_token_sequence [boundToken]
  let replacementSequence := standard_token_sequence replacement
  let piecesSequence :=
    standard_substitution_pieces_sequence
      source boundToken replacement
  let point : SetTerm := x#397
  let conclusion : SetFormula :=
    stdsubst_piece_value_condition
      sourceSequence boundSequence replacementSequence piecesSequence point
  have hPoint : Term.CheckCertificate point SetSort.set := by
    prove_term_check
  have hConclusion : Formula.CheckCertificate conclusion := by
    simpa [conclusion] using
      (stdsubst_piece_value_condition_check
        sourceSequence boundSequence replacementSequence piecesSequence point
        (by prove_term_check) (by prove_term_check) (by prove_term_check)
        (by prove_term_check) hPoint)
  have hCases :
      ⊢ₘ[standard_sequence_semantics_theory]
        stdseq_numeral_member_condition source.length point ⟶ₘ
          conclusion :=
    stdseq_numeral_member_condition_elim
      source.length point conclusion
      (fun index hIndex => by
        simpa [conclusion, sourceSequence, boundSequence,
          replacementSequence, piecesSequence, point] using
          stdsubst_piece_condition_at_equality
            source boundToken replacement point hPoint index hIndex)
      (hPointCheck := hPoint)
      (hConclusionCheck := hConclusion)
  have hSource : Term.CheckCertificate sourceSequence SetSort.set := by
    prove_term_check
  have hDomain : Term.CheckCertificate (domₘ(sourceSequence)) SetSort.set := by
    prove_term_check
  have hNumeral : Term.CheckCertificate (numₘ(source.length)) SetSort.set := by
    prove_term_check
  have hDomainEq :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(sourceSequence) ≐ₘ numₘ(source.length) := by
    simpa [sourceSequence] using
      standard_token_sequence_domain_eq_length source
  have hDomainIff :=
    membership_right_iff_of_equality
      point (domₘ(sourceSequence)) (numₘ(source.length))
      hPoint.admissible hDomain.admissible hNumeral.admissible hDomainEq
  have hNumeralIff :=
    stdseq_numeral_member_iff source.length point hPoint.admissible
  have hOpen :
      ⊢ₘ[standard_sequence_semantics_theory] (point ∈ₘ domₘ(sourceSequence)) ⟶ₘ conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    have hMembership :
        [point ∈ₘ domₘ(sourceSequence)]
          ⊢ₘ[standard_sequence_semantics_theory]
            point ∈ₘ domₘ(sourceSequence) :=
      FirstOrder.Derives.assumption (by simp)
    have hNumeralMembership := FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hDomainIff)
      hMembership
    have hCondition := FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons hNumeralIff)
      hNumeralMembership
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hCases)
      hCondition
  have hTheoryFresh :
      ∀ formula, standard_sequence_semantics_theory formula → (SetSort.set, 397) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    rw [(standard_sequence_semantics_theory_sentence hFormula).2]
    intro hMember
    cases hMember
  have hSourceClose :
      Term.closeFreeAt SetSort.set 397 0 sourceSequence =
        sourceSequence :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 397 0 sourceSequence hSource.admissible.2 (by
        rw [show Term.freeSupport sourceSequence = [] by
          simp [sourceSequence]]
        simp)
  have hBound : Term.CheckCertificate boundSequence SetSort.set := by
    prove_term_check
  have hBoundClose :
      Term.closeFreeAt SetSort.set 397 0 boundSequence =
        boundSequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 397 0 boundSequence hBound.admissible.2 (by
        rw [show Term.freeSupport boundSequence = [] by
          simp [boundSequence]]
        simp)
  have hReplacement : Term.CheckCertificate replacementSequence SetSort.set := by
    prove_term_check
  have hReplacementClose :
      Term.closeFreeAt SetSort.set 397 0 replacementSequence =
        replacementSequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 397 0 replacementSequence hReplacement.admissible.2 (by
        rw [show Term.freeSupport replacementSequence = [] by
          simp [replacementSequence]]
        simp)
  have hPieces : Term.CheckCertificate piecesSequence SetSort.set := by
    prove_term_check
  have hPiecesClose :
      Term.closeFreeAt SetSort.set 397 0 piecesSequence =
        piecesSequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 397 0 piecesSequence hPieces.admissible.2 (by
        rw [show Term.freeSupport piecesSequence = [] by
          simp [piecesSequence]]
        simp)
  have hZeroClose :
      Term.closeFreeAt SetSort.set 397 0 (numₘ(0)) = numₘ(0) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 397 0 (numₘ(0))
        (finite_numeral_term_check 0).admissible.2
        (by rw [finite_numeral_term_freeSupport]; simp)
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := standard_sequence_semantics_theory) (Γ := []) (sort := SetSort.set) (eigen := 397)
      hTheoryFresh (by simp) hOpen
  simpa [substitution_piece_condition,
    stdsubst_piece_value_condition, conclusion, point,
    Formula.closeFreeAt, Formula.next_depth, Term.closeFreeAt,
    set_variable, hSourceClose, hBoundClose, hReplacementClose,
    hPiecesClose, hZeroClose] using hGeneralized
/--
标准 token 串实现完整满足编码替换规格。
候选结果、源串、变量 singleton 与替换串都由外部 `List Nat` 明确给出；证明内部
见证规范分片族，并依次复用其序列空间成员、定义域、逐点二分和 flatten 正确性。
-/
theorem standard_token_sequence_code_substitution_spec (source : List Nat) (boundToken : Nat) (replacement : List Nat) :
    ⊢ₘ[standard_sequence_semantics_theory]
      code_substitution_spec (standard_token_sequence source) (standard_token_sequence [boundToken]) (standard_token_sequence replacement)
        (standard_token_sequence (substitute_tokens source boundToken replacement)) := by
  let sourceSequence := standard_token_sequence source
  let boundSequence := standard_token_sequence [boundToken]
  let replacementSequence := standard_token_sequence replacement
  let candidateSequence :=
    standard_token_sequence (substitute_tokens source boundToken replacement)
  let piecesSequence :=
    standard_substitution_pieces_sequence
      source boundToken replacement
  have hSource : Term.CheckCertificate sourceSequence SetSort.set := by
    prove_term_check
  have hBound : Term.CheckCertificate boundSequence SetSort.set := by
    prove_term_check
  have hReplacement :
      Term.CheckCertificate replacementSequence SetSort.set := by
    prove_term_check
  have hCandidate :
      Term.CheckCertificate candidateSequence SetSort.set := by
    prove_term_check
  have hPieces : Term.CheckCertificate piecesSequence SetSort.set := by
    prove_term_check
  have hCandidateMember :
      ⊢ₘ[standard_sequence_semantics_theory]
        candidateSequence ∈ₘ CodeStrₘ := by
    simpa [candidateSequence] using
      standard_token_sequence_mem_code_string (substitute_tokens source boundToken replacement)
  have hPiecesMember :
      ⊢ₘ[standard_sequence_semantics_theory]
        piecesSequence ∈ₘ seq_spaceₘ(CodeStrₘ) := by
    simpa [piecesSequence] using
      standard_substitution_pieces_sequence_mem_sequence_space
        source boundToken replacement
  have hPiecesDomain :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(piecesSequence) ≐ₘ numₘ(source.length) := by
    simpa [piecesSequence] using
      standard_substitution_pieces_sequence_domain_eq_length
        source boundToken replacement
  have hSourceDomain :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(sourceSequence) ≐ₘ numₘ(source.length) := by
    simpa [sourceSequence] using
      standard_token_sequence_domain_eq_length source
  have hSourceDomainBack :
      ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(source.length) ≐ₘ domₘ(sourceSequence) :=
    Metatheory.Derives.equality_symm hSourceDomain
  have hDomain :
      ⊢ₘ[standard_sequence_semantics_theory]
        domₘ(piecesSequence) ≐ₘ domₘ(sourceSequence) :=
    Metatheory.Derives.equality_trans hPiecesDomain hSourceDomainBack
  have hPointwise :
      ⊢ₘ[standard_sequence_semantics_theory]
        ∀ₘ[SetSort.set],
          substitution_piece_condition
            sourceSequence boundSequence replacementSequence
            piecesSequence bₛ#0 := by
    simpa [sourceSequence, boundSequence, replacementSequence,
      piecesSequence] using
      standard_substitution_pieces_sequence_pointwise
        source boundToken replacement
  have hFlatten :
      ⊢ₘ[standard_sequence_semantics_theory]
        candidateSequence ≐ₘ flattenₘ(piecesSequence) := by
    simpa [candidateSequence, piecesSequence] using
      standard_substitution_pieces_sequence_flatten_eq
        source boundToken replacement
  have hBody :
      ⊢ₘ[standard_sequence_semantics_theory] (((piecesSequence ∈ₘ seq_spaceₘ(CodeStrₘ)) ∧ₘ (domₘ(piecesSequence) ≐ₘ domₘ(sourceSequence))) ∧ₘ ((∀ₘ[SetSort.set],
            substitution_piece_condition
              sourceSequence boundSequence replacementSequence
              piecesSequence bₛ#0) ∧ₘ (candidateSequence ≐ₘ flattenₘ(piecesSequence)))) :=
    FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro hPiecesMember hDomain) (FirstOrder.Derives.conjIntro hPointwise hFlatten)
  have hSourceOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term sourceSequence =
        sourceSequence :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term sourceSequence hSource.admissible.2
  have hBoundOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term boundSequence =
        boundSequence :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term boundSequence hBound.admissible.2
  have hReplacementOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term replacementSequence =
        replacementSequence :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term replacementSequence hReplacement.admissible.2
  have hCandidateOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term candidateSequence =
        candidateSequence :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term candidateSequence hCandidate.admissible.2
  have hZeroOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term (numₘ(0)) = numₘ(0) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term (numₘ(0))
        (finite_numeral_term_check 0).admissible.2
  have hSourceClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth sourceSequence =
        sourceSequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth sourceSequence hSource.admissible.2 (by
        rw [show Term.freeSupport sourceSequence = [] by
          simp [sourceSequence]]
        exact List.not_mem_nil)
  have hBoundClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth boundSequence =
        boundSequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth boundSequence hBound.admissible.2 (by
        rw [show Term.freeSupport boundSequence = [] by
          simp [boundSequence]]
        exact List.not_mem_nil)
  have hReplacementClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth replacementSequence =
        replacementSequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth replacementSequence hReplacement.admissible.2 (by
        rw [show Term.freeSupport replacementSequence = [] by
          simp [replacementSequence]]
        exact List.not_mem_nil)
  have hCandidateClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth candidateSequence =
        candidateSequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth candidateSequence hCandidate.admissible.2 (by
        rw [show Term.freeSupport candidateSequence = [] by
          simp [candidateSequence]]
        exact List.not_mem_nil)
  have hZeroClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth (numₘ(0)) = numₘ(0) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth (numₘ(0))
        (finite_numeral_term_check 0).admissible.2
        (by rw [finite_numeral_term_freeSupport]; exact List.not_mem_nil)
  have hExists :
      ⊢ₘ[standard_sequence_semantics_theory]
        ∃ₘ[SetSort.set], (((bₛ#0 ∈ₘ seq_spaceₘ(CodeStrₘ)) ∧ₘ (domₘ(bₛ#0) ≐ₘ domₘ(sourceSequence))) ∧ₘ ((∀ₘ[SetSort.set],
              substitution_piece_condition
                sourceSequence boundSequence replacementSequence
                bₛ#1 bₛ#0) ∧ₘ (candidateSequence ≐ₘ flattenₘ(bₛ#0)))) := by
    nd_apply FirstOrder.Derives.exists_intro
      (term := piecesSequence)
      (hTermCheck := hPieces)
    simpa [substitution_piece_condition,
      Formula.openAt, Formula.next_depth, Term.openAt,
      hSourceOpen, hBoundOpen, hReplacementOpen, hCandidateOpen,
      hZeroOpen,
      sourceSequence, boundSequence, replacementSequence,
      candidateSequence, piecesSequence] using hBody
  simpa [code_substitution_spec, substitution_piece_condition,
    Formula.closeFreeAt, Formula.next_depth, Term.closeFreeAt,
    set_variable, set_bound_variable,
    hSourceClose, hBoundClose, hReplacementClose, hCandidateClose,
    hZeroClose, sourceSequence, boundSequence, replacementSequence,
    candidateSequence] using (FirstOrder.Derives.conjIntro hCandidateMember hExists)
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
