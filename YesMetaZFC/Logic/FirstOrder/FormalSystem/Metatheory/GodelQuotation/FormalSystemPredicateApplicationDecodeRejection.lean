import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemTermCodeDecodeClosure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoderComposition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.PredicateElimination
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.StandardOpening
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.HeadedApplicationInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.FamilyDomainElimination
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.FamilySlices
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.FlattenInversion

/-!
# FormalSystem 谓词应用原子的 checked 解码拒绝

本模块把对象内 `TermSeqₘ` 参数族恢复为宿主项 token 切片。若逐项 decoder 全部
成功，则公共谓词组合接口重组父公式；若失败，则对象层对应子项码成员与标准
切片等式交给已闭合的项码拒绝。
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

/-- 首 token 存在时，谓词应用定义条件与完整公式 decoder 失败推出对象矛盾。 -/
private theorem
    gq_predicate_application_condition_decode_falsum_of_head
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat) (token : Nat)
    (hGet : tokens[0]? = some token)
    (hTokens : FSFormulaTokens tokens)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    ⊢ₘ[godel_quotation_theory]
      predicate_application_code_condition
          (standard_token_sequence tokens) ⟶ₘ
        Formula.falsum := by
  let condition : SetFormula :=
    predicate_application_code_condition
      (standard_token_sequence tokens)
  have hCode :
      Term.Admissible
        (standard_token_sequence tokens)
        SetSort.set :=
    standard_token_sequence_admissible tokens
  have hCodeClosed :
      Term.freeSupport
          (standard_token_sequence tokens) =
        [] :=
    standard_token_sequence_freeSupport_nil tokens
  have hCondition :
      Formula.Admissible condition := by
    dsimp only [condition]
    prove_admissible
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [condition]
  have hApplication :
      Γ ⊢ₘ[godel_quotation_theory]
        predicate_application_code_condition
          (standard_token_sequence tokens) := by
    simpa [Γ, condition] using
      (FirstOrder.Derives.assumption
        (T := godel_quotation_theory)
        (Γ := Γ) (φ := condition)
        (by simp [Γ])
        (Formula.check_admissible_complete
          hCondition))
  apply gq_predicate_application_condition_elim_bounded
    tokens token hGet Formula.falsum
    Formula.Admissible.falsum
    (by
      intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      rw [List.eq_nil_iff_forall_not_mem]
      intro freeVariable hMember
      simp [condition,
        predicate_application_code_condition,
        Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList,
        Formula.mem_freeSupport_closeFreeAt_iff,
        hCodeClosed] at hMember
      simp only [finite_numeral_term_freeSupport,
        List.not_mem_nil, or_false] at hMember
      grind)
    (by simp [Formula.freeSupport])
    hApplication
  intro Δ arity index arguments
    _hArityBound _hIndexBound hArguments
    hArgumentsFresh hWeaken
    hTermSequence hDomain
    hSymbolEquality hEquality
  by_cases hHead :
      token =
        Numbered.predicate_token arity index
  · rcases
        fs_formula_token_eq_predicate_token
          (hTokens token <|
            List.mem_of_getElem? hGet)
          hHead with
      ⟨symbol, head, tail, hSymbol,
        hSymbolDomain, hArity, hIndex⟩
    subst arity
    subst index
    let count : Nat :=
      tail.length + 1
    let headCode : SetTerm :=
      coded_predicate_symbol_code_term
        (numₘ(tail.length))
        (numₘ(symbol.ctorIdx))
    let bodyCode : SetTerm :=
      flattenₘ(arguments)
    let parent : SetTerm :=
      predicate_application_code_term
        (numₘ(tail.length))
        (numₘ(symbol.ctorIdx))
        arguments
    have hDomainCount :
        Δ ⊢ₘ[godel_quotation_theory]
          domₘ(arguments) ≐ₘ numₘ(count) := by
      simpa [count] using hDomain
    have hFamily :
        Δ ⊢ₘ[godel_quotation_theory]
          finite_sequence_family_condition
            arguments :=
      gq_term_sequence_member_implies_family_condition
        arguments hArguments hArgumentsFresh
        hTermSequence
    have hBodyFinite :
        Δ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition bodyCode := by
      simpa [bodyCode] using
        gq_term_sequence_member_implies_flatten_finite
          arguments hArguments hArgumentsFresh
          hTermSequence
    have hHeadEquality :
        Δ ⊢ₘ[godel_quotation_theory]
          headCode ≐ₘ
            standard_token_sequence
              [Numbered.predicate_token
                tail.length symbol.ctorIdx] :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) <| by
          simpa [headCode] using
            coded_predicate_symbol_code_eq_standard_token_sequence
              tail.length symbol.ctorIdx
    have hHeadFinite :
        Δ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition headCode :=
      gq_finite_sequence_of_eq_standard_token_sequence
        headCode
        [Numbered.predicate_token
          tail.length symbol.ctorIdx]
        hHeadEquality
    have hHeadDomain :
        Δ ⊢ₘ[godel_quotation_theory]
          domₘ(headCode) ≐ₘ numₘ(1) := by
      simpa using
        gq_domain_eq_length_of_eq_standard_token_sequence_of_theory
          (fun _ hAxiom => hAxiom)
          headCode
          [Numbered.predicate_token
            tail.length symbol.ctorIdx]
          hHeadEquality
    by_cases hLeft :
        tokens[1]? =
          some (Numbered.logical_token
            .leftParenthesis)
    · apply gq_finite_family_domain_lengths_elim
        arguments parent tokens 0 count
        Formula.falsum
        (hMember := by
          intro offset hOffset
          simpa [parent, headCode, bodyCode,
            headed_application_code_term] using
            gq_headed_application_family_piece_domain_member
              (Γ := Δ)
              headCode arguments count offset
              (by
                simpa [headCode] using
                  coded_predicate_symbol_code_term_admissible
                    (numₘ(tail.length))
                    (numₘ(symbol.ctorIdx))
                    (finite_numeral_term_admissible
                      tail.length)
                    (finite_numeral_term_admissible
                      symbol.ctorIdx))
              hArguments
              hHeadFinite hHeadDomain
              hFamily hDomainCount hOffset)
        (hEquality := by
          simpa [parent, count] using hEquality)
      intro lengths hLengths
      let Λ : Context signature :=
        finite_family_domain_length_context
            arguments 0 lengths ++ Δ
      have hWeakenΔΛ :
          ∀ formula, formula ∈ Δ →
            formula ∈ Λ := by
        intro formula hFormula
        exact List.mem_append.mpr
          (Or.inr hFormula)
      have hTermSequenceΛ :
          Λ ⊢ₘ[godel_quotation_theory]
            arguments ∈ₘ TermSeqₘ :=
        FirstOrder.Derives.context_weaken
          (Γ := Δ) (Δ := Λ)
          hWeakenΔΛ hTermSequence
      have hDomainΛ :
          Λ ⊢ₘ[godel_quotation_theory]
            domₘ(arguments) ≐ₘ numₘ(count) :=
        FirstOrder.Derives.context_weaken
          (Γ := Δ) (Δ := Λ)
          hWeakenΔΛ hDomainCount
      have hFamilyΛ :
          Λ ⊢ₘ[godel_quotation_theory]
            finite_sequence_family_condition
              arguments :=
        FirstOrder.Derives.context_weaken
          (Γ := Δ) (Δ := Λ)
          hWeakenΔΛ hFamily
      have hEqualityΛ :
          Λ ⊢ₘ[godel_quotation_theory]
            standard_token_sequence tokens ≐ₘ
              parent :=
        FirstOrder.Derives.context_weaken
          (Γ := Δ) (Δ := Λ)
          hWeakenΔΛ <| by
            simpa [parent, count] using hEquality
      have hHeadEqualityΛ :
          Λ ⊢ₘ[godel_quotation_theory]
            headCode ≐ₘ
              standard_token_sequence
                [Numbered.predicate_token
                  tail.length symbol.ctorIdx] :=
        FirstOrder.Derives.context_weaken
          (Γ := Δ) (Δ := Λ)
          hWeakenΔΛ hHeadEquality
      have hHeadFiniteΛ :
          Λ ⊢ₘ[godel_quotation_theory]
            finite_sequence_condition headCode :=
        FirstOrder.Derives.context_weaken
          (Γ := Δ) (Δ := Λ)
          hWeakenΔΛ hHeadFinite
      have hHeadDomainΛ :
          Λ ⊢ₘ[godel_quotation_theory]
            domₘ(headCode) ≐ₘ numₘ(1) :=
        FirstOrder.Derives.context_weaken
          (Γ := Δ) (Δ := Λ)
          hWeakenΔΛ hHeadDomain
      have hBodyFiniteΛ :
          Λ ⊢ₘ[godel_quotation_theory]
            finite_sequence_condition bodyCode :=
        FirstOrder.Derives.context_weaken
          (Γ := Δ) (Δ := Λ)
          hWeakenΔΛ hBodyFinite
      have hPieceDomain :
          ∀ offset, offset < count →
            Λ ⊢ₘ[godel_quotation_theory]
              domₘ(arguments ·ₘ numₘ(offset)) ≐ₘ
                numₘ(finite_family_piece_length
                  lengths offset) := by
        intro offset hOffset
        have hOffsetLength :
            offset < lengths.length := by
          simpa [hLengths] using hOffset
        simpa [Λ] using
          gq_finite_family_domain_length_context_piece
            (Γ := Δ)
            arguments 0 lengths offset
            hOffsetLength
      have hFlattenDomainRaw :=
        gq_flatten_numeral_domain_eq_prefix_length
          (Γ := Λ)
          arguments count
          (finite_family_piece_length lengths)
          (finite_family_prefix_length lengths)
          hArguments hFamilyΛ hDomainΛ
          (finite_family_prefix_length_zero lengths)
          (fun offset _ =>
            finite_family_prefix_length_step
              lengths offset)
          hPieceDomain
      have hPrefixEnd :
          finite_family_prefix_length
              lengths count =
            lengths.sum := by
        rw [← hLengths]
        exact finite_family_prefix_length_at_end
          lengths
      have hFlattenDomain :
          Λ ⊢ₘ[godel_quotation_theory]
            domₘ(bodyCode) ≐ₘ
              numₘ(lengths.sum) := by
        rw [hPrefixEnd] at hFlattenDomainRaw
        simpa [bodyCode] using hFlattenDomainRaw
      by_cases hLength :
          tokens.length =
            2 + lengths.sum + 1
      · let flatTokens : List Nat :=
          (tokens.drop 2).take lengths.sum
        let slices : List (List Nat) :=
          finite_family_slices lengths flatTokens
        have hSliceBound :
            2 + lengths.sum ≤ tokens.length := by
          omega
        have hFlattenEquality :
            Λ ⊢ₘ[godel_quotation_theory]
              bodyCode ≐ₘ
                standard_token_sequence flatTokens := by
          simpa [flatTokens, parent, bodyCode,
            headCode, headed_application_code_term] using
            gq_headed_application_body_eq_standard_slice
              (Γ := Λ)
              (Numbered.predicate_token
                tail.length symbol.ctorIdx)
              headCode bodyCode tokens lengths.sum
              (by
                simpa [headCode] using
                  coded_predicate_symbol_code_term_admissible
                    (numₘ(tail.length))
                    (numₘ(symbol.ctorIdx))
                    (finite_numeral_term_admissible
                      tail.length)
                    (finite_numeral_term_admissible
                      symbol.ctorIdx))
              (by
                simpa [bodyCode] using
                  finite_sequence_flatten_term_admissible
                    arguments hArguments)
              hHeadEqualityΛ hBodyFiniteΛ
              hFlattenDomain hEqualityΛ hSliceBound
        have hStandardFlatten :
            Λ ⊢ₘ[godel_quotation_theory]
              standard_token_sequence flatTokens ≐ₘ
                bodyCode :=
          Metatheory.Derives.equality_symm
            hFlattenEquality
        have hFlatTokensLength :
            flatTokens.length = lengths.sum := by
          simp only [flatTokens, List.length_take,
            List.length_drop]
          omega
        have hSlicesLength :
            slices.length = lengths.length := by
          change
            (finite_family_slices
              lengths flatTokens).length =
              lengths.length
          exact finite_family_slices_length
            lengths flatTokens
        have hSlicesFlatten :
            slices.flatten = flatTokens := by
          simpa [slices] using
            finite_family_slices_flatten_eq_self
              lengths flatTokens
              hFlatTokensLength.symm
        have hSlicesFlattenLength :
            slices.flatten.length = lengths.sum := by
          rw [hSlicesFlatten, hFlatTokensLength]
        by_cases hRight :
            tokens[2 + lengths.sum]? =
              some (Numbered.logical_token
                .rightParenthesis)
        · have hHeadConcrete :
              tokens[0]? =
                some (Numbered.predicate_token
                  tail.length symbol.ctorIdx) := by
            simpa [hHead] using hGet
          have hWholeLength :
              tokens.length =
                2 + slices.flatten.length + 1 := by
            omega
          have hWholeBody :
              slices.flatten =
                (tokens.drop 2).take
                  slices.flatten.length := by
            calc
              slices.flatten = flatTokens :=
                hSlicesFlatten
              _ = (tokens.drop 2).take
                  lengths.sum := rfl
              _ = (tokens.drop 2).take
                  slices.flatten.length := by
                rw [hSlicesFlattenLength]
          have hWholeRight :
              tokens[2 + slices.flatten.length]? =
                some (Numbered.logical_token
                  .rightParenthesis) := by
            simpa [hSlicesFlattenLength] using hRight
          have hWholeRaw :=
            fs_headed_application_tokens_eq_of_slice
              tokens slices.flatten
              (Numbered.predicate_token
                tail.length symbol.ctorIdx)
              hWholeLength hHeadConcrete hLeft
              hWholeBody hWholeRight
          have hWhole :
              Numbered.predicate_application_tokens
                  tail.length symbol.ctorIdx slices =
                tokens := by
            simpa [Numbered.predicate_application_tokens]
              using hWholeRaw
          cases hMap :
              slices.mapM
                (fs_named_term_tokens_decode_with_env
                  freeBase boundNames) with
          | some decodedArguments =>
              have hDecodedLength :=
                fs_option_mapM_length hMap
              have hDecodedArity :
                  decodedArguments.length =
                    (signature.relDomain symbol).length := by
                calc
                  decodedArguments.length =
                      slices.length := hDecodedLength
                  _ = lengths.length := hSlicesLength
                  _ = count := hLengths
                  _ =
                      (signature.relDomain symbol).length := by
                    simp [count, hSymbolDomain]
              have hDecodedPredecessor :
                  decodedArguments.length - 1 =
                    tail.length := by
                rw [hDecodedArity, hSymbolDomain]
                simp
              have hSuccess :=
                fs_named_hilbert_tokens_decode_with_env_predicate_of_term_token_lists
                  freeBase boundNames symbol hSymbol
                  hMap hDecodedArity
              have hSuccessAtTokens :
                  fs_named_hilbert_tokens_decode_with_env
                      freeBase boundNames tokens =
                    some (.rel symbol decodedArguments) := by
                rw [← hWhole]
                simpa [hDecodedPredecessor] using hSuccess
              rw [hDecode] at hSuccessAtTokens
              contradiction
          | none =>
              rcases
                  fs_option_mapM_none_exists
                    (fs_named_term_tokens_decode_with_env
                      freeBase boundNames)
                    hMap with
                ⟨piece, hPieceMember, hPieceDecode⟩
              rcases List.getElem_of_mem hPieceMember with
                ⟨offset, hOffsetSlices, hPieceValue⟩
              have hOffsetLengths :
                  offset < lengths.length := by
                simpa [hSlicesLength] using
                  hOffsetSlices
              have hOffsetCount :
                  offset < count := by
                simpa [hLengths] using hOffsetLengths
              have hPieceGet :
                  slices[offset]? = some piece :=
                List.getElem?_eq_some_iff.mpr
                  ⟨hOffsetSlices, hPieceValue⟩
              have hCanonical :=
                finite_family_slices_getElem?
                  lengths flatTokens offset
                  hOffsetLengths
              rw [hPieceGet] at hCanonical
              have hPieceCanonical :
                  piece =
                    ((flatTokens.drop
                        (finite_family_prefix_length
                          lengths offset)).take
                      (finite_family_piece_length
                        lengths offset)) :=
                Option.some.inj hCanonical
              have hPieceLength :
                  piece.length =
                    finite_family_piece_length
                      lengths offset :=
                finite_family_slice_length_of_getElem?
                  lengths flatTokens piece offset
                  hOffsetLengths
                  hFlatTokensLength.symm
                  hPieceGet
              have hPieceBound :=
                finite_family_prefix_add_piece_le_sum
                  lengths offset hOffsetLengths
              have hPieceSliceBound :
                  finite_family_prefix_length
                        lengths offset +
                      finite_family_piece_length
                        lengths offset ≤
                    flatTokens.length := by
                rw [hFlatTokensLength]
                exact hPieceBound
              have hPieceTokens :
                  FSFormulaTokens piece := by
                intro pieceToken hPieceToken
                have hFlatMember :=
                  finite_family_slice_mem_source
                    lengths flatTokens piece
                    hPieceMember hPieceToken
                have hDropMember :
                    pieceToken ∈ tokens.drop 2 :=
                  List.mem_of_mem_take hFlatMember
                exact hTokens pieceToken
                  (List.mem_of_mem_drop hDropMember)
              have hChildMember :
                  Λ ⊢ₘ[godel_quotation_theory]
                    (arguments ·ₘ numₘ(offset)) ∈ₘ
                      TermCodeₘ :=
                gq_term_sequence_argument_member
                  arguments count offset
                  hArguments hArgumentsFresh
                  hTermSequenceΛ hDomainΛ hOffsetCount
              have hChildEqualityRaw :=
                gq_flatten_numeral_point_eq_standard_slice
                  (Γ := Λ)
                  arguments flatTokens
                  count offset
                  (finite_family_piece_length lengths)
                  (finite_family_prefix_length lengths)
                  hArguments hFamilyΛ hDomainΛ
                  (finite_family_prefix_length_zero
                    lengths)
                  (fun index _ =>
                    finite_family_prefix_length_step
                      lengths index)
                  hPieceDomain hStandardFlatten
                  hOffsetCount hPieceSliceBound
              have hChildEquality :
                  Λ ⊢ₘ[godel_quotation_theory]
                    (arguments ·ₘ numₘ(offset)) ≐ₘ
                      standard_token_sequence piece := by
                simpa [bodyCode, ← hPieceCanonical] using
                  hChildEqualityRaw
              exact
                gq_term_child_falsum_of_standard_rejection
                  (arguments ·ₘ numₘ(offset))
                  piece
                  (function_application_term_admissible
                    arguments (numₘ(offset))
                    hArguments
                    (finite_numeral_term_admissible
                      offset))
                  hChildMember hChildEquality
                  (gq_standard_term_code_not_of_decode_none
                    freeBase boundNames piece
                    hPieceTokens hPieceDecode)
        · exact
            gq_headed_application_standard_falsum_of_last_not_right
              headCode bodyCode tokens lengths.sum
              (by
                simpa [headCode] using
                  coded_predicate_symbol_code_term_admissible
                    (numₘ(tail.length))
                    (numₘ(symbol.ctorIdx))
                    (finite_numeral_term_admissible
                      tail.length)
                    (finite_numeral_term_admissible
                      symbol.ctorIdx))
              (by
                simpa [bodyCode] using
                  finite_sequence_flatten_term_admissible
                    arguments hArguments)
              hHeadFiniteΛ hHeadDomainΛ
              hBodyFiniteΛ hFlattenDomain
              (by
                simpa [parent, headCode, bodyCode,
                  headed_application_code_term] using
                  hEqualityΛ)
              hRight
      · exact
          gq_headed_application_standard_falsum_of_length_ne
            headCode bodyCode tokens lengths.sum
            (by
              simpa [headCode] using
                coded_predicate_symbol_code_term_admissible
                  (numₘ(tail.length))
                  (numₘ(symbol.ctorIdx))
                  (finite_numeral_term_admissible
                    tail.length)
                  (finite_numeral_term_admissible
                    symbol.ctorIdx))
            (by
              simpa [bodyCode] using
                finite_sequence_flatten_term_admissible
                  arguments hArguments)
            hHeadFiniteΛ hHeadDomainΛ
            hBodyFiniteΛ hFlattenDomain
            (by
              simpa [parent, headCode, bodyCode,
                headed_application_code_term] using
                hEqualityΛ)
            hLength
    · have hOpening :=
        FirstOrder.Derives.impElim
            (gq_predicate_application_formula_opening_inversion
              (Γ := Δ)
            (numₘ(tail.length))
            (numₘ(symbol.ctorIdx))
            arguments
            (finite_numeral_term_admissible tail.length)
            (finite_numeral_term_admissible
              symbol.ctorIdx)
            hArguments
            (reserved_ids_fresh_cons_closed
              (finite_numeral_term_freeSupport
                tail.length)
              (reserved_ids_fresh_cons_closed
                (finite_numeral_term_freeSupport
                  symbol.ctorIdx)
                (reserved_ids_fresh_nil [0, 1, 2])))
            hArgumentsFresh)
          hTermSequence
      exact
        gq_standard_token_sequence_falsum_of_point_not_expected
          tokens parent 1
          (Numbered.logical_token .leftParenthesis)
          hLeft
          (by simpa [parent, count] using hEquality)
          (by
            simpa [parent, count] using
              FirstOrder.Derives.conjElimRight
                hOpening)
  · exact FirstOrder.Derives.negElim
      hSymbolEquality
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) <|
          gq_symbol_code_ne_of_token_ne
            (coded_predicate_symbol_code_term
              (numₘ(arity)) (numₘ(index)))
            token
            (Numbered.predicate_token arity index)
            (coded_predicate_symbol_code_term_admissible
              (numₘ(arity)) (numₘ(index))
              (finite_numeral_term_admissible arity)
              (finite_numeral_term_admissible index))
            (coded_predicate_symbol_code_eq_standard_token_sequence
              arity index)
            hHead)

/--
有限签名检查通过时，谓词应用定义条件与 checked 公式 decoder 的具体失败矛盾。
-/
theorem gq_predicate_application_condition_decode_falsum
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat)
    (hTokens : FSFormulaTokens tokens)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    ⊢ₘ[godel_quotation_theory]
      predicate_application_code_condition
          (standard_token_sequence tokens) ⟶ₘ
        Formula.falsum := by
  cases tokens with
  | nil =>
      let code : SetTerm :=
        standard_token_sequence []
      let condition : SetFormula :=
        predicate_application_code_condition code
      have hCode :
          Term.Admissible code SetSort.set := by
        simpa [code] using
          standard_token_sequence_admissible []
      have hClosed :
          Term.freeSupport code = [] := by
        simp [code]
      have hFresh :
          ReservedIdsFresh [230, 231, 232] [code] :=
        reserved_ids_fresh_cons_closed hClosed <|
          reserved_ids_fresh_nil [230, 231, 232]
      have hCondition :
          Formula.Admissible condition := by
        dsimp only [condition]
        prove_admissible
      change
        ⊢ₘ[godel_quotation_theory]
          condition ⟶ₘ Formula.falsum
      nd_apply FirstOrder.Derives.impIntro
      let Γ : Context signature := [condition]
      have hAt :
          Γ ⊢ₘ[godel_quotation_theory]
            condition :=
        FirstOrder.Derives.assumption
          (by simp [Γ])
          (Formula.check_admissible_complete
            hCondition)
      have hOpening :
          Γ ⊢ₘ[godel_quotation_theory]
            formula_code_left_opening_condition code :=
        FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Γ) (by simp [Γ]) <|
              gq_predicate_application_condition_implies_opening
                code hCode hFresh)
          hAt
      simpa [code] using
        gq_standard_token_sequence_falsum_of_no_left_opening
          (Γ := Γ) []
          (by simp) (by simp) hOpening
  | cons token tail =>
      exact
        gq_predicate_application_condition_decode_falsum_of_head
          freeBase boundNames (token :: tail) token
          (by simp) hTokens hDecode

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
