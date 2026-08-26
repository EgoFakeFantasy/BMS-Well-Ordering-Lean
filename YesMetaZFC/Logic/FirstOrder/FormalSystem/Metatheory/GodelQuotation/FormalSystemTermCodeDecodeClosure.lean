import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.TermCodeInversion.ApplicationElimination
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.FamilyPositive
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.FamilyDomainElimination
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.FamilySlices
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.FlattenInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaTokenDecision

/-!
# FormalSystem 项码 checked 解码闭合

本模块把标准项 token decoder 的失败按长度强归纳翻译为对象层 `TermCodeₘ`
成员否定。所有递归调用都先把对象子项运输为闭的标准 token 序列。
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

/-- 相对于当前父串的严格短串项码拒绝族。 -/
def FSTermDecodeRejectionBelow
    (freeBase : Nat) (tokens : List Nat) : Prop :=
  ∀ (boundNames : List Nat) (childTokens : List Nat),
    childTokens.length < tokens.length →
      FSFormulaTokens childTokens →
        fs_named_term_tokens_decode_with_env
            freeBase boundNames childTokens =
          none →
          ⊢ₘ[godel_quotation_theory]
            ¬ₘ (standard_token_sequence childTokens ∈ₘ
              TermCodeₘ)

/--
对象子项等于标准短串时，把项码成员运输到标准闭码，再由短串拒绝结束当前上下文。
-/
theorem gq_term_child_falsum_of_standard_rejection
    {Γ : Context signature}
    (child : SetTerm) (childTokens : List Nat)
    (hChild : Term.Admissible child SetSort.set)
    (hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        child ∈ₘ TermCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        child ≐ₘ standard_token_sequence childTokens)
    (hReject :
      ⊢ₘ[godel_quotation_theory]
        ¬ₘ (standard_token_sequence childTokens ∈ₘ
          TermCodeₘ)) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  have hStandardMember :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence childTokens ∈ₘ
          TermCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (membership_left_iff_of_equality
        child
        (standard_token_sequence childTokens)
        TermCodeₘ
        hChild
        (standard_token_sequence_admissible childTokens)
        term_code_set_term_admissible
        hEquality)
      hMember
  exact FirstOrder.Derives.negElim
    hStandardMember
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      hReject)

/-- 参数域与逐点项码条件在任一有效外部下标上给出具体子项成员。 -/
theorem gq_term_application_argument_member
    {Γ : Context signature}
    (arguments : SetTerm)
    (count index : Nat)
    (hArguments :
      Term.Admissible arguments SetSort.set)
    (hFresh :
      (SetSort.set, 213) ∉
        Term.freeSupport arguments)
    (hDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(arguments) ≐ₘ numₘ(count))
    (hValues :
      Γ ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, 213],
          (x#213 ∈ₘ domₘ(arguments)) ⟶ₘ
            ((arguments ·ₘ x#213) ∈ₘ TermCodeₘ))
    (hIndex : index < count) :
    Γ ⊢ₘ[godel_quotation_theory]
      (arguments ·ₘ numₘ(index)) ∈ₘ
        TermCodeₘ := by
  have hNumeral :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ numₘ(count) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_mem_of_lt
            index count hIndex
  have hDomainMember :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(arguments) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(index))
        (domₘ(arguments))
        (numₘ(count))
        (finite_numeral_term_admissible index)
        (domain_term_admissible
          arguments hArguments)
        (finite_numeral_term_admissible count)
        hDomain)
      hNumeral
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := numₘ(index)) hValues
  have hArgumentsClose :
      Term.closeFreeAt SetSort.set 213 0 arguments =
        arguments :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 213 0 arguments
      hArguments.2 hFresh
  have hArgumentsOpen :
      Term.openAt SetSort.set 0
          (numₘ(index)) arguments =
        arguments :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (numₘ(index))
      arguments hArguments.2
  have hImp :
      Γ ⊢ₘ[godel_quotation_theory]
        (numₘ(index) ∈ₘ domₘ(arguments)) ⟶ₘ
          ((arguments ·ₘ numₘ(index)) ∈ₘ
            TermCodeₘ) := by
    simpa [Formula.openAt, Formula.next_depth,
      Formula.closeFreeAt, Term.closeFreeAt,
      Term.openAt, set_variable, set_bound_variable,
      domain_term, function_application_term,
      finite_numeral_term, hArgumentsClose,
      hArgumentsOpen] using hAt
  exact FirstOrder.Derives.impElim
    hImp hDomainMember

/--
项应用生成分支在完整 decoder 失败时推出对象矛盾。

参数长度由父标准码定义域有界消去；宿主 `mapM` 成功时重组父项，失败时定位一个
严格短子片并调用长度归纳拒绝。
-/
theorem gq_term_application_decode_falsum
    {Γ : Context signature}
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat) (token : Nat)
    (hGet : tokens[0]? = some token)
    (hLeft :
      tokens[1]? =
        some (Numbered.logical_token
          .leftParenthesis))
    (hToken : FSFormulaToken token)
    (hTokens : FSFormulaTokens tokens)
    (hRejectBelow :
      FSTermDecodeRejectionBelow freeBase tokens)
    (hDecode :
      fs_named_term_tokens_decode_with_env
          freeBase boundNames tokens =
        none)
    (hContextClosed :
      ∀ formula, formula ∈ Γ →
        Formula.freeSupport formula = [])
    (hApplication :
      Γ ⊢ₘ[godel_quotation_theory]
        term_application_from_condition
          TermCodeₘ
          (standard_token_sequence tokens)) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  apply gq_term_application_from_condition_elim_bounded
    tokens token hGet Formula.falsum
    Formula.Admissible.falsum
    hContextClosed
    (by simp [Formula.freeSupport])
    hApplication
  intro Δ arity index arguments
    hArityBound hIndexBound hArguments
    hArgumentsFresh hWeaken
    hPositive hDomain hValues
    hSymbolEquality hEquality
  by_cases hHead :
      token =
        Numbered.function_token arity index
  · rcases
        fs_formula_token_eq_function_token
          hToken hHead with
      ⟨symbol, head, tail, hSymbolDomain,
        hArity, hIndex⟩
    subst arity
    subst index
    let parent : SetTerm :=
      term_application_code_term
        (numₘ(tail.length))
        (numₘ(symbol.ctorIdx))
        arguments
    have hSymbolDomainLength :
        (signature.funcDomain symbol).length =
          tail.length + 1 := by
      simp [hSymbolDomain]
    apply gq_finite_family_domain_lengths_elim
      arguments parent tokens 0 (tail.length + 1)
      Formula.falsum
      (hMember := by
        intro offset hOffset
        simpa [parent] using
          gq_term_application_code_argument_domain_member
            (Γ := Δ)
            tail.length symbol.ctorIdx offset
            arguments hArguments hPositive
            hDomain hOffset)
      (hEquality := by
        simpa [parent] using hEquality)
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
    have hPositiveΛ :
        Λ ⊢ₘ[godel_quotation_theory]
          arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ) :=
      FirstOrder.Derives.context_weaken
        (Γ := Δ) (Δ := Λ)
        hWeakenΔΛ hPositive
    have hDomainΛ :
        Λ ⊢ₘ[godel_quotation_theory]
          domₘ(arguments) ≐ₘ
            numₘ(tail.length + 1) :=
      FirstOrder.Derives.context_weaken
        (Γ := Δ) (Δ := Λ)
        hWeakenΔΛ hDomain
    have hValuesΛ :
        Λ ⊢ₘ[godel_quotation_theory]
          ∀ₘ[SetSort.set, 213],
            (x#213 ∈ₘ domₘ(arguments)) ⟶ₘ
              ((arguments ·ₘ x#213) ∈ₘ
                TermCodeₘ) :=
      FirstOrder.Derives.context_weaken
        (Γ := Δ) (Δ := Λ)
        hWeakenΔΛ hValues
    have hEqualityΛ :
        Λ ⊢ₘ[godel_quotation_theory]
          standard_token_sequence tokens ≐ₘ
            term_application_code_term
              (numₘ(tail.length))
              (numₘ(symbol.ctorIdx))
              arguments :=
      FirstOrder.Derives.context_weaken
        (Γ := Δ) (Δ := Λ)
        hWeakenΔΛ hEquality
    have hFamily :
        Λ ⊢ₘ[godel_quotation_theory]
          finite_sequence_family_condition
            arguments :=
      gq_code_string_positive_sequence_member_implies_family_condition
        arguments hArguments hPositiveΛ
    have hPieceDomain :
        ∀ offset, offset < tail.length + 1 →
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
        arguments (tail.length + 1)
        (finite_family_piece_length lengths)
        (finite_family_prefix_length lengths)
        hArguments hFamily hDomainΛ
        (finite_family_prefix_length_zero lengths)
        (fun offset _ =>
          finite_family_prefix_length_step
            lengths offset)
        hPieceDomain
    have hPrefixEnd :
        finite_family_prefix_length
            lengths (tail.length + 1) =
          lengths.sum := by
      rw [← hLengths]
      exact finite_family_prefix_length_at_end
        lengths
    have hFlattenDomain :
        Λ ⊢ₘ[godel_quotation_theory]
          domₘ(flattenₘ(arguments)) ≐ₘ
            numₘ(lengths.sum) := by
      rw [hPrefixEnd] at hFlattenDomainRaw
      exact hFlattenDomainRaw
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
            flattenₘ(arguments) ≐ₘ
              standard_token_sequence flatTokens := by
        simpa [flatTokens] using
          gq_term_application_flatten_eq_standard_slice_of_domain
            (Γ := Λ)
            tail.length symbol.ctorIdx
            arguments tokens lengths.sum
            hArguments hPositiveΛ
            hFlattenDomain hEqualityΛ
            hSliceBound
      have hStandardFlatten :
          Λ ⊢ₘ[godel_quotation_theory]
            standard_token_sequence flatTokens ≐ₘ
              flattenₘ(arguments) :=
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
          (finite_family_slices lengths flatTokens).length =
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
              some (Numbered.function_token
                tail.length symbol.ctorIdx) := by
          simpa [hHead] using hGet
        have hWholeLength :
            tokens.length =
              2 + slices.flatten.length + 1 := by
          omega
        have hWholeMiddle :
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
        have hWhole :
            Numbered.function_application_tokens
                tail.length symbol.ctorIdx slices =
              tokens :=
          fs_function_application_tokens_eq_of_slice
            tokens slices tail.length symbol.ctorIdx
            hWholeLength hHeadConcrete hLeft
            hWholeMiddle hWholeRight
        cases hMap :
            slices.mapM
              (fs_named_term_tokens_decode_with_env
                freeBase boundNames) with
        | some decodedArguments =>
            have hDecodedLength :=
              fs_option_mapM_length hMap
            have hDecoderArity :
                decodedArguments.length =
                  (signature.funcDomain symbol).length := by
              calc
                decodedArguments.length =
                    slices.length := hDecodedLength
                _ = lengths.length := hSlicesLength
                _ = tail.length + 1 := hLengths
                _ =
                    (signature.funcDomain symbol).length :=
                  hSymbolDomainLength.symm
            have hDecodedArity :
                decodedArguments.length - 1 =
                  tail.length := by
              rw [hDecoderArity,
                hSymbolDomainLength]
              omega
            have hDecodedPositive :
                decodedArguments ≠ [] := by
              intro hNil
              have hLength :
                  decodedArguments.length =
                    tail.length + 1 := by
                calc
                  decodedArguments.length =
                      slices.length := hDecodedLength
                  _ = lengths.length := hSlicesLength
                  _ = tail.length + 1 := hLengths
              rw [hNil] at hLength
              simp at hLength
            have hSuccess :=
              fs_named_term_token_lists_decode_with_env_application
                freeBase boundNames symbol
                hMap hDecoderArity hDecodedPositive
            have hSuccessAtTokens :
                fs_named_term_tokens_decode_with_env
                    freeBase boundNames tokens =
                  some (.app symbol decodedArguments) := by
              rw [← hWhole]
              simpa [hDecodedArity] using hSuccess
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
                offset < tail.length + 1 := by
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
            have hPieceShort :
                piece.length < tokens.length := by
              omega
            have hPieceTokens :
                FSFormulaTokens piece := by
              intro pieceToken hPieceToken
              have hFlatMember :=
                finite_family_slice_mem_source
                  lengths flatTokens piece
                  hPieceMember hPieceToken
              have hDropMember :
                  pieceToken ∈ tokens.drop 2 := by
                exact List.mem_of_mem_take hFlatMember
              exact hTokens pieceToken
                (List.mem_of_mem_drop hDropMember)
            have hChildMember :
                Λ ⊢ₘ[godel_quotation_theory]
                  (arguments ·ₘ numₘ(offset)) ∈ₘ
                    TermCodeₘ :=
              gq_term_application_argument_member
                arguments (tail.length + 1) offset
                hArguments hArgumentsFresh
                hDomainΛ hValuesΛ hOffsetCount
            have hChildEqualityRaw :=
              gq_flatten_numeral_point_eq_standard_slice
                (Γ := Λ)
                arguments flatTokens
                (tail.length + 1) offset
                (finite_family_piece_length lengths)
                (finite_family_prefix_length lengths)
                hArguments hFamily hDomainΛ
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
              simpa [← hPieceCanonical] using
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
                (hRejectBelow boundNames piece
                  hPieceShort hPieceTokens
                  hPieceDecode)
      · exact
          gq_term_application_standard_code_falsum_of_last_not_right
            (Γ := Λ)
            tail.length symbol.ctorIdx
            arguments tokens lengths.sum
            hArguments hPositiveΛ
            hFlattenDomain hEqualityΛ hRight
    · exact
        gq_term_application_standard_code_falsum_of_length_ne
          (Γ := Λ)
          tail.length symbol.ctorIdx
          arguments tokens lengths.sum
          hArguments hPositiveΛ
          hFlattenDomain hEqualityΛ hLength
  · exact FirstOrder.Derives.negElim
      hSymbolEquality
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) <|
          gq_symbol_code_ne_of_token_ne
            (coded_function_symbol_code_term
              (numₘ(arity)) (numₘ(index)))
            token
            (Numbered.function_token arity index)
            (coded_function_symbol_code_term_admissible
              (numₘ(arity)) (numₘ(index))
              (finite_numeral_term_admissible arity)
              (finite_numeral_term_admissible index))
            (coded_function_symbol_code_eq_standard_token_sequence
              arity index)
            hHead)

/--
把应用生成分支封装成闭蕴含，供一步生成三分支消去直接调用。

内部有界消去只看到单公式闭上下文；其余生成分支无需知道参数族见证的布局。
-/
private theorem gq_term_application_decode_branch_falsum
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat) (token : Nat)
    (hGet : tokens[0]? = some token)
    (hLeft :
      tokens[1]? =
        some (Numbered.logical_token
          .leftParenthesis))
    (hToken : FSFormulaToken token)
    (hTokens : FSFormulaTokens tokens)
    (hRejectBelow :
      FSTermDecodeRejectionBelow freeBase tokens)
    (hDecode :
      fs_named_term_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    ⊢ₘ[godel_quotation_theory]
      term_application_from_condition
          TermCodeₘ
          (standard_token_sequence tokens) ⟶ₘ
        Formula.falsum := by
  let application : SetFormula :=
    term_application_from_condition
      TermCodeₘ
      (standard_token_sequence tokens)
  have hApplicationAdmissible :
      Formula.Admissible application := by
    have hGenerationAdmissible :
        Formula.Admissible
          (term_code_generation_condition
            TermCodeₘ
            (standard_token_sequence tokens)) :=
      Formula.Admissible.imp_right
        (gq_term_code_member_implies_generation
          (standard_token_sequence tokens)
          (standard_token_sequence_admissible tokens)
          (standard_token_sequence_freeSupport_nil
            tokens)).admissible
    simpa [application,
      term_code_generation_condition] using
        Formula.Admissible.disj_right <|
          Formula.Admissible.disj_right
            hGenerationAdmissible
  change
    ⊢ₘ[godel_quotation_theory]
      application ⟶ₘ Formula.falsum
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [application]
  have hApplication :
      Γ ⊢ₘ[godel_quotation_theory]
        term_application_from_condition
          TermCodeₘ
          (standard_token_sequence tokens) := by
    simpa [application] using
      FirstOrder.Derives.assumption
        (T := godel_quotation_theory)
        (Γ := Γ)
        (φ := application)
        (by simp [Γ])
        (Formula.check_admissible_complete
          hApplicationAdmissible)
  have hApplicationClosed :
      Formula.freeSupport application = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro freeVariable hMember
    simp [application,
      term_application_from_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      standard_token_sequence_freeSupport_nil] at hMember
    grind
  exact gq_term_application_decode_falsum
    freeBase boundNames tokens token hGet hLeft
    hToken hTokens hRejectBelow hDecode
    (by
      intro formula hFormula
      simp only [List.mem_singleton] at hFormula
      subst formula
      exact hApplicationClosed)
    hApplication

/--
一步项生成的变量、常元、函数应用三个分支统一排除 checked decoder 失败。

左括号已经确定应用形状，因此前两个 singleton 分支由长度立即排除；第三分支
调用严格短子项递归闭包。
-/
private theorem gq_term_generation_decode_falsum
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat)
    (hLeft :
      tokens[1]? =
        some (Numbered.logical_token
          .leftParenthesis))
    (hTokens : FSFormulaTokens tokens)
    (hRejectBelow :
      FSTermDecodeRejectionBelow freeBase tokens)
    (hDecode :
      fs_named_term_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    ⊢ₘ[godel_quotation_theory]
      term_code_generation_condition
          TermCodeₘ
          (standard_token_sequence tokens) ⟶ₘ
        Formula.falsum := by
  have hLength : tokens.length ≠ 1 := by
    intro hLength
    have hOutside : tokens[1]? = none := by
      rw [List.getElem?_eq_none]
      omega
    rw [hOutside] at hLeft
    contradiction
  cases tokens with
  | nil =>
      simp at hLeft
  | cons token tailTokens =>
    let parentTokens : List Nat := token :: tailTokens
    let code : SetTerm :=
      standard_token_sequence parentTokens
    let variableCase : SetFormula :=
      code ∈ₘ VarSymₘ
    let constant : SetFormula :=
      code ∈ₘ ConstSymₘ
    let application : SetFormula :=
      term_application_from_condition
        TermCodeₘ code
    let tail : SetFormula :=
      constant ∨ₘ application
    have hGenerationAdmissible :
        Formula.Admissible
          (term_code_generation_condition
            TermCodeₘ code) :=
      Formula.Admissible.imp_right
        (gq_term_code_member_implies_generation
          code
          (by
            simpa [code, parentTokens] using
              standard_token_sequence_admissible
                (token :: tailTokens))
          (by
            change
              Term.freeSupport
                  (standard_token_sequence
                    (token :: tailTokens)) =
                []
            exact
              standard_token_sequence_freeSupport_nil
                (token :: tailTokens))).admissible
    change
      ⊢ₘ[godel_quotation_theory]
        term_code_generation_condition
            TermCodeₘ code ⟶ₘ
          Formula.falsum
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature :=
      [term_code_generation_condition
        TermCodeₘ code]
    have hGeneration :
        Γ ⊢ₘ[godel_quotation_theory]
          term_code_generation_condition
            TermCodeₘ code :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete
          hGenerationAdmissible)
    have hShape :
        Γ ⊢ₘ[godel_quotation_theory]
          variableCase ∨ₘ tail := by
      simpa [term_code_generation_condition,
        variableCase, constant, application, tail] using
        hGeneration
    apply FirstOrder.Derives.disjElim hShape
    · let Δ : Context signature := variableCase :: Γ
      have hVariable :
          Δ ⊢ₘ[godel_quotation_theory]
            variableCase :=
        FirstOrder.Derives.assumption
          (by simp [Δ])
      exact
        gq_standard_token_sequence_base_symbol_falsum_of_length_ne_one
          (token :: tailTokens)
          hLength
          (by
            simpa [variableCase, code, parentTokens] using
              FirstOrder.Derives.disjIntroLeft
                hVariable)
    · let Δ : Context signature := tail :: Γ
      have hTail :
          Δ ⊢ₘ[godel_quotation_theory]
            tail :=
        FirstOrder.Derives.assumption
          (by simp [Δ])
      apply FirstOrder.Derives.disjElim hTail
      · let Ε : Context signature := constant :: Δ
        have hConstant :
            Ε ⊢ₘ[godel_quotation_theory]
              constant :=
          FirstOrder.Derives.assumption
            (by simp [Ε])
        exact
          gq_standard_token_sequence_base_symbol_falsum_of_length_ne_one
            (token :: tailTokens)
            hLength
            (by
              simpa [constant, code, parentTokens] using
                FirstOrder.Derives.disjIntroRight
                  hConstant)
      · let Ε : Context signature := application :: Δ
        exact FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ε)
            (by
              simp [Ε, application, code,
                parentTokens]) <|
              gq_term_application_decode_branch_falsum
                freeBase boundNames
                (token :: tailTokens) token
                (by simp)
                hLeft
                (hTokens token (by simp))
                hTokens hRejectBelow hDecode)
          (by
            simpa [Ε, application, code,
              parentTokens] using
              FirstOrder.Derives.assumption
                (T := godel_quotation_theory)
                (Γ := Ε)
                (φ := application)
                (by simp [Ε]))

/--
有限签名检查通过时，完整具名项 decoder 的具体失败可在对象层排除标准项码成员。

证明按 token 长度强归纳。函数应用分支的每个递归调用都来自参数族的精确连续
分片，并携带严格长度下降证书；singleton 分支只使用变量与常元的已检查 decoder。
-/
theorem gq_standard_term_code_not_of_decode_none
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat)
    (hTokens : FSFormulaTokens tokens)
    (hDecode :
      fs_named_term_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    ⊢ₘ[godel_quotation_theory]
      ¬ₘ (standard_token_sequence tokens ∈ₘ
        TermCodeₘ) := by
  have hRejectBelow :
      FSTermDecodeRejectionBelow freeBase tokens := by
    intro childBoundNames childTokens hLength
      hChildTokens hChildDecode
    exact
      gq_standard_term_code_not_of_decode_none
        freeBase childBoundNames childTokens
        hChildTokens hChildDecode
  by_cases hLeft :
      tokens[1]? =
        some (Numbered.logical_token
          .leftParenthesis)
  · let code : SetTerm :=
      standard_token_sequence tokens
    let membership : SetFormula :=
      code ∈ₘ TermCodeₘ
    have hCode :
        Term.Admissible code SetSort.set := by
      simpa [code] using
        standard_token_sequence_admissible tokens
    have hMembershipAdmissible :
        Formula.Admissible membership := by
      dsimp only [membership]
      exact membership_formula_admissible
        hCode term_code_set_term_admissible
    change
      ⊢ₘ[godel_quotation_theory]
        ¬ₘ membership
    apply FirstOrder.Derives.negIntro
      (hBodyCheck :=
        Formula.check_admissible_complete
          hMembershipAdmissible)
    let Γ : Context signature := [membership]
    have hMember :
        Γ ⊢ₘ[godel_quotation_theory]
          membership :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete
          hMembershipAdmissible)
    have hGeneration :
        Γ ⊢ₘ[godel_quotation_theory]
          term_code_generation_condition
            TermCodeₘ code :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp [Γ]) <|
            gq_term_code_member_implies_generation
              code hCode
              (by
                change
                  Term.freeSupport
                      (standard_token_sequence tokens) =
                    []
                exact
                  standard_token_sequence_freeSupport_nil
                    tokens))
        (by simpa [membership] using hMember)
    have hGenerationReject :
        Γ ⊢ₘ[godel_quotation_theory]
          term_code_generation_condition
              TermCodeₘ code ⟶ₘ
            Formula.falsum :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
          simpa [code] using
            gq_term_generation_decode_falsum
              freeBase boundNames tokens hLeft
              hTokens hRejectBelow hDecode
    exact FirstOrder.Derives.impElim
      hGenerationReject hGeneration
  · by_cases hLength : tokens.length = 1
    · rcases List.length_eq_one_iff.mp hLength with
        ⟨token, rfl⟩
      exact
        gq_standard_token_singleton_term_code_not_of_decode_none
          freeBase boundNames token
          (hTokens token (by simp)) hDecode
    · exact
        gq_standard_token_sequence_term_code_not_of_second_not_left_of_length_ne_one
          tokens hLeft hLength
termination_by tokens.length
decreasing_by
  exact hLength

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
