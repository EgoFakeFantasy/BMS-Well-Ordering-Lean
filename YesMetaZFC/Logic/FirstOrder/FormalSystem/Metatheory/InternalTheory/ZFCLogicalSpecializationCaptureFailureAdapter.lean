import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalFirstOrderFailureAdapter
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaAtomicShiftInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCEqAxiomReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoderSubstitution

namespace YesMetaZFC.Logic.FirstOrder

open Nonlogical.BasicSetTheory
open FormalSystem
open FormalSystem.Rosser
open FormalSystem.GodelQuotation
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

namespace FormalSystem.CertifiedProof

/-!
# 特化公理捕获失败适配

本模块只处理宿主 substitution-safe 判定失败与对象 substitutable 证书之间的矛盾。
成功反演由既有树解码和 occurrence 接口提供；这里不公开 trace，也不扩展反演层。
-/

/-- 非安全宿主代换见证与对象层可代换证书矛盾。 -/
theorem fs_zfc_support_raw_logical_substitution_capture_unsafe_elim
    {Γ Δ : Context signature}
    (freeBase eigen : Nat)
    (bodyTokens leftTokens : List Nat)
    (sourceTree : RawHilbertTokenTree)
    (replacementTree : RawTermTokenTree)
    (body : SetFormula) (term : SetTerm)
    (variableCode replacementCode sourceCode : SetTerm)
    (hVariable : Term.Admissible variableCode SetSort.set)
    (hReplacement : Term.Admissible replacementCode SetSort.set)
    (hSource : Term.Admissible sourceCode SetSort.set)
    (hVariableFresh :
      ∀ id, id ≤ 470 →
        (SetSort.set, id) ∉ Term.freeSupport variableCode)
    (hReplacementFresh :
      ∀ id, id ≤ 470 →
        (SetSort.set, id) ∉ Term.freeSupport replacementCode)
    (hSourceFresh :
      ∀ id, id ≤ 470 →
        (SetSort.set, id) ∉ Term.freeSupport sourceCode)
    (hWeaken : ∀ φ, φ ∈ Γ → φ ∈ Δ)
    (hSafe :
      ¬fs_named_hilbert_tree_substitution_safe
        (Numbered.variable_token (free_name eigen))
        replacementTree sourceTree)
    (hSourceParse :
      RawHilbertTokenTree.parse? bodyTokens = some sourceTree)
    (hSourceTreeDecode :
      fs_named_hilbert_token_tree_decode freeBase [] sourceTree = some body)
    (hReplacementParse :
      RawTermTokenTree.parse? leftTokens = some replacementTree)
    (hReplacementTreeDecode :
      fs_named_term_token_tree_decode freeBase [] replacementTree = some term)
    (hVariableStandard :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        variableCode ≐ₘ
          standard_token_sequence
            [Numbered.variable_token (free_name eigen)])
    (hBodyStandard :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceCode ≐ₘ standard_token_sequence bodyTokens)
    (hLeft :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        replacementCode ≐ₘ standard_token_sequence leftTokens)
    (hNoQuantifier :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ¬ₘ quantifier_occurs_condition variableCode sourceCode)
    (hSubstitutable :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        substitutableₘ(variableCode, replacementCode, sourceCode)) :
    Δ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  rcases
      fs_named_hilbert_tree_substitution_unsafe_witness_of_decode
        freeBase []
        (Numbered.variable_token
          (free_name eigen))
        replacementTree hSafe
        hSourceTreeDecode with
    ⟨prefixTokens, captureTree, suffixTokens,
      name, captureFormula, captureBoundNames,
      hTreeShape, hTarget, hReplacementName,
      hCaptureDecode⟩
  have hSourceTokens :
      sourceTree.tokens = bodyTokens :=
    RawHilbertTokenTree.parse?_sound
      hSourceParse
  have hReplacementTokens :
      replacementTree.tokens = leftTokens :=
    RawTermTokenTree.parse?_sound
      hReplacementParse
  have hTokenShape :
      bodyTokens =
        prefixTokens ++
          Numbered.universal_tokens
            name captureTree.tokens ++
            suffixTokens :=
    hSourceTokens.symm.trans hTreeShape
  have hNameInReplacement :
      Numbered.variable_token name ∈
        leftTokens := by
    rw [← hReplacementTokens]
    exact hReplacementName
  rcases List.mem_iff_getElem?.mp hTarget with
    ⟨index, hCaptureGet⟩
  have hIndex :
      index < captureTree.tokens.length :=
    (List.getElem?_eq_some_iff.mp
      hCaptureGet).1
  let positionIndex : Nat :=
    index + (3 + prefixTokens.length)
  have hUniversalGet :
      (Numbered.universal_tokens
          name captureTree.tokens)[3 + index]? =
        some (Numbered.variable_token
          (free_name eigen)) := by
    rw [Numbered.universal_tokens,
      List.getElem?_append_left]
    · rw [List.getElem?_append_right]
      · simpa using hCaptureGet
      · simp
    · simp only [List.length_append,
        List.length_cons, List.length_nil]
      omega
  have hWholeGet :
      bodyTokens[positionIndex]? =
        some (Numbered.variable_token
          (free_name eigen)) := by
    rw [hTokenShape]
    have hAt :
        (prefixTokens ++
            Numbered.universal_tokens
              name captureTree.tokens ++
              suffixTokens)[
            prefixTokens.length +
              (3 + index)]? =
          some (Numbered.variable_token
            (free_name eigen)) := by
      rw [List.getElem?_append_left]
      · rw [List.getElem?_append_right]
        · simpa using hUniversalGet
        · omega
      · simp [Numbered.universal_tokens]
        omega
    simpa [positionIndex, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hAt
  have hCaptureMember :
      ⊢ₘ[quotation_occurrence_theory]
        standard_token_sequence
            captureTree.tokens ∈ₘ
          FormulaCodeₘ :=
    qo_weaken_godel_quotation <|
      fs_named_hilbert_token_tree_decode_standard_formula_code
        freeBase hCaptureDecode
  have hBodyPosition :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        quantifier_body_position_condition
          (Numbered.named_variable_code name)
          (standard_token_sequence bodyTokens)
          (numₘ(positionIndex)) := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Δ) (by simp)
    apply FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_quotation_occurrence
          hFormula)
    simpa [hTokenShape, positionIndex] using
      standard_token_sequence_quantifier_body_position_of_formula_code
        prefixTokens captureTree.tokens
        suffixTokens name index hIndex
        hCaptureMember
  have hTargetPosition :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        variable_occurs_at_position_condition
          (Numbered.named_variable_code
            (free_name eigen))
          (standard_token_sequence bodyTokens)
          (numₘ(positionIndex)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Δ) (by simp) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_quotation_occurrence
              hFormula) <|
          standard_token_sequence_variable_occurs_at_position
            bodyTokens (free_name eigen)
            positionIndex hWholeGet
  have hStandardBound :
      GodelQuotation.Numbered.CodeBoundary
        (standard_token_sequence
          [Numbered.variable_token
            (free_name eigen)]) :=
    ⟨standard_token_sequence_admissible _,
      standard_token_sequence_freeSupport_nil _⟩
  have hStandardReplacement :
      GodelQuotation.Numbered.CodeBoundary
        (standard_token_sequence leftTokens) :=
    ⟨standard_token_sequence_admissible _,
      standard_token_sequence_freeSupport_nil _⟩
  have hStandardBody :
      GodelQuotation.Numbered.CodeBoundary
        (standard_token_sequence bodyTokens) :=
    ⟨standard_token_sequence_admissible _,
      standard_token_sequence_freeSupport_nil _⟩
  have hStandardPosition :
      GodelQuotation.Numbered.CodeBoundary
        (numₘ(positionIndex)) :=
    ⟨finite_numeral_term_admissible _,
      finite_numeral_term_freeSupport _⟩
  have hSubstitutableFresh :
      ReservedIdsFresh [467, 468, 469]
        [(standard_token_sequence
            [Numbered.variable_token
              (free_name eigen)]),
          variableCode,
          (standard_token_sequence leftTokens),
          replacementCode,
          (standard_token_sequence bodyTokens),
          sourceCode] := by
    intro value hValue id hId
    simp only [List.mem_cons,
      List.not_mem_nil, or_false] at hValue hId
    have hIdUpper : id ≤ 470 := by
      rcases hId with h | h
      · simp [h]
      · rcases h with h | h
        · simp [h]
        · simp [h]
    rcases hValue with
      rfl | rfl | rfl | rfl | rfl | rfl
    · rw [standard_token_sequence_freeSupport_nil]
      exact List.not_mem_nil
    · exact hVariableFresh id hIdUpper
    · rw [standard_token_sequence_freeSupport_nil]
      exact List.not_mem_nil
    · exact hReplacementFresh id hIdUpper
    · rw [standard_token_sequence_freeSupport_nil]
      exact List.not_mem_nil
    · exact hSourceFresh id hIdUpper
  have hStandardSubstitutable :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        substitutableₘ(
          (standard_token_sequence
            [Numbered.variable_token
              (free_name eigen)]),
          standard_token_sequence leftTokens,
          standard_token_sequence bodyTokens) :=
    by
      exact
        (fs_substitutable_of_equalities
          (T := fs_zfc_support_raw_theory)
          (Γ := Δ)
          (standard_token_sequence
            [Numbered.variable_token
              (free_name eigen)])
          variableCode
          (standard_token_sequence leftTokens)
          replacementCode
          (standard_token_sequence bodyTokens)
          sourceCode
          hStandardBound.1
          hVariable
          hStandardReplacement.1
          hReplacement
          hStandardBody.1
          hSource
          hSubstitutableFresh
          (Metatheory.Derives.equality_symm
            hVariableStandard)
          (Metatheory.Derives.equality_symm hLeft)
          (Metatheory.Derives.equality_symm
            hBodyStandard)
          (FirstOrder.Derives.context_weaken
            (Γ := Γ) (Δ := Δ) hWeaken
            hSubstitutable))
  have hCondition :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        substitutable_condition
          (standard_token_sequence
            [Numbered.variable_token
              (free_name eigen)])
          (standard_token_sequence leftTokens)
          (standard_token_sequence bodyTokens) := by
    exact
      (FirstOrder.Derives.iffElimRight
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp) <|
            fs_zfc_support_raw_substitutable_iff_condition
              _ _ _ hStandardBound
              hStandardReplacement hStandardBody)
        hStandardSubstitutable)
  have hNoCapture :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[SetSort.set, 420],
          ((x#420 ∈ₘ
              varsₘ(
                standard_token_sequence
                  leftTokens)) ⟶ₘ
            (∀ₘ[SetSort.set, 421],
              ((free_occurrence_position_condition
                  (standard_token_sequence
                    [Numbered.variable_token
                      (free_name eigen)])
                  (standard_token_sequence
                    bodyTokens)
                  (x#421)) ⟶ₘ
                (¬ₘ
                  quantifier_body_position_condition
                    (x#420)
                    (standard_token_sequence
                      bodyTokens)
                    (x#421))))) := by
    simpa [substitutable_condition] using
      FirstOrder.Derives.conjElimRight hCondition
  have hTermCodeGQ :
      ⊢ₘ[godel_quotation_theory]
        term_codeₘ(
          standard_token_sequence leftTokens) := by
    simpa [hReplacementTokens] using
      fs_named_term_token_tree_decode_standard_term_code
        freeBase [] hReplacementTreeDecode
  have hTermMemberGQ :
      ⊢ₘ[godel_quotation_theory]
        standard_token_sequence leftTokens ∈ₘ
          TermCodeₘ :=
    FirstOrder.Derives.iffElimRight
      (gq_term_code_definition_instance
        (standard_token_sequence leftTokens)
        hStandardReplacement.1)
      hTermCodeGQ
  have hSourceUnion :=
    qo_weaken_godel_quotation <|
      gq_mem_binary_union_left
        TermCodeₘ FormulaCodeₘ
        (standard_token_sequence leftTokens)
        term_code_set_term_admissible
        formula_code_set_term_admissible
        hStandardReplacement.1 hTermMemberGQ
  have hVariableInVarsQ :
      ⊢ₘ[quotation_occurrence_theory]
        Numbered.named_variable_code name ∈ₘ
          varsₘ(
            standard_token_sequence
              leftTokens) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        (FirstOrder.Derives.impElim
          (qo_weaken_godel_quotation <|
            gq_variable_collection_member_of_occurrence_imp
              (standard_token_sequence
                leftTokens)
              (Numbered.named_variable_code name)
              hStandardReplacement
              ⟨variable_code_term_admissible
                  (numₘ(name))
                  (finite_numeral_term_admissible
                    name),
                named_variable_code_freeSupport
                  name⟩)
          hSourceUnion)
        (qo_weaken_godel_quotation <|
          named_variable_code_mem_variable_symbols
            name))
      (standard_token_sequence_variable_symbol_occurs
        leftTokens name hNameInReplacement)
  have hVariableInVars :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        Numbered.named_variable_code name ∈ₘ
          varsₘ(
            standard_token_sequence leftTokens) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Δ) (by simp) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_quotation_occurrence
              hFormula)
          hVariableInVarsQ
  have hOccurrenceFresh :
      ReservedIdsFresh
        [320, 321, 322, 460, 461]
        [variableCode,
          (standard_token_sequence
            [Numbered.variable_token
              (free_name eigen)]),
          sourceCode,
          (standard_token_sequence bodyTokens)] := by
    intro value hValue id hId
    simp only [List.mem_cons,
      List.not_mem_nil, or_false] at hValue hId
    have hIdUpper : id ≤ 470 := by
      rcases hId with h | h
      · simp [h]
      · rcases h with h | h
        · simp [h]
        · rcases h with h | h
          · simp [h]
          · rcases h with h | h
            · simp [h]
            · simp [h]
    rcases hValue with rfl | rfl | rfl | rfl
    · exact hVariableFresh id hIdUpper
    · rw [standard_token_sequence_freeSupport_nil]
      exact List.not_mem_nil
    · exact hSourceFresh id hIdUpper
    · rw [standard_token_sequence_freeSupport_nil]
      exact List.not_mem_nil
  have hNoQuantifierStandard :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        ¬ₘ quantifier_occurs_condition
          (standard_token_sequence
            [Numbered.variable_token
              (free_name eigen)])
          (standard_token_sequence
            bodyTokens) := by
    have hOccurrenceCheck :
        Formula.CheckCertificate
          (quantifier_occurs_condition
            (standard_token_sequence
              [Numbered.variable_token
                (free_name eigen)])
            (standard_token_sequence
              bodyTokens)) :=
      Formula.check_admissible_complete <|
        quantifier_occurs_condition_admissible
          _ _ hStandardBound.1
          hStandardBody.1
    apply FirstOrder.Derives.negIntro
      (hBodyCheck := hOccurrenceCheck)
    have hStandardOccurrence :
        quantifier_occurs_condition
            (standard_token_sequence
              [Numbered.variable_token
                (free_name eigen)])
            (standard_token_sequence
              bodyTokens) :: Δ ⊢ₘ[
              fs_zfc_support_raw_theory]
          quantifier_occurs_condition
            (standard_token_sequence
              [Numbered.variable_token
                (free_name eigen)])
            (standard_token_sequence
              bodyTokens) :=
      FirstOrder.Derives.assumption
        (hCheck := hOccurrenceCheck) (by simp)
    have hActualOccurrence :=
      quantifier_occurs_of_equalities
        (T := fs_zfc_support_raw_theory)
        (Γ :=
          quantifier_occurs_condition
              (standard_token_sequence
                [Numbered.variable_token
                  (free_name eigen)])
              (standard_token_sequence
                bodyTokens) :: Δ)
        variableCode
        (standard_token_sequence
          [Numbered.variable_token
            (free_name eigen)])
        sourceCode
        (standard_token_sequence bodyTokens)
        hVariable
        hStandardBound.1
        hSource
        hStandardBody.1
        hOccurrenceFresh
        (FirstOrder.Derives.context_weaken_cons
          hVariableStandard)
        (FirstOrder.Derives.context_weaken_cons
          hBodyStandard)
        hStandardOccurrence
    exact FirstOrder.Derives.negElim
      hActualOccurrence <|
        FirstOrder.Derives.context_weaken
          (Γ := Γ)
          (Δ :=
            quantifier_occurs_condition
                (standard_token_sequence
                  [Numbered.variable_token
                    (free_name eigen)])
                (standard_token_sequence
                  bodyTokens) :: Δ)
          (by
            intro formula hFormula
            exact List.mem_cons_of_mem _ <|
              hWeaken formula hFormula)
          hNoQuantifier
  have hNamedVariableStandard :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        Numbered.named_variable_code
            (free_name eigen) ≐ₘ
          standard_token_sequence
            [Numbered.variable_token
              (free_name eigen)] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Δ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <|
          named_variable_code_eq_standard_token_sequence
            (free_name eigen)
  have hTargetDomain :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(positionIndex) ∈ₘ
          domₘ(
            standard_token_sequence
              bodyTokens) :=
    FirstOrder.Derives.conjElimLeft <| by
      simpa [variable_occurs_at_position_condition]
        using hTargetPosition
  have hTargetValue :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        (standard_token_sequence bodyTokens ·ₘ
            numₘ(positionIndex)) ≐ₘ
          (Numbered.named_variable_code
              (free_name eigen) ·ₘ
            numₘ(0)) :=
    FirstOrder.Derives.conjElimRight <| by
      simpa [variable_occurs_at_position_condition]
        using hTargetPosition
  have hTargetApplication :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        (Numbered.named_variable_code
              (free_name eigen) ·ₘ
            numₘ(0)) ≐ₘ
          (standard_token_sequence
              [Numbered.variable_token
                (free_name eigen)] ·ₘ
            numₘ(0)) :=
    function_application_term_congr_function_of_equality
      _ _ _
      (variable_code_term_admissible _
        (finite_numeral_term_admissible
          (free_name eigen)))
      hStandardBound.1
      (finite_numeral_term_admissible 0)
      hNamedVariableStandard
  have hTargetPositionStandard :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        variable_occurs_at_position_condition
          (standard_token_sequence
            [Numbered.variable_token
              (free_name eigen)])
          (standard_token_sequence bodyTokens)
          (numₘ(positionIndex)) := by
    simpa [variable_occurs_at_position_condition]
      using FirstOrder.Derives.conjIntro
        hTargetDomain
        (Metatheory.Derives.equality_trans
          hTargetValue hTargetApplication)
  have hNamedVariableBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (Numbered.named_variable_code name) :=
    ⟨variable_code_term_admissible _
        (finite_numeral_term_admissible name),
      named_variable_code_freeSupport name⟩
  have hNumeralBoundary (value : Nat) :
      GodelQuotation.Numbered.CodeBoundary
        (numₘ(value)) :=
    ⟨finite_numeral_term_admissible value,
      finite_numeral_term_freeSupport value⟩
  have hSubstituteClose
      (sourceId closedId : FreeVarId)
      (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary
          replacement)
      (hDistinct : sourceId ≠ closedId)
      (formula : SetFormula) :
      Formula.substituteFree SetSort.set
          sourceId replacement
          (Formula.closeFreeAt SetSort.set
            closedId 0 formula) =
        Formula.closeFreeAt SetSort.set
          closedId 0
          (Formula.substituteFree SetSort.set
            sourceId replacement formula) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId closedId 0
      replacement formula hDistinct
      hReplacement.1.2 (by
        rw [hReplacement.2]
        exact List.not_mem_nil)).symm
  have hFreePosition :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        free_occurrence_position_condition
          (standard_token_sequence
            [Numbered.variable_token
              (free_name eigen)])
          (standard_token_sequence bodyTokens)
          (numₘ(positionIndex)) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp) <|
            FirstOrder.Derives.theory_weaken
              (fun _ hFormula =>
                fs_zfc_support_raw_contains_quotation_occurrence
                  hFormula) <|
              free_occurrence_position_of_not_quantifier
                _ _ _ hStandardBound
                hStandardBody
                hStandardPosition)
        hNoQuantifierStandard)
      hTargetPositionStandard
  have hAtVariableRaw :=
    FirstOrder.Derives.forall_elim
      (term :=
        Numbered.named_variable_code name)
      hNoCapture
  have hAtVariable :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        (Numbered.named_variable_code name ∈ₘ
            varsₘ(
              standard_token_sequence
                leftTokens)) ⟶ₘ
          (∀ₘ[SetSort.set, 421],
            ((free_occurrence_position_condition
                  (standard_token_sequence
                    [Numbered.variable_token
                      (free_name eigen)])
                  (standard_token_sequence
                    bodyTokens)
                  (x#421)) ⟶ₘ
              (¬ₘ
                quantifier_body_position_condition
                  (Numbered.named_variable_code
                    name)
          (standard_token_sequence
                    bodyTokens)
                  (x#421)))) := by
    rw [
      Formula.openAt_closeFreeAt_eq_substituteFree]
      at hAtVariableRaw
    simpa [free_occurrence_position_condition,
      bound_occurrence_position_condition,
      variable_occurs_at_position_condition,
      binder_declaration_position_condition,
      quantifier_body_position_condition,
      universal_binder_at_condition,
      code_substring_at_condition,
      Formula.substituteFree, Term.openAt,
      Term.closeFreeAt, Term.substituteFree,
      set_variable, set_bound_variable,
      hSubstituteClose 420 421
        (Numbered.named_variable_code name)
        hNamedVariableBoundary (by decide),
      hSubstituteClose 420 320
        (Numbered.named_variable_code name)
        hNamedVariableBoundary (by decide),
      hSubstituteClose 420 323
        (Numbered.named_variable_code name)
        hNamedVariableBoundary (by decide),
      hSubstituteClose 420 324
        (Numbered.named_variable_code name)
        hNamedVariableBoundary (by decide),
      hSubstituteClose 420 325
        (Numbered.named_variable_code name)
        hNamedVariableBoundary (by decide),
      hSubstituteClose 420 326
        (Numbered.named_variable_code name)
        hNamedVariableBoundary (by decide),
      hSubstituteClose 420 327
        (Numbered.named_variable_code name)
        hNamedVariableBoundary (by decide),
      Numbered.CodeBoundary.substituteFree_eq
        hStandardBound,
      Numbered.CodeBoundary.substituteFree_eq
        hStandardBody,
      Numbered.CodeBoundary.substituteFree_eq
        hStandardPosition,
      Numbered.CodeBoundary.substituteFree_eq
        (hNumeralBoundary 0),
      Numbered.CodeBoundary.substituteFree_eq
        (hNumeralBoundary 2),
      Numbered.CodeBoundary.substituteFree_eq
        (hNumeralBoundary 3),
      Numbered.CodeBoundary.substituteFree_eq
        hStandardReplacement] using
      hAtVariableRaw
  have hAtPositionRaw :=
    FirstOrder.Derives.forall_elim
      (term := numₘ(positionIndex))
      (FirstOrder.Derives.impElim
        hAtVariable hVariableInVars)
  have hAtPosition :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        free_occurrence_position_condition
            (standard_token_sequence
              [Numbered.variable_token
                (free_name eigen)])
            (standard_token_sequence bodyTokens)
            (numₘ(positionIndex)) ⟶ₘ
          ¬ₘ
            quantifier_body_position_condition
              (Numbered.named_variable_code name)
              (standard_token_sequence
                bodyTokens)
              (numₘ(positionIndex)) := by
    rw [
      Formula.openAt_closeFreeAt_eq_substituteFree]
      at hAtPositionRaw
    simpa [free_occurrence_position_condition,
      bound_occurrence_position_condition,
      variable_occurs_at_position_condition,
      binder_declaration_position_condition,
      quantifier_body_position_condition,
      universal_binder_at_condition,
      code_substring_at_condition,
      Formula.substituteFree, Term.openAt,
      Term.closeFreeAt, Term.substituteFree,
      set_variable, set_bound_variable,
      hSubstituteClose 421 320
        (numₘ(positionIndex))
        hStandardPosition (by decide),
      hSubstituteClose 421 323
        (numₘ(positionIndex))
        hStandardPosition (by decide),
      hSubstituteClose 421 324
        (numₘ(positionIndex))
        hStandardPosition (by decide),
      hSubstituteClose 421 325
        (numₘ(positionIndex))
        hStandardPosition (by decide),
      hSubstituteClose 421 326
        (numₘ(positionIndex))
        hStandardPosition (by decide),
      hSubstituteClose 421 327
        (numₘ(positionIndex))
        hStandardPosition (by decide),
      Numbered.CodeBoundary.substituteFree_eq
        hNamedVariableBoundary,
      Numbered.CodeBoundary.substituteFree_eq
        hStandardBound,
      Numbered.CodeBoundary.substituteFree_eq
        hStandardBody,
      Numbered.CodeBoundary.substituteFree_eq
        hStandardPosition,
      Numbered.CodeBoundary.substituteFree_eq
        (hNumeralBoundary 0),
      Numbered.CodeBoundary.substituteFree_eq
        (hNumeralBoundary 2),
      Numbered.CodeBoundary.substituteFree_eq
        (hNumeralBoundary 3)] using
      hAtPositionRaw
  exact FirstOrder.Derives.negElim
    hBodyPosition <|
      FirstOrder.Derives.impElim
        hAtPosition hFreePosition

/--
宿主解码表明目标变量落在某个同名量词的作用域内时，对象层的
`¬ quantifier_occurs_condition` 立即给出矛盾。
-/
theorem fs_zfc_support_raw_logical_substitution_target_bound_elim
    {Γ Δ : Context signature}
    (freeBase eigen : Nat)
    (bodyTokens : List Nat)
    (sourceTree : RawHilbertTokenTree)
    (body : SetFormula)
    (variableCode sourceCode : SetTerm)
    (hVariable : Term.Admissible variableCode SetSort.set)
    (hSource : Term.Admissible sourceCode SetSort.set)
    (hVariableFresh :
      ∀ id, id ≤ 470 →
        (SetSort.set, id) ∉ Term.freeSupport variableCode)
    (hSourceFresh :
      ∀ id, id ≤ 470 →
        (SetSort.set, id) ∉ Term.freeSupport sourceCode)
    (hWeaken : ∀ φ, φ ∈ Γ → φ ∈ Δ)
    (hNotBound :
      ¬fs_named_hilbert_tree_target_not_bound
        (Numbered.variable_token (free_name eigen))
        sourceTree)
    (hSourceParse :
      RawHilbertTokenTree.parse? bodyTokens = some sourceTree)
    (hSourceTreeDecode :
      fs_named_hilbert_token_tree_decode freeBase [] sourceTree = some body)
    (hVariableStandard :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        variableCode ≐ₘ
          standard_token_sequence
            [Numbered.variable_token (free_name eigen)])
    (hBodyStandard :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        sourceCode ≐ₘ standard_token_sequence bodyTokens)
    (hNoQuantifier :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ¬ₘ quantifier_occurs_condition variableCode sourceCode) :
    Δ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  rcases
      fs_named_hilbert_tree_target_bound_witness_of_decode
        freeBase []
        (Numbered.variable_token (free_name eigen))
        hNotBound hSourceTreeDecode with
    ⟨prefixTokens, bodyTree, suffixTokens, name,
      bodyFormula, bodyBoundNames, hTreeShape,
      hTarget, hWitnessBodyDecode⟩
  have hSourceTokens :
      sourceTree.tokens = bodyTokens :=
    RawHilbertTokenTree.parse?_sound hSourceParse
  have hTokenShape :
      bodyTokens =
        prefixTokens ++
          Numbered.universal_tokens name bodyTree.tokens ++
          suffixTokens :=
    hSourceTokens.symm.trans hTreeShape
  have hWitnessBodyMember :
      ⊢ₘ[quotation_occurrence_theory]
        standard_token_sequence bodyTree.tokens ∈ₘ FormulaCodeₘ :=
    qo_weaken_godel_quotation <|
      fs_named_hilbert_token_tree_decode_standard_formula_code
        freeBase hWitnessBodyDecode
  have hStandardOccurrenceRaw :
      ⊢ₘ[fs_zfc_support_raw_theory]
        quantifier_occurs_condition
          (Numbered.named_variable_code name)
          (standard_token_sequence
            (prefixTokens ++
              Numbered.universal_tokens name bodyTree.tokens ++
              suffixTokens)) :=
    FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_quotation_occurrence hFormula) <|
      standard_token_sequence_quantifier_occurs_of_formula_code
        prefixTokens bodyTree.tokens suffixTokens name
        hWitnessBodyMember
  have hStandardOccurrence :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        quantifier_occurs_condition
          (Numbered.named_variable_code name)
          (standard_token_sequence bodyTokens) := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Δ) (by simp)
    simpa [hTokenShape] using hStandardOccurrenceRaw
  have hNamedVariableStandard :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        Numbered.named_variable_code name ≐ₘ
          standard_token_sequence
            [Numbered.variable_token name] :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Δ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <|
          named_variable_code_eq_standard_token_sequence name
  have hVariableStandardName :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        variableCode ≐ₘ
          standard_token_sequence
            [Numbered.variable_token name] := by
    simpa [hTarget] using hVariableStandard
  have hVariableNamed :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        variableCode ≐ₘ Numbered.named_variable_code name :=
    Metatheory.Derives.equality_trans
      hVariableStandardName
      (Metatheory.Derives.equality_symm hNamedVariableStandard)
  have hReservedUpper
      (id : FreeVarId)
      (hId : id ∈ [320, 321, 322, 460, 461]) :
      id ≤ 470 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
    rcases hId with rfl | rfl | rfl | rfl | rfl <;> decide
  have hOccurrenceFresh :
      ReservedIdsFresh
        [320, 321, 322, 460, 461]
        [variableCode, Numbered.named_variable_code name,
          sourceCode, standard_token_sequence bodyTokens] := by
    intro value hValue id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hValue
    rcases hValue with rfl | rfl | rfl | rfl
    · exact hVariableFresh id (hReservedUpper id hId)
    · rw [named_variable_code_freeSupport name]
      exact List.not_mem_nil
    · exact hSourceFresh id (hReservedUpper id hId)
    · rw [standard_token_sequence_freeSupport_nil]
      exact List.not_mem_nil
  have hOccurrence :
      Δ ⊢ₘ[fs_zfc_support_raw_theory]
        quantifier_occurs_condition variableCode sourceCode :=
    quantifier_occurs_of_equalities
      (T := fs_zfc_support_raw_theory)
      (Γ := Δ)
      variableCode
      (Numbered.named_variable_code name)
      sourceCode
      (standard_token_sequence bodyTokens)
      hVariable
      (variable_code_term_admissible
        (numₘ(name)) (finite_numeral_term_admissible name))
      hSource
      (standard_token_sequence_admissible bodyTokens)
      hOccurrenceFresh hVariableNamed hBodyStandard
      hStandardOccurrence
  exact FirstOrder.Derives.negElim
    hOccurrence <|
      FirstOrder.Derives.context_weaken
        (Γ := Γ) (Δ := Δ) hWeaken hNoQuantifier

/--
对象替换规格的结果由源串、变量串和替换串唯一确定。该接口同时比较对象项与
标准 token 串两套输入，避免各逻辑公理分支重复展开替换函数性。
-/
theorem fs_zfc_support_raw_logical_substitution_result_eq_standard
    {Γ : Context signature}
    (source boundVariable replacement result : SetTerm)
    (sourceTokens replacementTokens : List Nat)
    (boundToken : Nat)
    (hSource : Term.Admissible source SetSort.set)
    (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hReplacement : Term.Admissible replacement SetSort.set)
    (hResult : Term.Admissible result SetSort.set)
    (hObjectFresh :
      ReservedIdsFresh [310, 311]
        [source, boundVariable, replacement, result])
    (hPrecondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_precondition
          source boundVariable replacement)
    (hStandardPrecondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_precondition
          (standard_token_sequence sourceTokens)
          (standard_token_sequence [boundToken])
          (standard_token_sequence replacementTokens))
    (hSpecification :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec
          source boundVariable replacement result)
    (hSourceStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        source ≐ₘ standard_token_sequence sourceTokens)
    (hBoundStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        boundVariable ≐ₘ standard_token_sequence [boundToken])
    (hReplacementStandard :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        replacement ≐ₘ standard_token_sequence replacementTokens) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      result ≐ₘ
        standard_token_sequence
          (substitute_tokens sourceTokens boundToken replacementTokens) := by
  let resultTokens :=
    substitute_tokens sourceTokens boundToken replacementTokens
  have hObjectFunctional :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_precondition
              source boundVariable replacement ⟶ₘ
          code_substitution_spec
              source boundVariable replacement result ⟶ₘ
            result ≐ₘ
              code_substitution_term
                source boundVariable replacement :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <|
          gq_weaken_substitution_variable <|
            code_substitution_spec_implies_eq_term
              source boundVariable replacement result
              (Term.check_admissible_complete hSource)
              (Term.check_admissible_complete hBoundVariable)
              (Term.check_admissible_complete hReplacement)
              (Term.check_admissible_complete hResult)
              hObjectFresh
  have hObjectResult :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        result ≐ₘ
          code_substitution_term
            source boundVariable replacement :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        hObjectFunctional hPrecondition)
      hSpecification
  have hStandardSpecification :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec
          (standard_token_sequence sourceTokens)
          (standard_token_sequence [boundToken])
          (standard_token_sequence replacementTokens)
          (standard_token_sequence resultTokens) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <| by
        apply fs_zfc_support_raw_derives_of_godel_quotation
        apply gq_weaken_standard_sequence
        simpa [resultTokens] using
          standard_token_sequence_code_substitution_spec
            sourceTokens boundToken replacementTokens
  have hStandardFresh :
      ReservedIdsFresh [310, 311]
        [standard_token_sequence sourceTokens,
          (standard_token_sequence [boundToken]),
          standard_token_sequence replacementTokens,
          standard_token_sequence resultTokens] := by
    intro value hValue id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hValue
    rcases hValue with rfl | rfl | rfl | rfl <;>
      rw [standard_token_sequence_freeSupport_nil] <;>
      exact List.not_mem_nil
  have hStandardFunctional :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_precondition
              (standard_token_sequence sourceTokens)
              (standard_token_sequence [boundToken])
              (standard_token_sequence replacementTokens) ⟶ₘ
          code_substitution_spec
              (standard_token_sequence sourceTokens)
              (standard_token_sequence [boundToken])
              (standard_token_sequence replacementTokens)
              (standard_token_sequence resultTokens) ⟶ₘ
            standard_token_sequence resultTokens ≐ₘ
              code_substitution_term
                (standard_token_sequence sourceTokens)
                (standard_token_sequence [boundToken])
                (standard_token_sequence replacementTokens) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation <|
          gq_weaken_substitution_variable <|
            code_substitution_spec_implies_eq_term
              (standard_token_sequence sourceTokens)
              (standard_token_sequence [boundToken])
              (standard_token_sequence replacementTokens)
              (standard_token_sequence resultTokens)
              (by prove_term_check) (by prove_term_check)
              (by prove_term_check) (by prove_term_check)
              hStandardFresh
  have hStandardResult :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence resultTokens ≐ₘ
          code_substitution_term
            (standard_token_sequence sourceTokens)
            (standard_token_sequence [boundToken])
            (standard_token_sequence replacementTokens) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        hStandardFunctional hStandardPrecondition)
      hStandardSpecification
  have hCongruence :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_term
            source boundVariable replacement ≐ₘ
          code_substitution_term
            (standard_token_sequence sourceTokens)
            (standard_token_sequence [boundToken])
            (standard_token_sequence replacementTokens) :=
    Metatheory.Derives.ternary_term_constructor_congr_of_equalities
      code_substitution_term
      code_substitution_term_admissible
      (by
        intros
        simp [code_substitution_term, Term.substituteFree])
      source (standard_token_sequence sourceTokens)
      boundVariable (standard_token_sequence [boundToken])
      replacement (standard_token_sequence replacementTokens)
      hSource (standard_token_sequence_admissible sourceTokens)
      hBoundVariable (standard_token_sequence_admissible [boundToken])
      hReplacement (standard_token_sequence_admissible replacementTokens)
      hSourceStandard hBoundStandard hReplacementStandard
  simpa [resultTokens] using
    Metatheory.Derives.equality_trans hObjectResult <|
      Metatheory.Derives.equality_trans hCongruence <|
        Metatheory.Derives.equality_symm hStandardResult

end FormalSystem.CertifiedProof

end YesMetaZFC.Logic.FirstOrder
