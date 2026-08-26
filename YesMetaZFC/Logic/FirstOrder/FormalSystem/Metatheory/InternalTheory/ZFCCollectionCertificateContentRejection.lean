import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectCertificateContentRejection

/-!
# ZFC 收集模式证书的内容反演

本模块闭合 collection schema 的负向内容回放。证明只反演证书中的五个对象坐标，
并使用两次二元 primitive-recursive shift 关系的唯一性；不恢复完整内部 trace。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation
open Rosser

set_option autoImplicit false

/-- 二元 collection schema 条件承载真实规范码时，公式内容只能等于该实例。 -/
theorem fs_zfc_support_raw_collection_condition_with_base_neg_of_schema_formula_ne
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    (formula : SetTerm)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hFormulaNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (formula ≐ₘ
          fs_zfc_formula_code_term
            (Formula.hilbertize
              SetSort.set
              (fs_embed_project_sentence
                (_root_.YesMetaZFC.SetTheory.Axioms.Schema.collection
                  schema)))))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_collection_condition_with_base
        formula
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 1
              (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens)))))
        base) := by
  let tokens : List Nat :=
    (fs_project_hilbert_token_tree schema.body).tokens
  let bodyTokenValue : Nat :=
    nat_sequence_code_value tokens
  let raw : Nat :=
    godel_pair_value 1
      (godel_pair_value 1
        (fs_zfc_schema_certificate parameterCount bodyTokenValue))
  let body : SetFormula :=
    fs_zfc_collection_condition_open_body formula raw base
  have hExistsAdmissible :
      Formula.Admissible
        (∃ₘ[SetSort.set, base],
          ∃ₘ[SetSort.set, base + 1],
            ∃ₘ[SetSort.set, base + 2],
              ∃ₘ[SetSort.set, base + 3],
                ∃ₘ[SetSort.set, base + 4], body) := by
    rw [← fs_zfc_collection_condition_exists_shape
      formula raw base]
    exact fs_zfc_collection_condition_with_base_admissible
      formula (numₘ(raw)) base
      hFormula (finite_numeral_term_admissible raw)
  have hBody : Formula.Admissible body :=
    fs_zfc_exists_five_body_admissible
      base (base + 1) (base + 2)
      (base + 3) (base + 4)
      body hExistsAdmissible
  have hBodyTokenQuote :
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 2))
          (parameterCount + 2)
          (Formula.hilbertize
            SetSort.set
            (fs_embed_project_formula schema.body)) =
        some tokens := by
    simpa [tokens] using
      fs_project_hilbert_token_tree_tokens
        schema.body schema.freeClosed
  let sourceFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula schema.body)
  let firstFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula
        (schema.body.rename
          (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
            parameterCount)))
  let secondFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula
        (schema.body.rename
          (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
            parameterCount)))
  have hFirstFormulaShift :
      CanonicalProjectFormulaShift parameterCount
          (parameterCount + 2) sourceFormula firstFormula := by
    simpa [sourceFormula, firstFormula,
      fs_zfc_project_formula_rename_id] using
      (fs_embed_project_formula_rename_hilbert_shift
        schema.body
        (fun entry : Fin (parameterCount + 2) => entry)
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
          parameterCount)
        schema.freeClosed
        (by omega)
        (fs_zfc_collection_binary_index_shift_first
          parameterCount))
  have hSecondFormulaShift :
      CanonicalProjectFormulaShift parameterCount
          (parameterCount + 3) firstFormula secondFormula := by
    simpa [firstFormula, secondFormula] using
      (fs_embed_project_formula_rename_hilbert_shift
        schema.body
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
          parameterCount)
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
          parameterCount)
        schema.freeClosed
        (by omega)
        (fs_zfc_collection_binary_index_shift_second
          parameterCount))
  rcases fs_zfc_collection_binary_trace_bundle schema with
    ⟨bodyTrace, firstTrace, secondTrace,
      hBodyTrace, hFirstTrace, hSecondTrace, _, _⟩
  have hFirstQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 3))
          (parameterCount + 3) firstFormula =
        some firstTrace.rootCode := by
    simpa [firstFormula] using
      canonical_project_hilbert_trace_from?_root_quote hFirstTrace
  have hSecondQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 4))
          (parameterCount + 4) secondFormula =
        some secondTrace.rootCode := by
    simpa [secondFormula] using
      canonical_project_hilbert_trace_from?_root_quote hSecondTrace
  rcases CanonicalProjectFormulaShift.quote_hilbert_tokens_exists
      hFirstFormulaShift with
    ⟨sourceTokens, firstTokens, hSourceTokens, hFirstTokens⟩
  rcases CanonicalProjectFormulaShift.quote_hilbert_tokens_exists
      hSecondFormulaShift with
    ⟨firstTokens', secondTokens, hFirstTokens', hSecondTokens⟩
  have hSourceTokensEq : sourceTokens = tokens :=
    Option.some.inj <| hSourceTokens.symm.trans hBodyTokenQuote
  have hFirstTokensEq : firstTokens' = firstTokens :=
    Option.some.inj <| hFirstTokens'.symm.trans hFirstTokens
  subst sourceTokens
  subst firstTokens'
  have hFirstRelation :
      CanonicalProjectShiftTokens parameterCount
        tokens firstTokens :=
    CanonicalProjectFormulaShift.quote_hilbert_tokens_relation
      hFirstFormulaShift (by omega)
      hBodyTokenQuote hFirstTokens
  have hSecondRelation :
      CanonicalProjectShiftTokens parameterCount
        firstTokens secondTokens :=
    CanonicalProjectFormulaShift.quote_hilbert_tokens_relation
      hSecondFormulaShift (by omega)
      hFirstTokens hSecondTokens
  have hFirstRootEquality :
      Derives fs_zfc_support_raw_theory [] (
        firstTrace.rootCode ≐ₘ
          standard_token_sequence firstTokens) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
        GodelQuotation.free_name
        GodelQuotation.bound_name
        hFirstTokens hFirstQuote)
  have hSecondRootEquality :
      Derives fs_zfc_support_raw_theory [] (
        secondTrace.rootCode ≐ₘ
          standard_token_sequence secondTokens) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
        GodelQuotation.free_name
        GodelQuotation.bound_name
        hSecondTokens hSecondQuote)
  have hFormulaCanonical :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_formula_code_term
            (Formula.hilbertize
              SetSort.set
              (fs_embed_project_sentence
                (_root_.YesMetaZFC.SetTheory.Axioms.Schema.collection
                  schema))) ≐ₘ
          canonical_forall_prefix_code
            parameterCount
            (fs_zfc_collection_core_code
              (numₘ(parameterCount))
              firstTrace.rootCode secondTrace.rootCode)) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (fs_zfc_collection_formula_code_eq_canonical_prefix
        schema hFirstTrace hSecondTrace)
  have hCase :
      body ::
        (∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 2],
          ∃ₘ[SetSort.set, base + 3],
            ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 1],
          ∃ₘ[SetSort.set, base + 2],
            ∃ₘ[SetSort.set, base + 3],
              ∃ₘ[SetSort.set, base + 4], body) ::
        [(∃ₘ[SetSort.set, base],
          ∃ₘ[SetSort.set, base + 1],
            ∃ₘ[SetSort.set, base + 2],
              ∃ₘ[SetSort.set, base + 3],
                ∃ₘ[SetSort.set, base + 4], body)]
        ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
    let Γ : Context signature :=
      body ::
        (∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 2],
          ∃ₘ[SetSort.set, base + 3],
            ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 1],
          ∃ₘ[SetSort.set, base + 2],
            ∃ₘ[SetSort.set, base + 3],
              ∃ₘ[SetSort.set, base + 4], body) ::
        [(∃ₘ[SetSort.set, base],
          ∃ₘ[SetSort.set, base + 1],
            ∃ₘ[SetSort.set, base + 2],
              ∃ₘ[SetSort.set, base + 3],
                ∃ₘ[SetSort.set, base + 4], body)]
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption (by simp [Γ])
    have hCertificateEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            fs_zfc_schema_certificate_term
              (numₘ(1)) (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_collection_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hBounds :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_schema_certificate_bounds
            (numₘ(raw)) (numₘ(1))
            (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_collection_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hBodyAt)
    apply fs_zfc_support_raw_schema_certificate_coordinates_elim
      raw 1 (x#base) (x#(base + 1))
      Formula.falsum
      (set_variable_admissible base)
      (set_variable_admissible (base + 1))
      Formula.Admissible.falsum
      hCertificateEquality hBounds
    intro parameterValue decodedBodyTokenValue hRaw
    have hRaw' :
        godel_pair_value 1
            (godel_pair_value 1
              (godel_pair_value parameterCount bodyTokenValue)) =
          godel_pair_value 1
            (godel_pair_value 1
              (godel_pair_value
                parameterValue decodedBodyTokenValue)) := by
      simpa [raw, fs_zfc_schema_certificate] using hRaw
    have hCoordinates :
        parameterCount = parameterValue ∧
          bodyTokenValue = decodedBodyTokenValue :=
      godel_pair_value_eq_iff.mp <|
        (godel_pair_value_eq_iff.mp <|
          (godel_pair_value_eq_iff.mp hRaw').2).2
    rcases hCoordinates with
      ⟨hParameterValue, hDecodedBodyTokenValue⟩
    subst parameterValue
    subst decodedBodyTokenValue
    let Δ : Context signature :=
      (x#(base + 1) ≐ₘ numₘ(bodyTokenValue)) ::
        (x#base ≐ₘ numₘ(parameterCount)) :: Γ
    change Δ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum
    have hBodyAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption (by simp [Δ, Γ])
    have hBodyTokenEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 1) ≐ₘ numₘ(bodyTokenValue) :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hParameterEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#base ≐ₘ numₘ(parameterCount) :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hOffsetNe
        (left right : FreeVarId)
        (hNe : left ≠ right) :
        base + left ≠ base + right := by
      intro hEquality
      exact hNe (Nat.add_left_cancel hEquality)
    have hBaseNeOffset
        (offset : FreeVarId)
        (hPositive : 0 < offset) :
        base ≠ base + offset :=
      Nat.ne_of_lt (Nat.lt_add_of_pos_right hPositive)
    have hHighNe
        (threshold offset id : FreeVarId)
        (hOffset : offset < threshold)
        (hId : base + threshold ≤ id) :
        id ≠ base + offset :=
      Ne.symm <| Nat.ne_of_lt <|
        Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left hOffset base) hId
    have hOffsetFresh
        (left right : FreeVarId)
        (hNe : left ≠ right) :
        (SetSort.set, base + left) ∉
          Term.freeSupport (x#(base + right)) := by
      intro hMember
      change (SetSort.set, base + left) ∈
        [(SetSort.set, base + right)] at hMember
      exact hOffsetNe left right hNe <|
        congrArg Prod.snd (List.mem_singleton.mp hMember)
    have hHighFresh
        (threshold offset id : FreeVarId)
        (hOffset : offset < threshold)
        (hId : base + threshold ≤ id) :
        (SetSort.set, id) ∉
          Term.freeSupport (x#(base + offset)) := by
      intro hMember
      change (SetSort.set, id) ∈
        [(SetSort.set, base + offset)] at hMember
      exact hHighNe threshold offset id hOffset hId <|
        congrArg Prod.snd (List.mem_singleton.mp hMember)
    have hRest :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_collection_condition_open_rest formula base := by
      simpa only [body,
        fs_zfc_collection_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight hBodyAt)
    have hSequence :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          nat_sequence_code_condition_with_ids
            (x#(base + 2)) (x#(base + 1))
            (base + 5) (base + 6) := by
      simpa only [fs_zfc_collection_condition_open_rest] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hRest)
    have hShiftFirst :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
            (x#base) (x#(base + 2)) (x#(base + 3))
            (base + 17) (base + 18) (base + 19) := by
      simpa only [fs_zfc_collection_condition_open_rest] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight
            (FirstOrder.Derives.conjElimRight
              (FirstOrder.Derives.conjElimRight hRest)))
    have hShiftSecond :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
            (x#base) (x#(base + 3)) (x#(base + 4))
            (base + 25) (base + 26) (base + 27) := by
      simpa only [fs_zfc_collection_condition_open_rest] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight
            (FirstOrder.Derives.conjElimRight
              (FirstOrder.Derives.conjElimRight
                (FirstOrder.Derives.conjElimRight hRest))))
    have hPrefix :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_forall_prefix_code_condition_with_ids
            (x#base)
            (fs_zfc_collection_core_code
              (x#base) (x#(base + 3)) (x#(base + 4)))
            formula (base + 33) (base + 34) := by
      simpa only [fs_zfc_collection_condition_open_rest] using
        FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight
            (FirstOrder.Derives.conjElimRight
              (FirstOrder.Derives.conjElimRight
                (FirstOrder.Derives.conjElimRight hRest))))
    have hContextFreshFromFive :
        ∀ f, f ∈ Δ →
          ∀ id, base + 5 ≤ id →
            (SetSort.set, id) ∉ Formula.freeSupport f := by
      intro f hf id hid
      have hBodyFresh :
          (SetSort.set, id) ∉ Formula.freeSupport body := by
        intro hMember
        have hSupport :=
          fs_zfc_collection_condition_open_body_freeSupport_subset
            formula raw base (SetSort.set, id) hMember
        rw [fs_zfc_schema_open_support, hFormulaClosed] at hSupport
        simp only [List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false] at hSupport
        rcases hSupport with h0 | h1 | h2 | h3 | h4
        · exact hHighNe 5 0 id (by decide) hid <|
            congrArg Prod.snd h0
        · exact hHighNe 5 1 id (by decide) hid <|
            congrArg Prod.snd h1
        · exact hHighNe 5 2 id (by decide) hid <|
            congrArg Prod.snd h2
        · exact hHighNe 5 3 id (by decide) hid <|
            congrArg Prod.snd h3
        · exact hHighNe 5 4 id (by decide) hid <|
            congrArg Prod.snd h4
      have hCloseFresh
          (binder : FreeVarId)
          (source : SetFormula)
          (hSourceFresh :
            (SetSort.set, id) ∉ Formula.freeSupport source) :
          (SetSort.set, id) ∉
            Formula.freeSupport
              (∃ₘ[SetSort.set, binder], source) := by
        simpa only [Formula.freeSupport] using
          Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            (SetSort.set, id) SetSort.set binder 0
            source hSourceFresh
      have h4 := hCloseFresh (base + 4) body hBodyFresh
      have h34 := hCloseFresh (base + 3)
        (∃ₘ[SetSort.set, base + 4], body) h4
      have h234 := hCloseFresh (base + 2)
        (∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4], body) h34
      have h1234 := hCloseFresh (base + 1)
        (∃ₘ[SetSort.set, base + 2],
          ∃ₘ[SetSort.set, base + 3],
            ∃ₘ[SetSort.set, base + 4], body) h234
      have h01234 := hCloseFresh base
        (∃ₘ[SetSort.set, base + 1],
          ∃ₘ[SetSort.set, base + 2],
            ∃ₘ[SetSort.set, base + 3],
              ∃ₘ[SetSort.set, base + 4], body) h1234
      simp only [Δ, Γ, List.mem_cons,
        List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl
      · simpa only [Formula.freeSupport, finite_numeral_term_freeSupport,
          List.append_nil] using
          hHighFresh 5 1 id (by decide) hid
      · simpa only [Formula.freeSupport, finite_numeral_term_freeSupport,
          List.append_nil] using
          hHighFresh 5 0 id (by decide) hid
      · exact hBodyFresh
      · exact h4
      · exact h34
      · exact h234
      · exact h1234
      · exact h01234
    have hSequenceEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 2) ≐ₘ standard_token_sequence tokens := by
      apply fs_zfc_support_raw_nat_sequence_code_condition_unique_of_code_equality
        (x#(base + 2)) (x#(base + 1)) tokens
        (base + 5) (base + 6)
      · exact set_variable_admissible (base + 2)
      · exact set_variable_admissible (base + 1)
      · exact hOffsetNe 5 6 (by decide)
      · exact hOffsetFresh 5 2 (by decide)
      · exact hOffsetFresh 6 2 (by decide)
      · exact hOffsetFresh 6 1 (by decide)
      · intro f hf
        exact hContextFreshFromFive f hf (base + 5)
          (Nat.le_refl _)
      · exact hSequence
      · exact hBodyTokenEquality
    let shiftFirstSource : SetFormula :=
      canonical_project_shift_code_condition_with_ids
        (x#base) (x#(base + 2)) (x#(base + 3))
        (base + 17) (base + 18) (base + 19)
    have hShiftFirstSubstitution :
        Formula.substituteFree SetSort.set base
            (numₘ(parameterCount)) shiftFirstSource =
          canonical_project_shift_code_condition_with_ids
            (numₘ(parameterCount))
            (x#(base + 2)) (x#(base + 3))
            (base + 17) (base + 18) (base + 19) := by
      simpa [shiftFirstSource] using
        canonical_project_shift_code_condition_with_ids_substitute_closed
          (x#base) (x#(base + 2)) (x#(base + 3))
          (numₘ(parameterCount))
          (numₘ(parameterCount))
          (x#(base + 2)) (x#(base + 3))
          base (base + 17) (base + 18) (base + 19)
          (hBaseNeOffset 17 (by decide))
          (hBaseNeOffset 18 (by decide))
          (hBaseNeOffset 19 (by decide))
          ⟨finite_numeral_term_admissible parameterCount,
            finite_numeral_term_freeSupport parameterCount⟩
          (by simp [Term.substituteFree, set_variable])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport])
    have hShiftFirstNumeral :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
            (numₘ(parameterCount))
            (x#(base + 2)) (x#(base + 3))
            (base + 17) (base + 18) (base + 19) := by
      have hSource :
          Δ ⊢ₘ[fs_zfc_support_raw_theory]
            Formula.substituteFree SetSort.set base
              (x#base) shiftFirstSource := by
        simpa [shiftFirstSource, Formula.substituteFree_self] using
          hShiftFirst
      have hTransport :=
        FirstOrder.Derives.eq_subst_m
          hParameterEquality hSource
      simpa [hShiftFirstSubstitution] using hTransport
    have hShiftFirstEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 3) ≐ₘ standard_token_sequence firstTokens := by
      apply fs_zfc_support_raw_canonical_project_shift_code_unique
        hFirstRelation
        (x#(base + 2)) (x#(base + 3)) (base + 17)
      · exact Term.check_certificate_of_admissible
          (set_variable_admissible (base + 2))
      · exact Term.check_certificate_of_admissible
          (set_variable_admissible (base + 3))
      · exact hSequenceEquality
      · intro id hid
        exact hHighFresh 17 2 id (by decide) hid
      · intro id hid
        exact hHighFresh 17 3 id (by decide) hid
      · intro f hf id hid
        exact hContextFreshFromFive f hf id <|
          Nat.le_trans
            (Nat.add_le_add_left (by decide : 5 ≤ 17) base) hid
      · simpa [Nat.add_assoc] using hShiftFirstNumeral
    have hShiftFirstRoot :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 3) ≐ₘ firstTrace.rootCode :=
      Metatheory.Derives.equality_trans
        hShiftFirstEquality
        (Metatheory.Derives.equality_symm
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Δ) (by simp) hFirstRootEquality))
    let shiftSecondSource : SetFormula :=
      canonical_project_shift_code_condition_with_ids
        (x#base) (x#(base + 3)) (x#(base + 4))
        (base + 25) (base + 26) (base + 27)
    have hShiftSecondSubstitution :
        Formula.substituteFree SetSort.set base
            (numₘ(parameterCount)) shiftSecondSource =
          canonical_project_shift_code_condition_with_ids
            (numₘ(parameterCount))
            (x#(base + 3)) (x#(base + 4))
            (base + 25) (base + 26) (base + 27) := by
      simpa [shiftSecondSource] using
        canonical_project_shift_code_condition_with_ids_substitute_closed
          (x#base) (x#(base + 3)) (x#(base + 4))
          (numₘ(parameterCount))
          (numₘ(parameterCount))
          (x#(base + 3)) (x#(base + 4))
          base (base + 25) (base + 26) (base + 27)
          (hBaseNeOffset 25 (by decide))
          (hBaseNeOffset 26 (by decide))
          (hBaseNeOffset 27 (by decide))
          ⟨finite_numeral_term_admissible parameterCount,
            finite_numeral_term_freeSupport parameterCount⟩
          (by simp [Term.substituteFree, set_variable])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport])
    have hShiftSecondNumeral :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
            (numₘ(parameterCount))
            (x#(base + 3)) (x#(base + 4))
            (base + 25) (base + 26) (base + 27) := by
      have hSource :
          Δ ⊢ₘ[fs_zfc_support_raw_theory]
            Formula.substituteFree SetSort.set base
              (x#base) shiftSecondSource := by
        simpa [shiftSecondSource, Formula.substituteFree_self] using
          hShiftSecond
      have hTransport :=
        FirstOrder.Derives.eq_subst_m
          hParameterEquality hSource
      simpa [hShiftSecondSubstitution] using hTransport
    have hShiftSecondEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 4) ≐ₘ standard_token_sequence secondTokens := by
      apply fs_zfc_support_raw_canonical_project_shift_code_unique
        hSecondRelation
        (x#(base + 3)) (x#(base + 4)) (base + 25)
      · exact Term.check_certificate_of_admissible
          (set_variable_admissible (base + 3))
      · exact Term.check_certificate_of_admissible
          (set_variable_admissible (base + 4))
      · exact hShiftFirstEquality
      · intro id hid
        exact hHighFresh 25 3 id (by decide) hid
      · intro id hid
        exact hHighFresh 25 4 id (by decide) hid
      · intro f hf id hid
        exact hContextFreshFromFive f hf id <|
          Nat.le_trans
            (Nat.add_le_add_left (by decide : 5 ≤ 25) base) hid
      · simpa [Nat.add_assoc] using hShiftSecondNumeral
    have hShiftSecondRoot :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 4) ≐ₘ secondTrace.rootCode :=
      Metatheory.Derives.equality_trans
        hShiftSecondEquality
        (Metatheory.Derives.equality_symm
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Δ) (by simp) hSecondRootEquality))
    let prefixSource : SetFormula :=
      canonical_forall_prefix_code_condition_with_ids
        (x#base)
        (fs_zfc_collection_core_code
          (x#base) (x#(base + 3)) (x#(base + 4)))
        formula (base + 33) (base + 34)
    have hPrefixSubstitution :
        Formula.substituteFree SetSort.set base
            (numₘ(parameterCount)) prefixSource =
          canonical_forall_prefix_code_condition_with_ids
            (numₘ(parameterCount))
            (fs_zfc_collection_core_code
              (numₘ(parameterCount))
              (x#(base + 3)) (x#(base + 4)))
            formula (base + 33) (base + 34) := by
      simpa [prefixSource] using
        canonical_forall_prefix_code_condition_with_ids_substitute_closed
          (x#base)
          (fs_zfc_collection_core_code
            (x#base) (x#(base + 3)) (x#(base + 4)))
          formula (numₘ(parameterCount))
          (numₘ(parameterCount))
          (fs_zfc_collection_core_code
            (numₘ(parameterCount))
            (x#(base + 3)) (x#(base + 4)))
          formula
          base (base + 33) (base + 34)
          (hBaseNeOffset 33 (by decide))
          (hBaseNeOffset 34 (by decide))
          ⟨finite_numeral_term_admissible parameterCount,
            finite_numeral_term_freeSupport parameterCount⟩
          (by simp [Term.substituteFree, set_variable])
          (by
            have hNumeralSubstitution (n : Nat) :
                Term.substituteFree SetSort.set base
                    (numₘ(parameterCount)) (numₘ(n)) =
                  numₘ(n) := by
              apply Term.substituteFree_eq_self_of_not_mem
              rw [finite_numeral_term_freeSupport]
              exact List.not_mem_nil
            simp [fs_zfc_collection_core_code,
              Term.substituteFree, set_variable,
              hNumeralSubstitution])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            rw [hFormulaClosed]
            exact List.not_mem_nil)
    have hPrefixNumeral :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_forall_prefix_code_condition_with_ids
            (numₘ(parameterCount))
            (fs_zfc_collection_core_code
              (numₘ(parameterCount))
              (x#(base + 3)) (x#(base + 4)))
            formula (base + 33) (base + 34) := by
      have hSource :
          Δ ⊢ₘ[fs_zfc_support_raw_theory]
            Formula.substituteFree SetSort.set base
              (x#base) prefixSource := by
        simpa [prefixSource, Formula.substituteFree_self] using hPrefix
      have hTransport :=
        FirstOrder.Derives.eq_subst_m
          hParameterEquality hSource
      simpa [hPrefixSubstitution] using hTransport
    have hPrefixEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          formula ≐ₘ
            canonical_forall_prefix_code
              parameterCount
              (fs_zfc_collection_core_code
                (numₘ(parameterCount))
                (x#(base + 3)) (x#(base + 4))) := by
      apply fs_zfc_support_raw_canonical_forall_prefix_code_condition_unique
        (fs_zfc_collection_core_code
          (numₘ(parameterCount))
          (x#(base + 3)) (x#(base + 4)))
        formula parameterCount
        (base + 33) (base + 34)
      · exact fs_zfc_collection_core_code_admissible
          (numₘ(parameterCount))
          (x#(base + 3)) (x#(base + 4))
          (finite_numeral_term_admissible parameterCount)
          (set_variable_admissible (base + 3))
          (set_variable_admissible (base + 4))
      · exact hFormula
      · exact hOffsetNe 33 34 (by decide)
      · intro hMember
        rcases
            fs_zfc_collection_core_code_freeSupport_subset
              (numₘ(parameterCount))
              (x#(base + 3)) (x#(base + 4))
              (SetSort.set, base + 33) hMember with
          hParameter | hShiftOne | hShiftTwo
        · simp [finite_numeral_term_freeSupport] at hParameter
        · exact hOffsetFresh 33 3 (by decide) hShiftOne
        · exact hOffsetFresh 33 4 (by decide) hShiftTwo
      · rw [hFormulaClosed]
        exact List.not_mem_nil
      · intro f hf
        exact hContextFreshFromFive f hf (base + 33) <|
          Nat.add_le_add_left (by decide : 5 ≤ 33) base
      · exact hPrefixNumeral
    have hCoreEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_collection_core_code
              (numₘ(parameterCount))
              (x#(base + 3)) (x#(base + 4)) ≐ₘ
            fs_zfc_collection_core_code
              (numₘ(parameterCount))
              firstTrace.rootCode secondTrace.rootCode :=
      fs_zfc_collection_core_code_congr_of_equalities
        parameterCount
        (x#(base + 3)) firstTrace.rootCode
        (x#(base + 4)) secondTrace.rootCode
        (set_variable_admissible (base + 3))
        (canonical_project_hilbert_trace_from?_root_code_boundary
          hFirstTrace).1
        (set_variable_admissible (base + 4))
        (canonical_project_hilbert_trace_from?_root_code_boundary
          hSecondTrace).1
        hShiftFirstRoot hShiftSecondRoot
    have hPrefixTransport :=
      canonical_forall_prefix_code_from_congr_of_equality
        (T := fs_zfc_support_raw_theory)
        (Γ := Δ)
        0 parameterCount
        (fs_zfc_collection_core_code
          (numₘ(parameterCount))
          (x#(base + 3)) (x#(base + 4)))
        (fs_zfc_collection_core_code
          (numₘ(parameterCount))
          firstTrace.rootCode secondTrace.rootCode)
        (fs_zfc_collection_core_code_admissible
          (numₘ(parameterCount))
          (x#(base + 3)) (x#(base + 4))
          (finite_numeral_term_admissible parameterCount)
          (set_variable_admissible (base + 3))
          (set_variable_admissible (base + 4)))
        (fs_zfc_collection_core_code_admissible
          (numₘ(parameterCount))
          firstTrace.rootCode secondTrace.rootCode
          (finite_numeral_term_admissible parameterCount)
          (canonical_project_hilbert_trace_from?_root_code_boundary
            hFirstTrace).1
          (canonical_project_hilbert_trace_from?_root_code_boundary
            hSecondTrace).1)
        hCoreEquality
    have hFormulaEquality :=
      Metatheory.Derives.equality_trans
        hPrefixEquality
        (Metatheory.Derives.equality_trans
          (by simpa [canonical_forall_prefix_code] using
            hPrefixTransport)
          (Metatheory.Derives.equality_symm
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Δ) (by simp) hFormulaCanonical)))
    exact FirstOrder.Derives.negElim
      hFormulaEquality
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) hFormulaNe)
  rw [fs_zfc_collection_condition_exists_shape
    formula raw base]
  simpa [raw, tokens, bodyTokenValue] using
    fs_zfc_support_raw_exists_five_neg
      base (base + 1) (base + 2)
      (base + 3) (base + 4)
      body hBody hCase

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
