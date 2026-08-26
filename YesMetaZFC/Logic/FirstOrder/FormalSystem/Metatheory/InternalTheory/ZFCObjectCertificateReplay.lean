import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSeparationVerifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCollectionCertificateReplay

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation

set_option autoImplicit false

theorem fs_zfc_fixed_table_row_of_getElem?
    (wrap : Nat → Nat)
    (start index : Nat)
    (formulas : List SetFormula)
    (formula : SetFormula)
    (hGet : formulas[index]? = some formula) :
    (wrap (start + index),
      fs_zfc_formula_code_term
        (Formula.hilbertize SetSort.set formula)) ∈
      fs_zfc_fixed_table_rows_from wrap start formulas := by
  induction formulas generalizing start index formula with
  | nil =>
      simp at hGet
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero] at hGet
          cases Option.some.inj hGet
          simp [fs_zfc_fixed_table_rows_from]
      | succ index =>
          simp only [List.getElem?_cons_succ] at hGet
          have hTail := ih (start + 1) index formula hGet
          simp only [fs_zfc_fixed_table_rows_from, List.mem_cons]
          right
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail

/-- 固定表中的任意行可注入任意 schema 插件表组成的对象 verifier。 -/
theorem fs_zfc_support_raw_object_certificate_condition_with_plugins_of_fixed_row
    (plugins : List ProofT.SchemaPlugin)
    {row : Nat × SetTerm}
    (hRow : row ∈ fs_zfc_fixed_table_rows)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_plugins
        plugins row.2 (numₘ(row.1)) base) := by
  have hFormula :
      Term.Admissible row.2 SetSort.set :=
    fs_zfc_fixed_table_rows_admissible hRow
  have hCertificate :
      Term.Admissible (numₘ(row.1)) SetSort.set :=
    finite_numeral_term_admissible row.1
  have hFixed :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_fixed_axiom_table.condition
          row.2 (numₘ(row.1))) :=
    fs_zfc_fixed_axiom_table.condition_of_mem
      (T := fs_zfc_support_raw_theory) hRow
  nd_apply FirstOrder.Derives.disjIntroLeft
  exact hFixed

private theorem fs_zfc_support_raw_object_certificate_condition_of_fixed_row
    {row : Nat × SetTerm}
    (hRow : row ∈ fs_zfc_fixed_table_rows) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition
        row.2 (numₘ(row.1))) := by
  simpa [fs_zfc_object_certificate_condition,
    fs_zfc_object_certificate_condition_with_base] using
    fs_zfc_support_raw_object_certificate_condition_with_plugins_of_fixed_row
      fs_zfc_schema_plugins hRow
      (ProofT.schema_base [row.2, numₘ(row.1)])

private theorem fs_zfc_support_raw_object_certificate_condition_with_base_of_fixed_row
    {row : Nat × SetTerm}
    (hRow : row ∈ fs_zfc_fixed_table_rows)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_base
        row.2 (numₘ(row.1)) base) := by
  exact
    fs_zfc_support_raw_object_certificate_condition_with_plugins_of_fixed_row
      fs_zfc_schema_plugins hRow base

private theorem fs_zfc_support_raw_object_certificate_condition_of_internal_getElem?
    {index : Nat}
    {formula : SetFormula}
    (hGet :
      fs_internal_encoding_finite_presentation.axioms[index]? =
        some formula) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition
        (fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set formula))
        (numₘ(godel_pair_value 0 index))) := by
  have hSegment :=
    fs_zfc_fixed_table_row_of_getElem?
      (fun value => godel_pair_value 0 value)
      0 index
      fs_internal_encoding_finite_presentation.axioms
      formula hGet
  have hRow :
      (godel_pair_value 0 index,
        fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set formula)) ∈
        fs_zfc_fixed_table_rows := by
    unfold fs_zfc_fixed_table_rows
    simp only [List.mem_append]
    exact Or.inl (Or.inl (by
      simpa only [Nat.zero_add] using hSegment))
  exact fs_zfc_support_raw_object_certificate_condition_of_fixed_row hRow

private theorem fs_zfc_support_raw_object_certificate_condition_with_base_of_internal_getElem?
    {index : Nat}
    {formula : SetFormula}
    (hGet :
      fs_internal_encoding_finite_presentation.axioms[index]? =
        some formula)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_base
        (fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set formula))
        (numₘ(godel_pair_value 0 index)) base) := by
  have hSegment :=
    fs_zfc_fixed_table_row_of_getElem?
      (fun value => godel_pair_value 0 value)
      0 index
      fs_internal_encoding_finite_presentation.axioms
      formula hGet
  have hRow :
      (godel_pair_value 0 index,
        fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set formula)) ∈
        fs_zfc_fixed_table_rows := by
    unfold fs_zfc_fixed_table_rows
    simp only [List.mem_append]
    exact Or.inl (Or.inl (by
      simpa only [Nat.zero_add] using hSegment))
  exact
    fs_zfc_support_raw_object_certificate_condition_with_base_of_fixed_row
      hRow base

private theorem fs_zfc_support_raw_object_certificate_condition_of_project_definition_getElem?
    {index : Nat}
    {formula : SetFormula}
    (hGet :
      fs_project_definition_finite_presentation.axioms[index]? =
        some formula) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition
        (fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set formula))
        (numₘ(
          godel_pair_value 2 index))) := by
  have hSegment :=
    fs_zfc_fixed_table_row_of_getElem?
      (fun value =>
        godel_pair_value 2 value)
      0 index
      fs_project_definition_finite_presentation.axioms
      formula hGet
  have hRow :
      (godel_pair_value 2 index,
        fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set formula)) ∈
        fs_zfc_fixed_table_rows := by
    unfold fs_zfc_fixed_table_rows
    simp only [List.mem_append]
    exact Or.inl (Or.inr (by
      simpa only [Nat.zero_add] using hSegment))
  exact fs_zfc_support_raw_object_certificate_condition_of_fixed_row hRow

private theorem fs_zfc_support_raw_object_certificate_condition_with_base_of_project_definition_getElem?
    {index : Nat}
    {formula : SetFormula}
    (hGet :
      fs_project_definition_finite_presentation.axioms[index]? =
        some formula)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_base
        (fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set formula))
        (numₘ(godel_pair_value 2 index)) base) := by
  have hSegment :=
    fs_zfc_fixed_table_row_of_getElem?
      (fun value => godel_pair_value 2 value)
      0 index
      fs_project_definition_finite_presentation.axioms
      formula hGet
  have hRow :
      (godel_pair_value 2 index,
        fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set formula)) ∈
        fs_zfc_fixed_table_rows := by
    unfold fs_zfc_fixed_table_rows
    simp only [List.mem_append]
    exact Or.inl (Or.inr (by
      simpa only [Nat.zero_add] using hSegment))
  exact
    fs_zfc_support_raw_object_certificate_condition_with_base_of_fixed_row
      hRow base

private theorem fs_zfc_support_raw_object_certificate_condition_of_fixed_zfc_getElem?
    {index : Nat}
    {sentence : FsProjectSentence}
    (hGet :
      fs_zfc_fixed_axioms[index]? =
        some sentence) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition
        (fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence)))
        (numₘ(
          godel_pair_value 3 index))) := by
  have hSegment :=
    fs_zfc_fixed_table_row_of_getElem?
      (fun value =>
        godel_pair_value 3 value)
      0 index
      (fs_zfc_fixed_axioms.map
        (fun source => fs_embed_project_sentence source))
      (fs_embed_project_sentence sentence) (by
        simpa only [List.getElem?_map] using
          congrArg
            (Option.map (fun source =>
              fs_embed_project_sentence source)) hGet)
  have hRow :
      (godel_pair_value 3 index,
        fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence))) ∈
        fs_zfc_fixed_table_rows := by
    unfold fs_zfc_fixed_table_rows
    simp only [List.mem_append]
    exact Or.inr (by
      simpa only [Nat.zero_add] using hSegment)
  exact fs_zfc_support_raw_object_certificate_condition_of_fixed_row hRow

private theorem fs_zfc_support_raw_object_certificate_condition_with_base_of_fixed_zfc_getElem?
    {index : Nat}
    {sentence : FsProjectSentence}
    (hGet :
      fs_zfc_fixed_axioms[index]? =
        some sentence)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_base
        (fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence)))
        (numₘ(godel_pair_value 3 index)) base) := by
  have hSegment :=
    fs_zfc_fixed_table_row_of_getElem?
      (fun value => godel_pair_value 3 value)
      0 index
      (fs_zfc_fixed_axioms.map
        (fun source => fs_embed_project_sentence source))
      (fs_embed_project_sentence sentence) (by
        simpa only [List.getElem?_map] using
          congrArg
            (Option.map (fun source =>
              fs_embed_project_sentence source)) hGet)
  have hRow :
      (godel_pair_value 3 index,
        fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence))) ∈
        fs_zfc_fixed_table_rows := by
    unfold fs_zfc_fixed_table_rows
    simp only [List.mem_append]
    exact Or.inr (by
      simpa only [Nat.zero_add] using hSegment)
  exact
    fs_zfc_support_raw_object_certificate_condition_with_base_of_fixed_row
      hRow base

private theorem fs_zfc_support_raw_object_certificate_condition_of_internal_generate
    {certificate : Nat}
    {formula : SetFormula}
    (hGenerate :
      (HilbertTheoryGenerator.hilbertize
        SetSort.set
        (HilbertTheoryGenerator.ofFinite
          fs_internal_encoding_finite_presentation)).generate
        certificate =
        some formula) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition
        (fs_zfc_formula_code_term formula)
        (numₘ(godel_pair_value 0 certificate))) := by
  change
    (fs_internal_encoding_finite_presentation.axioms[certificate]?).map
        (Formula.hilbertize SetSort.set) =
      some formula at hGenerate
  cases hSource :
      fs_internal_encoding_finite_presentation.axioms[certificate]? with
  | none =>
      simp [hSource] at hGenerate
  | some source =>
      simp only [hSource, Option.map_some,
        Option.some.injEq] at hGenerate
      subst formula
      exact
        fs_zfc_support_raw_object_certificate_condition_of_internal_getElem?
          hSource

private theorem fs_zfc_support_raw_object_certificate_condition_of_project_definition_generate
    {certificate : Nat}
    {formula : SetFormula}
    (hGenerate :
      (HilbertTheoryGenerator.hilbertize
        SetSort.set
        (HilbertTheoryGenerator.ofFinite
          fs_project_definition_finite_presentation)).generate
        certificate =
        some formula) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition
        (fs_zfc_formula_code_term formula)
        (numₘ(
          godel_pair_value 2 certificate))) := by
  change
    (fs_project_definition_finite_presentation.axioms[certificate]?).map
        (Formula.hilbertize SetSort.set) =
      some formula at hGenerate
  cases hSource :
      fs_project_definition_finite_presentation.axioms[certificate]? with
  | none =>
      simp [hSource] at hGenerate
  | some source =>
      simp only [hSource, Option.map_some,
        Option.some.injEq] at hGenerate
      subst formula
      exact
        fs_zfc_support_raw_object_certificate_condition_of_project_definition_getElem?
          hSource

private theorem fs_project_bound_term_decode_token_eq
    {depth token : Nat}
    {entry : Fin depth}
    (hDecode :
      fs_project_bound_term_decode depth token =
        some (.bound entry)) :
    token = fs_project_bound_token entry := by
  induction depth with
  | zero =>
      exact Fin.elim0 entry
  | succ depth ih =>
      simp only [fs_project_bound_term_decode] at hDecode
      split at hDecode
      next hNewest =>
        simp only [Option.some.injEq] at hDecode
        cases hDecode
        simpa [fs_project_bound_token] using hNewest
      next hNotNewest =>
        cases hPrevious :
            fs_project_bound_term_decode depth token with
        | none =>
            simp [hPrevious] at hDecode
        | some previous =>
            cases previous with
            | bound previousEntry =>
                simp [hPrevious] at hDecode
                subst entry
                simpa [fs_project_bound_token] using
                  ih hPrevious
            | free id =>
                simp [hPrevious] at hDecode

private theorem fs_project_bound_term_decode_no_free
    {depth token : Nat}
    {id : SetTheory.FreeVarId}
    (hDecode :
      fs_project_bound_term_decode depth token =
        some (.free id)) :
    False := by
  induction depth with
  | zero =>
      simp [fs_project_bound_term_decode] at hDecode
  | succ depth ih =>
      simp only [fs_project_bound_term_decode] at hDecode
      split at hDecode
      next hNewest =>
          simp at hDecode
      next hNotNewest =>
          cases hPrevious :
              fs_project_bound_term_decode depth token with
          | none =>
              simp [hPrevious] at hDecode
          | some previous =>
              cases previous with
              | bound entry =>
                  simp [hPrevious] at hDecode
              | free previousId =>
                  simp [hPrevious] at hDecode

private theorem fs_project_term_token_tree_tokens_of_decode
    {depth : Nat}
    {tree : GodelQuotation.RawTermTokenTree}
    {term : _root_.YesMetaZFC.SetTheory.Definitional.Project.Term depth}
    (hDecode :
      fs_project_term_token_tree_decode depth tree =
        some term) :
    tree.tokens =
      (fs_project_term_token_tree term).tokens := by
  cases tree with
  | atom token =>
      cases term with
      | bound entry =>
          simpa [GodelQuotation.RawTermTokenTree.tokens,
            fs_project_term_token_tree] using
            fs_project_bound_term_decode_token_eq hDecode
      | free id =>
          exact (fs_project_bound_term_decode_no_free hDecode).elim
  | application head arguments =>
      simp [fs_project_term_token_tree_decode] at hDecode

theorem fs_project_hilbert_token_tree_tokens_of_decode
    {depth : Nat}
    {tree : GodelQuotation.RawHilbertTokenTree}
    {formula :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula 1 depth}
    (hDecode :
      fs_project_hilbert_token_tree_decode depth tree =
        some formula) :
    tree.tokens =
      (fs_project_hilbert_token_tree formula).tokens := by
  revert formula
  induction tree generalizing depth with
  | equality left right =>
      intro formula hDecode
      simp only [fs_project_hilbert_token_tree_decode] at hDecode
      cases hLeft :
          fs_project_term_token_tree_decode depth left with
      | none =>
          simp [hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_project_term_token_tree_decode depth right with
          | none =>
              simp [hLeft, hRight] at hDecode
          | some rightTerm =>
              simp [hLeft, hRight] at hDecode
              subst formula
              have hLeftTokens :=
                fs_project_term_token_tree_tokens_of_decode hLeft
              have hRightTokens :=
                fs_project_term_token_tree_tokens_of_decode hRight
              simp [GodelQuotation.RawHilbertTokenTree.tokens,
                fs_project_hilbert_token_tree,
                _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula.extensionalEq,
                hLeftTokens, hRightTokens]
  | membership left right =>
      intro formula hDecode
      simp only [fs_project_hilbert_token_tree_decode] at hDecode
      cases hLeft :
          fs_project_term_token_tree_decode depth left with
      | none =>
          simp [hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_project_term_token_tree_decode depth right with
          | none =>
              simp [hLeft, hRight] at hDecode
          | some rightTerm =>
              simp [hLeft, hRight] at hDecode
              subst formula
              have hLeftTokens :=
                fs_project_term_token_tree_tokens_of_decode hLeft
              have hRightTokens :=
                fs_project_term_token_tree_tokens_of_decode hRight
              simp [GodelQuotation.RawHilbertTokenTree.tokens,
                fs_project_hilbert_token_tree,
                hLeftTokens, hRightTokens]
  | predicate head arguments =>
      intro formula hDecode
      simp only [fs_project_hilbert_token_tree_decode] at hDecode
      split at hDecode
      next hHead =>
        cases arguments with
        | nil =>
            simp at hDecode
        | cons first rest =>
            cases rest with
            | nil =>
                simp at hDecode
            | cons second tail =>
                cases tail with
                | nil =>
                    cases hLeft :
                        fs_project_term_token_tree_decode
                          depth first with
                    | none =>
                        simp [hLeft] at hDecode
                    | some leftTerm =>
                        cases hRight :
                            fs_project_term_token_tree_decode
                              depth second with
                        | none =>
                            simp [hLeft, hRight] at hDecode
                        | some rightTerm =>
                            simp [hLeft, hRight] at hDecode
                            subst formula
                            have hLeftTokens :=
                              fs_project_term_token_tree_tokens_of_decode hLeft
                            have hRightTokens :=
                              fs_project_term_token_tree_tokens_of_decode hRight
                            simp [GodelQuotation.RawHilbertTokenTree.tokens,
                              GodelQuotation.RawTermTokenTree.list_tokens,
                              fs_project_hilbert_token_tree,
                              _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula.subset,
                              _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula.pairArguments_get_zero,
                              _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula.pairArguments_get_one,
                              hHead,
                              hLeftTokens, hRightTokens]
                | cons third tail =>
                    simp at hDecode
      next hNotHead =>
        simp at hDecode
  | negation body ih =>
      intro formula hDecode
      simp only [fs_project_hilbert_token_tree_decode] at hDecode
      cases hBody :
          fs_project_hilbert_token_tree_decode depth body with
      | none =>
          simp [hBody] at hDecode
      | some bodyFormula =>
          simp [hBody] at hDecode
          subst formula
          have hBodyTokens :=
            ih (depth := depth)
              (formula := bodyFormula) hBody
          simp [GodelQuotation.RawHilbertTokenTree.tokens,
            fs_project_hilbert_token_tree,
            hBodyTokens]
  | implication left right ihLeft ihRight =>
      intro formula hDecode
      simp only [fs_project_hilbert_token_tree_decode] at hDecode
      cases hLeft :
          fs_project_hilbert_token_tree_decode depth left with
      | none =>
          simp [hLeft] at hDecode
      | some leftFormula =>
          cases hRight :
              fs_project_hilbert_token_tree_decode depth right with
          | none =>
              simp [hLeft, hRight] at hDecode
          | some rightFormula =>
              simp [hLeft, hRight] at hDecode
              subst formula
              have hLeftTokens :=
                ihLeft (depth := depth)
                  (formula := leftFormula) hLeft
              have hRightTokens :=
                ihRight (depth := depth)
                  (formula := rightFormula) hRight
              simp [GodelQuotation.RawHilbertTokenTree.tokens,
                fs_project_hilbert_token_tree,
                hLeftTokens, hRightTokens]
  | universal variableToken body ih =>
      intro formula hDecode
      simp only [fs_project_hilbert_token_tree_decode] at hDecode
      split at hDecode
      next hVariable =>
        cases hBody :
            fs_project_hilbert_token_tree_decode
              (depth + 1) body with
        | none =>
            simp [hBody] at hDecode
        | some bodyFormula =>
            simp [hBody] at hDecode
            subst formula
            have hBodyTokens :=
              ih (depth := depth + 1)
                (formula := bodyFormula) hBody
            simp [GodelQuotation.RawHilbertTokenTree.tokens,
              fs_project_hilbert_token_tree,
              hVariable, hBodyTokens]
      next hNotVariable =>
        simp at hDecode

theorem fs_project_hilbert_code_decode_code_eq
    {depth code : Nat}
    {formula :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula 1 depth}
    (hDecode :
      fs_project_hilbert_code_decode depth code =
        some formula) :
    code =
      nat_sequence_code_value
        (fs_project_hilbert_token_tree formula).tokens := by
  unfold fs_project_hilbert_code_decode at hDecode
  cases hParse :
      GodelQuotation.RawHilbertTokenTree.parse?
        (nat_sequence_decode code) with
  | none =>
      simp [hParse, fs_project_hilbert_tokens_decode] at hDecode
  | some tree =>
      have hTreeDecode :
          fs_project_hilbert_token_tree_decode depth tree =
            some formula := by
        simpa [fs_project_hilbert_tokens_decode, hParse] using hDecode
      have hTreeTokens :
          tree.tokens =
            (fs_project_hilbert_token_tree formula).tokens := by
        exact fs_project_hilbert_token_tree_tokens_of_decode hTreeDecode
      calc
        code =
            nat_sequence_code_value (nat_sequence_decode code) := by
              symm
              exact nat_sequence_code_value_decode code
        _ =
            nat_sequence_code_value
              (fs_project_hilbert_token_tree formula).tokens := by
              rw [← hTreeTokens]
              exact congrArg nat_sequence_code_value
                (GodelQuotation.RawHilbertTokenTree.parse?_sound hParse).symm

/-! ## schema 生成分支的局部解码桥 -/

theorem fs_project_unary_schema_hilbert_decode_body
    {parameterCount bodyTokenCode : Nat}
    {schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
        parameterCount}
    (hDecode :
      fs_project_unary_schema_hilbert_decode
        parameterCount bodyTokenCode =
        some schema) :
    fs_project_hilbert_code_decode
        (parameterCount + 1) bodyTokenCode =
      some schema.body := by
  unfold fs_project_unary_schema_hilbert_decode at hDecode
  cases hBody :
      fs_project_hilbert_code_decode
        (parameterCount + 1) bodyTokenCode with
  | none =>
      simp [hBody] at hDecode
  | some body =>
      simp only [hBody] at hDecode
      split at hDecode
      next hClosed =>
        simp only [Option.some.injEq] at hDecode
        cases hDecode
        rfl
      next hNotClosed =>
        simp at hDecode

theorem fs_project_binary_schema_hilbert_decode_body
    {parameterCount bodyTokenCode : Nat}
    {schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount}
    (hDecode :
      fs_project_binary_schema_hilbert_decode
        parameterCount bodyTokenCode =
        some schema) :
    fs_project_hilbert_code_decode
        (parameterCount + 2) bodyTokenCode =
      some schema.body := by
  unfold fs_project_binary_schema_hilbert_decode at hDecode
  cases hBody :
      fs_project_hilbert_code_decode
        (parameterCount + 2) bodyTokenCode with
  | none =>
      simp [hBody] at hDecode
  | some body =>
      simp only [hBody] at hDecode
      split at hDecode
      next hClosed =>
        simp only [Option.some.injEq] at hDecode
        cases hDecode
        rfl
      next hNotClosed =>
        simp at hDecode

private theorem fs_zfc_support_raw_object_certificate_condition_of_separation_generate
    {payload : Nat}
    {sentence : FsProjectSentence}
    (hGenerate :
      fs_zfc_separation_generate payload =
        some sentence) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition
        (fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence)))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 0 payload)))) := by
  unfold fs_zfc_separation_generate at hGenerate
  dsimp only at hGenerate
  cases hDecode :
      fs_project_unary_schema_hilbert_decode
        (godel_unpair_value payload).1
        (godel_unpair_value payload).2 with
  | none =>
      simp [hDecode] at hGenerate
  | some schema =>
      simp only [hDecode, Option.map_some,
        Option.some.injEq] at hGenerate
      subst sentence
      have hBodyDecode :=
        fs_project_unary_schema_hilbert_decode_body hDecode
      have hBodyCode :
          (godel_unpair_value payload).2 =
            nat_sequence_code_value
              (fs_project_hilbert_token_tree schema.body).tokens :=
        fs_project_hilbert_code_decode_code_eq hBodyDecode
      have hPayload :
          payload =
            fs_zfc_schema_certificate
              (godel_unpair_value payload).1
              (nat_sequence_code_value
                (fs_project_hilbert_token_tree schema.body).tokens) := by
        calc
          payload =
              godel_pair_value
                (godel_unpair_value payload).1
                (godel_unpair_value payload).2 := by
            symm
            exact godel_unpair_value_spec payload
          _ =
              fs_zfc_schema_certificate
                (godel_unpair_value payload).1
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens) := by
            simp [fs_zfc_schema_certificate, hBodyCode]
      have hSchema :=
        fs_zfc_support_raw_object_certificate_condition_of_separation_schema
          schema
      have hCertificate :
          numₘ(
              godel_pair_value 1
                (godel_pair_value 0 payload)) =
            numₘ(
              godel_pair_value 1
                (godel_pair_value 0
                  (fs_zfc_schema_certificate
                    (godel_unpair_value payload).1
                    (nat_sequence_code_value
                      (fs_project_hilbert_token_tree schema.body).tokens)))) := by
        exact congrArg
          (fun value =>
            numₘ(godel_pair_value 1
              (godel_pair_value 0 value)))
          hPayload
      rw [hCertificate]
      exact hSchema

private theorem fs_zfc_support_raw_object_certificate_condition_of_collection_generate
    {payload : Nat}
    {sentence : FsProjectSentence}
    (hGenerate :
      fs_zfc_collection_generate payload =
        some sentence) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition
        (fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence)))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 1 payload)))) := by
  unfold fs_zfc_collection_generate at hGenerate
  dsimp only at hGenerate
  cases hDecode :
      fs_project_binary_schema_hilbert_decode
        (godel_unpair_value payload).1
        (godel_unpair_value payload).2 with
  | none =>
      simp [hDecode] at hGenerate
  | some schema =>
      simp only [hDecode, Option.map_some,
        Option.some.injEq] at hGenerate
      subst sentence
      have hBodyDecode :=
        fs_project_binary_schema_hilbert_decode_body hDecode
      have hBodyCode :
          (godel_unpair_value payload).2 =
            nat_sequence_code_value
              (fs_project_hilbert_token_tree schema.body).tokens :=
        fs_project_hilbert_code_decode_code_eq hBodyDecode
      have hPayload :
          payload =
            fs_zfc_schema_certificate
              (godel_unpair_value payload).1
              (nat_sequence_code_value
                (fs_project_hilbert_token_tree schema.body).tokens) := by
        calc
          payload =
              godel_pair_value
                (godel_unpair_value payload).1
                (godel_unpair_value payload).2 := by
            symm
            exact godel_unpair_value_spec payload
          _ =
              fs_zfc_schema_certificate
                (godel_unpair_value payload).1
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens) := by
            simp [fs_zfc_schema_certificate, hBodyCode]
      have hSchema :=
        fs_zfc_support_raw_object_certificate_condition_of_collection_schema
          schema
      have hCertificate :
          numₘ(
              godel_pair_value 1
                (godel_pair_value 1 payload)) =
            numₘ(
              godel_pair_value 1
                (godel_pair_value 1
                  (fs_zfc_schema_certificate
                    (godel_unpair_value payload).1
                    (nat_sequence_code_value
                      (fs_project_hilbert_token_tree schema.body).tokens)))) := by
        exact congrArg
          (fun value =>
            numₘ(godel_pair_value 1
              (godel_pair_value 1 value)))
          hPayload
      rw [hCertificate]
      exact hSchema

private theorem fs_zfc_support_raw_object_certificate_condition_of_schema_generate
    {payload : Nat}
    {formula : SetFormula}
    (hGenerate :
      fs_zfc_embedded_hilbert_generator.generate
        (godel_pair_value 1 payload) =
        some formula) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition
        (fs_zfc_formula_code_term formula)
        (numₘ(godel_pair_value 1 payload))) := by
  change
    (fs_zfc_axiom_generate
      (godel_pair_value 1 payload)).map
        (fun sentence =>
          Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence)) =
      some formula at hGenerate
  cases hAxiom :
      fs_zfc_axiom_generate
        (godel_pair_value 1 payload) with
  | none =>
      simp [hAxiom] at hGenerate
  | some sentence =>
      simp only [hAxiom, Option.map_some,
        Option.some.injEq] at hGenerate
      subst formula
      unfold fs_zfc_axiom_generate at hAxiom
      simp [godel_unpair_value_pair] at hAxiom
      rcases
          ProofT.SchemaGeneratorPlugin.generate_list_some
            fs_zfc_schema_generator_plugins
            (godel_unpair_value payload).1
            (godel_unpair_value payload).2 hAxiom with
        ⟨plugin, hPlugin, hTag, hPluginGenerate⟩
      have hPluginCase :
          plugin = fs_zfc_separation_generator_plugin ∨
            plugin = fs_zfc_collection_generator_plugin :=
        fs_zfc_schema_generator_plugins_elim
          (P := fun member =>
            member = fs_zfc_separation_generator_plugin ∨
              member = fs_zfc_collection_generator_plugin)
          (Or.inl rfl) (Or.inr rfl) plugin hPlugin
      rcases hPluginCase with hSeparation | hCollection
      · subst plugin
        change (godel_unpair_value payload).1 = 0 at hTag
        change
          fs_zfc_separation_generate
              (godel_unpair_value payload).2 =
            some sentence at hPluginGenerate
        have hProof :=
          fs_zfc_support_raw_object_certificate_condition_of_separation_generate
            hPluginGenerate
        have hPayload :
            payload =
              godel_pair_value 0
                (godel_unpair_value payload).2 := by
          calc
            payload =
                godel_pair_value
                  (godel_unpair_value payload).1
                  (godel_unpair_value payload).2 := by
              symm
              exact godel_unpair_value_spec payload
            _ =
                godel_pair_value 0
                  (godel_unpair_value payload).2 := by
              rw [hTag]
        have hCertificate :
            numₘ(godel_pair_value 1 payload) =
              numₘ(
                godel_pair_value 1
                  (godel_pair_value 0
                    (godel_unpair_value payload).2)) := by
          exact congrArg
            (fun value => numₘ(godel_pair_value 1 value))
            hPayload
        rw [hCertificate]
        exact hProof
      · subst plugin
        change (godel_unpair_value payload).1 = 1 at hTag
        change
          fs_zfc_collection_generate
              (godel_unpair_value payload).2 =
            some sentence at hPluginGenerate
        have hProof :=
          fs_zfc_support_raw_object_certificate_condition_of_collection_generate
            hPluginGenerate
        have hPayload :
            payload =
              godel_pair_value 1
                (godel_unpair_value payload).2 := by
          calc
            payload =
                godel_pair_value
                  (godel_unpair_value payload).1
                  (godel_unpair_value payload).2 := by
              symm
              exact godel_unpair_value_spec payload
            _ =
                godel_pair_value 1
                  (godel_unpair_value payload).2 := by
              rw [hTag]
        have hCertificate :
            numₘ(godel_pair_value 1 payload) =
              numₘ(
                godel_pair_value 1
                  (godel_pair_value 1
                    (godel_unpair_value payload).2)) := by
          exact congrArg
            (fun value => numₘ(godel_pair_value 1 value))
            hPayload
        rw [hCertificate]
        exact hProof

private theorem fs_zfc_support_raw_object_certificate_condition_of_fixed_zfc_generate
    {payload : Nat}
    {formula : SetFormula}
    (hGenerate :
      fs_zfc_embedded_hilbert_generator.generate
        (godel_pair_value 0 payload) =
        some formula) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition
        (fs_zfc_formula_code_term formula)
        (numₘ(godel_pair_value 3 payload))) := by
  change
    (fs_zfc_axiom_generate
      (godel_pair_value 0 payload)).map
        (fun sentence =>
          Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence)) =
      some formula at hGenerate
  cases hAxiom :
      fs_zfc_axiom_generate
        (godel_pair_value 0 payload) with
  | none =>
      simp [hAxiom] at hGenerate
  | some sentence =>
      simp only [hAxiom, Option.map_some,
        Option.some.injEq] at hGenerate
      subst formula
      unfold fs_zfc_axiom_generate at hAxiom
      simp [godel_unpair_value_pair] at hAxiom
      exact
        fs_zfc_support_raw_object_certificate_condition_of_fixed_zfc_getElem?
          hAxiom

private theorem fs_zfc_support_raw_object_certificate_condition_with_base_of_internal_generate
    {certificate : Nat}
    {formula : SetFormula}
    (hGenerate :
      (HilbertTheoryGenerator.hilbertize
        SetSort.set
        (HilbertTheoryGenerator.ofFinite
          fs_internal_encoding_finite_presentation)).generate
        certificate =
        some formula)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_base
        (fs_zfc_formula_code_term formula)
        (numₘ(godel_pair_value 0 certificate)) base) := by
  change
    (fs_internal_encoding_finite_presentation.axioms[certificate]?).map
        (Formula.hilbertize SetSort.set) =
      some formula at hGenerate
  cases hSource :
      fs_internal_encoding_finite_presentation.axioms[certificate]? with
  | none =>
      simp [hSource] at hGenerate
  | some source =>
      simp only [hSource, Option.map_some,
        Option.some.injEq] at hGenerate
      subst formula
      exact
        fs_zfc_support_raw_object_certificate_condition_with_base_of_internal_getElem?
          hSource base

private theorem fs_zfc_support_raw_object_certificate_condition_with_base_of_project_definition_generate
    {certificate : Nat}
    {formula : SetFormula}
    (hGenerate :
      (HilbertTheoryGenerator.hilbertize
        SetSort.set
        (HilbertTheoryGenerator.ofFinite
          fs_project_definition_finite_presentation)).generate
        certificate =
        some formula)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_base
        (fs_zfc_formula_code_term formula)
        (numₘ(godel_pair_value 2 certificate)) base) := by
  change
    (fs_project_definition_finite_presentation.axioms[certificate]?).map
        (Formula.hilbertize SetSort.set) =
      some formula at hGenerate
  cases hSource :
      fs_project_definition_finite_presentation.axioms[certificate]? with
  | none =>
      simp [hSource] at hGenerate
  | some source =>
      simp only [hSource, Option.map_some,
        Option.some.injEq] at hGenerate
      subst formula
      exact
        fs_zfc_support_raw_object_certificate_condition_with_base_of_project_definition_getElem?
          hSource base

private theorem fs_zfc_support_raw_object_certificate_condition_with_base_of_fixed_zfc_generate
    {payload : Nat}
    {formula : SetFormula}
    (hGenerate :
      fs_zfc_embedded_hilbert_generator.generate
        (godel_pair_value 0 payload) =
        some formula)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_base
        (fs_zfc_formula_code_term formula)
        (numₘ(godel_pair_value 3 payload)) base) := by
  change
    (fs_zfc_axiom_generate
      (godel_pair_value 0 payload)).map
        (fun sentence =>
          Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence)) =
      some formula at hGenerate
  cases hAxiom :
      fs_zfc_axiom_generate
        (godel_pair_value 0 payload) with
  | none =>
      simp [hAxiom] at hGenerate
  | some sentence =>
      simp only [hAxiom, Option.map_some,
        Option.some.injEq] at hGenerate
      subst formula
      unfold fs_zfc_axiom_generate at hAxiom
      simp [godel_unpair_value_pair] at hAxiom
      exact
        fs_zfc_support_raw_object_certificate_condition_with_base_of_fixed_zfc_getElem?
          hAxiom base

private theorem fs_zfc_support_raw_object_certificate_condition_with_base_of_separation_generate
    {payload : Nat}
    {sentence : FsProjectSentence}
    (hGenerate :
      fs_zfc_separation_generate payload =
        some sentence)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_base
        (fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence)))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 0 payload))) base) := by
  unfold fs_zfc_separation_generate at hGenerate
  dsimp only at hGenerate
  cases hDecode :
      fs_project_unary_schema_hilbert_decode
        (godel_unpair_value payload).1
        (godel_unpair_value payload).2 with
  | none =>
      simp [hDecode] at hGenerate
  | some schema =>
      simp only [hDecode, Option.map_some,
        Option.some.injEq] at hGenerate
      subst sentence
      have hBodyDecode :=
        fs_project_unary_schema_hilbert_decode_body hDecode
      have hBodyCode :
          (godel_unpair_value payload).2 =
            nat_sequence_code_value
              (fs_project_hilbert_token_tree schema.body).tokens :=
        fs_project_hilbert_code_decode_code_eq hBodyDecode
      have hPayload :
          payload =
            fs_zfc_schema_certificate
              (godel_unpair_value payload).1
              (nat_sequence_code_value
                (fs_project_hilbert_token_tree schema.body).tokens) := by
        calc
          payload =
              godel_pair_value
                (godel_unpair_value payload).1
                (godel_unpair_value payload).2 := by
            symm
            exact godel_unpair_value_spec payload
          _ =
              fs_zfc_schema_certificate
                (godel_unpair_value payload).1
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens) := by
            simp [fs_zfc_schema_certificate, hBodyCode]
      have hSchema :=
        fs_zfc_support_raw_object_certificate_condition_of_separation_schema_at_base
          schema base
      have hCertificate :
          numₘ(
              godel_pair_value 1
                (godel_pair_value 0 payload)) =
            numₘ(
              godel_pair_value 1
                (godel_pair_value 0
                  (fs_zfc_schema_certificate
                    (godel_unpair_value payload).1
                    (nat_sequence_code_value
                      (fs_project_hilbert_token_tree schema.body).tokens)))) := by
        exact congrArg
          (fun value =>
            numₘ(godel_pair_value 1
              (godel_pair_value 0 value)))
          hPayload
      rw [hCertificate]
      exact hSchema

private theorem fs_zfc_support_raw_object_certificate_condition_with_base_of_collection_generate
    {payload : Nat}
    {sentence : FsProjectSentence}
    (hGenerate :
      fs_zfc_collection_generate payload =
        some sentence)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_base
        (fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence)))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 1 payload))) base) := by
  unfold fs_zfc_collection_generate at hGenerate
  dsimp only at hGenerate
  cases hDecode :
      fs_project_binary_schema_hilbert_decode
        (godel_unpair_value payload).1
        (godel_unpair_value payload).2 with
  | none =>
      simp [hDecode] at hGenerate
  | some schema =>
      simp only [hDecode, Option.map_some,
        Option.some.injEq] at hGenerate
      subst sentence
      have hBodyDecode :=
        fs_project_binary_schema_hilbert_decode_body hDecode
      have hBodyCode :
          (godel_unpair_value payload).2 =
            nat_sequence_code_value
              (fs_project_hilbert_token_tree schema.body).tokens :=
        fs_project_hilbert_code_decode_code_eq hBodyDecode
      have hPayload :
          payload =
            fs_zfc_schema_certificate
              (godel_unpair_value payload).1
              (nat_sequence_code_value
                (fs_project_hilbert_token_tree schema.body).tokens) := by
        calc
          payload =
              godel_pair_value
                (godel_unpair_value payload).1
                (godel_unpair_value payload).2 := by
            symm
            exact godel_unpair_value_spec payload
          _ =
              fs_zfc_schema_certificate
                (godel_unpair_value payload).1
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens) := by
            simp [fs_zfc_schema_certificate, hBodyCode]
      have hSchema :=
        fs_zfc_support_raw_object_certificate_condition_of_collection_schema_at_base
          schema base
      have hCertificate :
          numₘ(
              godel_pair_value 1
                (godel_pair_value 1 payload)) =
            numₘ(
              godel_pair_value 1
                (godel_pair_value 1
                  (fs_zfc_schema_certificate
                    (godel_unpair_value payload).1
                    (nat_sequence_code_value
                      (fs_project_hilbert_token_tree schema.body).tokens)))) := by
        exact congrArg
          (fun value =>
            numₘ(godel_pair_value 1
              (godel_pair_value 1 value)))
          hPayload
      rw [hCertificate]
      exact hSchema

private theorem fs_zfc_support_raw_object_certificate_condition_with_base_of_schema_generate
    {payload : Nat}
    {formula : SetFormula}
    (hGenerate :
      fs_zfc_embedded_hilbert_generator.generate
        (godel_pair_value 1 payload) =
        some formula)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_base
        (fs_zfc_formula_code_term formula)
        (numₘ(godel_pair_value 1 payload)) base) := by
  change
    (fs_zfc_axiom_generate
      (godel_pair_value 1 payload)).map
        (fun sentence =>
          Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence)) =
      some formula at hGenerate
  cases hAxiom :
      fs_zfc_axiom_generate
        (godel_pair_value 1 payload) with
  | none =>
      simp [hAxiom] at hGenerate
  | some sentence =>
      simp only [hAxiom, Option.map_some,
        Option.some.injEq] at hGenerate
      subst formula
      unfold fs_zfc_axiom_generate at hAxiom
      simp [godel_unpair_value_pair] at hAxiom
      rcases
          ProofT.SchemaGeneratorPlugin.generate_list_some
            fs_zfc_schema_generator_plugins
            (godel_unpair_value payload).1
            (godel_unpair_value payload).2 hAxiom with
        ⟨plugin, hPlugin, hTag, hPluginGenerate⟩
      have hPluginCase :
          plugin = fs_zfc_separation_generator_plugin ∨
            plugin = fs_zfc_collection_generator_plugin :=
        fs_zfc_schema_generator_plugins_elim
          (P := fun member =>
            member = fs_zfc_separation_generator_plugin ∨
              member = fs_zfc_collection_generator_plugin)
          (Or.inl rfl) (Or.inr rfl) plugin hPlugin
      rcases hPluginCase with hSeparation | hCollection
      · subst plugin
        change (godel_unpair_value payload).1 = 0 at hTag
        change
          fs_zfc_separation_generate
              (godel_unpair_value payload).2 =
            some sentence at hPluginGenerate
        have hProof :=
          fs_zfc_support_raw_object_certificate_condition_with_base_of_separation_generate
            hPluginGenerate base
        have hPayload :
            payload =
              godel_pair_value 0
                (godel_unpair_value payload).2 := by
          calc
            payload =
                godel_pair_value
                  (godel_unpair_value payload).1
                  (godel_unpair_value payload).2 := by
              symm
              exact godel_unpair_value_spec payload
            _ =
                godel_pair_value 0
                  (godel_unpair_value payload).2 := by
              rw [hTag]
        have hCertificate :
            numₘ(godel_pair_value 1 payload) =
              numₘ(
                godel_pair_value 1
                  (godel_pair_value 0
                    (godel_unpair_value payload).2)) := by
          exact congrArg
            (fun value => numₘ(godel_pair_value 1 value))
            hPayload
        rw [hCertificate]
        exact hProof
      · subst plugin
        change (godel_unpair_value payload).1 = 1 at hTag
        change
          fs_zfc_collection_generate
              (godel_unpair_value payload).2 =
            some sentence at hPluginGenerate
        have hProof :=
          fs_zfc_support_raw_object_certificate_condition_with_base_of_collection_generate
            hPluginGenerate base
        have hPayload :
            payload =
              godel_pair_value 1
                (godel_unpair_value payload).2 := by
          calc
            payload =
                godel_pair_value
                  (godel_unpair_value payload).1
                  (godel_unpair_value payload).2 := by
              symm
              exact godel_unpair_value_spec payload
            _ =
                godel_pair_value 1
                  (godel_unpair_value payload).2 := by
              rw [hTag]
        have hCertificate :
            numₘ(godel_pair_value 1 payload) =
              numₘ(
                godel_pair_value 1
                  (godel_pair_value 1
                    (godel_unpair_value payload).2)) := by
          exact congrArg
            (fun value => numₘ(godel_pair_value 1 value))
            hPayload
        rw [hCertificate]
        exact hProof

theorem fs_zfc_support_raw_object_certificate_condition_of_generate
    {certificate : Nat}
    {formula : SetFormula}
    (hGenerate :
      fs_zfc_support_generate certificate =
        some formula) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition
        (fs_zfc_formula_code_term formula)
        (numₘ(certificate))) := by
  unfold fs_zfc_support_generate at hGenerate
  dsimp only at hGenerate
  split at hGenerate
  next hInternal =>
    have hProof :=
      fs_zfc_support_raw_object_certificate_condition_of_internal_generate
        hGenerate
    have hCertificate :
        certificate =
          godel_pair_value 0
            (godel_unpair_value certificate).2 := by
      calc
        certificate =
            godel_pair_value
              (godel_unpair_value certificate).1
              (godel_unpair_value certificate).2 := by
          symm
          exact godel_unpair_value_spec certificate
        _ =
            godel_pair_value 0
              (godel_unpair_value certificate).2 := by
          rw [hInternal]
    rw [hCertificate]
    exact hProof
  next hNotInternal =>
    split at hGenerate
    next hSchema =>
      have hProof :=
        fs_zfc_support_raw_object_certificate_condition_of_schema_generate
          hGenerate
      have hCertificate :
          certificate =
            godel_pair_value 1
              (godel_unpair_value certificate).2 := by
        calc
          certificate =
              godel_pair_value
                (godel_unpair_value certificate).1
                (godel_unpair_value certificate).2 := by
            symm
            exact godel_unpair_value_spec certificate
          _ =
              godel_pair_value 1
                (godel_unpair_value certificate).2 := by
            rw [hSchema]
      rw [hCertificate]
      exact hProof
    next hNotSchema =>
      split at hGenerate
      next hProject =>
        have hProof :=
          fs_zfc_support_raw_object_certificate_condition_of_project_definition_generate
            hGenerate
        have hCertificate :
            certificate =
              godel_pair_value 2
                (godel_unpair_value certificate).2 := by
          calc
            certificate =
                godel_pair_value
                  (godel_unpair_value certificate).1
                  (godel_unpair_value certificate).2 := by
              symm
              exact godel_unpair_value_spec certificate
            _ =
                godel_pair_value 2
                  (godel_unpair_value certificate).2 := by
              rw [hProject]
        rw [hCertificate]
        exact hProof
      next hNotProject =>
        split at hGenerate
        next hFixed =>
          have hProof :=
            fs_zfc_support_raw_object_certificate_condition_of_fixed_zfc_generate
              hGenerate
          have hCertificate :
              certificate =
                godel_pair_value 3
                  (godel_unpair_value certificate).2 := by
            calc
              certificate =
                  godel_pair_value
                    (godel_unpair_value certificate).1
                    (godel_unpair_value certificate).2 := by
                symm
                exact godel_unpair_value_spec certificate
              _ =
                  godel_pair_value 3
                    (godel_unpair_value certificate).2 := by
                rw [hFixed]
          rw [hCertificate]
          exact hProof
        next hNotFixed =>
          simp at hGenerate

/-- 生成器成功的显式 base 对象证书条件。 -/
theorem fs_zfc_support_raw_object_certificate_condition_with_base_of_generate
    {certificate : Nat}
    {formula : SetFormula}
    (hGenerate :
      fs_zfc_support_generate certificate =
        some formula)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_base
        (fs_zfc_formula_code_term formula)
        (numₘ(certificate)) base) := by
  unfold fs_zfc_support_generate at hGenerate
  dsimp only at hGenerate
  split at hGenerate
  next hInternal =>
    have hProof :=
      fs_zfc_support_raw_object_certificate_condition_with_base_of_internal_generate
        hGenerate base
    have hCertificate :
        certificate =
          godel_pair_value 0
            (godel_unpair_value certificate).2 := by
      calc
        certificate =
            godel_pair_value
              (godel_unpair_value certificate).1
              (godel_unpair_value certificate).2 := by
          symm
          exact godel_unpair_value_spec certificate
        _ =
            godel_pair_value 0
              (godel_unpair_value certificate).2 := by
          rw [hInternal]
    rw [hCertificate]
    exact hProof
  next hNotInternal =>
    split at hGenerate
    next hSchema =>
      have hProof :=
        fs_zfc_support_raw_object_certificate_condition_with_base_of_schema_generate
          hGenerate base
      have hCertificate :
          certificate =
            godel_pair_value 1
              (godel_unpair_value certificate).2 := by
        calc
          certificate =
              godel_pair_value
                (godel_unpair_value certificate).1
                (godel_unpair_value certificate).2 := by
            symm
            exact godel_unpair_value_spec certificate
          _ =
              godel_pair_value 1
                (godel_unpair_value certificate).2 := by
            rw [hSchema]
      rw [hCertificate]
      exact hProof
    next hNotSchema =>
      split at hGenerate
      next hProject =>
        have hProof :=
          fs_zfc_support_raw_object_certificate_condition_with_base_of_project_definition_generate
            hGenerate base
        have hCertificate :
            certificate =
              godel_pair_value 2
                (godel_unpair_value certificate).2 := by
          calc
            certificate =
                godel_pair_value
                  (godel_unpair_value certificate).1
                  (godel_unpair_value certificate).2 := by
              symm
              exact godel_unpair_value_spec certificate
            _ =
                godel_pair_value 2
                  (godel_unpair_value certificate).2 := by
              rw [hProject]
        rw [hCertificate]
        exact hProof
      next hNotProject =>
        split at hGenerate
        next hFixed =>
          have hProof :=
            fs_zfc_support_raw_object_certificate_condition_with_base_of_fixed_zfc_generate
              hGenerate base
          have hCertificate :
              certificate =
                godel_pair_value 3
                  (godel_unpair_value certificate).2 := by
            calc
              certificate =
                  godel_pair_value
                    (godel_unpair_value certificate).1
                    (godel_unpair_value certificate).2 := by
                symm
                exact godel_unpair_value_spec certificate
              _ =
                  godel_pair_value 3
                    (godel_unpair_value certificate).2 := by
                rw [hFixed]
          rw [hCertificate]
          exact hProof
        next hNotFixed =>
          simp at hGenerate

/-!
将递归枚举器的布尔 verifier 收口到显式 fresh-base 的对象证书条件。
-/
theorem fs_zfc_support_raw_object_certificate_condition_with_base_of_verifier
    {certificate : Nat}
    {formula : SetFormula}
    (hVerifier :
      fs_zfc_support_enumeration.certificate_verifier
        certificate formula = true)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_base
        (fs_zfc_formula_code_term formula)
        (numₘ(certificate)) base) := by
  simp only [
    fs_zfc_support_enumeration,
    HilbertTheoryGenerator.toEnumeration] at hVerifier
  cases hGenerate : fs_zfc_support_generator.generate certificate with
  | none =>
      simp [hGenerate] at hVerifier
  | some candidate =>
      simp only [hGenerate] at hVerifier
      have hCode :
          GodelQuotation.SyntaxCoding.formula_encode candidate =
            GodelQuotation.SyntaxCoding.formula_encode formula := by
        exact of_decide_eq_true hVerifier
      have hFormula : candidate = formula :=
        GodelQuotation.SyntaxCoding.formula_encode_injective hCode
      subst formula
      exact
        fs_zfc_support_raw_object_certificate_condition_with_base_of_generate
          hGenerate base

/-!
将递归枚举器的布尔 verifier 收口到对象层证书条件。

这里不重新展开四类生成分支；候选公式的 Gödel 编码比较由
`toEnumeration` 本身负责，生成器回放合同则统一承担对象层证明。
-/
theorem fs_zfc_support_raw_object_certificate_condition_of_verifier
    {certificate : Nat}
    {formula : SetFormula}
    (hVerifier :
      fs_zfc_support_enumeration.certificate_verifier
        certificate formula = true) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition
        (fs_zfc_formula_code_term formula)
        (numₘ(certificate))) := by
  simp only [
    fs_zfc_support_enumeration,
    HilbertTheoryGenerator.toEnumeration] at hVerifier
  cases hGenerate : fs_zfc_support_generator.generate certificate with
  | none =>
      simp [hGenerate] at hVerifier
  | some candidate =>
      simp only [hGenerate] at hVerifier
      have hCode :
          GodelQuotation.SyntaxCoding.formula_encode candidate =
            GodelQuotation.SyntaxCoding.formula_encode formula := by
        exact of_decide_eq_true hVerifier
      have hFormula : candidate = formula :=
        GodelQuotation.SyntaxCoding.formula_encode_injective hCode
      subst formula
      exact
        fs_zfc_support_raw_object_certificate_condition_of_generate
          hGenerate

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
