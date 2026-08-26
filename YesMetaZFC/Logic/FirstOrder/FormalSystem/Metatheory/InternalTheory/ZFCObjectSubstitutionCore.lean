import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.CheckedSyntax
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay

/-!
# ZFC 对象验证器的公共闭项代换核心

本模块只保存固定表闭性与有限层闭量词代换。对象证书验证器和逐行回放
共同依赖这些语法事实，避免让验证器代换层反向依赖完整逐行回放。
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

set_option autoImplicit false

theorem fs_zfc_formula_code_term_freeSupport_nil
    (formula : SetFormula) :
    Term.freeSupport (fs_zfc_formula_code_term formula) = [] := by
  unfold fs_zfc_formula_code_term
  cases hQuote : GodelQuotation.Numbered.quote? formula with
  | none =>
      simp [standard_token_sequence_freeSupport_nil]
  | some code =>
      exact
        (GodelQuotation.Numbered.quote?_code_boundary hQuote).2

theorem fs_zfc_fixed_table_rows_freeSupport_nil
    {row : Nat × SetTerm}
    (hRow : row ∈ fs_zfc_fixed_table_rows) :
    Term.freeSupport row.2 = [] := by
  have hFrom :
      ∀ (wrap : Nat → Nat) (start : Nat)
        (formulas : List SetFormula) {row : Nat × SetTerm},
        row ∈ fs_zfc_fixed_table_rows_from wrap start formulas →
          Term.freeSupport row.2 = [] := by
    intro wrap start formulas
    induction formulas generalizing start with
    | nil =>
        intro row hRow
        simp [fs_zfc_fixed_table_rows_from] at hRow
    | cons formula formulas ih =>
        intro row hRow
        simp only [fs_zfc_fixed_table_rows_from, List.mem_cons] at hRow
        rcases hRow with rfl | hRow
        · exact fs_zfc_formula_code_term_freeSupport_nil _
        · exact ih (start + 1) hRow
  unfold fs_zfc_fixed_table_rows at hRow
  simp only [List.mem_append] at hRow
  rcases hRow with hRow | hRow
  ·
    rcases hRow with hRow | hRow
    · exact hFrom
        (fun index => godel_pair_value 0 index)
        0 fs_internal_encoding_finite_presentation.axioms hRow
    · exact hFrom
        (fun index => godel_pair_value 2 index)
        0 fs_project_definition_finite_presentation.axioms hRow
  · exact hFrom
      (fun index => godel_pair_value 3 index)
      0 (fs_zfc_fixed_axioms.map
        (fun sentence => fs_embed_project_sentence sentence)) hRow

theorem fs_zfc_substitute_free_exists_closed
    (sourceId closedId : FreeVarId)
    (replacement : SetTerm)
    (body bodyResult : SetFormula)
    (hDistinct : sourceId ≠ closedId)
    (hReplacementClosed : Term.BoundClosed replacement)
    (hReplacementFresh :
      (SetSort.set, closedId) ∉ Term.freeSupport replacement)
    (hBody :
      Formula.substituteFree SetSort.set sourceId replacement body =
        bodyResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (Formula.existsE SetSort.set
          (Formula.closeFreeAt SetSort.set closedId 0 body)) =
      Formula.existsE SetSort.set
        (Formula.closeFreeAt SetSort.set closedId 0 bodyResult) := by
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set sourceId closedId 0 replacement body
    hDistinct hReplacementClosed hReplacementFresh]
  rw [hBody]

theorem fs_zfc_substitute_free_exists_five_closed
    (sourceId id1 id2 id3 id4 id5 : FreeVarId)
    (replacement : SetTerm)
    (body bodyResult : SetFormula)
    (hDistinct1 : sourceId ≠ id1)
    (hDistinct2 : sourceId ≠ id2)
    (hDistinct3 : sourceId ≠ id3)
    (hDistinct4 : sourceId ≠ id4)
    (hDistinct5 : sourceId ≠ id5)
    (hReplacementClosed : Term.BoundClosed replacement)
    (hFresh1 :
      (SetSort.set, id1) ∉ Term.freeSupport replacement)
    (hFresh2 :
      (SetSort.set, id2) ∉ Term.freeSupport replacement)
    (hFresh3 :
      (SetSort.set, id3) ∉ Term.freeSupport replacement)
    (hFresh4 :
      (SetSort.set, id4) ∉ Term.freeSupport replacement)
    (hFresh5 :
      (SetSort.set, id5) ∉ Term.freeSupport replacement)
    (hBody :
      Formula.substituteFree SetSort.set sourceId replacement body =
        bodyResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (∃ₘ[SetSort.set, id1],
          ∃ₘ[SetSort.set, id2],
            ∃ₘ[SetSort.set, id3],
              ∃ₘ[SetSort.set, id4],
                ∃ₘ[SetSort.set, id5], body) =
      (∃ₘ[SetSort.set, id1],
        ∃ₘ[SetSort.set, id2],
          ∃ₘ[SetSort.set, id3],
            ∃ₘ[SetSort.set, id4],
              ∃ₘ[SetSort.set, id5], bodyResult) := by
  have h5 :
      Formula.substituteFree SetSort.set sourceId replacement
          (∃ₘ[SetSort.set, id5], body) =
        (∃ₘ[SetSort.set, id5], bodyResult) :=
    fs_zfc_substitute_free_exists_closed
      sourceId id5 replacement body bodyResult
      hDistinct5 hReplacementClosed hFresh5 hBody
  have h4 :
      Formula.substituteFree SetSort.set sourceId replacement
          (∃ₘ[SetSort.set, id4],
            ∃ₘ[SetSort.set, id5], body) =
        (∃ₘ[SetSort.set, id4],
          ∃ₘ[SetSort.set, id5], bodyResult) :=
    fs_zfc_substitute_free_exists_closed
      sourceId id4 replacement
      (∃ₘ[SetSort.set, id5], body)
      (∃ₘ[SetSort.set, id5], bodyResult)
      hDistinct4 hReplacementClosed hFresh4 h5
  have h3 :
      Formula.substituteFree SetSort.set sourceId replacement
          (∃ₘ[SetSort.set, id3],
            ∃ₘ[SetSort.set, id4],
              ∃ₘ[SetSort.set, id5], body) =
        (∃ₘ[SetSort.set, id3],
          ∃ₘ[SetSort.set, id4],
            ∃ₘ[SetSort.set, id5], bodyResult) :=
    fs_zfc_substitute_free_exists_closed
      sourceId id3 replacement
      (∃ₘ[SetSort.set, id4],
        ∃ₘ[SetSort.set, id5], body)
      (∃ₘ[SetSort.set, id4],
        ∃ₘ[SetSort.set, id5], bodyResult)
      hDistinct3 hReplacementClosed hFresh3 h4
  have h2 :
      Formula.substituteFree SetSort.set sourceId replacement
          (∃ₘ[SetSort.set, id2],
            ∃ₘ[SetSort.set, id3],
              ∃ₘ[SetSort.set, id4],
                ∃ₘ[SetSort.set, id5], body) =
        (∃ₘ[SetSort.set, id2],
          ∃ₘ[SetSort.set, id3],
            ∃ₘ[SetSort.set, id4],
              ∃ₘ[SetSort.set, id5], bodyResult) :=
    fs_zfc_substitute_free_exists_closed
      sourceId id2 replacement
      (∃ₘ[SetSort.set, id3],
        ∃ₘ[SetSort.set, id4],
          ∃ₘ[SetSort.set, id5], body)
      (∃ₘ[SetSort.set, id3],
        ∃ₘ[SetSort.set, id4],
          ∃ₘ[SetSort.set, id5], bodyResult)
      hDistinct2 hReplacementClosed hFresh2 h3
  exact
    fs_zfc_substitute_free_exists_closed
      sourceId id1 replacement
      (∃ₘ[SetSort.set, id2],
        ∃ₘ[SetSort.set, id3],
          ∃ₘ[SetSort.set, id4],
            ∃ₘ[SetSort.set, id5], body)
      (∃ₘ[SetSort.set, id2],
        ∃ₘ[SetSort.set, id3],
          ∃ₘ[SetSort.set, id4],
            ∃ₘ[SetSort.set, id5], bodyResult)
      hDistinct1 hReplacementClosed hFresh1 h2

/--
闭项替换逐层穿过任意有限见证闭包。

该列表归纳接口统一覆盖 separation、collection 与 replacement 的不同见证数，
避免为每个 schema 重复维护固定长度的存在量词交换链。
-/
theorem fs_zfc_witness_closure_substitute_closed
    (ids : List FreeVarId)
    (sourceId : FreeVarId)
    (replacement : SetTerm)
    (body bodyResult : SetFormula)
    (hDistinct :
      ∀ id, id ∈ ids → sourceId ≠ id)
    (hReplacementClosed : Term.BoundClosed replacement)
    (hReplacementFresh :
      ∀ id, id ∈ ids →
        (SetSort.set, id) ∉ Term.freeSupport replacement)
    (hBody :
      Formula.substituteFree SetSort.set sourceId replacement body =
        bodyResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (ProofT.SchemaPlugin.witness_closure ids body) =
      ProofT.SchemaPlugin.witness_closure ids bodyResult := by
  induction ids with
  | nil =>
      simpa [ProofT.SchemaPlugin.witness_closure] using hBody
  | cons id ids ih =>
      have hTail :
          Formula.substituteFree SetSort.set sourceId replacement
              (ProofT.SchemaPlugin.witness_closure ids body) =
            ProofT.SchemaPlugin.witness_closure ids bodyResult :=
        ih
          (fun id' hId =>
            hDistinct id' (by simp [hId]))
          (fun id' hId =>
            hReplacementFresh id' (by simp [hId]))
      simpa [ProofT.SchemaPlugin.witness_closure] using
        fs_zfc_substitute_free_exists_closed
          sourceId id replacement
          (ProofT.SchemaPlugin.witness_closure ids body)
          (ProofT.SchemaPlugin.witness_closure ids bodyResult)
          (hDistinct id (by simp))
          hReplacementClosed
          (hReplacementFresh id (by simp))
          hTail

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
