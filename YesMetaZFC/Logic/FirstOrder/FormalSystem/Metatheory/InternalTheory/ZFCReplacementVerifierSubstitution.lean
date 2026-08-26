import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifierSubstitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCReplacementCertificateReplay

/-!
# replacement 对象 verifier 的闭项替换

本模块闭合 replacement 十见证条件的 substitution 合同，并将它与固定公理表及
separation 插件合成为公开 replacement verifier 的完整合同。
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

private theorem fs_zfc_replacement_source_ne_schema_id
    {sourceId internalId : FreeVarId}
    (hSource : sourceId < 904)
    (hInternal : 904 ≤ internalId) :
    sourceId ≠ internalId :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le hSource hInternal)

/--
replacement 的十见证条件在保留编号区间以下逐参数保持闭项替换。

开放 body 内部的捕获规避 substitution 已由
`fs_zfc_replacement_condition_body_substitute_closed` 完成；此处只负责固定内部
变量、证明保留编号新鲜，并统一穿过十层存在闭包。
-/
theorem fs_zfc_replacement_condition_with_reserved_base_substitute_closed
    (formula certificate replacement
      formulaResult certificateResult : SetTerm)
    (sourceId : FreeVarId)
    (hSource : sourceId < 904)
    (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement)
    (hFormulaSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formula =
        formulaResult)
    (hCertificateSubstitution :
      Term.substituteFree SetSort.set sourceId replacement certificate =
        certificateResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (fs_zfc_replacement_condition_with_base
          formula certificate 904) =
      fs_zfc_replacement_condition_with_base
        formulaResult certificateResult 904 := by
  have hNe (id : FreeVarId) (hId : 904 ≤ id) :
      sourceId ≠ id :=
    fs_zfc_replacement_source_ne_schema_id hSource hId
  have hVariableFixed (id : FreeVarId) (hId : 904 ≤ id) :
      Term.substituteFree SetSort.set sourceId replacement (x#id) =
        x#id := by
    simp [Term.substituteFree, set_variable,
      Ne.symm (hNe id hId)]
  let Fresh (term : SetTerm) : Prop :=
    ∀ id, id ∈ [310, 311] →
      (SetSort.set, id) ∉ Term.freeSupport term
  have hClosedFresh :
      Fresh replacement := by
    intro id _
    rw [hReplacement.2]
    exact List.not_mem_nil
  have hVariableFresh (offset : Nat) :
      Fresh (x#(904 + offset)) := by
    intro id hId hMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
    change
      (SetSort.set, id) ∈
        [(SetSort.set, 904 + offset)]
      at hMember
    have hEquality :
        id = 904 + offset :=
      congrArg Prod.snd (List.mem_singleton.mp hMember)
    rcases hId with rfl | rfl
    · exact
        (Nat.ne_of_gt <|
          Nat.lt_of_lt_of_le (by decide : 310 < 904)
            (Nat.le_add_right 904 offset))
          hEquality.symm
    · exact
        (Nat.ne_of_gt <|
          Nat.lt_of_lt_of_le (by decide : 311 < 904)
            (Nat.le_add_right 904 offset))
          hEquality.symm
  have hNamedFresh :
      Fresh
        (GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.free_name 0)) := by
    intro id _
    rw [GodelQuotation.named_variable_code_freeSupport]
    exact List.not_mem_nil
  have hReserved :
      ReservedIdsFresh [310, 311]
        [replacement, (x#(904 + 6)),
          canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(x#904)))),
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0),
          (x#(904 + 7)),
          canonical_binder_variable_code_term
            (Sₘ(Sₘ(x#904))),
          (x#(904 + 8)), (x#(904 + 9))] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
    rcases hTerm with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hClosedFresh id hId
    · exact hVariableFresh 6 id hId
    · simpa [canonical_binder_variable_code_term,
        canonical_binder_name_term,
        Term.freeSupport, Term.freeSupportList] using
        hVariableFresh 0 id hId
    · exact hNamedFresh id hId
    · exact hVariableFresh 7 id hId
    · simpa [canonical_binder_variable_code_term,
        canonical_binder_name_term,
        Term.freeSupport, Term.freeSupportList] using
        hVariableFresh 0 id hId
    · exact hVariableFresh 8 id hId
    · exact hVariableFresh 9 id hId
  have hBody :
      Formula.substituteFree SetSort.set sourceId replacement
          (fs_zfc_replacement_condition_open_body
            formula certificate 904) =
        fs_zfc_replacement_condition_open_body
          formulaResult certificateResult 904 := by
    change
      Formula.substituteFree SetSort.set sourceId replacement
          (fs_zfc_replacement_condition_body
            formula certificate
            (x#904) (x#(904 + 1)) (x#(904 + 2))
            (x#(904 + 3)) (x#(904 + 4))
            (x#(904 + 5)) (x#(904 + 6))
            (x#(904 + 7)) (x#(904 + 8)) (x#(904 + 9))
            904) =
        fs_zfc_replacement_condition_body
          formulaResult certificateResult
          (x#904) (x#(904 + 1)) (x#(904 + 2))
          (x#(904 + 3)) (x#(904 + 4))
          (x#(904 + 5)) (x#(904 + 6))
          (x#(904 + 7)) (x#(904 + 8)) (x#(904 + 9))
          904
    simpa [hFormulaSubstitution, hCertificateSubstitution,
      hVariableFixed] using
      fs_zfc_replacement_condition_body_substitute_closed
        formula certificate
        (x#904) (x#(904 + 1)) (x#(904 + 2))
        (x#(904 + 3)) (x#(904 + 4))
        (x#(904 + 5)) (x#(904 + 6))
        (x#(904 + 7)) (x#(904 + 8)) (x#(904 + 9))
        replacement 904 sourceId
        (Nat.lt_trans hSource (by decide)) hReplacement
        (by prove_term_check) (by prove_term_check)
        (by prove_term_check) (by prove_term_check)
        (by prove_term_check) hReserved
  have hDistinct :
      ∀ id,
        id ∈ (List.range 10 |>.map (904 + ·)) →
          sourceId ≠ id := by
    intro id hId
    simp only [List.mem_map, List.mem_range] at hId
    rcases hId with ⟨offset, hOffset, rfl⟩
    exact hNe (904 + offset) (Nat.le_add_right 904 offset)
  have hFresh :
      ∀ id,
        id ∈ (List.range 10 |>.map (904 + ·)) →
          (SetSort.set, id) ∉ Term.freeSupport replacement := by
    intro id _
    rw [hReplacement.2]
    exact List.not_mem_nil
  rw [fs_zfc_replacement_condition_exists_shape,
    fs_zfc_replacement_condition_exists_shape]
  exact
    fs_zfc_witness_closure_substitute_closed
      (List.range 10 |>.map (904 + ·))
      sourceId replacement
      (fs_zfc_replacement_condition_open_body
        formula certificate 904)
      (fs_zfc_replacement_condition_open_body
        formulaResult certificateResult 904)
      hDistinct hReplacement.1.2 hFresh hBody

/-- 固定内部基点 `904` 的 replacement 对象 verifier 保持闭项替换。 -/
theorem fs_zfc_replacement_object_certificate_condition_with_reserved_base_substitute_closed
    (formula certificate replacement
      formulaResult certificateResult : SetTerm)
    (sourceId : FreeVarId)
    (hSource : sourceId < 904)
    (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement)
    (hFormulaSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formula =
        formulaResult)
    (hCertificateSubstitution :
      Term.substituteFree SetSort.set sourceId replacement certificate =
        certificateResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (fs_zfc_replacement_object_certificate_condition_with_base
          formula certificate 904) =
      fs_zfc_replacement_object_certificate_condition_with_base
        formulaResult certificateResult 904 := by
  have hFixedTable :
      Formula.substituteFree SetSort.set sourceId replacement
          (fs_zfc_fixed_axiom_table.condition formula certificate) =
        fs_zfc_fixed_axiom_table.condition
          formulaResult certificateResult :=
    ProofT.FixedAxiomTable.condition_rows_substitute
      fs_zfc_fixed_table_rows
      formula certificate formulaResult certificateResult
      replacement sourceId
      (fun row hRow =>
        fs_zfc_fixed_table_rows_freeSupport_nil hRow)
      hFormulaSubstitution hCertificateSubstitution
  have hSeparation :=
    fs_zfc_separation_condition_with_reserved_base_substitute_closed
      formula certificate replacement
      formulaResult certificateResult sourceId
      hSource hReplacement
      hFormulaSubstitution hCertificateSubstitution
  have hReplacementCondition :=
    fs_zfc_replacement_condition_with_reserved_base_substitute_closed
      formula certificate replacement
      formulaResult certificateResult sourceId
      hSource hReplacement
      hFormulaSubstitution hCertificateSubstitution
  exact
    fs_zfc_object_certificate_condition_with_plugins_reserved_base_substitute_closed
      fs_zfc_replacement_schema_plugins
      formula certificate replacement
      formulaResult certificateResult sourceId
      hFixedTable
      (fs_zfc_replacement_schema_plugins_elim
        (by
          simpa [fs_zfc_separation_schema_plugin] using
            hSeparation)
        (by
          simpa [fs_zfc_replacement_schema_plugin] using
            hReplacementCondition))

/-- 公开 replacement verifier 的完整闭项替换合同。 -/
theorem ProofT.ZFCRep.verifier_substitute
    (formula certificate replacement
      formulaResult certificateResult : SetTerm)
    (sourceId : FreeVarId)
    (hSource : sourceId < 904)
    (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement)
    (hFormulaSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formula =
        formulaResult)
    (hCertificateSubstitution :
      Term.substituteFree SetSort.set sourceId replacement certificate =
        certificateResult)
    (hSourceBase :
      ProofT.schema_base [formula, certificate] = 904)
    (hTargetBase :
      ProofT.schema_base
        [formulaResult, certificateResult] = 904) :
    Formula.substituteFree SetSort.set sourceId replacement
        (fs_zfc_replacement_object_certificate_verifier.condition
          formula certificate) =
      fs_zfc_replacement_object_certificate_verifier.condition
        formulaResult certificateResult := by
  change Formula.substituteFree SetSort.set sourceId replacement
      (fs_zfc_replacement_object_certificate_condition
        formula certificate) =
    fs_zfc_replacement_object_certificate_condition
      formulaResult certificateResult
  simp only [fs_zfc_replacement_object_certificate_condition]
  rw [hSourceBase, hTargetBase]
  exact
    fs_zfc_replacement_object_certificate_condition_with_reserved_base_substitute_closed
      formula certificate replacement
      formulaResult certificateResult sourceId
      hSource hReplacement
      hFormulaSubstitution hCertificateSubstitution

/-- separation+replacement verifier 满足 checked 运输合同。 -/
def ProofT.ZFCRep.verifier_transport :
    ProofT.VerifierTransport
      fs_zfc_replacement_object_certificate_verifier where
  formula_condition := rfl
  substitute_closed :=
    ProofT.ZFCRep.verifier_substitute

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
