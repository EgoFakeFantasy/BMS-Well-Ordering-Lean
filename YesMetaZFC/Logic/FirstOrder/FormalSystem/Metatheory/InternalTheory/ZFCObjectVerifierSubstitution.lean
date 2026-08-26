import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectSubstitutionCore
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTraceLegality.FormulaTrace
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTraceLegality.ForallPrefix
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CheckedSubstitution

/-!
# ZFC 对象证书 verifier 的闭项替换

本模块集中证明保留编号区间以下的闭项替换可以穿过 ZFC schema verifier。
`904` 及以上编号只属于 verifier 内部见证；Rosser 证明码和逐行回放使用的
外层编号严格低于该边界。
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

private theorem fs_zfc_source_ne_schema_id
    {sourceId internalId : FreeVarId}
    (hSource : sourceId < 904)
    (hInternal : 904 ≤ internalId) :
    sourceId ≠ internalId :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le hSource hInternal)

private theorem fs_zfc_schema_nat_sequence_condition_fixed
    (sourceId : FreeVarId)
    (replacement : SetTerm)
    (hSource : sourceId < 904) :
    Formula.substituteFree SetSort.set sourceId replacement
        (nat_sequence_code_condition_with_ids
          (x#906) (x#905) 909 910) =
      nat_sequence_code_condition_with_ids
        (x#906) (x#905) 909 910 := by
  apply Formula.substituteFree_eq_self_of_not_mem
  simp [nat_sequence_code_condition_with_ids,
    sequence_domain_code_bound,
    nat_sequence_value_code_bound_with_id,
    sequence_trace_code_bound_with_id,
    nat_sequence_code_step_condition,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt, Formula.freeSupport,
    Term.freeSupport, Term.freeSupportList, set_variable,
    finite_numeral_term_freeSupport,
    Term.not_mem_freeSupport_closeFreeAt_of_not_mem]
  have h905 : sourceId ≠ 905 :=
    Nat.ne_of_lt (Nat.lt_trans hSource (by decide))
  have h906 : sourceId ≠ 906 :=
    Nat.ne_of_lt (Nat.lt_trans hSource (by decide))
  simp [h905, h906]

/--
分离 schema 条件在保留编号区间以下逐参数保持闭项替换。

内部五个见证和三组分类轨迹均位于 `904` 以上，因此调用方只需给出
两个外部实参的替换结果。
-/
theorem fs_zfc_separation_condition_with_reserved_base_substitute_closed
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
        (fs_zfc_separation_condition_with_base
          formula certificate 904) =
      fs_zfc_separation_condition_with_base
        formulaResult certificateResult 904 := by
  have hNe (id : FreeVarId) (hId : 904 ≤ id) :
      sourceId ≠ id :=
    fs_zfc_source_ne_schema_id hSource hId
  have hVariableFixed (id : FreeVarId) (hId : 904 ≤ id) :
      Term.substituteFree SetSort.set sourceId replacement (x#id) =
        x#id := by
    simp [Term.substituteFree, set_variable,
      Ne.symm (hNe id hId)]
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set sourceId replacement
          (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hOmegaFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (ωₘ : SetTerm) =
        ωₘ := by
    apply Term.substituteFree_eq_self_of_not_mem
    change (SetSort.set, sourceId) ∉ []
    exact List.not_mem_nil
  have hParameterFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#904) =
        x#904 :=
    hVariableFixed 904 (by decide)
  have hBodyTokenFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#905) =
        x#905 :=
    hVariableFixed 905 (by decide)
  have hBodyCodeFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#906) =
        x#906 :=
    hVariableFixed 906 (by decide)
  have hShiftOneFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#907) =
        x#907 :=
    hVariableFixed 907 (by decide)
  have hShiftTwoFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#908) =
        x#908 :=
    hVariableFixed 908 (by decide)
  have hParameterOneFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (Sₘ(x#904)) =
        Sₘ(x#904) := by
    simp [Term.substituteFree, hParameterFixed]
  have hParameterTwoFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (Sₘ(Sₘ(x#904))) =
        Sₘ(Sₘ(x#904)) := by
    simp [Term.substituteFree, hParameterFixed]
  have hCertificateTermFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (fs_zfc_schema_certificate_term
            (numₘ(0)) (x#904) (x#905)) =
        fs_zfc_schema_certificate_term
          (numₘ(0)) (x#904) (x#905) := by
    simp [fs_zfc_schema_certificate_term,
      fs_zfc_schema_payload_term,
      fs_zfc_schema_body_payload_term,
      Term.substituteFree, set_variable,
      hParameterFixed, hBodyTokenFixed,
      hNumeralFixed 0, hNumeralFixed 1

      ]
  have hCertificate :
      Formula.substituteFree SetSort.set sourceId replacement
          (certificate ≐ₘ
            fs_zfc_schema_certificate_term
              (numₘ(0)) (x#904) (x#905)) =
        (certificateResult ≐ₘ
          fs_zfc_schema_certificate_term
            (numₘ(0)) (x#904) (x#905)) := by
    simp [Formula.substituteFree,
      hCertificateSubstitution, hCertificateTermFixed]
  have hCertificateBounds :
      Formula.substituteFree SetSort.set sourceId replacement
          (fs_zfc_schema_certificate_bounds
            certificate (numₘ(0)) (x#904) (x#905)) =
        fs_zfc_schema_certificate_bounds
          certificateResult (numₘ(0)) (x#904) (x#905) := by
    simp [fs_zfc_schema_certificate_bounds,
      fs_zfc_schema_payload_term,
      fs_zfc_schema_body_payload_term,
      Formula.substituteFree, Term.substituteFree,
      hCertificateSubstitution, hParameterFixed,
      hBodyTokenFixed, hNumeralFixed]
  have hParameterNatural :
      Formula.substituteFree SetSort.set sourceId replacement
          (x#904 ∈ₘ ωₘ) =
        (x#904 ∈ₘ ωₘ) := by
    apply Formula.substituteFree_eq_self_of_not_mem
    simp [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      hNe 904 (by decide)]
  have hSequence :
      Formula.substituteFree SetSort.set sourceId replacement
          (nat_sequence_code_condition_with_ids
            (x#906) (x#905) 909 910) =
        nat_sequence_code_condition_with_ids
          (x#906) (x#905) 909 910 :=
    fs_zfc_schema_nat_sequence_condition_fixed
      sourceId replacement hSource
  have hClassifier :
      Formula.substituteFree SetSort.set sourceId replacement
          (canonical_project_formula_code_condition_with_ids
            (Sₘ(x#904)) (x#906)
            911 912 913 914 915 916 917 918 919 920) =
        canonical_project_formula_code_condition_with_ids
          (Sₘ(x#904)) (x#906)
          911 912 913 914 915 916 917 918 919 920 := by
    simpa using
      canonical_project_formula_code_condition_with_ids_substitute_closed
        (Sₘ(x#904)) (x#906) replacement
        (Sₘ(x#904)) (x#906)
        sourceId 911 912 913 914 915 916 917 918 919 920
        (hNe 911 (by decide)) (hNe 912 (by decide))
        (hNe 913 (by decide)) (hNe 914 (by decide))
        (hNe 915 (by decide)) (hNe 916 (by decide))
        (hNe 917 (by decide)) (hNe 918 (by decide))
        (hNe 919 (by decide)) (hNe 920 (by decide))
        hReplacement hParameterOneFixed hBodyCodeFixed
  have hShiftFirst :
      Formula.substituteFree SetSort.set sourceId replacement
          (canonical_project_shift_code_condition_with_ids
            (x#904) (x#906) (x#907) 921 922 923) =
        canonical_project_shift_code_condition_with_ids
          (x#904) (x#906) (x#907) 921 922 923 := by
    simpa using
      canonical_project_shift_code_condition_with_ids_substitute_closed
        (x#904) (x#906) (x#907) replacement
        (x#904) (x#906) (x#907)
        sourceId 921 922 923
        (hNe 921 (by decide)) (hNe 922 (by decide))
        (hNe 923 (by decide))
        hReplacement hParameterFixed hBodyCodeFixed hShiftOneFixed
  have hShiftSecond :
      Formula.substituteFree SetSort.set sourceId replacement
          (canonical_project_shift_code_condition_with_ids
            (x#904) (x#907) (x#908) 929 930 931) =
        canonical_project_shift_code_condition_with_ids
          (x#904) (x#907) (x#908) 929 930 931 := by
    simpa using
      canonical_project_shift_code_condition_with_ids_substitute_closed
        (x#904) (x#907) (x#908) replacement
        (x#904) (x#907) (x#908)
        sourceId 929 930 931
        (hNe 929 (by decide)) (hNe 930 (by decide))
        (hNe 931 (by decide))
        hReplacement hParameterFixed hShiftOneFixed hShiftTwoFixed
  have hCoreFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (fs_zfc_separation_core_code (x#904) (x#908)) =
        fs_zfc_separation_core_code (x#904) (x#908) := by
    apply Term.substituteFree_eq_self_of_not_mem
    simp [fs_zfc_separation_core_code,
      fs_zfc_hilbert_iff_code,
      Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport,
      set_variable, hNe 904 (by decide),
      hNe 908 (by decide)]
  have hPrefix :
      Formula.substituteFree SetSort.set sourceId replacement
          (canonical_forall_prefix_code_condition_with_ids
            (x#904)
            (fs_zfc_separation_core_code (x#904) (x#908))
            formula 937 938) =
        canonical_forall_prefix_code_condition_with_ids
          (x#904)
          (fs_zfc_separation_core_code (x#904) (x#908))
          formulaResult 937 938 := by
    simpa using
      canonical_forall_prefix_code_condition_with_ids_substitute_closed
        (x#904)
        (fs_zfc_separation_core_code (x#904) (x#908))
        formula replacement
        (x#904)
        (fs_zfc_separation_core_code (x#904) (x#908))
        formulaResult
        sourceId 937 938
        (hNe 937 (by decide)) (hNe 938 (by decide))
        hReplacement hParameterFixed hCoreFixed hFormulaSubstitution
  let bodySource : SetFormula :=
    (certificate ≐ₘ
        fs_zfc_schema_certificate_term
          (numₘ(0)) (x#904) (x#905)) ∧ₘ
      ((fs_zfc_schema_certificate_bounds
          certificate (numₘ(0)) (x#904) (x#905)) ∧ₘ
        ((x#904 ∈ₘ ωₘ) ∧ₘ
          ((nat_sequence_code_condition_with_ids
              (x#906) (x#905) 909 910) ∧ₘ
            ((canonical_project_formula_code_condition_with_ids
                (Sₘ(x#904)) (x#906)
                911 912 913 914 915 916 917 918 919 920) ∧ₘ
              ((canonical_project_shift_code_condition_with_ids
                  (x#904) (x#906) (x#907) 921 922 923) ∧ₘ
                ((canonical_project_shift_code_condition_with_ids
                    (x#904) (x#907) (x#908) 929 930 931) ∧ₘ
                  canonical_forall_prefix_code_condition_with_ids
                    (x#904)
                    (fs_zfc_separation_core_code
                      (x#904) (x#908))
                    formula 937 938))))))
  let bodyTarget : SetFormula :=
    (certificateResult ≐ₘ
        fs_zfc_schema_certificate_term
          (numₘ(0)) (x#904) (x#905)) ∧ₘ
      ((fs_zfc_schema_certificate_bounds
          certificateResult (numₘ(0)) (x#904) (x#905)) ∧ₘ
        ((x#904 ∈ₘ ωₘ) ∧ₘ
          ((nat_sequence_code_condition_with_ids
              (x#906) (x#905) 909 910) ∧ₘ
            ((canonical_project_formula_code_condition_with_ids
                (Sₘ(x#904)) (x#906)
                911 912 913 914 915 916 917 918 919 920) ∧ₘ
              ((canonical_project_shift_code_condition_with_ids
                  (x#904) (x#906) (x#907) 921 922 923) ∧ₘ
                ((canonical_project_shift_code_condition_with_ids
                    (x#904) (x#907) (x#908) 929 930 931) ∧ₘ
                  canonical_forall_prefix_code_condition_with_ids
                    (x#904)
                    (fs_zfc_separation_core_code
                      (x#904) (x#908))
                    formulaResult 937 938))))))
  have hBody :
      Formula.substituteFree SetSort.set sourceId replacement
          bodySource =
        bodyTarget := by
    simp [bodySource, bodyTarget, Formula.substituteFree,
      hCertificateSubstitution, hCertificateTermFixed,
      hParameterFixed, hOmegaFixed,
      hCertificateBounds,
      hSequence,
      hClassifier, hShiftFirst, hShiftSecond, hPrefix]
  have hFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport replacement := by
    rw [hReplacement.2]
    exact List.not_mem_nil
  have hNested :=
    fs_zfc_substitute_free_exists_five_closed
      sourceId 904 905 906 907 908 replacement
      bodySource bodyTarget
      (hNe 904 (by decide)) (hNe 905 (by decide))
      (hNe 906 (by decide)) (hNe 907 (by decide))
      (hNe 908 (by decide)) hReplacement.1.2
      (hFresh 904) (hFresh 905) (hFresh 906)
      (hFresh 907) (hFresh 908) hBody
  simpa [fs_zfc_separation_condition_with_base,
    bodySource, bodyTarget] using hNested

/-- 收集 schema 条件在保留编号区间以下逐参数保持闭项替换。 -/
theorem fs_zfc_collection_condition_with_reserved_base_substitute_closed
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
        (fs_zfc_collection_condition_with_base
          formula certificate 904) =
      fs_zfc_collection_condition_with_base
        formulaResult certificateResult 904 := by
  have hNe (id : FreeVarId) (hId : 904 ≤ id) :
      sourceId ≠ id :=
    fs_zfc_source_ne_schema_id hSource hId
  have hVariableFixed (id : FreeVarId) (hId : 904 ≤ id) :
      Term.substituteFree SetSort.set sourceId replacement (x#id) =
        x#id := by
    simp [Term.substituteFree, set_variable,
      Ne.symm (hNe id hId)]
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set sourceId replacement
          (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hOmegaFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (ωₘ : SetTerm) =
        ωₘ := by
    apply Term.substituteFree_eq_self_of_not_mem
    change (SetSort.set, sourceId) ∉ []
    exact List.not_mem_nil
  have hParameterFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#904) =
        x#904 :=
    hVariableFixed 904 (by decide)
  have hBodyTokenFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#905) =
        x#905 :=
    hVariableFixed 905 (by decide)
  have hBodyCodeFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#906) =
        x#906 :=
    hVariableFixed 906 (by decide)
  have hShiftOneFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#907) =
        x#907 :=
    hVariableFixed 907 (by decide)
  have hShiftTwoFixed :
      Term.substituteFree SetSort.set sourceId replacement (x#908) =
        x#908 :=
    hVariableFixed 908 (by decide)
  have hParameterTwoFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (Sₘ(Sₘ(x#904))) =
        Sₘ(Sₘ(x#904)) := by
    simp [Term.substituteFree, hParameterFixed]
  have hParameterThreeFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (Sₘ(Sₘ(Sₘ(x#904)))) =
        Sₘ(Sₘ(Sₘ(x#904))) := by
    simp [Term.substituteFree, hParameterFixed]
  have hCertificateTermFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (fs_zfc_schema_certificate_term
            (numₘ(1)) (x#904) (x#905)) =
        fs_zfc_schema_certificate_term
          (numₘ(1)) (x#904) (x#905) := by
    simp [fs_zfc_schema_certificate_term,
      fs_zfc_schema_payload_term,
      fs_zfc_schema_body_payload_term,
      Term.substituteFree, set_variable,
      hParameterFixed, hBodyTokenFixed,
      hNumeralFixed 1]
  have hCertificate :
      Formula.substituteFree SetSort.set sourceId replacement
          (certificate ≐ₘ
            fs_zfc_schema_certificate_term
              (numₘ(1)) (x#904) (x#905)) =
        (certificateResult ≐ₘ
          fs_zfc_schema_certificate_term
            (numₘ(1)) (x#904) (x#905)) := by
    simp [Formula.substituteFree,
      hCertificateSubstitution, hCertificateTermFixed]
  have hCertificateBounds :
      Formula.substituteFree SetSort.set sourceId replacement
          (fs_zfc_schema_certificate_bounds
            certificate (numₘ(1)) (x#904) (x#905)) =
        fs_zfc_schema_certificate_bounds
          certificateResult (numₘ(1)) (x#904) (x#905) := by
    simp [fs_zfc_schema_certificate_bounds,
      fs_zfc_schema_payload_term,
      fs_zfc_schema_body_payload_term,
      Formula.substituteFree, Term.substituteFree,
      hCertificateSubstitution, hParameterFixed,
      hBodyTokenFixed, hNumeralFixed]
  have hParameterNatural :
      Formula.substituteFree SetSort.set sourceId replacement
          (x#904 ∈ₘ ωₘ) =
        (x#904 ∈ₘ ωₘ) := by
    apply Formula.substituteFree_eq_self_of_not_mem
    simp [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList, hNe 904 (by decide)]
  have hSequence :
      Formula.substituteFree SetSort.set sourceId replacement
          (nat_sequence_code_condition_with_ids
            (x#906) (x#905) 909 910) =
        nat_sequence_code_condition_with_ids
          (x#906) (x#905) 909 910 :=
    fs_zfc_schema_nat_sequence_condition_fixed
      sourceId replacement hSource
  have hClassifier :
      Formula.substituteFree SetSort.set sourceId replacement
          (canonical_project_formula_code_condition_with_ids
            (Sₘ(Sₘ(x#904))) (x#906)
            911 912 913 914 915 916 917 918 919 920) =
        canonical_project_formula_code_condition_with_ids
          (Sₘ(Sₘ(x#904))) (x#906)
          911 912 913 914 915 916 917 918 919 920 := by
    simpa using
      canonical_project_formula_code_condition_with_ids_substitute_closed
        (Sₘ(Sₘ(x#904))) (x#906) replacement
        (Sₘ(Sₘ(x#904))) (x#906)
        sourceId 911 912 913 914 915 916 917 918 919 920
        (hNe 911 (by decide)) (hNe 912 (by decide))
        (hNe 913 (by decide)) (hNe 914 (by decide))
        (hNe 915 (by decide)) (hNe 916 (by decide))
        (hNe 917 (by decide)) (hNe 918 (by decide))
        (hNe 919 (by decide)) (hNe 920 (by decide))
        hReplacement hParameterTwoFixed hBodyCodeFixed
  have hShiftFirst :
      Formula.substituteFree SetSort.set sourceId replacement
          (canonical_project_shift_code_condition_with_ids
            (x#904) (x#906) (x#907) 921 922 923) =
        canonical_project_shift_code_condition_with_ids
          (x#904) (x#906) (x#907) 921 922 923 := by
    simpa using
      canonical_project_shift_code_condition_with_ids_substitute_closed
        (x#904) (x#906) (x#907) replacement
        (x#904) (x#906) (x#907)
        sourceId 921 922 923
        (hNe 921 (by decide)) (hNe 922 (by decide))
        (hNe 923 (by decide))
        hReplacement hParameterFixed hBodyCodeFixed hShiftOneFixed
  have hShiftSecond :
      Formula.substituteFree SetSort.set sourceId replacement
          (canonical_project_shift_code_condition_with_ids
            (x#904) (x#907) (x#908) 929 930 931) =
        canonical_project_shift_code_condition_with_ids
          (x#904) (x#907) (x#908) 929 930 931 := by
    simpa using
      canonical_project_shift_code_condition_with_ids_substitute_closed
        (x#904) (x#907) (x#908) replacement
        (x#904) (x#907) (x#908)
        sourceId 929 930 931
        (hNe 929 (by decide)) (hNe 930 (by decide))
        (hNe 931 (by decide))
        hReplacement hParameterFixed hShiftOneFixed hShiftTwoFixed
  have hCoreFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (fs_zfc_collection_core_code
            (x#904) (x#907) (x#908)) =
        fs_zfc_collection_core_code
          (x#904) (x#907) (x#908) := by
    apply Term.substituteFree_eq_self_of_not_mem
    simp [fs_zfc_collection_core_code,

      Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport,
      set_variable, hNe 904 (by decide),
      hNe 907 (by decide), hNe 908 (by decide)]
  have hPrefix :
      Formula.substituteFree SetSort.set sourceId replacement
          (canonical_forall_prefix_code_condition_with_ids
            (x#904)
            (fs_zfc_collection_core_code
              (x#904) (x#907) (x#908))
            formula 937 938) =
        canonical_forall_prefix_code_condition_with_ids
          (x#904)
          (fs_zfc_collection_core_code
            (x#904) (x#907) (x#908))
          formulaResult 937 938 := by
    simpa using
      canonical_forall_prefix_code_condition_with_ids_substitute_closed
        (x#904)
        (fs_zfc_collection_core_code
          (x#904) (x#907) (x#908))
        formula replacement
        (x#904)
        (fs_zfc_collection_core_code
          (x#904) (x#907) (x#908))
        formulaResult
        sourceId 937 938
        (hNe 937 (by decide)) (hNe 938 (by decide))
        hReplacement hParameterFixed hCoreFixed hFormulaSubstitution
  let bodySource : SetFormula :=
    (certificate ≐ₘ
        fs_zfc_schema_certificate_term
          (numₘ(1)) (x#904) (x#905)) ∧ₘ
      ((fs_zfc_schema_certificate_bounds
          certificate (numₘ(1)) (x#904) (x#905)) ∧ₘ
        ((x#904 ∈ₘ ωₘ) ∧ₘ
          ((nat_sequence_code_condition_with_ids
              (x#906) (x#905) 909 910) ∧ₘ
            ((canonical_project_formula_code_condition_with_ids
                (Sₘ(Sₘ(x#904))) (x#906)
                911 912 913 914 915 916 917 918 919 920) ∧ₘ
              ((canonical_project_shift_code_condition_with_ids
                  (x#904) (x#906) (x#907) 921 922 923) ∧ₘ
                ((canonical_project_shift_code_condition_with_ids
                    (x#904) (x#907) (x#908) 929 930 931) ∧ₘ
                  canonical_forall_prefix_code_condition_with_ids
                    (x#904)
                    (fs_zfc_collection_core_code
                      (x#904) (x#907) (x#908))
                    formula 937 938))))))
  let bodyTarget : SetFormula :=
    (certificateResult ≐ₘ
        fs_zfc_schema_certificate_term
          (numₘ(1)) (x#904) (x#905)) ∧ₘ
      ((fs_zfc_schema_certificate_bounds
          certificateResult (numₘ(1)) (x#904) (x#905)) ∧ₘ
        ((x#904 ∈ₘ ωₘ) ∧ₘ
          ((nat_sequence_code_condition_with_ids
              (x#906) (x#905) 909 910) ∧ₘ
            ((canonical_project_formula_code_condition_with_ids
                (Sₘ(Sₘ(x#904))) (x#906)
                911 912 913 914 915 916 917 918 919 920) ∧ₘ
              ((canonical_project_shift_code_condition_with_ids
                  (x#904) (x#906) (x#907) 921 922 923) ∧ₘ
                ((canonical_project_shift_code_condition_with_ids
                    (x#904) (x#907) (x#908) 929 930 931) ∧ₘ
                  canonical_forall_prefix_code_condition_with_ids
                    (x#904)
                    (fs_zfc_collection_core_code
                      (x#904) (x#907) (x#908))
                    formulaResult 937 938))))))
  have hBody :
      Formula.substituteFree SetSort.set sourceId replacement
          bodySource =
        bodyTarget := by
    simp [bodySource, bodyTarget, Formula.substituteFree,
      hCertificateSubstitution, hCertificateTermFixed,
      hParameterFixed, hOmegaFixed,
      hCertificateBounds,
      hSequence,
      hClassifier, hShiftFirst, hShiftSecond, hPrefix]
  have hFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport replacement := by
    rw [hReplacement.2]
    exact List.not_mem_nil
  have hNested :=
    fs_zfc_substitute_free_exists_five_closed
      sourceId 904 905 906 907 908 replacement
      bodySource bodyTarget
      (hNe 904 (by decide)) (hNe 905 (by decide))
      (hNe 906 (by decide)) (hNe 907 (by decide))
      (hNe 908 (by decide)) hReplacement.1.2
      (hFresh 904) (hFresh 905) (hFresh 906)
      (hFresh 907) (hFresh 908) hBody
  simpa [fs_zfc_collection_condition_with_base,
    bodySource, bodyTarget] using hNested

/-!
固定表与任意 schema 插件表的替换组合器。插件自身的替换合同由调用方提供，
本定理只负责把它们与固定公理表合成为对象条件合同。
-/
theorem fs_zfc_object_certificate_condition_with_plugins_reserved_base_substitute_closed
    (plugins : List ProofT.SchemaPlugin)
    (formula certificate replacement
      formulaResult certificateResult : SetTerm)
    (sourceId : FreeVarId)
    (hFixedTable :
      Formula.substituteFree SetSort.set sourceId replacement
          (fs_zfc_fixed_axiom_table.condition formula certificate) =
        fs_zfc_fixed_axiom_table.condition
          formulaResult certificateResult)
    (hPlugin :
      ∀ plugin, plugin ∈ plugins →
        Formula.substituteFree SetSort.set sourceId replacement
            (plugin.condition_with_base
              formula certificate 904) =
          plugin.condition_with_base
            formulaResult certificateResult 904) :
    Formula.substituteFree SetSort.set sourceId replacement
        (fs_zfc_object_certificate_condition_with_plugins
          plugins formula certificate 904) =
      fs_zfc_object_certificate_condition_with_plugins
        plugins formulaResult certificateResult 904 := by
  have hSchemas :
      Formula.substituteFree SetSort.set sourceId replacement
          (ProofT.SchemaPlugin.condition_list
            plugins formula certificate 904) =
        ProofT.SchemaPlugin.condition_list
          plugins formulaResult certificateResult 904 :=
    ProofT.SchemaPlugin.condition_list_substitute
      plugins formula certificate replacement
      formulaResult certificateResult sourceId 904 hPlugin
  simp [fs_zfc_object_certificate_condition_with_plugins,
    Formula.substituteFree, hFixedTable, hSchemas]

/--
固定内部基点 `904` 的 ZFC 对象证书条件逐参数保持闭项替换。

这是证明码层消费 verifier 时所需的完整语法合同；三类公理分支均在本层闭合。
-/
theorem fs_zfc_object_certificate_condition_with_reserved_base_substitute_closed
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
        (fs_zfc_object_certificate_condition_with_base
          formula certificate 904) =
      fs_zfc_object_certificate_condition_with_base
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
  have hCollection :=
    fs_zfc_collection_condition_with_reserved_base_substitute_closed
      formula certificate replacement
      formulaResult certificateResult sourceId
      hSource hReplacement
      hFormulaSubstitution hCertificateSubstitution
  exact
    fs_zfc_object_certificate_condition_with_plugins_reserved_base_substitute_closed
      fs_zfc_schema_plugins
      formula certificate replacement
      formulaResult certificateResult sourceId
      hFixedTable
      (fs_zfc_schema_plugins_elim
        (by
          simpa [fs_zfc_separation_schema_plugin] using
            hSeparation)
        (by
          simpa [fs_zfc_collection_schema_plugin] using
            hCollection))

/--
当替换前后的自动新鲜基点都落在保留边界 `904` 时，公开 ZFC verifier
满足同一闭项替换合同。
-/
theorem ProofT.ZFC.verifier_substitute
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
        (fs_zfc_object_certificate_verifier.condition
          formula certificate) =
      fs_zfc_object_certificate_verifier.condition
        formulaResult certificateResult := by
  change Formula.substituteFree SetSort.set sourceId replacement
      (fs_zfc_object_certificate_condition formula certificate) =
    fs_zfc_object_certificate_condition
      formulaResult certificateResult
  simp only [fs_zfc_object_certificate_condition]
  rw [hSourceBase, hTargetBase]
  exact
    fs_zfc_object_certificate_condition_with_reserved_base_substitute_closed
      formula certificate replacement
      formulaResult certificateResult sourceId
      hSource hReplacement
      hFormulaSubstitution hCertificateSubstitution

/-- 当前 separation+collection verifier 满足 checked 运输合同。 -/
def ProofT.ZFC.verifier_transport :
    ProofT.VerifierTransport
      fs_zfc_object_certificate_verifier where
  formula_condition := rfl
  substitute_closed :=
    ProofT.ZFC.verifier_substitute

/-- 当前 separation+collection verifier 的序列替换特例。 -/
theorem ProofT.ZFC.sequence_condition_substitute
    (sequence certificates replacement
      sequenceResult certificatesResult : SetTerm)
    (sourceId : FreeVarId)
    (hSource : sourceId < ProofT.lc_sequence_id)
    (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement)
    (hSequenceSubstitution :
      Term.substituteFree SetSort.set sourceId replacement sequence =
        sequenceResult)
    (hCertificatesSubstitution :
      Term.substituteFree SetSort.set sourceId replacement certificates =
        certificatesResult)
    (hVerifierSourceBase :
      ProofT.schema_base
          [sequence ·ₘ (x#ProofT.line_index_id),
            (x#ProofT.certificate_code_id)] =
        904)
    (hVerifierTargetBase :
      ProofT.schema_base
          [sequenceResult ·ₘ (x#ProofT.line_index_id),
            (x#ProofT.certificate_code_id)] =
        904) :
    Formula.substituteFree SetSort.set sourceId replacement
        (ProofT.ZFC.sequence_condition sequence certificates) =
      ProofT.ZFC.sequence_condition
        sequenceResult certificatesResult := by
  exact
    ProofT.sequence_condition_substitute
      fs_zfc_object_certificate_verifier
      ProofT.ZFC.verifier_transport
      sequence certificates replacement
      sequenceResult certificatesResult sourceId
      hSource hReplacement
      hSequenceSubstitution hCertificatesSubstitution
      hVerifierSourceBase hVerifierTargetBase

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
