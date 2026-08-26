import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CanonicalDelta0
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta0Encoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Sigma1Encoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.LogicalCertificateSigma1

/-
# ZFC schema 条件的 Lévy 层级

固定公理表与 schema 矩阵中的编码关系都是 Delta0；schema 本身还要关闭一列
外部见证，因此其公开条件属于 Sigma1。本模块只交付这个句法层级证书，不把
尚未完成的 substitution-spec 关系误标为 Delta0。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofT
open ProofT.Delta0Encoding

set_option autoImplicit false

/-! ## separation/collection 共用的 Delta0 矩阵 -/

/-- 两个五见证 schema 共用的对象层矩阵。 -/
def fs_zfc_schema_condition_body
    (schemaTag certificate parameter bodyTokenCode bodyCode
      shiftOne shiftTwo parameterDepth core formula : SetTerm)
    (base : FreeVarId) : SetFormula :=
  (certificate ≐ₘ
    fs_zfc_schema_certificate_term
      schemaTag parameter bodyTokenCode) ∧ₘ
    ((fs_zfc_schema_certificate_bounds
        certificate schemaTag parameter bodyTokenCode) ∧ₘ
      ((parameter ∈ₘ ωₘ) ∧ₘ
        ((nat_sequence_code_condition_with_ids
            bodyCode bodyTokenCode
            (base + 5) (base + 6)) ∧ₘ
          ((canonical_project_formula_code_condition_with_ids
              parameterDepth bodyCode
              (base + 7) (base + 8)
              (base + 9) (base + 10)
              (base + 11) (base + 12)
              (base + 13) (base + 14)
              (base + 15) (base + 16)) ∧ₘ
            ((canonical_project_shift_code_condition_with_ids
                parameter bodyCode shiftOne
                (base + 17) (base + 18) (base + 19)) ∧ₘ
              ((canonical_project_shift_code_condition_with_ids
                  parameter shiftOne shiftTwo
                  (base + 25) (base + 26) (base + 27)) ∧ₘ
                canonical_forall_prefix_code_condition_with_ids
                  parameter core formula
                  (base + 33) (base + 34)))))))

theorem fs_zfc_schema_condition_body_delta0
    (schemaTag certificate parameter bodyTokenCode bodyCode
      shiftOne shiftTwo parameterDepth core formula : SetTerm)
    (base : FreeVarId)
    (hCertificate :
      Formula.IsDelta0 set_levy_bound
        (certificate ≐ₘ
          fs_zfc_schema_certificate_term
            schemaTag parameter bodyTokenCode))
    (hBounds :
      Formula.IsDelta0 set_levy_bound
        (fs_zfc_schema_certificate_bounds
          certificate schemaTag parameter bodyTokenCode))
    (hParameter :
      Formula.IsDelta0 set_levy_bound
        (parameter ∈ₘ ωₘ))
    (hSequence :
      Formula.IsDelta0 set_levy_bound
        (nat_sequence_code_condition_with_ids
          bodyCode bodyTokenCode
          (base + 5) (base + 6)))
    (hClassifier :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_formula_code_condition_with_ids
          parameterDepth bodyCode
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16)))
    (hShiftOne :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_shift_code_condition_with_ids
          parameter bodyCode shiftOne
          (base + 17) (base + 18) (base + 19)))
    (hShiftTwo :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_shift_code_condition_with_ids
          parameter shiftOne shiftTwo
          (base + 25) (base + 26) (base + 27)))
    (hPrefix :
      Formula.IsDelta0 set_levy_bound
        (canonical_forall_prefix_code_condition_with_ids
          parameter core formula
          (base + 33) (base + 34))) :
    Formula.IsDelta0 set_levy_bound
      (fs_zfc_schema_condition_body
        schemaTag certificate parameter bodyTokenCode bodyCode
        shiftOne shiftTwo parameterDepth core formula base) := by
  simpa [fs_zfc_schema_condition_body] using
    Formula.IsDelta0.conj
      hCertificate
      (Formula.IsDelta0.conj
        hBounds
        (Formula.IsDelta0.conj
          hParameter
          (Formula.IsDelta0.conj
            hSequence
            (Formula.IsDelta0.conj
              hClassifier
              (Formula.IsDelta0.conj
                hShiftOne
                (Formula.IsDelta0.conj hShiftTwo hPrefix))))))

/-! ## 外层五见证闭包 -/

theorem fs_zfc_separation_condition_with_base_sigma1
    (formula certificate : SetTerm)
    (base : FreeVarId) :
    Formula.IsSigma1 set_levy_bound
      (fs_zfc_separation_condition_with_base
        formula certificate base) := by
  let parameter := x#base
  let bodyTokenCode := x#(base + 1)
  let bodyCode := x#(base + 2)
  let shiftOne := x#(base + 3)
  let shiftTwo := x#(base + 4)
  let parameterDepth := Sₘ(parameter)
  let core := fs_zfc_separation_core_code parameter shiftTwo
  have hFreshVar (i j : Nat) (hNe : i ≠ j) :
      (SetSort.set, base + i) ∉
        Term.freeSupport (x#(base + j)) := by
    change (SetSort.set, base + i) ∉
      [(SetSort.set, base + j)]
    intro hMember
    have hEq := congrArg Prod.snd
      (List.mem_singleton.mp hMember)
    exact hNe (Nat.add_left_cancel hEq)
  have hFreshDom (i j : Nat) (hNe : i ≠ j) :
      (SetSort.set, base + i) ∉
        Term.freeSupport (domₘ(x#(base + j))) := by
    change (SetSort.set, base + i) ∉
      [(SetSort.set, base + j)]
    intro hMember
    have hEq := congrArg Prod.snd
      (List.mem_singleton.mp hMember)
    exact hNe (Nat.add_left_cancel hEq)
  have hFreshApp (i j k : Nat)
      (hNeJ : i ≠ j) (hNeK : i ≠ k) :
      (SetSort.set, base + i) ∉
        Term.freeSupport
          (x#(base + j) ·ₘ x#(base + k)) := by
    change (SetSort.set, base + i) ∉
      ([(SetSort.set, base + j)] ++
        [(SetSort.set, base + k)])
    intro hMember
    rcases List.mem_append.mp hMember with hMember | hMember
    · have hEq := congrArg Prod.snd
        (List.mem_singleton.mp hMember)
      exact hNeJ (Nat.add_left_cancel hEq)
    · have hEq := congrArg Prod.snd
        (List.mem_singleton.mp hMember)
      exact hNeK (Nat.add_left_cancel hEq)
  have hFreshShiftApp (i j k : Nat)
      (hNeJ : i ≠ j) (hNeK : i ≠ k) :
      (SetSort.set, base + i) ∉
        Term.freeSupport
          (Sₘ(x#(base + j) ·ₘ x#(base + k))) := by
    change (SetSort.set, base + i) ∉
      ([(SetSort.set, base + j)] ++
        [(SetSort.set, base + k)])
    intro hMember
    rcases List.mem_append.mp hMember with hMember | hMember
    · have hEq := congrArg Prod.snd
        (List.mem_singleton.mp hMember)
      exact hNeJ (Nat.add_left_cancel hEq)
    · have hEq := congrArg Prod.snd
        (List.mem_singleton.mp hMember)
      exact hNeK (Nat.add_left_cancel hEq)
  have hCertificate :
      Formula.IsDelta0 set_levy_bound
        (certificate ≐ₘ
          fs_zfc_schema_certificate_term
            (numₘ(0)) parameter bodyTokenCode) :=
    Formula.IsDelta0.equal certificate
      (fs_zfc_schema_certificate_term
        (numₘ(0)) parameter bodyTokenCode)
  have hBounds :
      Formula.IsDelta0 set_levy_bound
        (fs_zfc_schema_certificate_bounds
          certificate (numₘ(0)) parameter bodyTokenCode) :=
    fs_zfc_schema_certificate_bounds_delta0
      certificate (numₘ(0)) parameter bodyTokenCode
  have hParameter :
      Formula.IsDelta0 set_levy_bound
        (parameter ∈ₘ ωₘ) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership [parameter, ωₘ]
  have hSequence :
      Formula.IsDelta0 set_levy_bound
        (nat_sequence_code_condition_with_ids
          bodyCode bodyTokenCode
          (base + 5) (base + 6)) :=
    nat_sequence_code_condition_with_ids_delta0
      bodyCode bodyTokenCode
      (base + 5) (base + 6)
      (by simpa [bodyCode] using hFreshDom 6 2 (by omega))
      (by simpa [bodyTokenCode] using hFreshDom 6 5 (by omega))
  have hClassifier :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_formula_code_condition_with_ids
          parameterDepth bodyCode
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16)) :=
    canonical_project_formula_code_condition_with_ids_delta0
      parameterDepth bodyCode
      (base + 7) (base + 8)
      (base + 9) (base + 10)
      (base + 11) (base + 12)
      (base + 13) (base + 14)
      (base + 15) (base + 16)
      (by simpa [bodyCode] using hFreshDom 10 7 (by omega))
      (by simpa using hFreshVar 11 10 (by omega))
      (by simpa using hFreshVar 12 10 (by omega))
      (by simpa using hFreshApp 15 8 10 (by omega) (by omega))
      (by simpa using hFreshApp 16 8 10 (by omega) (by omega))
      (by simpa [bodyCode] using hFreshDom 9 7 (by omega))
  have hShiftOne :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_shift_code_condition_with_ids
          parameter bodyCode shiftOne
          (base + 17) (base + 18) (base + 19)) :=
    canonical_project_shift_code_condition_with_ids_delta0
      parameter bodyCode shiftOne
      (base + 17) (base + 18) (base + 19)
      (by simpa [bodyCode] using hFreshDom 17 2 (by omega))
      (by simpa [bodyCode] using
        hFreshShiftApp 18 2 17 (by omega) (by omega))
  have hShiftTwo :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_shift_code_condition_with_ids
          parameter shiftOne shiftTwo
          (base + 25) (base + 26) (base + 27)) :=
    canonical_project_shift_code_condition_with_ids_delta0
      parameter shiftOne shiftTwo
      (base + 25) (base + 26) (base + 27)
      (by simpa [shiftOne] using hFreshDom 25 3 (by omega))
      (by simpa [shiftOne] using
        hFreshShiftApp 26 3 25 (by omega) (by omega))
  have hPrefix :
      Formula.IsDelta0 set_levy_bound
        (canonical_forall_prefix_code_condition_with_ids
          parameter core formula
          (base + 33) (base + 34)) :=
    canonical_forall_prefix_code_condition_with_ids_delta0
      parameter core formula
      (base + 33) (base + 34)
      (by simpa [parameter] using hFreshVar 34 0 (by omega))
  have hBody :
      Formula.IsDelta0 set_levy_bound
        (fs_zfc_schema_condition_body
          (numₘ(0)) certificate parameter bodyTokenCode bodyCode
          shiftOne shiftTwo parameterDepth core formula base) :=
    fs_zfc_schema_condition_body_delta0
      (numₘ(0)) certificate parameter bodyTokenCode bodyCode
      shiftOne shiftTwo parameterDepth core formula base
      hCertificate hBounds hParameter hSequence hClassifier
      hShiftOne hShiftTwo hPrefix
  have hWitness4 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 4],
          fs_zfc_schema_condition_body
            (numₘ(0)) certificate parameter bodyTokenCode bodyCode
            (x#(base + 3)) (x#(base + 4))
            parameterDepth
            (fs_zfc_separation_core_code parameter (x#(base + 4)))
            formula base) := by
    simpa [parameter, bodyTokenCode, bodyCode, shiftOne, shiftTwo,
      parameterDepth, core] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 4) hBody.to_sigma1
  have hWitness3 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4],
            fs_zfc_schema_condition_body
              (numₘ(0)) certificate parameter bodyTokenCode bodyCode
              (x#(base + 3)) (x#(base + 4))
              parameterDepth
              (fs_zfc_separation_core_code parameter (x#(base + 4)))
              formula base) := by
    simpa [parameter, bodyTokenCode, bodyCode, shiftOne, shiftTwo,
      parameterDepth, core] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 3) hWitness4
  have hWitness2 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 2],
          ∃ₘ[SetSort.set, base + 3],
            ∃ₘ[SetSort.set, base + 4],
              fs_zfc_schema_condition_body
                (numₘ(0)) certificate parameter bodyTokenCode bodyCode
                (x#(base + 3)) (x#(base + 4))
                parameterDepth
                (fs_zfc_separation_core_code parameter (x#(base + 4)))
                formula base) := by
    simpa [parameter, bodyTokenCode, bodyCode, shiftOne, shiftTwo,
      parameterDepth, core] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 2) hWitness3
  have hWitness1 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 1],
          ∃ₘ[SetSort.set, base + 2],
            ∃ₘ[SetSort.set, base + 3],
              ∃ₘ[SetSort.set, base + 4],
                fs_zfc_schema_condition_body
                  (numₘ(0)) certificate parameter bodyTokenCode bodyCode
                  (x#(base + 3)) (x#(base + 4))
                  parameterDepth
                  (fs_zfc_separation_core_code parameter (x#(base + 4)))
                  formula base) := by
    simpa [parameter, bodyTokenCode, bodyCode, shiftOne, shiftTwo,
      parameterDepth, core] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 1) hWitness2
  simpa [fs_zfc_separation_condition_with_base,
    parameter, bodyTokenCode, bodyCode, shiftOne, shiftTwo,
    parameterDepth, core, fs_zfc_schema_condition_body] using
    Formula.IsSigma1.exists_closeFreeAt
      SetSort.set base hWitness1

theorem fs_zfc_collection_condition_with_base_sigma1
    (formula certificate : SetTerm)
    (base : FreeVarId) :
    Formula.IsSigma1 set_levy_bound
      (fs_zfc_collection_condition_with_base
        formula certificate base) := by
  let parameter := x#base
  let bodyTokenCode := x#(base + 1)
  let bodyCode := x#(base + 2)
  let shiftOne := x#(base + 3)
  let shiftTwo := x#(base + 4)
  let parameterDepth := Sₘ(Sₘ(parameter))
  let core :=
    fs_zfc_collection_core_code
      parameter shiftOne shiftTwo
  have hFreshVar (i j : Nat) (hNe : i ≠ j) :
      (SetSort.set, base + i) ∉
        Term.freeSupport (x#(base + j)) := by
    change (SetSort.set, base + i) ∉
      [(SetSort.set, base + j)]
    intro hMember
    have hEq := congrArg Prod.snd
      (List.mem_singleton.mp hMember)
    exact hNe (Nat.add_left_cancel hEq)
  have hFreshDom (i j : Nat) (hNe : i ≠ j) :
      (SetSort.set, base + i) ∉
        Term.freeSupport (domₘ(x#(base + j))) := by
    change (SetSort.set, base + i) ∉
      [(SetSort.set, base + j)]
    intro hMember
    have hEq := congrArg Prod.snd
      (List.mem_singleton.mp hMember)
    exact hNe (Nat.add_left_cancel hEq)
  have hFreshApp (i j k : Nat)
      (hNeJ : i ≠ j) (hNeK : i ≠ k) :
      (SetSort.set, base + i) ∉
        Term.freeSupport
          (x#(base + j) ·ₘ x#(base + k)) := by
    change (SetSort.set, base + i) ∉
      ([(SetSort.set, base + j)] ++
        [(SetSort.set, base + k)])
    intro hMember
    rcases List.mem_append.mp hMember with hMember | hMember
    · have hEq := congrArg Prod.snd
        (List.mem_singleton.mp hMember)
      exact hNeJ (Nat.add_left_cancel hEq)
    · have hEq := congrArg Prod.snd
        (List.mem_singleton.mp hMember)
      exact hNeK (Nat.add_left_cancel hEq)
  have hFreshShiftApp (i j k : Nat)
      (hNeJ : i ≠ j) (hNeK : i ≠ k) :
      (SetSort.set, base + i) ∉
        Term.freeSupport
          (Sₘ(x#(base + j) ·ₘ x#(base + k))) := by
    change (SetSort.set, base + i) ∉
      ([(SetSort.set, base + j)] ++
        [(SetSort.set, base + k)])
    intro hMember
    rcases List.mem_append.mp hMember with hMember | hMember
    · have hEq := congrArg Prod.snd
        (List.mem_singleton.mp hMember)
      exact hNeJ (Nat.add_left_cancel hEq)
    · have hEq := congrArg Prod.snd
        (List.mem_singleton.mp hMember)
      exact hNeK (Nat.add_left_cancel hEq)
  have hCertificate :
      Formula.IsDelta0 set_levy_bound
        (certificate ≐ₘ
          fs_zfc_schema_certificate_term
            (numₘ(1)) parameter bodyTokenCode) :=
    Formula.IsDelta0.equal certificate
      (fs_zfc_schema_certificate_term
        (numₘ(1)) parameter bodyTokenCode)
  have hBounds :
      Formula.IsDelta0 set_levy_bound
        (fs_zfc_schema_certificate_bounds
          certificate (numₘ(1)) parameter bodyTokenCode) :=
    fs_zfc_schema_certificate_bounds_delta0
      certificate (numₘ(1)) parameter bodyTokenCode
  have hParameter :
      Formula.IsDelta0 set_levy_bound
        (parameter ∈ₘ ωₘ) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership [parameter, ωₘ]
  have hSequence :
      Formula.IsDelta0 set_levy_bound
        (nat_sequence_code_condition_with_ids
          bodyCode bodyTokenCode
          (base + 5) (base + 6)) :=
    nat_sequence_code_condition_with_ids_delta0
      bodyCode bodyTokenCode
      (base + 5) (base + 6)
      (by simpa [bodyCode] using hFreshDom 6 2 (by omega))
      (by simpa [bodyTokenCode] using hFreshDom 6 5 (by omega))
  have hClassifier :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_formula_code_condition_with_ids
          parameterDepth bodyCode
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16)) :=
    canonical_project_formula_code_condition_with_ids_delta0
      parameterDepth bodyCode
      (base + 7) (base + 8)
      (base + 9) (base + 10)
      (base + 11) (base + 12)
      (base + 13) (base + 14)
      (base + 15) (base + 16)
      (by simpa [bodyCode] using hFreshDom 10 7 (by omega))
      (by simpa using hFreshVar 11 10 (by omega))
      (by simpa using hFreshVar 12 10 (by omega))
      (by simpa using hFreshApp 15 8 10 (by omega) (by omega))
      (by simpa using hFreshApp 16 8 10 (by omega) (by omega))
      (by simpa [bodyCode] using hFreshDom 9 7 (by omega))
  have hShiftOne :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_shift_code_condition_with_ids
          parameter bodyCode shiftOne
          (base + 17) (base + 18) (base + 19)) :=
    canonical_project_shift_code_condition_with_ids_delta0
      parameter bodyCode shiftOne
      (base + 17) (base + 18) (base + 19)
      (by simpa [bodyCode] using hFreshDom 17 2 (by omega))
      (by simpa [bodyCode] using
        hFreshShiftApp 18 2 17 (by omega) (by omega))
  have hShiftTwo :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_shift_code_condition_with_ids
          parameter shiftOne shiftTwo
          (base + 25) (base + 26) (base + 27)) :=
    canonical_project_shift_code_condition_with_ids_delta0
      parameter shiftOne shiftTwo
      (base + 25) (base + 26) (base + 27)
      (by simpa [shiftOne] using hFreshDom 25 3 (by omega))
      (by simpa [shiftOne] using
        hFreshShiftApp 26 3 25 (by omega) (by omega))
  have hPrefix :
      Formula.IsDelta0 set_levy_bound
        (canonical_forall_prefix_code_condition_with_ids
          parameter core formula
          (base + 33) (base + 34)) :=
    canonical_forall_prefix_code_condition_with_ids_delta0
      parameter core formula
      (base + 33) (base + 34)
      (by simpa [parameter] using hFreshVar 34 0 (by omega))
  have hBody :
      Formula.IsDelta0 set_levy_bound
        (fs_zfc_schema_condition_body
          (numₘ(1)) certificate parameter bodyTokenCode bodyCode
          shiftOne shiftTwo parameterDepth core formula base) :=
    fs_zfc_schema_condition_body_delta0
      (numₘ(1)) certificate parameter bodyTokenCode bodyCode
      shiftOne shiftTwo parameterDepth core formula base
      hCertificate hBounds hParameter hSequence hClassifier
      hShiftOne hShiftTwo hPrefix
  have hWitness4 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 4],
          fs_zfc_schema_condition_body
            (numₘ(1)) certificate parameter bodyTokenCode bodyCode
            (x#(base + 3)) (x#(base + 4))
            parameterDepth
            (fs_zfc_collection_core_code
              parameter (x#(base + 3)) (x#(base + 4)))
            formula base) := by
    simpa [parameter, bodyTokenCode, bodyCode, shiftOne, shiftTwo,
      parameterDepth, core] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 4) hBody.to_sigma1
  have hWitness3 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4],
            fs_zfc_schema_condition_body
              (numₘ(1)) certificate parameter bodyTokenCode bodyCode
              (x#(base + 3)) (x#(base + 4))
              parameterDepth
              (fs_zfc_collection_core_code
                parameter (x#(base + 3)) (x#(base + 4)))
              formula base) := by
    simpa [parameter, bodyTokenCode, bodyCode, shiftOne, shiftTwo,
      parameterDepth, core] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 3) hWitness4
  have hWitness2 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 2],
          ∃ₘ[SetSort.set, base + 3],
            ∃ₘ[SetSort.set, base + 4],
              fs_zfc_schema_condition_body
                (numₘ(1)) certificate parameter bodyTokenCode bodyCode
                (x#(base + 3)) (x#(base + 4))
                parameterDepth
                (fs_zfc_collection_core_code
                  parameter (x#(base + 3)) (x#(base + 4)))
                formula base) := by
    simpa [parameter, bodyTokenCode, bodyCode, shiftOne, shiftTwo,
      parameterDepth, core] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 2) hWitness3
  have hWitness1 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 1],
          ∃ₘ[SetSort.set, base + 2],
            ∃ₘ[SetSort.set, base + 3],
              ∃ₘ[SetSort.set, base + 4],
                fs_zfc_schema_condition_body
                  (numₘ(1)) certificate parameter bodyTokenCode bodyCode
                  (x#(base + 3)) (x#(base + 4))
                  parameterDepth
                  (fs_zfc_collection_core_code
                    parameter (x#(base + 3)) (x#(base + 4)))
                  formula base) := by
    simpa [parameter, bodyTokenCode, bodyCode, shiftOne, shiftTwo,
      parameterDepth, core] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 1) hWitness2
  simpa [fs_zfc_collection_condition_with_base,
    parameter, bodyTokenCode, bodyCode, shiftOne, shiftTwo,
    parameterDepth, core, fs_zfc_schema_condition_body] using
    Formula.IsSigma1.exists_closeFreeAt
      SetSort.set base hWitness1

theorem fs_zfc_replacement_condition_with_base_sigma1
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hBase : 904 ≤ base) :
    Formula.IsSigma1 set_levy_bound
      (fs_zfc_replacement_condition_with_base
        formula certificate base) := by
  let parameter := x#base
  let bodyTokenCode := x#(base + 1)
  let bodyCode := x#(base + 2)
  let firstOutputCode := x#(base + 3)
  let secondOutputCode := x#(base + 4)
  let underOneCode := x#(base + 5)
  let underTwoCode := x#(base + 6)
  let temporaryCode := x#(base + 7)
  let swappedInputCode := x#(base + 8)
  let imageCode := x#(base + 9)
  let parameterOne := Sₘ(parameter)
  let parameterTwo := Sₘ(parameterOne)
  let parameterThree := Sₘ(parameterTwo)
  let inputVariable :=
    canonical_binder_variable_code_term parameterTwo
  let outputVariable :=
    canonical_binder_variable_code_term parameterThree
  let temporaryVariable :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.free_name 0)
  let core :=
    fs_zfc_replacement_core_code
      parameter firstOutputCode secondOutputCode imageCode
  have hFreshVar (i j : Nat) (hNe : i ≠ j) :
      (SetSort.set, base + i) ∉
        Term.freeSupport (x#(base + j)) := by
    change (SetSort.set, base + i) ∉
      [(SetSort.set, base + j)]
    intro hMember
    have hEq := congrArg Prod.snd
      (List.mem_singleton.mp hMember)
    exact hNe (Nat.add_left_cancel hEq)
  have hFreshDom (i j : Nat) (hNe : i ≠ j) :
      (SetSort.set, base + i) ∉
        Term.freeSupport (domₘ(x#(base + j))) := by
    change (SetSort.set, base + i) ∉
      [(SetSort.set, base + j)]
    intro hMember
    have hEq := congrArg Prod.snd
      (List.mem_singleton.mp hMember)
    exact hNe (Nat.add_left_cancel hEq)
  have hFreshApp (i j k : Nat)
      (hNeJ : i ≠ j) (hNeK : i ≠ k) :
      (SetSort.set, base + i) ∉
        Term.freeSupport
          (x#(base + j) ·ₘ x#(base + k)) := by
    change (SetSort.set, base + i) ∉
      ([(SetSort.set, base + j)] ++
        [(SetSort.set, base + k)])
    intro hMember
    rcases List.mem_append.mp hMember with hMember | hMember
    · have hEq := congrArg Prod.snd
        (List.mem_singleton.mp hMember)
      exact hNeJ (Nat.add_left_cancel hEq)
    · have hEq := congrArg Prod.snd
        (List.mem_singleton.mp hMember)
      exact hNeK (Nat.add_left_cancel hEq)
  have hFreshShiftApp (i j k : Nat)
      (hNeJ : i ≠ j) (hNeK : i ≠ k) :
      (SetSort.set, base + i) ∉
        Term.freeSupport
          (Sₘ(x#(base + j) ·ₘ x#(base + k))) := by
    change (SetSort.set, base + i) ∉
      ([(SetSort.set, base + j)] ++
        [(SetSort.set, base + k)])
    intro hMember
    rcases List.mem_append.mp hMember with hMember | hMember
    · have hEq := congrArg Prod.snd
        (List.mem_singleton.mp hMember)
      exact hNeJ (Nat.add_left_cancel hEq)
    · have hEq := congrArg Prod.snd
        (List.mem_singleton.mp hMember)
      exact hNeK (Nat.add_left_cancel hEq)
  have hInternalFresh (j : Nat) :
      (SetSort.set, 311) ∉
        Term.freeSupport (domₘ(x#(base + j))) := by
    change (SetSort.set, 311) ∉
      [(SetSort.set, base + j)]
    intro hMember
    have hEq : 311 = base + j :=
      congrArg Prod.snd (List.mem_singleton.mp hMember)
    have hBaseLt : 311 < base :=
      Nat.lt_of_lt_of_le (by decide) hBase
    have hLt : 311 < base + j :=
      Nat.lt_of_lt_of_le hBaseLt (Nat.le_add_right base j)
    exact (Nat.ne_of_lt hLt) hEq
  have hCertificate :
      Formula.IsDelta0 set_levy_bound
        (certificate ≐ₘ
          fs_zfc_schema_certificate_term
            (numₘ(2)) parameter bodyTokenCode) :=
    Formula.IsDelta0.equal certificate
      (fs_zfc_schema_certificate_term
        (numₘ(2)) parameter bodyTokenCode)
  have hBounds :
      Formula.IsDelta0 set_levy_bound
        (fs_zfc_schema_certificate_bounds
          certificate (numₘ(2)) parameter bodyTokenCode) :=
    fs_zfc_schema_certificate_bounds_delta0
      certificate (numₘ(2)) parameter bodyTokenCode
  have hParameter :
      Formula.IsDelta0 set_levy_bound
        (parameter ∈ₘ ωₘ) :=
    Formula.IsDelta0.rel
      RelationSymbol.membership [parameter, ωₘ]
  have hSequence :
      Formula.IsDelta0 set_levy_bound
        (nat_sequence_code_condition_with_ids
          bodyCode bodyTokenCode
          (base + 10) (base + 11)) :=
    nat_sequence_code_condition_with_ids_delta0
      bodyCode bodyTokenCode
      (base + 10) (base + 11)
      (by simpa [bodyCode] using hFreshDom 11 2 (by omega))
      (by simpa [bodyTokenCode] using hFreshDom 11 10 (by omega))
  have hClassifier :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_formula_code_condition_with_ids
          parameterTwo bodyCode
          (base + 12) (base + 13)
          (base + 14) (base + 15)
          (base + 16) (base + 17)
          (base + 18) (base + 19)
          (base + 20) (base + 21)) :=
    canonical_project_formula_code_condition_with_ids_delta0
      parameterTwo bodyCode
      (base + 12) (base + 13)
      (base + 14) (base + 15)
      (base + 16) (base + 17)
      (base + 18) (base + 19)
      (base + 20) (base + 21)
      (by simpa [bodyCode] using hFreshDom 15 12 (by omega))
      (by simpa using hFreshVar 16 15 (by omega))
      (by simpa using hFreshVar 17 15 (by omega))
      (by simpa using hFreshApp 20 13 15 (by omega) (by omega))
      (by simpa using hFreshApp 21 13 15 (by omega) (by omega))
      (by simpa [bodyCode] using hFreshDom 14 12 (by omega))
  have hShiftOne :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_shift_code_condition_with_ids
          parameterTwo bodyCode firstOutputCode
          (base + 22) (base + 23) (base + 24)) :=
    canonical_project_shift_code_condition_with_ids_delta0
      parameterTwo bodyCode firstOutputCode
      (base + 22) (base + 23) (base + 24)
      (by simpa [bodyCode] using hFreshDom 22 2 (by omega))
      (by simpa [bodyCode] using
        hFreshShiftApp 23 2 22 (by omega) (by omega))
  have hShiftTwo :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_shift_code_condition_with_ids
          parameterOne bodyCode secondOutputCode
          (base + 30) (base + 31) (base + 32)) :=
    canonical_project_shift_code_condition_with_ids_delta0
      parameterOne bodyCode secondOutputCode
      (base + 30) (base + 31) (base + 32)
      (by simpa [bodyCode] using hFreshDom 30 2 (by omega))
      (by simpa [bodyCode] using
        hFreshShiftApp 31 2 30 (by omega) (by omega))
  have hUnderOne :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_shift_code_condition_with_ids
          parameter bodyCode underOneCode
          (base + 38) (base + 39) (base + 40)) :=
    canonical_project_shift_code_condition_with_ids_delta0
      parameter bodyCode underOneCode
      (base + 38) (base + 39) (base + 40)
      (by simpa [bodyCode] using hFreshDom 38 2 (by omega))
      (by simpa [bodyCode] using
        hFreshShiftApp 39 2 38 (by omega) (by omega))
  have hUnderTwo :
      Formula.IsDelta0 set_levy_bound
        (canonical_project_shift_code_condition_with_ids
          parameter underOneCode underTwoCode
          (base + 46) (base + 47) (base + 48)) :=
    canonical_project_shift_code_condition_with_ids_delta0
      parameter underOneCode underTwoCode
      (base + 46) (base + 47) (base + 48)
      (by simpa [underOneCode] using hFreshDom 46 5 (by omega))
      (by simpa [underOneCode] using
        hFreshShiftApp 47 5 46 (by omega) (by omega))
  have hSubOne :
      Formula.IsDelta0 set_levy_bound
        (code_substitution_spec
          underTwoCode outputVariable temporaryVariable temporaryCode) :=
    code_substitution_spec_delta0
      underTwoCode outputVariable temporaryVariable temporaryCode
      (hInternalFresh 6)
  have hSubTwo :
      Formula.IsDelta0 set_levy_bound
        (code_substitution_spec
          temporaryCode inputVariable outputVariable swappedInputCode) :=
    code_substitution_spec_delta0
      temporaryCode inputVariable outputVariable swappedInputCode
      (hInternalFresh 7)
  have hSubThree :
      Formula.IsDelta0 set_levy_bound
        (code_substitution_spec
          swappedInputCode temporaryVariable inputVariable imageCode) :=
    code_substitution_spec_delta0
      swappedInputCode temporaryVariable inputVariable imageCode
      (hInternalFresh 8)
  have hPrefix :
      Formula.IsDelta0 set_levy_bound
        (canonical_forall_prefix_code_condition_with_ids
          parameter core formula
          (base + 54) (base + 55)) :=
    canonical_forall_prefix_code_condition_with_ids_delta0
      parameter core formula
      (base + 54) (base + 55)
      (by simpa [parameter] using hFreshVar 55 0 (by omega))
  have hRest :
      Formula.IsDelta0 set_levy_bound
        (fs_zfc_replacement_condition_rest
          formula parameter bodyTokenCode bodyCode
          firstOutputCode secondOutputCode underOneCode underTwoCode
          temporaryCode swappedInputCode imageCode base) := by
    simpa [fs_zfc_replacement_condition_rest,
      parameterOne, parameterTwo, parameterThree,
      inputVariable, outputVariable, temporaryVariable, core] using
      Formula.IsDelta0.conj
        hParameter
        (Formula.IsDelta0.conj
          hSequence
          (Formula.IsDelta0.conj
            hClassifier
            (Formula.IsDelta0.conj
              hShiftOne
              (Formula.IsDelta0.conj
                hShiftTwo
                (Formula.IsDelta0.conj
                  hUnderOne
                  (Formula.IsDelta0.conj
                    hUnderTwo
                    (Formula.IsDelta0.conj
                      hSubOne
                      (Formula.IsDelta0.conj
                        hSubTwo
                        (Formula.IsDelta0.conj
                          hSubThree hPrefix)))))))))
  let openBody :=
    fs_zfc_replacement_condition_open_body
      formula certificate base
  have hOpenBody :
      Formula.IsDelta0 set_levy_bound openBody := by
    simpa [openBody, fs_zfc_replacement_condition_open_body,
      fs_zfc_replacement_condition_body,
      fs_zfc_schema_condition_open_body] using
      Formula.IsDelta0.conj hCertificate
        (Formula.IsDelta0.conj hBounds hRest)
  have hWitness9 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 9], openBody) := by
    simpa [openBody] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 9) hOpenBody.to_sigma1
  have hWitness8 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 8],
          ∃ₘ[SetSort.set, base + 9], openBody) := by
    simpa [openBody] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 8) hWitness9
  have hWitness7 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 7],
          ∃ₘ[SetSort.set, base + 8],
            ∃ₘ[SetSort.set, base + 9], openBody) := by
    simpa [openBody] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 7) hWitness8
  have hWitness6 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 6],
          ∃ₘ[SetSort.set, base + 7],
            ∃ₘ[SetSort.set, base + 8],
              ∃ₘ[SetSort.set, base + 9], openBody) := by
    simpa [openBody] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 6) hWitness7
  have hWitness5 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 5],
          ∃ₘ[SetSort.set, base + 6],
            ∃ₘ[SetSort.set, base + 7],
              ∃ₘ[SetSort.set, base + 8],
                ∃ₘ[SetSort.set, base + 9], openBody) := by
    simpa [openBody] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 5) hWitness6
  have hWitness4 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 4],
          ∃ₘ[SetSort.set, base + 5],
            ∃ₘ[SetSort.set, base + 6],
              ∃ₘ[SetSort.set, base + 7],
                ∃ₘ[SetSort.set, base + 8],
                  ∃ₘ[SetSort.set, base + 9], openBody) := by
    simpa [openBody] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 4) hWitness5
  have hWitness3 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4],
            ∃ₘ[SetSort.set, base + 5],
              ∃ₘ[SetSort.set, base + 6],
                ∃ₘ[SetSort.set, base + 7],
                  ∃ₘ[SetSort.set, base + 8],
                    ∃ₘ[SetSort.set, base + 9], openBody) := by
    simpa [openBody] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 3) hWitness4
  have hWitness2 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 2],
          ∃ₘ[SetSort.set, base + 3],
            ∃ₘ[SetSort.set, base + 4],
              ∃ₘ[SetSort.set, base + 5],
                ∃ₘ[SetSort.set, base + 6],
                  ∃ₘ[SetSort.set, base + 7],
                    ∃ₘ[SetSort.set, base + 8],
                      ∃ₘ[SetSort.set, base + 9], openBody) := by
    simpa [openBody] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 2) hWitness3
  have hWitness1 :
      Formula.IsSigma1 set_levy_bound
        (∃ₘ[SetSort.set, base + 1],
          ∃ₘ[SetSort.set, base + 2],
            ∃ₘ[SetSort.set, base + 3],
              ∃ₘ[SetSort.set, base + 4],
                ∃ₘ[SetSort.set, base + 5],
                  ∃ₘ[SetSort.set, base + 6],
                    ∃ₘ[SetSort.set, base + 7],
                      ∃ₘ[SetSort.set, base + 8],
                        ∃ₘ[SetSort.set, base + 9], openBody) := by
    simpa [openBody] using
      Formula.IsSigma1.exists_closeFreeAt
        SetSort.set (base + 1) hWitness2
  simpa [fs_zfc_replacement_condition_with_base,
    fs_zfc_replacement_condition_exists_shape,
    openBody, fs_zfc_replacement_condition_open_body] using
    Formula.IsSigma1.exists_closeFreeAt
      SetSort.set base hWitness1

theorem fs_zfc_replacement_condition_sigma1
    (formula certificate : SetTerm) :
    Formula.IsSigma1 set_levy_bound
      (fs_zfc_replacement_certificate_condition
        formula certificate) := by
  simpa [fs_zfc_replacement_certificate_condition] using
    fs_zfc_replacement_condition_with_base_sigma1
      formula certificate
      (ProofT.schema_base [formula, certificate])
      (by
        unfold ProofT.schema_base
        exact Nat.le_max_left _ _)

/-! ## 总 ZFC schema verifier 的 Sigma1 汇总 -/

theorem fs_zfc_object_certificate_condition_with_plugins_sigma1
    (plugins : List ProofT.SchemaPlugin)
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hPlugins :
      ∀ plugin, plugin ∈ plugins →
        Formula.IsSigma1 set_levy_bound
          (plugin.condition_with_base
            formula certificate base)) :
    Formula.IsSigma1 set_levy_bound
      (fs_zfc_object_certificate_condition_with_plugins
        plugins formula certificate base) := by
  exact Formula.IsSigma1.disj
    (fs_zfc_fixed_axiom_table.condition_sigma1
      formula certificate)
    (ProofT.SchemaPlugin.condition_list_sigma1
      plugins formula certificate base hPlugins)

theorem fs_zfc_object_certificate_condition_with_base_sigma1
    (formula certificate : SetTerm)
    (base : FreeVarId) :
    Formula.IsSigma1 set_levy_bound
      (fs_zfc_object_certificate_condition_with_base
        formula certificate base) := by
  apply fs_zfc_object_certificate_condition_with_plugins_sigma1
  intro plugin hPlugin
  simp [fs_zfc_schema_plugins] at hPlugin
  rcases hPlugin with rfl | rfl
  · simpa [fs_zfc_separation_schema_plugin] using
      fs_zfc_separation_condition_with_base_sigma1
        formula certificate base
  · simpa [fs_zfc_collection_schema_plugin] using
      fs_zfc_collection_condition_with_base_sigma1
        formula certificate base

theorem fs_zfc_object_certificate_condition_sigma1
    (formula certificate : SetTerm) :
    Formula.IsSigma1 set_levy_bound
      (fs_zfc_object_certificate_condition
        formula certificate) := by
  simpa [fs_zfc_object_certificate_condition] using
    fs_zfc_object_certificate_condition_with_base_sigma1
      formula certificate
      (ProofT.schema_base [formula, certificate])

theorem fs_zfc_replacement_object_certificate_condition_with_base_sigma1
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hBase : 904 ≤ base) :
    Formula.IsSigma1 set_levy_bound
      (fs_zfc_replacement_object_certificate_condition_with_base
        formula certificate base) := by
  apply fs_zfc_object_certificate_condition_with_plugins_sigma1
  intro plugin hPlugin
  simp [fs_zfc_replacement_schema_plugins] at hPlugin
  rcases hPlugin with rfl | rfl
  · simpa [fs_zfc_separation_schema_plugin] using
      fs_zfc_separation_condition_with_base_sigma1
        formula certificate base
  · simpa [fs_zfc_replacement_schema_plugin] using
      fs_zfc_replacement_condition_with_base_sigma1
        formula certificate base hBase

theorem fs_zfc_replacement_object_certificate_condition_sigma1
    (formula certificate : SetTerm) :
    Formula.IsSigma1 set_levy_bound
      (fs_zfc_replacement_object_certificate_condition
        formula certificate) := by
  simpa [fs_zfc_replacement_object_certificate_condition] using
    fs_zfc_replacement_object_certificate_condition_with_base_sigma1
      formula certificate
      (ProofT.schema_base [formula, certificate])
      (by
        unfold ProofT.schema_base
        exact Nat.le_max_left _ _)

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
