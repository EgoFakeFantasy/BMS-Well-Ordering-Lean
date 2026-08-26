import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalPayloadFailureInversion

/-!
# 逻辑基础证书的标签错配拒绝

本模块只保留标签错配所需的公共二元核：对象证书给出的配对等式与宿主证书码
共同唯一确定标签。各分支存在见证的打开由终局失败适配器统一处理。
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

namespace CertifiedProof

/-- 宿主证书的实际标签不同于分支标签时，对应配对编码必不相等。 -/
theorem fs_zfc_logical_tag_mismatch_invalid
    (raw tag : Nat)
    (hTagMismatch :
      (godel_unpair_value raw).1 ≠ tag) :
    raw ≠
      godel_pair_value tag
        (godel_unpair_value raw).2 := by
  intro hRaw
  apply hTagMismatch
  have hPair :
      godel_pair_value
          (godel_unpair_value raw).1
          (godel_unpair_value raw).2 =
        godel_pair_value tag
          (godel_unpair_value raw).2 := by
    calc
      godel_pair_value
          (godel_unpair_value raw).1
          (godel_unpair_value raw).2 = raw :=
        godel_unpair_value_spec raw
      _ = godel_pair_value tag
          (godel_unpair_value raw).2 := hRaw
  exact (godel_pair_value_eq_iff.mp hPair).1

/--
对象证书分支声称的标签与地面证书实际标签不同时推出矛盾。

该接口只消费证书码、配对字段和 payload 的自然数性，不读取 payload 内容。
-/
theorem fs_zfc_support_raw_logical_tag_mismatch_falsum
    {Γ : Context signature}
    (raw tag : Nat)
    (certificate payload : SetTerm)
    (hPayload : Term.Admissible payload SetSort.set)
    (hCertificateCode :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        certificate ≐ₘ numₘ(raw))
    (hPairField :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        certificate ≐ₘ
          godel_pairₘ(⟨numₘ(tag), payload⟩ₘ))
    (hPayloadNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        payload ∈ₘ ωₘ)
    (hTagMismatch :
      (godel_unpair_value raw).1 ≠ tag) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      Formula.falsum := by
  have hPair :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(raw) ≐ₘ
          godel_pairₘ(⟨numₘ(tag), payload⟩ₘ) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hCertificateCode)
      hPairField
  have hPayloadEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        payload ≐ₘ
          numₘ((godel_unpair_value raw).2) :=
    ProofT.pair_right_unique
      ProofT.ZFC.pairing_core
      raw tag payload hPayload hPayloadNatural hPair
  exact ProofT.falsum_of_tagged_code
    ProofT.ZFC.certificate_core
    tag (godel_unpair_value raw).2 raw
    certificate payload
    hCertificateCode hPairField hPayload hPayloadEquality
    (fs_zfc_logical_tag_mismatch_invalid raw tag hTagMismatch)

/-- 打开标签分支的首字段与 payload 自然数性即可推出反证。 -/
theorem fs_zfc_support_raw_logical_tagged_body_imp_falsum
    (raw tag : Nat)
    (certificate payload : SetTerm)
    (body : SetFormula)
    (hPayload : Term.Admissible payload SetSort.set)
    (hBody : Formula.Admissible body)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hPairField :
      ∀ {Γ : Context signature},
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body →
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            certificate ≐ₘ
              godel_pairₘ(⟨numₘ(tag), payload⟩ₘ))
    (hPayloadNatural :
      ∀ {Γ : Context signature},
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body →
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            payload ∈ₘ ωₘ)
    (hTagMismatch :
      (godel_unpair_value raw).1 ≠ tag) :
    Derives fs_zfc_support_raw_theory [] (
      body ⟶ₘ Formula.falsum) := by
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck :=
      Formula.check_admissible_complete hBody)
  let Γ : Context signature := [body]
  have hBodyAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hBody)
  exact fs_zfc_support_raw_logical_tag_mismatch_falsum
    raw tag certificate payload hPayload
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      hCertificateCode)
    (hPairField hBodyAt)
    (hPayloadNatural hBodyAt)
    hTagMismatch

/-- 一次性把标签错配反证提升过分支的全部 witness。 -/
theorem fs_zfc_support_raw_logical_tagged_exists_neg
    (assignments : List (FreeVarId × SetTerm))
    (raw tag : Nat)
    (certificate payload : SetTerm)
    (body : SetFormula)
    (hPayload : Term.Admissible payload SetSort.set)
    (hBody : Formula.Admissible body)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ numₘ(raw)))
    (hPairField :
      ∀ {Γ : Context signature},
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body →
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            certificate ≐ₘ
              godel_pairₘ(⟨numₘ(tag), payload⟩ₘ))
    (hPayloadNatural :
      ∀ {Γ : Context signature},
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body →
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            payload ∈ₘ ωₘ)
    (hTagMismatch :
      (godel_unpair_value raw).1 ≠ tag) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ Formula.existsFreeAssignments
        SetSort.set assignments body) :=
  fs_zfc_support_raw_exists_assignments_neg assignments body <|
    fs_zfc_support_raw_logical_tagged_body_imp_falsum
      raw tag certificate payload body hPayload hBody
      hCertificateCode hPairField hPayloadNatural hTagMismatch

/-- 公式 payload 组件条件直接给出其数值码属于对象自然数。 -/
theorem fs_zfc_support_raw_logical_formula_payload_numeric_mem_omega
    {Γ : Context signature}
    (formulaCode numericCode : SetTerm)
    (traceId indexId : FreeVarId)
    (hComponent :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_formula_payload_component_condition_with_ids
          formulaCode numericCode traceId indexId) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      numericCode ∈ₘ ωₘ := by
  exact
    (fs_zfc_support_raw_nat_sequence_code_condition_parts
      formulaCode numericCode traceId indexId
      (FirstOrder.Derives.conjElimRight hComponent)).2.1

/-- 两层 Gödel 配对的三个自然数坐标仍给出自然数 payload。 -/
theorem fs_zfc_support_raw_logical_nested_pair_payload_mem_omega
    {Γ : Context signature}
    (payload eigen left right : SetTerm)
    (hPayload : Term.Admissible payload SetSort.set)
    (hEigen : Term.Admissible eigen SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEigenNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] eigen ∈ₘ ωₘ)
    (hLeftNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] left ∈ₘ ωₘ)
    (hRightNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] right ∈ₘ ωₘ)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        payload ≐ₘ
          godel_pairₘ(⟨eigen,
            godel_pairₘ(⟨left, right⟩ₘ)⟩ₘ)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] payload ∈ₘ ωₘ := by
  have hInnerAdmissible :
      Term.Admissible
        (godel_pairₘ(⟨left, right⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible _ <|
      ordered_pair_term_admissible left right hLeft hRight
  have hInnerNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        godel_pairₘ(⟨left, right⟩ₘ) ∈ₘ ωₘ :=
    fs_zfc_support_raw_godel_pairing_mem_omega
      left right hLeft hRight hLeftNatural hRightNatural
  exact fs_zfc_support_raw_godel_pairing_mem_omega_of_equality
    payload eigen (godel_pairₘ(⟨left, right⟩ₘ))
    hPayload hEigen hInnerAdmissible
    hEigenNatural hInnerNatural hEquality

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
