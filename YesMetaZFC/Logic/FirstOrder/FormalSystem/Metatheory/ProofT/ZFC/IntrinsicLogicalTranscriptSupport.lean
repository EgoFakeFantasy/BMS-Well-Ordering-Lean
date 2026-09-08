import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedSequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicFirstOrderLogicalLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicVerifier

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC

open Nonlogical.BasicSetTheory
open StructuredCertificateCondition
open IntrinsicLogicalCertificate
open IntrinsicCheckedLine
open IntrinsicCheckedSequence
open IntrinsicFirstOrderLogicalLine
open IntrinsicVerifier

open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

theorem intrinsic_zfc_certificate_payload_bound_of_at
    {free : SetContext} {Γ : Context signature free}
    (certificates certificate : SetOpenTerm free)
    (index : Nat)
    (hCertificateBound : Γ ⊢ₘ[intrinsic_zfc_theory] certificate ∈ₘ ωₘ)
    (hLogicalCertificate : Γ ⊢ₘ[intrinsic_zfc_theory]
      (certificates ·ₘ numₘ(index)) ≐ₘ logical_certificate_code certificate) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      certificate_payload_bound certificates (numₘ(index)) certificate := by
  unfold certificate_payload_bound
  have hZero : Γ ⊢ₘ[intrinsic_zfc_theory]
      (numₘ(0) : SetOpenTerm free) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 0
  have hNodeEq : Γ ⊢ₘ[intrinsic_zfc_theory]
      godel_pairₘ(numₘ(0), certificate) ≐ₘ
        certificates ·ₘ numₘ(index) := by
    simpa [logical_certificate_code] using
      Metatheory.Derives.equality_symm hLogicalCertificate
  have hNodeEqS : Γ ⊢ₘ[intrinsic_zfc_theory]
      Sₘ(godel_pairₘ(numₘ(0), certificate)) ≐ₘ
        Sₘ(certificates ·ₘ numₘ(index)) :=
    successor_term_congr_of_equality
      (godel_pairₘ(numₘ(0), certificate))
      (certificates ·ₘ numₘ(index)) hNodeEq
  have hCoordinateAxiom : Γ ⊢ₘ[intrinsic_zfc_theory]
      ((numₘ(0) ∈ₘ (ωₘ : SetOpenTerm free)) ∧ₘ
        (certificate ∈ₘ ωₘ)) ⟶ₘ
      ((numₘ(0) ∈ₘ Sₘ(godel_pairₘ(numₘ(0), certificate))) ∧ₘ
        (certificate ∈ₘ Sₘ(godel_pairₘ(numₘ(0), certificate)))) :=
    FirstOrder.Derives.theory_weaken
      natural_addition_bound_theory_subset_intrinsic_zfc_theory
      (natural_godel_pairing_coordinate_bound_instance_derives
        (Γ := Γ) (numₘ(0)) certificate)
  have hPayloadNode : Γ ⊢ₘ[intrinsic_zfc_theory]
      certificate ∈ₘ Sₘ(godel_pairₘ(numₘ(0), certificate)) :=
    FirstOrder.Derives.conj_elim_right <|
      FirstOrder.Derives.imp_elim hCoordinateAxiom
        (FirstOrder.Derives.conj_intro hZero hCertificateBound)
  exact FirstOrder.Derives.iff_elim_left
    (membership_right_iff_of_equality
      certificate
      (Sₘ(godel_pairₘ(numₘ(0), certificate)))
      (Sₘ(certificates ·ₘ numₘ(index))) hNodeEqS)
    hPayloadNode

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
