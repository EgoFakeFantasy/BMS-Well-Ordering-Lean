import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.AxiomDecode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicProofCertificate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatDecode

/-! # 支撑公理理论上的具体自然数证明解码入口 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open Nonlogical.BasicSetTheory
set_option autoImplicit false

/-- 不含经典选择的具体正向解码函数。 -/
def intrinsic_zfc_nat_decode : Nat → Option IntrinsicClosedProofCertificate :=
  NatDecode.decode intrinsic_zfc_axiom_decode

def intrinsic_zfc_nat_check : Nat → SetSentence → Bool :=
  NatDecode.check intrinsic_zfc_axiom_decode

theorem intrinsic_zfc_nat_decode_sound {code : Nat} {certificate : IntrinsicClosedProofCertificate}
    (hDecoded : intrinsic_zfc_nat_decode code = some certificate) :
    Derives intrinsic_zfc_theory [] certificate.conclusion :=
  NatDecode.decode_sound intrinsic_zfc_axiom_decode hDecoded

theorem intrinsic_zfc_nat_check_sound {code : Nat} {formula : SetSentence}
    (hChecked : intrinsic_zfc_nat_check code formula = true) :
    Derives intrinsic_zfc_theory [] formula :=
  NatDecode.check_sound intrinsic_zfc_axiom_decode hChecked

theorem intrinsic_zfc_nat_check_eq_true_iff (code : Nat) (formula : SetSentence) :
    intrinsic_zfc_nat_check code formula = true ↔
      ∃ certificate, intrinsic_zfc_nat_decode code = some certificate ∧ certificate.conclusion = formula :=
  NatDecode.check_eq_true_iff intrinsic_zfc_axiom_decode code formula
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
