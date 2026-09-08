import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.AxiomEncode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.NatDecode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatEncode

/-!
# 支撑公理理论的自然数证明表示：编码、往返与完备性

本层闭合宿主可计算检查器的可靠性与完备性。
对象语言中的正负表示合同仍由后续 Delta1 实例承担。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open Nonlogical.BasicSetTheory
set_option autoImplicit false

def intrinsic_zfc_nat_encode : IntrinsicClosedProofCertificate → Nat :=
  NatEncode.encode intrinsic_zfc_axiom_codec

/-- 每一个结构闭证明都从其自然数编码恢复为同一个证书。 -/
@[simp] theorem intrinsic_zfc_nat_decode_encode (certificate : IntrinsicClosedProofCertificate) :
    intrinsic_zfc_nat_decode (intrinsic_zfc_nat_encode certificate) = some certificate :=
  NatEncode.decode_encode intrinsic_zfc_axiom_codec certificate

theorem intrinsic_zfc_nat_encode_injective : Function.Injective intrinsic_zfc_nat_encode := by
  intro left right h
  have hDecoded := congrArg intrinsic_zfc_nat_decode h
  rw [intrinsic_zfc_nat_decode_encode, intrinsic_zfc_nat_decode_encode] at hDecoded
  exact Option.some.inj hDecoded

@[simp] theorem intrinsic_zfc_nat_check_encode (certificate : IntrinsicClosedProofCertificate) :
    intrinsic_zfc_nat_check (intrinsic_zfc_nat_encode certificate) certificate.conclusion = true :=
  NatEncode.check_encode intrinsic_zfc_axiom_codec certificate

/-- 原理论的任意可证闭句均拥有一个可接受的自然数证明码。 -/
theorem intrinsic_zfc_nat_check_complete {formula : SetSentence}
    (h : Derives intrinsic_zfc_theory [] formula) :
    ∃ code, intrinsic_zfc_nat_check code formula = true :=
  NatEncode.check_complete intrinsic_zfc_axiom_codec h

/-- 自然数检查器精确刻画原支撑公理理论的普通可证性。 -/
theorem intrinsic_zfc_derives_iff_nat_certificate (formula : SetSentence) :
    Derives intrinsic_zfc_theory [] formula ↔ ∃ code, intrinsic_zfc_nat_check code formula = true := by
  constructor
  · exact intrinsic_zfc_nat_check_complete
  · rintro ⟨code, hCode⟩
    exact intrinsic_zfc_nat_check_sound hCode
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
