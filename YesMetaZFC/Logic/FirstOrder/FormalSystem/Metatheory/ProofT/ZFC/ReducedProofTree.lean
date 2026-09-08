import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedAxiomPacket
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProofTreeCheck

/-! # 原支撑理论的完整自然数证明树检查器

公理节点直接消费已完成对象表示的精简公理包。树检查器的可靠性和完备性
经推导等价回到原支撑理论；不增加公理，不改变原 Hilbert 核。
此处完成计算检查，局部变换的对象正负表示仍是完整证明表示的剩余依赖。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofTree
open Nonlogical.BasicSetTheory
set_option autoImplicit false
attribute [local irreducible] ReducedAxioms.basis

def decoder : AxiomDecoder ReducedAxioms.axiomPresentation := ReducedAxiomPacket.decodeTree

def codec : AxiomCodec decoder where
  encode := ReducedAxiomPacket.encodeTree
  roundtrip := ReducedAxiomPacket.tree_roundtrip

def encode (proof : ClosedProofCertificate ReducedAxioms.axiomPresentation) : Nat :=
  ProofTreeCode.encode codec proof.proof

def checked (code : Nat) (formula : SetSentence) : Bool := ProofTreeCode.checked decoder code formula

theorem checked_sound {code : Nat} {formula : SetSentence} (h : checked code formula = true) :
    Derives intrinsic_zfc_theory [] formula :=
  ReducedAxioms.derives_iff.mp (ProofTreeCode.checked_sound decoder h)

theorem checked_encode (proof : ClosedProofCertificate ReducedAxioms.axiomPresentation) :
    checked (encode proof) proof.conclusion = true := ProofTreeCode.checked_encode codec proof

theorem checked_complete {formula : SetSentence} (h : Derives intrinsic_zfc_theory [] formula) :
    ∃ code, checked code formula = true :=
  ProofTreeCode.checked_complete codec (ReducedAxioms.derives_iff.mpr h)

theorem derives_iff (formula : SetSentence) :
    Derives intrinsic_zfc_theory [] formula ↔ ∃ code, checked code formula = true :=
  ⟨checked_complete, fun ⟨_, h⟩ => checked_sound h⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedProofTree
