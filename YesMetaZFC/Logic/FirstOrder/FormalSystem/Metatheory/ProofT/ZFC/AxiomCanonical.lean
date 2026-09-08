import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaBody
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaEnvelope
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatPacketCanonical

/-! # 基础公理证书的规范性

成功解码后的重新编码逐节点恢复输入，包括任意参数数目的两个模式。
因此实际自然数包的成功可以直接转成规范证书的正向对象推导。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open Nonlogical.BasicSetTheory NatPacket
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false

namespace ProjectDecode
theorem unarySchema_encode_of_decode {n : Nat} {input : Tree} {schema : Project.UnarySchema n}
    (h : unarySchema n input = some schema) : ProjectEncode.formula schema.body = input := by
  obtain ⟨body, hBody, hResult⟩ := Option.bind_eq_some_iff.mp h
  have hClosed := (SchemaBody.decode_spec _ _ _ hBody).1
  simp only [dif_pos hClosed, Option.some.injEq] at hResult
  cases hResult
  exact (SchemaBody.decode_spec _ _ _ hBody).2

theorem binarySchema_encode_of_decode {n : Nat} {input : Tree} {schema : Project.BinarySchema n}
    (h : binarySchema n input = some schema) : ProjectEncode.formula schema.body = input := by
  obtain ⟨body, hBody, hResult⟩ := Option.bind_eq_some_iff.mp h
  have hClosed := (SchemaBody.decode_spec _ _ _ hBody).1
  simp only [dif_pos hClosed, Option.some.injEq] at hResult
  cases hResult
  exact (SchemaBody.decode_spec _ _ _ hBody).2
end ProjectDecode

theorem zfc_base_axiom_encode_of_decode {input : Tree} {certificate : ZFCAxiomCertificate}
    (h : zfc_base_axiom_decode input = some certificate) : zfc_base_axiom_encode certificate = input := by
  fun_cases zfc_base_axiom_decode input
  case case1 | case2 | case3 | case4 | case5 | case6 | case7 | case8 => cases h; rfl
  case case9 countTree body =>
    obtain ⟨count, hCount, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨schema, hSchema, hResult⟩ := Option.bind_eq_some_iff.mp hRest
    cases hResult
    have hBody := ProjectDecode.unarySchema_encode_of_decode hSchema
    cases countTree with
    | node tag fields =>
      cases fields with
      | nil => cases hCount; simp [zfc_base_axiom_encode, hBody, leaf]
      | cons _ _ => cases hCount
  case case10 countTree body =>
    obtain ⟨count, hCount, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨schema, hSchema, hResult⟩ := Option.bind_eq_some_iff.mp hRest
    cases hResult
    have hBody := ProjectDecode.binarySchema_encode_of_decode hSchema
    cases countTree with
    | node tag fields =>
      cases fields with
      | nil => cases hCount; simp [zfc_base_axiom_encode, hBody, leaf]
      | cons _ _ => cases hCount
  case case11 =>
    unfold zfc_base_axiom_decode at h
    split at h <;> simp_all

theorem zfc_base_axiom_decode_eq_some_iff (input : Tree) (certificate : ZFCAxiomCertificate) :
    zfc_base_axiom_decode input = some certificate ↔ zfc_base_axiom_encode certificate = input :=
  ⟨zfc_base_axiom_encode_of_decode, fun h => h ▸ zfc_base_axiom_roundtrip certificate⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
