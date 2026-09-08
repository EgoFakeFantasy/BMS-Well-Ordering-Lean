import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedAxioms

/-! # 完整等价公理基的实际证书包与对象公式连接

ZFC 原分支使用标签 0–9；有限支撑基使用标签 10 和一个自然数索引。
新格式有明确边界，不与原完整 union 路径混用。往返及规范性覆盖全部证书和失败输入。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedAxiomPacket
open Nonlogical.BasicSetTheory NatPacket ReducedAxioms
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
attribute [local irreducible] ReducedAxioms.basis

abbrev Certificate := ZFCAxiomCertificate ⊕ Fin basis.axioms.length

def encodeTree : Certificate → Tree
  | .inl certificate => zfc_base_axiom_encode certificate
  | .inr index => .node 10 [leaf index.val]

def decodeTree : Tree → Option Certificate
  | .node 10 [.node index []] =>
    if h : index < basis.axioms.length then some (.inr ⟨index, h⟩) else none
  | input => (zfc_base_axiom_decode input).map Sum.inl

theorem tree_roundtrip (certificate : Certificate) : decodeTree (encodeTree certificate) = some certificate := by
  cases certificate with
  | inl certificate =>
    have h := congrArg (Option.map (Sum.inl : ZFCAxiomCertificate → Certificate))
      (zfc_base_axiom_roundtrip certificate)
    cases certificate <;>
      simpa only [encodeTree, zfc_base_axiom_encode, leaf, decodeTree, Option.map_some] using h
  | inr index => simp only [encodeTree, leaf, decodeTree, dif_pos index.isLt]

theorem tree_canonical {input : Tree} {certificate : Certificate}
    (h : decodeTree input = some certificate) : encodeTree certificate = input := by
  unfold decodeTree at h
  split at h
  · split at h
    · have h := Option.some.inj h
      subst certificate
      rfl
    · cases h
  · obtain ⟨source, hSource, hCertificate⟩ := Option.map_eq_some_iff.mp h
    subst certificate
    exact zfc_base_axiom_encode_of_decode hSource

def encode (certificate : Certificate) : Nat := NatPacket.encode (encodeTree certificate)
def decode (packet : Nat) : Option Certificate := (NatPacket.decode packet).bind decodeTree

theorem decode_encode (certificate : Certificate) : decode (encode certificate) = some certificate := by
  simp only [decode, encode, NatPacket.decode_encode, Option.bind_some, tree_roundtrip]

theorem decode_eq_some_iff (packet : Nat) (certificate : Certificate) :
    decode packet = some certificate ↔ encode certificate = packet := by
  constructor
  · intro h
    obtain ⟨input, hPacket, hCertificate⟩ := Option.bind_eq_some_iff.mp h
    unfold encode
    rw [tree_canonical hCertificate]
    exact NatPacket.encode_of_decode hPacket
  · intro h
    rw [← h]
    exact decode_encode certificate

/-- 实际解码后使用原有精确语法比较，不以对象公式的真假定义检查器。 -/
def checked (packet : Nat) (φ : SetSentence) : Bool :=
  match decode packet with
  | none => false
  | some certificate => axiomPresentation.check certificate φ

theorem checked_eq_true_iff (packet : Nat) (φ : SetSentence) :
    checked packet φ = true ↔ ∃ certificate,
      encode certificate = packet ∧ axiomPresentation.sentence certificate = φ := by
  have h : checked packet φ = true ↔ ∃ certificate,
      decode packet = some certificate ∧ axiomPresentation.sentence certificate = φ := by
    unfold checked
    cases h : decode packet with
    | none => simp
    | some certificate =>
      simp only [Option.some.injEq]
      constructor
      · intro hChecked
        exact ⟨certificate, rfl, (axiomPresentation.check_eq_true_iff certificate φ).mp hChecked⟩
      · rintro ⟨other, hOther, hFormula⟩
        subst other
        exact (axiomPresentation.check_eq_true_iff certificate φ).mpr hFormula
  simpa only [decode_eq_some_iff] using h

/-- 独立包检查器与公理对象表示的有限表、模式分支逐项一致。 -/
theorem checked_agrees (packet : Nat) (φ : SetSentence) :
    checked packet φ = ReducedAxioms.presentation.checked packet φ := by
  apply Bool.eq_iff_iff.mpr
  rw [checked_eq_true_iff]
  dsimp only [ReducedAxioms.presentation, Delta1AxiomPresentation.union,
    BaseAxiomPacket.presentation, ObjectFiniteAxioms.presentation]
  rw [Bool.or_eq_true_iff, BaseAxiomPacket.checked_eq_true_iff, ObjectFiniteAxioms.checked_eq_true_iff]
  constructor
  · rintro ⟨certificate, hPacket, hFormula⟩
    cases certificate with
    | inl certificate =>
      exact Or.inl ⟨certificate, (BaseAxiomPacket.decode_eq_some_iff packet certificate).mpr hPacket, hFormula⟩
    | inr index => exact Or.inr ⟨index, hPacket.symm, hFormula⟩
  · rintro (⟨certificate, hPacket, hFormula⟩ | ⟨index, hPacket, hFormula⟩)
    · exact ⟨.inl certificate, (BaseAxiomPacket.decode_eq_some_iff packet certificate).mp hPacket, hFormula⟩
    · exact ⟨.inr index, hPacket.symm, hFormula⟩

/-- 使用实际包解码器的完整公理基表示；目标理论仍明确保留为等价公理基。 -/
def presentation : Delta1AxiomPresentation intrinsic_zfc_theory ReducedAxioms.theory where
  condition := ReducedAxioms.presentation.condition
  delta0 := ReducedAxioms.presentation.delta0
  checked := checked
  checked_sound h := ReducedAxioms.presentation.checked_sound (by rwa [← checked_agrees])
  checked_complete h := by
    obtain ⟨packet, hPacket⟩ := ReducedAxioms.presentation.checked_complete h
    exact ⟨packet, by rwa [checked_agrees]⟩
  condition_positive h := ReducedAxioms.presentation.condition_positive (by rwa [← checked_agrees])
  condition_negative h := ReducedAxioms.presentation.condition_negative (by rwa [← checked_agrees])

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedAxiomPacket
