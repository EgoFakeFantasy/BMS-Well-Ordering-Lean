import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.BaseAxiomPacketGraph
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta1AxiomPresentation

/-! # ZFC 基础公理检查器的具体表示实例

用原 `AxiomPresentation.check` 比较内核闭句。接受恰好表示原 ZFC 公理像，
正负对象推导在既有支撑理论中成立；没有把公理检查冒充完整证明检查。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.BaseAxiomPacket
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def checked (packet : Nat) (formula : SetSentence) : Bool :=
  match decode packet with
  | none => false
  | some certificate => intrinsic_zfc_base_axiom_presentation.check certificate formula

theorem checked_eq_true_iff (packet : Nat) (formula : SetSentence) :
    checked packet formula = true ↔ ∃ certificate,
      decode packet = some certificate ∧ project_sentence certificate.sentence = formula := by
  unfold checked
  cases h : decode packet with
  | none => simp
  | some certificate => simp [AxiomPresentation.check_eq_true_iff, intrinsic_zfc_base_axiom_presentation]

theorem checked_run (packet : Nat) (formula : SetSentence) :
    checked packet formula = true ↔ run packet = some (SyntaxEncode.formula formula) := by
  rw [checked_eq_true_iff]
  simp only [run, Option.map_eq_some_iff]
  constructor
  · rintro ⟨certificate, hCertificate, hFormula⟩
    exact ⟨certificate, hCertificate, congrArg SyntaxEncode.formula hFormula⟩
  · rintro ⟨certificate, hCertificate, hCode⟩
    refine ⟨certificate, hCertificate, ?_⟩
    have hDecoded := congrArg (SyntaxDecode.formula [] []) hCode
    simpa only [conclusion, SyntaxEncode.formula_roundtrip, Option.some.injEq] using hDecoded

theorem checked_sound {packet : Nat} {formula : SetSentence} (h : checked packet formula = true) :
    intrinsic_zfc_axiom_theory formula := by
  obtain ⟨certificate, _, rfl⟩ := (checked_eq_true_iff packet formula).mp h
  exact intrinsic_zfc_base_axiom_presentation.sound certificate

theorem checked_complete {formula : SetSentence} (h : intrinsic_zfc_axiom_theory formula) :
    ∃ packet, checked packet formula = true := by
  obtain ⟨certificate, hCertificate⟩ := intrinsic_zfc_base_axiom_presentation.complete h
  refine ⟨NatPacket.encode (zfc_base_axiom_encode certificate), ?_⟩
  exact (checked_eq_true_iff _ _).mpr ⟨certificate, decode_encode certificate, hCertificate⟩

theorem checked_positive {packet : Nat} {formula : SetSentence} (h : checked packet formula = true) :
    Derives intrinsic_zfc_theory [] (condition (numₘ(packet)) (IntrinsicQuotation.quote formula)) :=
  positive_at_tree packet (SyntaxEncode.formula formula) ((checked_run packet formula).mp h)

theorem checked_negative {packet : Nat} {formula : SetSentence} (h : checked packet formula = false) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(packet)) (IntrinsicQuotation.quote formula)) :=
  negative_at_tree packet (SyntaxEncode.formula formula) (by
    intro hRun
    have hTrue := (checked_run packet formula).mpr hRun
    rw [h] at hTrue
    cases hTrue)

/-- 完整基础公理关系的具体实例，所有字段均由本轮及模式层的定理填入。 -/
def presentation : Delta1AxiomPresentation intrinsic_zfc_theory intrinsic_zfc_axiom_theory where
  condition := template
  delta0 packet output := by rw [template_apply]; exact condition_delta0 packet output
  checked := checked
  checked_sound := checked_sound
  checked_complete := checked_complete
  condition_positive h := by rw [template_apply]; exact checked_positive h
  condition_negative h := by rw [template_apply]; exact checked_negative h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.BaseAxiomPacket
