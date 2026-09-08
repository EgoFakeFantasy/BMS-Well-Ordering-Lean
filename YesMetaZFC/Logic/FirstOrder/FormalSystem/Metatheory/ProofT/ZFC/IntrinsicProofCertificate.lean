import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProofCertificate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicAxiomCertificate

/-!
# 支撑公理理论上的具体结构证明证书

公理证书覆盖 ZFC 与全部原有支撑；推导证书覆盖既有 Hilbert 核的全部规则。
以下可靠性和完备性定理针对结构证书。它们没有把结构证书冒充自然数，
也没有假定对象层正负表示；`Delta1ProofPresentation` 的装配仍须补齐这两层。
-/

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC

open Nonlogical.BasicSetTheory

set_option autoImplicit false

/-- 支撑公理理论的具体闭证明证书类型。 -/
abbrev IntrinsicClosedProofCertificate :=
  ClosedProofCertificate intrinsic_zfc_axiom_presentation

/-- 结构证书的实际可计算结论检查。 -/
def intrinsic_zfc_certificate_check
    (certificate : IntrinsicClosedProofCertificate) (formula : SetSentence) : Bool :=
  certificate.check formula

/-- 检查成功的结构证书可重放为目标理论的普通推导。 -/
theorem intrinsic_zfc_certificate_check_sound
    {certificate : IntrinsicClosedProofCertificate} {formula : SetSentence}
    (hChecked : intrinsic_zfc_certificate_check certificate formula = true) :
    Derives intrinsic_zfc_theory [] formula :=
  ClosedProofCertificate.check_sound hChecked

/-- 目标理论的每个普通闭推导均有检查成功的结构证书。 -/
theorem intrinsic_zfc_certificate_check_complete
    {formula : SetSentence} (hFormula : Derives intrinsic_zfc_theory [] formula) :
    ∃ certificate : IntrinsicClosedProofCertificate,
      intrinsic_zfc_certificate_check certificate formula = true :=
  ClosedProofCertificate.check_complete intrinsic_zfc_axiom_presentation hFormula

/-- 更换公理行和推导证书格式不改变目标理论的可证闭句。 -/
theorem intrinsic_zfc_derives_iff_certificate (formula : SetSentence) :
    Derives intrinsic_zfc_theory [] formula ↔
      ∃ certificate : IntrinsicClosedProofCertificate,
        intrinsic_zfc_certificate_check certificate formula = true := by
  constructor
  · exact intrinsic_zfc_certificate_check_complete
  · rintro ⟨certificate, hChecked⟩
    exact intrinsic_zfc_certificate_check_sound hChecked

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
