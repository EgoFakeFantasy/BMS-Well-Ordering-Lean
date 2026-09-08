import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicAxiomCertificate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel

/-!
# ZFC 与证明支撑公理的统一证书入口

ZFC 的八条固定公理和两个 schema 分支保留为显式构造子。
与公共支撑公理证书作带标签的和以后，检查器覆盖的理论精确为
`intrinsic_zfc_theory`，包含支撑中的参数化分离公理族。
-/

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC

open Nonlogical.BasicSetTheory QuineEncoding

set_option autoImplicit false

private abbrev Project := _root_.YesMetaZFC.SetTheory.Definitional.Project.Sentence

/-- ZFC 公理行的语法证书；schema 携带实际的参数数目和公式。 -/
inductive ZFCAxiomCertificate where
  | extensionality
  | emptySet
  | pairing
  | union
  | powerSet
  | infinity
  | foundation
  | choice
  | separation {parameterCount : Nat}
      (schema : _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema parameterCount)
  | collection {parameterCount : Nat}
      (schema : _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema parameterCount)

namespace ZFCAxiomCertificate

open _root_.YesMetaZFC.SetTheory

/-- 从证书直接重建 Project 公理闭句。 -/
def sentence : ZFCAxiomCertificate → Project
  | .extensionality => Axioms.extensionality
  | .emptySet => Axioms.emptySet
  | .pairing => Axioms.pairing
  | .union => Axioms.union
  | .powerSet => Axioms.powerSet
  | .infinity => Axioms.infinity
  | .foundation => Axioms.foundation
  | .choice => Axioms.choice
  | .separation schema => Axioms.Schema.separation schema
  | .collection schema => Axioms.Schema.collection schema

theorem sound (certificate : ZFCAxiomCertificate) :
    _root_.YesMetaZFC.SetTheory.ZFC certificate.sentence := by
  cases certificate with
  | choice => exact .choice
  | extensionality => exact .zf .extensionality
  | emptySet => exact .zf .emptySet
  | pairing => exact .zf .pairing
  | union => exact .zf .union
  | powerSet => exact .zf .powerSet
  | infinity => exact .zf .infinity
  | foundation => exact .zf .foundation
  | separation schema => exact .zf (.separation schema)
  | collection schema => exact .zf (.collection schema)

theorem complete {formula : Project}
    (hFormula : _root_.YesMetaZFC.SetTheory.ZFC formula) :
    ∃ certificate : ZFCAxiomCertificate, certificate.sentence = formula := by
  cases hFormula with
  | choice => exact ⟨.choice, rfl⟩
  | zf hZF =>
      cases hZF with
      | extensionality => exact ⟨.extensionality, rfl⟩
      | emptySet => exact ⟨.emptySet, rfl⟩
      | pairing => exact ⟨.pairing, rfl⟩
      | union => exact ⟨.union, rfl⟩
      | powerSet => exact ⟨.powerSet, rfl⟩
      | infinity => exact ⟨.infinity, rfl⟩
      | foundation => exact ⟨.foundation, rfl⟩
      | separation schema => exact ⟨.separation schema, rfl⟩
      | collection schema => exact ⟨.collection schema, rfl⟩

end ZFCAxiomCertificate

/-- ZFC 公理像的精确证书表示。 -/
def intrinsic_zfc_base_axiom_presentation :
    AxiomPresentation intrinsic_zfc_axiom_theory where
  Certificate := ZFCAxiomCertificate
  sentence := fun certificate => project_sentence certificate.sentence
  sound := fun certificate => ⟨certificate.sentence, certificate.sound, rfl⟩
  complete := by
    rintro formula ⟨source, hSource, rfl⟩
    obtain ⟨certificate, hCertificate⟩ := ZFCAxiomCertificate.complete hSource
    exact ⟨certificate, congrArg project_sentence hCertificate⟩

/-- 完整支撑公理理论的公理检查入口。 -/
def intrinsic_zfc_axiom_presentation : AxiomPresentation intrinsic_zfc_theory :=
  AxiomPresentation.union intrinsic_zfc_base_axiom_presentation
    intrinsic_proof_axiom_presentation

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
