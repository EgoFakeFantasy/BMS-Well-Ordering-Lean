import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedLine

/-!
# ProofT 内在逻辑证书行

本模块把逻辑证书载荷直接装入 checked 行的首个分支。见证由类型化 bound
槽位承载，逻辑条件只经公共四元模板实例化一次，不展开其具体公理分支。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace IntrinsicLogicalLine

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open StructuredCertificateCondition

set_option autoImplicit false

/-- 已验证的逻辑证书载荷直接生成 checked 行。 -/
theorem line_instance_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (sequence certificates certificateCode : SetOpenTerm free)
    (index : Nat)
    (hPayloadBound :
      Γ ⊢ₘ[T]
        certificate_payload_bound
          certificates (numₘ(index)) certificateCode)
    (hCertificate :
      Γ ⊢ₘ[T]
        (certificates ·ₘ numₘ(index)) ≐ₘ
          logical_certificate_code certificateCode)
    (hLogical :
      Γ ⊢ₘ[T]
        verifier.logical_condition
          sequence certificates (numₘ(index)) certificateCode) :
    Γ ⊢ₘ[T]
      IntrinsicCheckedLine.line_instance
        verifier sequence certificates index := by
  let sequenceOne : SetTerm [SetSort.set] free :=
    sequence.weakenBound SetSort.set
  let certificatesOne : SetTerm [SetSort.set] free :=
    certificates.weakenBound SetSort.set
  let indexOne : SetTerm [SetSort.set] free :=
    (numₘ(index) : SetOpenTerm free).weakenBound SetSort.set
  let certificateVariable : SetTerm [SetSort.set] free :=
    .bvar .here
  let logicalBody : SetFormula [SetSort.set] free :=
    (certificatesOne ·ₘ indexOne ≐ₘ
        logical_certificate_code certificateVariable) ∧ₘ
      verifier.logical_condition
        sequenceOne certificatesOne indexOne certificateVariable
  have hBody : Γ ⊢ₘ[T]
      logicalBody.instantiateTop certificateCode := by
    simpa [logicalBody, sequenceOne, certificatesOne, indexOne,
      certificateVariable, logical_certificate_code,
      Formula.instantiateTop, Formula.substitute,
      Substitution.instantiateTop, Formula.substituteMapped,
      Term.instantiateTop, Term.substitute, Term.substituteMapped,
      Arguments.substituteMapped,
      VariableSubstitution.instantiateTop,
      VariableSubstitution.cons, VariableSubstitution.empty,
      VariableSubstitution.liftBound, VariableSubstitution.freeId,
      VariableSubstitution.boundId,
      Term.substituteMapped_weakenBound,
      Arguments.substituteMapped_weakenBound,
      FormulaTemplate.apply_four_substituteMapped,
      finite_numeral_term_substituteMapped] using
      FirstOrder.Derives.conj_intro hCertificate hLogical
  have hBranch : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedExists set_levy_bound
        (Sₘ(certificates ·ₘ numₘ(index))) logicalBody :=
    bounded_exists_intro
      (Sₘ(certificates ·ₘ numₘ(index))) logicalBody certificateCode
      hPayloadBound hBody
  have hLine : Γ ⊢ₘ[T]
      verifier.line_condition
        sequence certificates (numₘ(index)) := by
    apply FirstOrder.Derives.disj_intro_left
    simpa [CheckedVerifier.line_condition,
      line_condition_with_logical, logicalBody, sequenceOne,
      certificatesOne, indexOne, certificateVariable] using hBranch
  simpa [IntrinsicCheckedLine.line_instance] using hLine

end IntrinsicLogicalLine
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
