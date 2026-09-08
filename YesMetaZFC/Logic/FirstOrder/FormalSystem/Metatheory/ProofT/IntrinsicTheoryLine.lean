import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicLogicalLine

/-!
# ProofT 内在理论公理行

理论公理分支与逻辑分支共享同一 checked 行骨架。这里仅替换分支条件，
不引入旧证书回放或变量新鲜性合同。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace IntrinsicTheoryLine

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open StructuredCertificateCondition

set_option autoImplicit false

/-- 已验证的理论公理载荷直接生成 checked 行。 -/
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
          theory_certificate_code certificateCode)
    (hCondition :
      Γ ⊢ₘ[T]
        verifier.condition
          (sequence ·ₘ numₘ(index)) certificateCode) :
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
  let theoryBody : SetFormula [SetSort.set] free :=
    (certificatesOne ·ₘ indexOne ≐ₘ
        theory_certificate_code certificateVariable) ∧ₘ
      verifier.condition
        (sequenceOne ·ₘ indexOne) certificateVariable
  have hBody : Γ ⊢ₘ[T]
      theoryBody.instantiateTop certificateCode := by
    simpa [theoryBody, sequenceOne, certificatesOne, indexOne,
      certificateVariable, theory_certificate_code,
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
      FormulaTemplate.apply_two_substituteMapped,
      finite_numeral_term_substituteMapped] using
      FirstOrder.Derives.conj_intro hCertificate hCondition
  have hBranch : Γ ⊢ₘ[T]
      Formula.LevyBound.boundedExists set_levy_bound
        (Sₘ(certificates ·ₘ numₘ(index))) theoryBody :=
    bounded_exists_intro
      (Sₘ(certificates ·ₘ numₘ(index))) theoryBody certificateCode
      hPayloadBound hBody
  have hLine : Γ ⊢ₘ[T]
      verifier.line_condition
        sequence certificates (numₘ(index)) := by
    apply FirstOrder.Derives.disj_intro_right
    apply FirstOrder.Derives.disj_intro_left
    simpa [CheckedVerifier.line_condition,
      line_condition_with_logical, theory_certificate_line_condition,
      theoryBody, sequenceOne,
      certificatesOne, indexOne, certificateVariable] using! hBranch
  simpa [IntrinsicCheckedLine.line_instance] using hLine

end IntrinsicTheoryLine
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
