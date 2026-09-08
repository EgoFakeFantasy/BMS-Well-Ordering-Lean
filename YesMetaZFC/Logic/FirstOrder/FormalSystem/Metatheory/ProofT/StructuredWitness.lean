import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.StructuredCertificateCondition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicProofSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceInversion

/-!
# ProofT 的内在结构化见证

本层把总证明码的坐标反演与两个有限序列的规范反演直接串接起来。
所有项都使用内在上下文；因此接口不再暴露自由变量编号、支撑集、可容许性或新鲜性桥接义务。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace StructuredWitness

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open StructuredCertificateCondition

set_option autoImplicit false

/-! ## 坐标反演后的规范序列见证 -/

/--
总证明码确定证明序列与证书序列的规范有限图。

`number` 的两个 Gödel 坐标分别是二维证明序列码与自然数证书序列码；
`SequenceInversion` 只需消费对应的对象编码条件与坐标等式。
-/
theorem witness_sequences
    {T : SetTheory}
    (P : IntrinsicProofSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (number : Nat)
    (sequence certificates formulaCode certificateCode : SetOpenTerm free)
    (hProofCondition :
      Γ ⊢ₘ[T] proof_sequence_code_condition sequence formulaCode)
    (hCertificateCondition :
      Γ ⊢ₘ[T] nat_sequence_code_condition certificates certificateCode)
    (hFormulaBound :
      Γ ⊢ₘ[T]
        proof_code_component_bound (numₘ(number)) formulaCode)
    (hCertificateBound :
      Γ ⊢ₘ[T]
        proof_code_component_bound (numₘ(number)) certificateCode)
    (hPair :
      Γ ⊢ₘ[T]
        numₘ(number) ≐ₘ godel_pairₘ(formulaCode, certificateCode)) :
    Γ ⊢ₘ[T]
      (sequence ≐ₘ
          proof_sequence_graph_term
            (proof_sequence_decode (godel_unpair_value number).1)) ∧ₘ
        (certificates ≐ₘ
          nat_sequence_graph_term
            (nat_sequence_decode (godel_unpair_value number).2)) := by
  let rows : List (List Nat) :=
    proof_sequence_decode (godel_unpair_value number).1
  let tokens : List Nat :=
    nat_sequence_decode (godel_unpair_value number).2
  have hCoordinates :=
    StructuredCertificateCondition.components_unique
      P.certificate_core number formulaCode certificateCode
      hFormulaBound hCertificateBound hPair
  have hFormulaCode :
      Γ ⊢ₘ[T] formulaCode ≐ₘ numₘ(proof_sequence_code_value rows) := by
    have hLeftCoordinate :=
      FirstOrder.Derives.conj_elim_left hCoordinates
    simpa [rows, proof_sequence_code_value_decode] using hLeftCoordinate
  have hCertificateCode :
      Γ ⊢ₘ[T] certificateCode ≐ₘ numₘ(nat_sequence_code_value tokens) := by
    have hRightCoordinate :=
      FirstOrder.Derives.conj_elim_right hCoordinates
    simpa [tokens, nat_sequence_code_value_decode] using hRightCoordinate
  have hSequence :=
    P.sequence_inversion.proof_unique sequence formulaCode rows
      hProofCondition hFormulaCode
  have hCertificates :=
    P.sequence_inversion.nat_unique certificates certificateCode tokens
      hCertificateCondition hCertificateCode
  exact FirstOrder.Derives.conj_intro hSequence hCertificates

end StructuredWitness
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
