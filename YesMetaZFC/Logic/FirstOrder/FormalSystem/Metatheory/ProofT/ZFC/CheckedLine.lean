import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifierSubstitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CheckedLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.CheckedSyntax

/-!
# ZFC verifier 的 checked 行实例

具体 ZFC 层只选择 verifier 与 replay 合同；逐行实例化证明复用通用 `ProofT`
接口，不复制 substitution 推导。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 当前 ZFC verifier 的具体行实例。 -/
def ProofT.ZFC.line_instance
    (sequence certificates : SetTerm)
    (index : Nat) : SetFormula :=
  ProofT.line_instance
    fs_zfc_object_certificate_verifier
    sequence certificates index

/-- ZFC sequence condition 在定义域位置给出公式条件与行实例。 -/
theorem ProofT.ZFC.formula_and_line_of_sequence
    {T : SetTheory}
    {Γ : Context signature}
    (sequence certificates : SetTerm)
    (index : Nat)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCondition :
      Γ ⊢ₘ[T]
        ProofT.ZFC.sequence_condition
          sequence certificates)
    (hIndexDomain :
      Γ ⊢ₘ[T]
        numₘ(index) ∈ₘ domₘ(sequence)) :
    Γ ⊢ₘ[T]
      fs_zfc_object_certificate_verifier.formula_condition
          (sequence ·ₘ numₘ(index)) ∧ₘ
        ProofT.ZFC.line_instance
          sequence certificates index := by
  simpa [ProofT.ZFC.sequence_condition,
    ProofT.ZFC.line_instance] using
    ProofT.formula_and_line_of_sequence
      fs_zfc_object_certificate_verifier
      ProofT.ZFC.verifier_transport
      sequence certificates index
      hSequenceClosed hCondition hIndexDomain

/-- ZFC sequence condition 在定义域位置给出行实例。 -/
theorem ProofT.ZFC.line_of_sequence
    {T : SetTheory}
    {Γ : Context signature}
    (sequence certificates : SetTerm)
    (index : Nat)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCondition :
      Γ ⊢ₘ[T]
        ProofT.ZFC.sequence_condition
          sequence certificates)
    (hIndexDomain :
      Γ ⊢ₘ[T]
        numₘ(index) ∈ₘ domₘ(sequence)) :
    Γ ⊢ₘ[T]
      ProofT.ZFC.line_instance
        sequence certificates index :=
  FirstOrder.Derives.conjElimRight <|
    ProofT.ZFC.formula_and_line_of_sequence
      sequence certificates index
      hSequenceClosed hCondition hIndexDomain

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
