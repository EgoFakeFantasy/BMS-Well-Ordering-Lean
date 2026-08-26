import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProofRows
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CheckedSyntax

/-!
# ProofT checked 行实例化

本模块把证明序列条件中的逐行全称式实例化到一个具体 numeral。实例保留为
对象公式的规范 capture-avoiding substitution，不展开具体 verifier 或证书分支。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation

set_option autoImplicit false

/-- 参数化 verifier 的 checked 行条件在具体索引上的规范闭 substitution 实例。 -/
def ProofT.line_instance
    (verifier : ObjectCertificateVerifier)
    (sequence certificates : SetTerm)
    (index : Nat) : SetFormula :=
  Formula.substituteFree SetSort.set
    ProofT.line_index_id (numₘ(index))
    (ProofT.line_condition verifier
      sequence certificates
      (x#ProofT.line_index_id))

/--
参数化证明序列条件与具体定义域成员共同给出该位置的公式 replay 条件和
checked 行实例。
-/
theorem
    ProofT.formula_and_line_of_sequence
    {T : SetTheory}
    {Γ : Context signature}
    (verifier : ObjectCertificateVerifier)
    (hTransport : ProofT.VerifierTransport verifier)
    (sequence certificates : SetTerm)
    (index : Nat)
    (hSequenceClosed :
      Term.freeSupport sequence = [])
    (hCondition :
      Γ ⊢ₘ[T]
        ProofT.sequence_condition
          verifier sequence certificates)
    (hIndexDomain :
      Γ ⊢ₘ[T]
        numₘ(index) ∈ₘ domₘ(sequence)) :
    Γ ⊢ₘ[T]
      verifier.formula_condition
          (sequence ·ₘ numₘ(index)) ∧ₘ
        ProofT.line_instance
          verifier sequence certificates index := by
  have hAllLines :
      Γ ⊢ₘ[T]
        ∀ₘ[SetSort.set, ProofT.line_index_id],
          (x#ProofT.line_index_id ∈ₘ
              domₘ(sequence)) ⟶ₘ
            verifier.formula_condition
                (sequence ·ₘ x#ProofT.line_index_id) ∧ₘ
              ProofT.line_condition verifier
                sequence certificates
                (x#ProofT.line_index_id) := by
    simpa [ProofT.sequence_condition,
      CertifiedProof.sequence_condition_with_ids] using
      FirstOrder.Derives.conjElimRight hCondition
  have hAtRaw :=
    FirstOrder.Derives.forall_elim
      (term := numₘ(index)) hAllLines
  rw [Formula.openAt_closeFreeAt_eq_substituteFree] at hAtRaw
  have hAt :
      Γ ⊢ₘ[T]
        Formula.substituteFree SetSort.set
            ProofT.line_index_id (numₘ(index))
            (x#ProofT.line_index_id ∈ₘ
              domₘ(sequence)) ⟶ₘ
          (Formula.substituteFree SetSort.set
                ProofT.line_index_id (numₘ(index))
                (verifier.formula_condition
                  (sequence ·ₘ x#ProofT.line_index_id))) ∧ₘ
            ProofT.line_instance
              verifier sequence certificates index := by
    simpa [ProofT.line_instance,
      Formula.substituteFree] using hAtRaw
  have hSequenceFixed :
      Term.substituteFree SetSort.set
          ProofT.line_index_id (numₘ(index))
          sequence =
        sequence :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set ProofT.line_index_id
      (numₘ(index)) sequence (by
        rw [hSequenceClosed]
        exact List.not_mem_nil)
  have hIndexDomainSubstituted :
      Γ ⊢ₘ[T]
        Formula.substituteFree SetSort.set
          ProofT.line_index_id (numₘ(index))
          (x#ProofT.line_index_id ∈ₘ
            domₘ(sequence)) := by
    simpa [Formula.substituteFree,
      Term.substituteFree, set_variable,
      hSequenceFixed] using hIndexDomain
  have hFormulaAt :
      Term.substituteFree SetSort.set
          ProofT.line_index_id (numₘ(index))
          (sequence ·ₘ x#ProofT.line_index_id) =
        sequence ·ₘ numₘ(index) := by
    simp [Term.substituteFree, set_variable,
      hSequenceFixed]
  have hFormulaConditionSubstituted :
      Formula.substituteFree SetSort.set
          ProofT.line_index_id (numₘ(index))
          (verifier.formula_condition
            (sequence ·ₘ x#ProofT.line_index_id)) =
        verifier.formula_condition
          (sequence ·ₘ numₘ(index)) := by
    rw [hTransport.formula_condition]
    exact
      fs_formula_replay_condition_substitute
        (sequence ·ₘ x#ProofT.line_index_id)
        (numₘ(index))
        (sequence ·ₘ numₘ(index))
        ProofT.line_index_id hFormulaAt
  rw [hFormulaConditionSubstituted] at hAt
  exact FirstOrder.Derives.impElim
    hAt hIndexDomainSubstituted

/-- 参数化证明序列条件在具体定义域位置给出 checked 行实例。 -/
theorem
    ProofT.line_of_sequence
    {T : SetTheory}
    {Γ : Context signature}
    (verifier : ObjectCertificateVerifier)
    (hTransport : ProofT.VerifierTransport verifier)
    (sequence certificates : SetTerm)
    (index : Nat)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCondition :
      Γ ⊢ₘ[T]
        ProofT.sequence_condition
          verifier sequence certificates)
    (hIndexDomain :
      Γ ⊢ₘ[T]
        numₘ(index) ∈ₘ domₘ(sequence)) :
    Γ ⊢ₘ[T]
      ProofT.line_instance
        verifier sequence certificates index :=
  FirstOrder.Derives.conjElimRight <|
    ProofT.formula_and_line_of_sequence
      verifier hTransport sequence certificates index
      hSequenceClosed hCondition hIndexDomain

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
