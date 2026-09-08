import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.StructuredCertificateCondition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuantifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicProofRows

/-!
# ProofT 内在 checked 行实例

本模块直接消费内在 `CheckedVerifier.sequence_condition`。行下标由类型化自由
上下文的顶部槽位承载，具体 numeral 实例化只执行标准的顶部替换，不再引入
`FreeVarId`、`Admissible` 或额外的新鲜性合同。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace IntrinsicCheckedLine

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open StructuredCertificateCondition

set_option autoImplicit false

/-- 内在逐行条件在一个具体自然数下的直接实例。 -/
def line_instance
    (verifier : CheckedVerifier)
    {free : SetContext}
    (sequence certificates : SetOpenTerm free)
    (index : Nat) : SetOpenFormula free :=
  verifier.line_condition sequence certificates (numₘ(index))

/-- 序列条件在定义域成员处给出内在 checked 行实例。 -/
theorem line_of_sequence
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (sequence certificates : SetOpenTerm free)
    (index : Nat)
    (hCondition :
      Γ ⊢ₘ[T]
        verifier.sequence_condition sequence certificates)
    (hIndexDomain :
      Γ ⊢ₘ[T]
        numₘ(index) ∈ₘ domₘ(sequence)) :
    Γ ⊢ₘ[T]
      line_instance verifier sequence certificates index := by
  let sequenceOne : SetTerm [SetSort.set] free :=
    sequence.weakenBound SetSort.set
  let certificatesOne : SetTerm [SetSort.set] free :=
    certificates.weakenBound SetSort.set
  let indexVariable : SetTerm [SetSort.set] free := .bvar .here
  let lineBody : SetFormula [SetSort.set] free :=
    verifier.formula_condition
        (sequenceOne ·ₘ indexVariable) ∧ₘ
      verifier.line_condition
        sequenceOne certificatesOne indexVariable
  let allLines : SetFormula [] free :=
    Formula.LevyBound.boundedForall set_levy_bound
      (domₘ(sequence)) lineBody
  have hAllLines :
      Γ ⊢ₘ[T] allLines := by
    simpa [allLines, lineBody, sequenceOne, certificatesOne, indexVariable,
      CheckedVerifier.sequence_condition,
      StructuredCertificateCondition.sequence_condition,
      Formula.LevyBound.boundedForall] using!
      FirstOrder.Derives.conj_elim_right hCondition
  have hResult :=
    bounded_forall_elim
      (domₘ(sequence))
      lineBody
      (numₘ(index))
      hAllLines
      hIndexDomain
  have hLine := FirstOrder.Derives.conj_elim_right hResult
  simpa [line_instance, lineBody, allLines, sequenceOne, certificatesOne,
    indexVariable, Formula.LevyBound.boundedForall] using! hLine

/-- 内在证明序列条件在具体定义域位置给出公式条件和 checked 行实例。 -/
theorem formula_and_line_of_sequence
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (sequence certificates : SetOpenTerm free)
    (index : Nat)
    (hCondition :
      Γ ⊢ₘ[T]
        verifier.sequence_condition sequence certificates)
    (hIndexDomain :
      Γ ⊢ₘ[T]
        numₘ(index) ∈ₘ domₘ(sequence)) :
    Γ ⊢ₘ[T]
      verifier.formula_condition
        (sequence ·ₘ numₘ(index)) ∧ₘ
      line_instance verifier sequence certificates index := by
  let sequenceOne : SetTerm [SetSort.set] free :=
    sequence.weakenBound SetSort.set
  let certificatesOne : SetTerm [SetSort.set] free :=
    certificates.weakenBound SetSort.set
  let indexVariable : SetTerm [SetSort.set] free := .bvar .here
  let lineBody : SetFormula [SetSort.set] free :=
    verifier.formula_condition
        (sequenceOne ·ₘ indexVariable) ∧ₘ
      verifier.line_condition
        sequenceOne certificatesOne indexVariable
  let allLines : SetFormula [] free :=
    Formula.LevyBound.boundedForall set_levy_bound
      (domₘ(sequence)) lineBody
  have hAllLines :
      Γ ⊢ₘ[T] allLines := by
    simpa [allLines, lineBody, sequenceOne, certificatesOne, indexVariable,
      CheckedVerifier.sequence_condition,
      StructuredCertificateCondition.sequence_condition,
      Formula.LevyBound.boundedForall] using!
      FirstOrder.Derives.conj_elim_right hCondition
  have hResult :=
    bounded_forall_elim
      (domₘ(sequence))
      lineBody
      (numₘ(index))
      hAllLines
      hIndexDomain
  have hFormulaRaw := FirstOrder.Derives.conj_elim_left hResult
  have hLineRaw := FirstOrder.Derives.conj_elim_right hResult
  have hFormula : Γ ⊢ₘ[T]
      verifier.formula_condition
        (sequence ·ₘ numₘ(index)) := by
    change Γ ⊢ₘ[T]
      Formula.substituteMapped
        (VariableSubstitution.instantiateTop (numₘ(index)))
        VariableSubstitution.freeId
        (verifier.formula_condition
          (sequenceOne ·ₘ indexVariable)) at hFormulaRaw
    have hFormulaTransport :
        Formula.substituteMapped
            (VariableSubstitution.instantiateTop (numₘ(index)))
            VariableSubstitution.freeId
            (verifier.formula_condition
              (sequenceOne ·ₘ indexVariable)) =
          verifier.formula_condition
            (sequence ·ₘ numₘ(index)) := by
      exact FormulaTemplate.apply_one_substituteMapped_instantiateTop
        verifier.formula_condition sequence (numₘ(index))
    rw [hFormulaTransport] at hFormulaRaw
    exact hFormulaRaw
  have hLine : Γ ⊢ₘ[T]
      line_instance verifier sequence certificates index := by
    simpa [line_instance, lineBody, sequenceOne, certificatesOne,
      indexVariable, Formula.LevyBound.boundedForall] using! hLineRaw
  exact FirstOrder.Derives.conj_intro hFormula hLine

/-- 规范证明行图在有效外部行下标处直接给出 checked 行实例。 -/
theorem line_of_proof_sequence_graph
    {T : SetTheory}
    (S : FiniteSequenceGraphSupport T)
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (certificates : SetOpenTerm free)
    (rows : List (List Nat))
    (index : Nat)
    (hCondition :
      Γ ⊢ₘ[T]
        verifier.sequence_condition
          (proof_sequence_graph_term rows) certificates)
    (hIndex : index < rows.length) :
    Γ ⊢ₘ[T]
      line_instance verifier
        (proof_sequence_graph_term rows) certificates index := by
  exact line_of_sequence
    verifier
    (proof_sequence_graph_term rows)
    certificates
    index
    hCondition
    (row_index_mem_of_domain
      S.toArithmeticSupport
      (proof_sequence_graph_term rows)
      rows.length index
      (proof_sequence_graph_domain_eq
        (Γ := Γ) S rows)
      hIndex)

end IntrinsicCheckedLine
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
