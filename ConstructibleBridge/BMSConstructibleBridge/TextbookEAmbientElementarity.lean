import BMSConstructibleBridge.TextbookEAmbientAgreementFormula
import BMSConstructibleBridge.TextbookEStageElementarity

/-!
# Ambient 真值一致性与可构造层初等性

有限真值分类器的正确性把一元一致性公式右端还原为当前层中的公式满足关系。
本文件再用 textbook E 编译定理证明，该一致性恰好是具名层到当前层的有限
`Sigma` 初等性。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Constructible.FiniteSequenceZF

/-- 在来自较低层的正元元组上，正确分类器等价于当前层的 textbook E 成员关系。 -/
theorem satisfiesIn_textbookAmbientTruthClassifier_iff_textbookEZF_l
    {top α : Ordinal.{u}} (hαtop : α < top)
    {level positiveArity code : Nat}
    (hCode : TextbookBoundedIsSigmaCode_l level (positiveArity + 1) code)
    (classifier : FOFormula 5)
    (hClassifier : TextbookAmbientTruthClassifierStageCorrectFor_l
      top level classifier)
    {tuple : ZFSet.{u}}
    (hTuple : tuple ∈ textbookTupleSpace (LStageZF α) (positiveArity + 1)) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) classifier
        ![Ordinal.omega0.toZFSet, tuple, natCode 1,
          natCode (positiveArity + 1), natCode code] ↔
      tuple ∈ textbookEZF (LStageZF top)
        (natCode (positiveArity + 1)) (natCode code) := by
  have hFunction : ZFSet.IsFunc (natCode (positiveArity + 1))
      (LStageZF α) tuple := mem_textbookTupleSpace_iff.mp hTuple
  rcases exists_textbookTupleGraph_eq_of_isFunc hFunction with
    ⟨assignment, hAssignment⟩
  let targetAssignment : Tuple (StageCarrier top) (positiveArity + 1) :=
    externalStageTuple_l hαtop.le assignment
  have hTargetGraph : textbookTupleGraph targetAssignment = tuple := by
    rw [textbookTupleGraph_externalStageTuple_l hαtop.le assignment]
    exact hAssignment
  rcases hCode.decode with ⟨formula, hFormulaCode, hFormula⟩
  have hClassifierAt := hClassifier targetAssignment true code
  simp only [ite_true] at hClassifierAt
  have hCertificate := textbookAmbientSigmaCertificate_iff_l
    formula hFormula targetAssignment
  rw [hFormulaCode] at hCertificate
  have hCompiled := textbookTupleGraph_mem_compiledRelation_iff_l
    (LStageZF top) formula targetAssignment
  calc
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) classifier
        ![Ordinal.omega0.toZFSet, tuple, natCode 1,
          natCode (positiveArity + 1), natCode code] ↔
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) classifier
        ![Ordinal.omega0.toZFSet, textbookTupleGraph targetAssignment,
          natCode 1, natCode (positiveArity + 1), natCode code] := by
            rw [hTargetGraph]
    _ ↔ TextbookAmbientSigmaCertificate_l top level code
        targetAssignment := hClassifierAt
    _ ↔ FOFormula.Satisfies (stageMembership_l top)
        formula targetAssignment := hCertificate
    _ ↔ textbookTupleGraph targetAssignment ∈
        textbookEZF (LStageZF top) (natCode (positiveArity + 1))
          (natCode (textbookFormulaCode_l formula)) := hCompiled.symm
    _ ↔ tuple ∈ textbookEZF (LStageZF top)
        (natCode (positiveArity + 1)) (natCode code) := by
          rw [hTargetGraph, hFormulaCode]

/-- 正确分类器的一致性语义推出 E 码初等性。 -/
theorem eCodeSigmaElementaryAt_of_textbookEAmbientAgreement_l
    {top α : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmegaTop : Ordinal.omega0 < top) (hαtop : α < top)
    (hOmegaα : Ordinal.omega0 < α) {level : Nat}
    (classifier : FOFormula 5)
    (hClassifier : TextbookAmbientTruthClassifierStageCorrectFor_l
      top level classifier)
    (hAgreement : TextbookEAmbientLevelAgreementFor_l top level
      (LStageZF α) classifier) :
    ECodeSigmaElementaryAt_l level α top := by
  let sourceNonempty : Nonempty (StageCarrier α) :=
    ⟨⟨natCode 0, natCode_mem_stage_l hOmegaα 0⟩⟩
  let targetNonempty : Nonempty (StageCarrier top) :=
    ⟨⟨natCode 0, natCode_mem_stage_l hOmegaTop 0⟩⟩
  refine ⟨sourceNonempty, targetNonempty, hαtop.le, ?_⟩
  intro positiveArity code hCode assignment
  have hTuple : textbookTupleGraph assignment ∈
      textbookTupleSpace (LStageZF α) (positiveArity + 1) :=
    textbookTupleGraph_mem_tupleSpace assignment
  have hCompared := hAgreement positiveArity code hCode
    (textbookTupleGraph assignment) hTuple
  have hClassifierE :=
    satisfiesIn_textbookAmbientTruthClassifier_iff_textbookEZF_l
      hαtop hCode classifier hClassifier hTuple
  rw [hClassifierE] at hCompared
  rw [textbookTupleGraph_externalStageTuple_l hαtop.le assignment]
  exact hCompared

/-- E 码初等性与正确分类器共同恢复统一 ambient 真值一致性。 -/
theorem textbookEAmbientAgreement_of_eCodeSigmaElementaryAt_l
    {top α : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmegaTop : Ordinal.omega0 < top) (hαtop : α < top)
    {level : Nat} (classifier : FOFormula 5)
    (hClassifier : TextbookAmbientTruthClassifierStageCorrectFor_l
      top level classifier)
    (hElementary : ECodeSigmaElementaryAt_l level α top) :
    TextbookEAmbientLevelAgreementFor_l top level
      (LStageZF α) classifier := by
  rcases hElementary with
    ⟨_sourceNonempty, _targetNonempty, hαtop', hElementary⟩
  intro positiveArity code hCode tuple hTuple
  have hFunction : ZFSet.IsFunc (natCode (positiveArity + 1))
      (LStageZF α) tuple := mem_textbookTupleSpace_iff.mp hTuple
  rcases exists_textbookTupleGraph_eq_of_isFunc hFunction with
    ⟨assignment, hAssignment⟩
  have hCompared := hElementary hCode assignment
  have hClassifierE :=
    satisfiesIn_textbookAmbientTruthClassifier_iff_textbookEZF_l
      hαtop hCode classifier hClassifier hTuple
  rw [hClassifierE]
  rw [← hAssignment]
  simpa only [textbookTupleGraph_externalStageTuple_l hαtop' assignment] using
    hCompared

/-- 统一 ambient 真值一致性恰好是具名层到当前层的有限 `Sigma` 初等性。 -/
theorem textbookEAmbientLevelAgreement_iff_boundedExternal_l
    {top α : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmegaTop : Ordinal.omega0 < top) (hαtop : α < top)
    (hOmegaα : Ordinal.omega0 < α) {level : Nat}
    (classifier : FOFormula 5)
    (hClassifier : TextbookAmbientTruthClassifierStageCorrectFor_l
      top level classifier) :
    TextbookEAmbientLevelAgreementFor_l top level
        (LStageZF α) classifier ↔
      BoundedExternalStageSigmaElementaryAt_l level α top :=
  ⟨fun hAgreement => externalStageSigmaElementaryAt_of_eCode_l
      (eCodeSigmaElementaryAt_of_textbookEAmbientAgreement_l
        hTop hOmegaTop hαtop hOmegaα classifier hClassifier hAgreement),
    fun hElementary => textbookEAmbientAgreement_of_eCodeSigmaElementaryAt_l
      hTop hOmegaTop hαtop classifier hClassifier
        (eCodeSigmaElementaryAt_of_external_l hElementary)⟩

/-- 递归生成的公开一元公式精确表达具名层到 ambient 层的初等性。 -/
theorem satisfiesIn_textbookEAmbientLevelAgreementFormula_iff_l
    {top α : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmegaTop : Ordinal.omega0 < top) (hαtop : α < top)
    (hα : Order.IsSuccLimit α) (hOmegaα : Ordinal.omega0 < α)
    (level : Nat) {A : ZFSet.{u}}
    (hA : A ∈ LStageZF top) (hAValue : A = LStageZF α) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookEAmbientLevelAgreementFormulaFor_l level
          (textbookAmbientTruthClassifierFormula_l level)) ![A] ↔
      BoundedExternalStageSigmaElementaryAt_l level α top := by
  rw [satisfiesIn_textbookEAmbientLevelAgreementFormulaFor_iff_l
    hTop hOmegaTop hαtop hα hOmegaα level
    (textbookAmbientTruthClassifierFormula_l level) hA hAValue]
  rw [hAValue]
  exact textbookEAmbientLevelAgreement_iff_boundedExternal_l
    hTop hOmegaTop hαtop hOmegaα
    (textbookAmbientTruthClassifierFormula_l level)
    (textbookAmbientTruthClassifierFormula_correct_l
      hTop hOmegaTop level)

end YesMetaZFC.BMS.ConstructibleBridge
