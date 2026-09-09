import BMSConstructibleBridge.TextbookAmbientTruthClassifierFormula

/-!
# 环境真值分类器的降层调用语义

先消去对象公式中为极性、层级引入的数码见证，再把降层叶节点接到严格较低
层级的分类器。这些结论只假定较低层的语义规格，不假定待证当前层的正确性。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 一个五元对象公式在给定层级上精确判定正、负真值证书。 -/
def TextbookAmbientTruthClassifierStageCorrectFor_l
    (top : Ordinal.{u}) (level : Nat) (classifier : FOFormula 5) : Prop :=
  ∀ {arity : Nat} (assignment : Tuple (StageCarrier top) arity)
      (isSigma : Bool) (code : Nat),
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) classifier
        ![Ordinal.omega0.toZFSet, textbookTupleGraph assignment,
          natCode (textbookBoundedLevyPolarityCode_l isSigma),
          natCode arity, natCode code] ↔
      if isSigma then
        TextbookAmbientSigmaCertificate_l top level code assignment
      else TextbookAmbientPiFalseCertificate_l top level code assignment

/-- 固定极性的调用等价于向分类器传入该极性的规范数码。 -/
theorem satisfiesIn_textbookAmbientTruthFixedPolarityClassifierFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (φ : FOFormula 5) (isSigma : Bool) (values : Tuple ZFSet.{u} 8)
    (hValues : ∀ i, values i ∈ LStageZF θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (textbookAmbientTruthFixedPolarityClassifierFormula_l φ isSigma) values ↔
      Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u}) φ
        ![values 0, values 3,
          natCode (textbookBoundedLevyPolarityCode_l isSigma), values 6, values 7] := by
  let polarity := textbookBoundedLevyPolarityCode_l isSigma
  have hExtended (p : ZFSet.{u}) (hp : p ∈ LStageZF θ) :
      ∀ i, snoc values p i ∈ LStageZF θ := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [snoc_last] using hp
    · simpa only [snoc_castSucc] using hValues j
  have hRename (p : ZFSet.{u}) :
      (fun i => snoc values p (![(0 : Fin 9), 3, 8, 6, 7] i)) =
        ![values 0, values 3, p, values 6, values 7] := by
    ext i
    fin_cases i <;> rfl
  change (∃ p : ZFSet.{u}, p ∈ LStageZF θ ∧
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      (Delta0Formula.natLiteralDeltaAt polarity (8 : Fin 9)).toFO (snoc values p) ∧
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      (FOFormula.rename ![0, 3, 8, 6, 7] φ) (snoc values p)) ↔ _
  constructor
  · rintro ⟨p, hp, hLiteral, hφ⟩
    rw [satisfiesIn_natLiteralDeltaAt_stage_iff_l polarity 8 _
      (hExtended p hp)] at hLiteral
    have hCode : p = natCode polarity := hLiteral
    rw [Model.satisfiesIn_rename, hRename, hCode] at hφ
    exact hφ
  · intro hφ
    have hp := natCode_mem_LStageZF_of_isSuccLimit hθ polarity
    refine ⟨natCode polarity, hp, ?_, ?_⟩
    · rw [satisfiesIn_natLiteralDeltaAt_stage_iff_l polarity 8 _
        (hExtended _ hp)]
      rfl
    · rw [Model.satisfiesIn_rename, hRename]
      exact hφ

/-- 两个规范数码见证将降层分类调用化为既有的有限 Lévy 分类器。 -/
theorem satisfiesIn_textbookAmbientTruthLowerClassificationFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (lowerLevel arity code : Nat)
    (isSigma : Bool) (values : Tuple ZFSet.{u} 8)
    (hValues : ∀ i, values i ∈ LStageZF θ)
    (hOmega : values 0 = Ordinal.omega0.toZFSet)
    (hArity : values 6 = natCode arity) (hCode : values 7 = natCode code) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (textbookAmbientTruthLowerClassificationFormula_l lowerLevel isSigma) values ↔
      if isSigma then TextbookBoundedIsSigmaCode_l lowerLevel arity code
      else TextbookBoundedIsPiCode_l lowerLevel arity code := by
  let polarity := textbookBoundedLevyPolarityCode_l isSigma
  have hExtended (w : Tuple ZFSet.{u} 2)
      (hw : ∀ i, w i ∈ LStageZF θ) :
      ∀ i, Fin.append values w i ∈ LStageZF θ := by
    intro i
    exact Fin.addCases (fun j => by simpa using hValues j)
      (fun j => by simpa using hw j) i
  have hRename (w : Tuple ZFSet.{u} 2)
      (hp : w 0 = natCode polarity) (hl : w 1 = natCode lowerLevel) :
      (fun i => Fin.append values w (![(0 : Fin 10), 8, 9, 6, 7] i)) =
        ![Ordinal.omega0.toZFSet, natCode polarity, natCode lowerLevel,
          natCode arity, natCode code] := by
    funext i
    fin_cases i
    · exact hOmega
    · exact hp
    · exact hl
    · exact hArity
    · exact hCode
  rw [textbookAmbientTruthLowerClassificationFormula_l,
    satisfiesIn_externalExistentialClosure_l]
  constructor
  · rintro ⟨w, hw, hPolarity, hLevel, hClass⟩
    rw [satisfiesIn_natLiteralDeltaAt_stage_iff_l polarity 8 _
      (hExtended w hw)] at hPolarity
    rw [satisfiesIn_natLiteralDeltaAt_stage_iff_l lowerLevel 9 _
      (hExtended w hw)] at hLevel
    have hp : w 0 = natCode polarity := hPolarity
    have hl : w 1 = natCode lowerLevel := hLevel
    rw [Model.satisfiesIn_rename, hRename w hp hl] at hClass
    exact (satisfiesIn_textbookBoundedLevyClassifierFormula_iff_l hθ hω
      ⟨isSigma, lowerLevel, arity, code⟩).mp hClass
  · intro hClass
    let w : Tuple ZFSet.{u} 2 := ![natCode polarity, natCode lowerLevel]
    have hw : ∀ i, w i ∈ LStageZF θ := by
      intro i
      fin_cases i <;> exact natCode_mem_stage_l hω _
    refine ⟨w, hw, ?_, ?_, ?_⟩
    · rw [satisfiesIn_natLiteralDeltaAt_stage_iff_l polarity 8 _ (hExtended w hw)]
      rfl
    · rw [satisfiesIn_natLiteralDeltaAt_stage_iff_l lowerLevel 9 _ (hExtended w hw)]
      rfl
    · rw [Model.satisfiesIn_rename, hRename w rfl rfl]
      exact (satisfiesIn_textbookBoundedLevyClassifierFormula_iff_l hθ hω
        ⟨isSigma, lowerLevel, arity, code⟩).mpr hClass

/-- 四个降层分支恰好对应较低层证书的正负调用。 -/
theorem satisfiesIn_textbookAmbientTruthLowerRuleFormula_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top) (lowerLevel : Nat)
    (lowerClassifier : FOFormula 5)
    (hLower : TextbookAmbientTruthClassifierStageCorrectFor_l
      top lowerLevel lowerClassifier)
    {arity : Nat} (assignment : Tuple (StageCarrier top) arity)
    (isSigma : Bool) (code : Nat) (graph position : ZFSet.{u})
    (hGraph : graph ∈ LStageZF top) (hPosition : position ∈ LStageZF top) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookAmbientTruthLowerRuleFormula_l lowerLevel lowerClassifier)
        ![Ordinal.omega0.toZFSet, graph, position,
          textbookTupleGraph assignment,
          natCode (textbookBoundedLevyPolarityCode_l isSigma),
          natCode (lowerLevel + 1), natCode arity, natCode code] ↔
      (isSigma = true ∧
        TextbookAmbientSigmaCertificate_l top lowerLevel code assignment) ∨
      (isSigma = true ∧ TextbookBoundedIsPiCode_l lowerLevel arity code ∧
        ¬ TextbookAmbientPiFalseCertificate_l top lowerLevel code assignment) ∨
      (isSigma = false ∧
        TextbookAmbientPiFalseCertificate_l top lowerLevel code assignment) ∨
      (isSigma = false ∧ TextbookBoundedIsSigmaCode_l lowerLevel arity code ∧
        ¬ TextbookAmbientSigmaCertificate_l top lowerLevel code assignment) := by
  let values : Tuple ZFSet.{u} 8 :=
    ![Ordinal.omega0.toZFSet, graph, position, textbookTupleGraph assignment,
      natCode (textbookBoundedLevyPolarityCode_l isSigma),
      natCode (lowerLevel + 1), natCode arity, natCode code]
  have hValues : ∀ i, values i ∈ LStageZF top := by
    intro i
    fin_cases i
    · exact omega_toZFSet_mem_stage_l hOmega
    · exact hGraph
    · exact hPosition
    · exact textbookTupleGraph_mem_stage_l hTop assignment
    · exact natCode_mem_stage_l hOmega _
    · exact natCode_mem_stage_l hOmega _
    · exact natCode_mem_stage_l hOmega _
    · exact natCode_mem_stage_l hOmega _
  have hPolarity (polarity : Nat) :
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
          (Delta0Formula.natLiteralDeltaAt polarity (4 : Fin 8)).toFO values ↔
        textbookBoundedLevyPolarityCode_l isSigma = polarity := by
    rw [satisfiesIn_natLiteralDeltaAt_stage_iff_l polarity 4 values hValues]
    simp [values]
  have hFixed (polarity : Bool) :
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
          (textbookAmbientTruthFixedPolarityClassifierFormula_l
            lowerClassifier polarity) values ↔
        if polarity then
          TextbookAmbientSigmaCertificate_l top lowerLevel code assignment
        else TextbookAmbientPiFalseCertificate_l top lowerLevel code assignment := by
    rw [satisfiesIn_textbookAmbientTruthFixedPolarityClassifierFormula_iff_l
      hTop lowerClassifier polarity values hValues]
    have hRename :
        ![values 0, values 3,
          natCode (textbookBoundedLevyPolarityCode_l polarity), values 6, values 7] =
        ![Ordinal.omega0.toZFSet, textbookTupleGraph assignment,
          natCode (textbookBoundedLevyPolarityCode_l polarity),
          natCode arity, natCode code] := by
      ext i
      fin_cases i <;> rfl
    rw [hRename]
    exact hLower assignment polarity code
  have hClassification (polarity : Bool) :
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
          (textbookAmbientTruthLowerClassificationFormula_l
            lowerLevel polarity) values ↔
        if polarity then TextbookBoundedIsSigmaCode_l lowerLevel arity code
        else TextbookBoundedIsPiCode_l lowerLevel arity code := by
    exact satisfiesIn_textbookAmbientTruthLowerClassificationFormula_iff_l
      hTop hOmega lowerLevel arity code polarity values hValues rfl rfl rfl
  change Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthLowerRuleFormula_l lowerLevel lowerClassifier) values ↔ _
  simp only [textbookAmbientTruthLowerRuleFormula_l,
    Model.satisfiesIn_disj_iff, Model.SatisfiesIn]
  rw [hPolarity 1, hPolarity 0, hFixed true, hFixed false,
    hClassification false, hClassification true]
  cases h : isSigma <;>
    simp [h, textbookBoundedLevyPolarityCode_l]

end YesMetaZFC.BMS.ConstructibleBridge
