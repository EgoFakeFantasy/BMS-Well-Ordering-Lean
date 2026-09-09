import BMSConstructibleBridge.TextbookAmbientTruthCertificate
import BMSConstructibleBridge.TextbookBoundedLevyRecordZF
import BMSConstructibleBridge.TextbookBoundedLevyTraceBounds
import BMSConstructibleBridge.TextbookBoundedLevyRecordAbsolute

/-!
# Ambient truth certificate records

An ambient truth row is a bounded-Levy classification judgment together with
the code of the assignment on which that judgment is evaluated.  Keeping the
classification record as the left component lets the truth construction reuse
the existing canonical four-field decoder without inventing a second syntax
code format.
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

set_option maxRecDepth 10000

/-- One row of a fixed-level ambient truth certificate. -/
structure TextbookAmbientTruthJudgment_l where
  classification : TextbookBoundedLevyJudgment
  assignmentCode : ZFSet.{u}

namespace TextbookAmbientTruthJudgment_l

/-- The polarity carried by a truth row. -/
abbrev isSigma (entry : TextbookAmbientTruthJudgment_l.{u}) : Bool :=
  entry.classification.isSigma

/-- The finite Levy level carried by a truth row. -/
abbrev level (entry : TextbookAmbientTruthJudgment_l.{u}) : Nat :=
  entry.classification.level

/-- The arity carried by a truth row. -/
abbrev arity (entry : TextbookAmbientTruthJudgment_l.{u}) : Nat :=
  entry.classification.arity

/-- The textbook formula code carried by a truth row. -/
abbrev code (entry : TextbookAmbientTruthJudgment_l.{u}) : Nat :=
  entry.classification.code

end TextbookAmbientTruthJudgment_l

/-- Canonical set code `pair(classificationRecord, assignmentCode)`. -/
noncomputable def textbookAmbientTruthRecordZF_l
    (entry : TextbookAmbientTruthJudgment_l.{u}) : ZFSet.{u} :=
  ZFSet.pair
    (textbookBoundedLevyRecordZF_l entry.classification)
    entry.assignmentCode

/-- The outer pairing does not identify distinct ambient truth rows. -/
theorem textbookAmbientTruthRecordZF_injective_l :
    Function.Injective
      (textbookAmbientTruthRecordZF_l :
        TextbookAmbientTruthJudgment_l.{u} → ZFSet.{u}) := by
  rintro ⟨leftClassification, leftAssignment⟩
    ⟨rightClassification, rightAssignment⟩ hEqual
  obtain ⟨hClassification, hAssignment⟩ := ZFSet.pair_inj.mp hEqual
  have hClassification' :=
    textbookBoundedLevyRecordZF_injective_l hClassification
  cases hClassification'
  cases hAssignment
  rfl

/-- Every canonical ambient row is constructible when its assignment is. -/
theorem textbookAmbientTruthRecordZF_mem_L_l
    (entry : TextbookAmbientTruthJudgment_l.{u})
    (hAssignment : entry.assignmentCode ∈ L) :
    textbookAmbientTruthRecordZF_l entry ∈ L :=
  orderedPair_mem_L
    (textbookBoundedLevyRecordZF_mem_L_l entry.classification)
    hAssignment

/-- A truth row lies in a successor-limit stage whenever its assignment does. -/
theorem textbookAmbientTruthRecordZF_mem_stage_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (entry : TextbookAmbientTruthJudgment_l.{u})
    (hAssignment : entry.assignmentCode ∈ LStageZF top) :
    textbookAmbientTruthRecordZF_l entry ∈ LStageZF top := by
  exact orderedPair_mem_LStageZF_of_isSuccLimit hTop
    (LStageZF_mono (le_of_lt hOmega)
      (textbookBoundedLevyRecordZF_mem_LStageOmega_l entry.classification))
    hAssignment

/-!
The public layout is
`[omega, row, polarity, level, arity, formulaCode, assignmentCode]`.
The sole witness is the already existing four-field classification record.
-/

/-- Eight-coordinate matrix exposing the two components of an ambient row. -/
def textbookAmbientTruthRecordMatrix_l : FOFormula 8 :=
  .conj
    (Delta0Formula.kuratowskiPairEqAt
      (1 : Fin 8) (7 : Fin 8) (6 : Fin 8)).toFO
    (FOFormula.rename ![0, 7, 2, 3, 4, 5]
      textbookBoundedLevyRecordComponentsFormula_l)

/-- Seven-coordinate decoder for an ambient truth row. -/
def textbookAmbientTruthRecordComponentsFormula_l : FOFormula 7 :=
  .ex textbookAmbientTruthRecordMatrix_l

/-- The decoder has exactly the advertised canonical raw-set semantics. -/
theorem satisfies_textbookAmbientTruthRecordComponentsFormula_iff_l
    (value polarity level arity code assignment : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        textbookAmbientTruthRecordComponentsFormula_l
        ![Ordinal.omega0.toZFSet, value, polarity, level, arity, code,
          assignment] ↔
      ∃ entry : TextbookAmbientTruthJudgment_l.{u},
        polarity = natCode
          (textbookBoundedLevyPolarityCode_l entry.isSigma) ∧
        level = natCode entry.level ∧
        arity = natCode entry.arity ∧
        code = natCode entry.code ∧
        assignment = entry.assignmentCode ∧
        value = textbookAmbientTruthRecordZF_l entry := by
  simp only [textbookAmbientTruthRecordComponentsFormula_l,
    FOFormula.Satisfies]
  constructor
  · rintro ⟨classificationCode, hMatrix⟩
    simp only [textbookAmbientTruthRecordMatrix_l, FOFormula.Satisfies,
      Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_kuratowskiPairEqAt,
      FOFormula.satisfies_rename] at hMatrix
    rcases hMatrix with ⟨hPair, hClassification⟩
    simp only [externalSnoc_eq_finSnoc_l] at hPair hClassification
    change value = ZFSet.pair classificationCode assignment at hPair
    have hClassification' :
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookBoundedLevyRecordComponentsFormula_l
          ![Ordinal.omega0.toZFSet, classificationCode, polarity,
            level, arity, code] := by
      convert hClassification using 1 <;>
        ext position <;> fin_cases position <;> rfl
    rw [satisfies_textbookBoundedLevyRecordComponentsFormula_iff_l]
      at hClassification'
    obtain ⟨classification, hPolarity, hLevel, hArity, hCode,
      hClassificationCode⟩ := hClassification'
    refine ⟨⟨classification, assignment⟩, hPolarity, hLevel,
      hArity, hCode, rfl, ?_⟩
    simpa only [textbookAmbientTruthRecordZF_l,
      hClassificationCode] using hPair
  · rintro ⟨entry, hPolarity, hLevel, hArity, hCode,
      hAssignment, hValue⟩
    rcases entry with ⟨classification, assignmentCode⟩
    simp only [TextbookAmbientTruthJudgment_l.isSigma,
      TextbookAmbientTruthJudgment_l.level,
      TextbookAmbientTruthJudgment_l.arity,
      TextbookAmbientTruthJudgment_l.code]
      at hPolarity hLevel hArity hCode
    subst polarity
    subst level
    subst arity
    subst code
    subst assignment
    subst value
    refine ⟨textbookBoundedLevyRecordZF_l classification, ?_⟩
    simp only [textbookAmbientTruthRecordMatrix_l, FOFormula.Satisfies,
      Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_kuratowskiPairEqAt,
      FOFormula.satisfies_rename]
    simp only [externalSnoc_eq_finSnoc_l]
    constructor
    · change textbookAmbientTruthRecordZF_l
        ⟨classification, assignmentCode⟩ =
          ZFSet.pair (textbookBoundedLevyRecordZF_l classification)
            assignmentCode
      rfl
    · have hCanonical :=
        (satisfies_textbookBoundedLevyRecordComponentsFormula_iff_l
          (textbookBoundedLevyRecordZF_l classification)
          (natCode (textbookBoundedLevyPolarityCode_l
            classification.isSigma))
          (natCode classification.level) (natCode classification.arity)
          (natCode classification.code)).mpr
          ⟨classification, rfl, rfl, rfl, rfl, rfl⟩
      convert hCanonical using 1 <;>
        ext position <;> fin_cases position <;> rfl

/-- The ambient row decoder is absolute for transitive carriers. -/
theorem textbookAmbientTruthRecordComponentsFormula_absolute_l
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    (values : Tuple ZFSet.{u} 7)
    (hValues : ∀ position, values position ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        textbookAmbientTruthRecordComponentsFormula_l values ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookAmbientTruthRecordComponentsFormula_l values := by
  rw [textbookAmbientTruthRecordComponentsFormula_l]
  constructor
  · rintro ⟨classificationCode, hClassificationCode, hMatrix⟩
    change classificationCode ∈ M at hClassificationCode
    refine ⟨classificationCode, ?_⟩
    simp only [textbookAmbientTruthRecordMatrix_l,
      Model.SatisfiesIn, FOFormula.Satisfies,
      Model.satisfiesIn_rename, FOFormula.satisfies_rename] at hMatrix ⊢
    have hExtended : ∀ position,
        (snoc values classificationCode) position ∈ M := by
      intro position
      refine Fin.lastCases ?_ (fun original => ?_) position
      · simpa only [snoc_last] using hClassificationCode
      · simpa only [snoc_castSucc] using hValues original
    refine ⟨?_, ?_⟩
    · exact (Model.satisfiesIn_delta0_iff hM
        (Delta0Formula.kuratowskiPairEqAt
          (1 : Fin 8) (7 : Fin 8) (6 : Fin 8)) _ hExtended).mp hMatrix.1
    · exact (textbookBoundedLevyRecordComponentsFormula_absolute_l
        hM _ (fun position => hExtended
          (![(0 : Fin 8), 7, 2, 3, 4, 5] position))).mp hMatrix.2
  · rintro ⟨classificationCode, hMatrix⟩
    simp only [textbookAmbientTruthRecordMatrix_l,
      FOFormula.Satisfies, FOFormula.satisfies_rename,
      Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_kuratowskiPairEqAt] at hMatrix
    have hSnoc : snoc values classificationCode =
        ![values 0, values 1, values 2, values 3,
          values 4, values 5, values 6, classificationCode] := by
      funext position
      fin_cases position <;> rfl
    rw [hSnoc] at hMatrix
    have hClassificationCode : classificationCode ∈ M := by
      have hPair : values 1 = ZFSet.pair classificationCode (values 6) := by
        exact hMatrix.1
      have hPairM : ZFSet.pair classificationCode (values 6) ∈ M :=
        hPair ▸ hValues 1
      obtain ⟨hLeft, _⟩ := boundedLevy_pair_components_mem_of_transitive_l
        hM hPairM
      exact hLeft
    refine ⟨classificationCode, hClassificationCode, ?_⟩
    simp only [textbookAmbientTruthRecordMatrix_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename]
    have hExtended : ∀ position,
        (snoc values classificationCode) position ∈ M := by
      intro position
      refine Fin.lastCases ?_ (fun original => ?_) position
      · simpa only [snoc_last] using hClassificationCode
      · simpa only [snoc_castSucc] using hValues original
    have hPairOriginal :
        (snoc values classificationCode) 1 =
          ZFSet.pair (snoc values classificationCode 7)
            (snoc values classificationCode 6) := by
      rw [hSnoc]
      exact hMatrix.1
    have hClassificationOriginal :
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookBoundedLevyRecordComponentsFormula_l
          (fun position => (snoc values classificationCode)
            (![(0 : Fin 8), 7, 2, 3, 4, 5] position)) := by
      rw [hSnoc]
      exact hMatrix.2
    constructor
    · apply (Model.satisfiesIn_delta0_iff hM
        (Delta0Formula.kuratowskiPairEqAt
          (1 : Fin 8) (7 : Fin 8) (6 : Fin 8)) _ hExtended).mpr
      simpa only [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt] using hPairOriginal
    · apply (textbookBoundedLevyRecordComponentsFormula_absolute_l
        hM _ (fun position => hExtended
          (![(0 : Fin 8), 7, 2, 3, 4, 5] position))).mpr
      exact hClassificationOriginal

end YesMetaZFC.BMS.ConstructibleBridge
