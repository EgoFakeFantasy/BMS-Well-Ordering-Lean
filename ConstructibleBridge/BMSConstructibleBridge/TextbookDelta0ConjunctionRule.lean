import BMSConstructibleBridge.TextbookDelta0NegationRule

/-!
# `Delta0` 合取规则的成员语言公式

合取读取两条严格先前记录，要求它们元数相同，并检查当前码等于
`E(leftCode, rightCode, 3)`。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 合取规则矩阵。前五坐标为当前环境，随后依次为左右子记录的三个字段
和标签三。 -/
def textbookDelta0ConjunctionRuleBody_l : FOFormula 12 :=
  .conj
    (FOFormula.rename ![0, 1, 2, 5, 6, 7]
      textbookDelta0EarlierRecordFormula_l) <|
  .conj
    (FOFormula.rename ![0, 1, 2, 8, 9, 10]
      textbookDelta0EarlierRecordFormula_l) <|
  .conj (.eq 6 9) <|
  .conj (.eq 3 6) <|
  .conj (Delta0Formula.natLiteralDeltaAt 3 (11 : Fin 12)).toFO
    (TextbookNatFormula.textbookECodeFormulaAt 0 7 10 11 4)

/-- 关闭七个内部见证。 -/
def textbookDelta0ConjunctionRuleFormula_l : FOFormula 5 :=
  externalExistentialClosure_l 7 textbookDelta0ConjunctionRuleBody_l

/-- 七个隐藏坐标追加后的显式布局。 -/
theorem textbookDelta0ConjunctionRuleAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 5) (witnesses : Tuple Carrier 7) :
    Fin.append base witnesses =
      ![base 0, base 1, base 2, base 3, base 4,
        witnesses 0, witnesses 1, witnesses 2,
        witnesses 3, witnesses 4, witnesses 5, witnesses 6] := by
  funext position
  fin_cases position <;> rfl

/-- 合取公式精确等价于元层的一步合取规则。 -/
theorem satisfies_textbookDelta0ConjunctionRuleFormula_iff_l
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (entry : TextbookDelta0Judgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0ConjunctionRuleFormula_l
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
          textbookDelta0TraceGraphZF_l trace, natCode index.1,
          natCode entry.arity, natCode entry.code] ↔
      ∃ left,
        (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = left) ∧
      ∃ right,
        (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = right) ∧
        left.arity = right.arity ∧ entry = left.conjoin right := by
  rw [textbookDelta0ConjunctionRuleFormula_l,
    satisfies_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 5 :=
    ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
      natCode index.1, natCode entry.arity, natCode entry.code]
  change (∃ witnesses : Tuple ZFSet.{u} 7,
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookDelta0ConjunctionRuleBody_l
      (Fin.append base witnesses)) ↔ _
  simp only [textbookDelta0ConjunctionRuleAssignment_l]
  constructor
  · rintro ⟨w, hBody⟩
    simp only [textbookDelta0ConjunctionRuleBody_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt] at hBody
    obtain ⟨hLeftRaw, hRightRaw, hChildrenArity,
      hEntryArity, hTag, hECode⟩ := hBody
    have hLeft : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0EarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, w 0, w 1, w 2] := by
      have hAssignment :
          (fun i : Fin 6 =>
            ![base 0, base 1, base 2, base 3, base 4,
              w 0, w 1, w 2, w 3, w 4, w 5, w 6]
              (![0, 1, 2, 5, 6, 7] i)) =
            ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
              natCode index.1, w 0, w 1, w 2] := by
        funext i
        fin_cases i <;> rfl
      simpa only [hAssignment] using hLeftRaw
    have hRight : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0EarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, w 3, w 4, w 5] := by
      have hAssignment :
          (fun i : Fin 6 =>
            ![base 0, base 1, base 2, base 3, base 4,
              w 0, w 1, w 2, w 3, w 4, w 5, w 6]
              (![0, 1, 2, 8, 9, 10] i)) =
            ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
              natCode index.1, w 3, w 4, w 5] := by
        funext i
        fin_cases i <;> rfl
      simpa only [hAssignment] using hRightRaw
    obtain ⟨left, hLeftPrior, _hLeftRecord, hLeftArity, hLeftCode⟩ :=
      (satisfies_textbookDelta0EarlierRecordFormula_iff_l
        trace index (w 0) (w 1) (w 2)).mp hLeft
    obtain ⟨right, hRightPrior, _hRightRecord, hRightArity, hRightCode⟩ :=
      (satisfies_textbookDelta0EarlierRecordFormula_iff_l
        trace index (w 3) (w 4) (w 5)).mp hRight
    have hArity : left.arity = right.arity := by
      apply @natCode_injective.{u}
      simpa [hLeftArity, hRightArity] using hChildrenArity
    have hEntryArity' : entry.arity = left.arity := by
      apply @natCode_injective.{u}
      simpa [base, hLeftArity] using hEntryArity
    change w 6 = natCode 3 at hTag
    rw [hLeftCode, hRightCode, hTag] at hECode
    have hCode : entry.code = textbookECode left.code right.code 3 := by
      apply @natCode_injective.{u}
      apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
        left.code right.code 3 (natCode entry.code)).mp
      simpa [base] using hECode
    refine ⟨left, hLeftPrior, right, hRightPrior, hArity, ?_⟩
    cases entry
    cases left
    cases right
    simp_all [TextbookDelta0Judgment.conjoin]
  · rintro ⟨left, hLeftPrior, right, hRightPrior, hArity, rfl⟩
    let witnesses : Tuple ZFSet.{u} 7 :=
      ![textbookDelta0RecordZF_l left, natCode left.arity,
        natCode left.code, textbookDelta0RecordZF_l right,
        natCode right.arity, natCode right.code, natCode 3]
    refine ⟨witnesses, ?_⟩
    simp only [textbookDelta0ConjunctionRuleBody_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt]
    have hLeft :=
      (satisfies_textbookDelta0EarlierRecordFormula_iff_l
        trace index (textbookDelta0RecordZF_l left)
        (natCode left.arity) (natCode left.code)).mpr
        ⟨left, hLeftPrior, rfl, rfl, rfl⟩
    have hRight :=
      (satisfies_textbookDelta0EarlierRecordFormula_iff_l
        trace index (textbookDelta0RecordZF_l right)
        (natCode right.arity) (natCode right.code)).mpr
        ⟨right, hRightPrior, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hLeft using 1 <;> ext i <;> fin_cases i <;> rfl
    · convert hRight using 1 <;> ext i <;> fin_cases i <;> rfl
    · simp [witnesses, hArity]
    · simp [TextbookDelta0Judgment.conjoin, base, witnesses]
    · simp [witnesses]
    · simpa [TextbookDelta0Judgment.conjoin, base, witnesses] using
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          left.code right.code 3
          (natCode (textbookECode left.code right.code 3))).mpr rfl

end YesMetaZFC.BMS.ConstructibleBridge
