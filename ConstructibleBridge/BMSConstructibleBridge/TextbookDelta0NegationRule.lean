import BMSConstructibleBridge.TextbookDelta0EarlierRecord

/-!
# `Delta0` 否定规则的成员语言公式

否定读取一条严格先前记录，保持元数，并检查当前码等于
`E(childCode, 0, 2)`。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 否定规则矩阵。前五坐标为当前环境，随后为
`childRecord, childArity, childCode, zero, tag`。 -/
def textbookDelta0NegationRuleBody_l : FOFormula 10 :=
  .conj
    (FOFormula.rename ![0, 1, 2, 5, 6, 7]
      textbookDelta0EarlierRecordFormula_l) <|
  .conj (.eq 3 6) <|
  .conj (Delta0Formula.natLiteralDeltaAt 0 (8 : Fin 10)).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt 2 (9 : Fin 10)).toFO
    (TextbookNatFormula.textbookECodeFormulaAt 0 7 8 9 4)

/-- 关闭五个内部见证。 -/
def textbookDelta0NegationRuleFormula_l : FOFormula 5 :=
  externalExistentialClosure_l 5 textbookDelta0NegationRuleBody_l

/-- 五个隐藏坐标追加后的显式布局。 -/
theorem textbookDelta0NegationRuleAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 5) (witnesses : Tuple Carrier 5) :
    Fin.append base witnesses =
      ![base 0, base 1, base 2, base 3, base 4,
        witnesses 0, witnesses 1, witnesses 2,
        witnesses 3, witnesses 4] := by
  funext position
  fin_cases position <;> rfl

/-- 否定公式精确等价于元层的一步否定规则。 -/
theorem satisfies_textbookDelta0NegationRuleFormula_iff_l
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (entry : TextbookDelta0Judgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0NegationRuleFormula_l
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
          textbookDelta0TraceGraphZF_l trace, natCode index.1,
          natCode entry.arity, natCode entry.code] ↔
      ∃ child,
        (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = child) ∧
        entry = child.negate := by
  rw [textbookDelta0NegationRuleFormula_l,
    satisfies_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 5 :=
    ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
      natCode index.1, natCode entry.arity, natCode entry.code]
  change (∃ witnesses : Tuple ZFSet.{u} 5,
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookDelta0NegationRuleBody_l
      (Fin.append base witnesses)) ↔ _
  simp only [textbookDelta0NegationRuleAssignment_l]
  constructor
  · rintro ⟨w, hBody⟩
    simp only [textbookDelta0NegationRuleBody_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt] at hBody
    have hEarlier : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0EarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, w 0, w 1, w 2] := by
      have hAssignment :
          (fun i : Fin 6 =>
            ![base 0, base 1, base 2, base 3, base 4,
              w 0, w 1, w 2, w 3, w 4]
              (![0, 1, 2, 5, 6, 7] i)) =
            ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
              natCode index.1, w 0, w 1, w 2] := by
        funext i
        fin_cases i <;> rfl
      simpa only [hAssignment] using hBody.1
    obtain ⟨child, hPrior, _hRecord, hArity, hCode⟩ :=
      (satisfies_textbookDelta0EarlierRecordFormula_iff_l
        trace index (w 0) (w 1) (w 2)).mp hEarlier
    have hArityEq := hBody.2.1
    have hZero := hBody.2.2.1
    have hTag := hBody.2.2.2.1
    have hECode := hBody.2.2.2.2
    change w 3 = natCode 0 at hZero
    change w 4 = natCode 2 at hTag
    rw [hCode, hZero, hTag] at hECode
    have hCode' : (natCode entry.code : ZFSet.{u}) =
        natCode (textbookECode child.code 0 2) := by
      apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
        child.code 0 2 (natCode entry.code)).mp
      simpa [base] using hECode
    have hArity' : entry.arity = child.arity := by
      apply @natCode_injective.{u}
      simpa [base, hArity] using hArityEq
    have hCodeEq : entry.code = textbookECode child.code 0 2 :=
      (@natCode_injective.{u}) hCode'
    refine ⟨child, hPrior, ?_⟩
    cases entry
    cases child
    simp_all [TextbookDelta0Judgment.negate]
  · rintro ⟨child, hPrior, rfl⟩
    let witnesses : Tuple ZFSet.{u} 5 :=
      ![textbookDelta0RecordZF_l child, natCode child.arity,
        natCode child.code, natCode 0, natCode 2]
    refine ⟨witnesses, ?_⟩
    simp only [textbookDelta0NegationRuleBody_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt]
    have hEarlier :=
      (satisfies_textbookDelta0EarlierRecordFormula_iff_l
        trace index (textbookDelta0RecordZF_l child)
        (natCode child.arity) (natCode child.code)).mpr
        ⟨child, hPrior, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hAssignment :
          (fun i : Fin 6 =>
            ![base 0, base 1, base 2, base 3, base 4,
              witnesses 0, witnesses 1, witnesses 2,
              witnesses 3, witnesses 4]
              (![0, 1, 2, 5, 6, 7] i)) =
            ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
              natCode index.1, textbookDelta0RecordZF_l child,
              natCode child.arity, natCode child.code] := by
        funext i
        fin_cases i <;> rfl
      simpa only [hAssignment] using hEarlier
    · simp [TextbookDelta0Judgment.negate, base, witnesses]
    · simp [witnesses]
    · simp [witnesses]
    · simpa [TextbookDelta0Judgment.negate, base, witnesses] using
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          child.code 0 2
          (natCode (textbookECode child.code 0 2))).mpr rfl

end YesMetaZFC.BMS.ConstructibleBridge
