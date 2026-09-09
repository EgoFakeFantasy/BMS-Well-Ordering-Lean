import BMSConstructibleBridge.TextbookLevyEarlierRecord

/-!
# 否定分类规则的成员语言公式

否定规则读取一条严格先前记录，翻转极性，保持层级和元数，并检查输出码为
`E(childCode, 0, 2)`。零和标签二都由对象语言的自然数字面量公式给出。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/--
否定规则矩阵。前七个坐标是当前记录环境，其后依次为
`childRecord, childPolarity, childLevel, childArity, childCode, zero, tag`。
-/
def textbookLevyNegationRuleBody_l : FOFormula 14 :=
  .conj
    (FOFormula.rename ![0, 1, 2, 7, 8, 9, 10, 11]
      textbookLevyEarlierRecordFormula_l) <|
  .conj
    (FOFormula.disj
      (.conj (Delta0Formula.natLiteralDeltaAt 0 (3 : Fin 14)).toFO
        (Delta0Formula.natLiteralDeltaAt 1 (8 : Fin 14)).toFO)
      (.conj (Delta0Formula.natLiteralDeltaAt 1 (3 : Fin 14)).toFO
        (Delta0Formula.natLiteralDeltaAt 0 (8 : Fin 14)).toFO)) <|
  .conj (.eq 4 9) <|
  .conj (.eq 5 10) <|
  .conj (Delta0Formula.natLiteralDeltaAt 0 (12 : Fin 14)).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt 2 (13 : Fin 14)).toFO
    (TextbookNatFormula.textbookECodeFormulaAt 0 11 12 13 6)

/-- 关闭子记录的五个字段以及零、标签两个算术见证。 -/
def textbookLevyNegationRuleFormula_l : FOFormula 7 :=
  externalExistentialClosure_l 7 textbookLevyNegationRuleBody_l

/-- 七个隐藏坐标追加到当前记录环境后的显式布局。 -/
theorem textbookLevyNegationRuleAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 7) (witnesses : Tuple Carrier 7) :
    Fin.append base witnesses =
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        witnesses 0, witnesses 1, witnesses 2, witnesses 3,
        witnesses 4, witnesses 5, witnesses 6] := by
  funext position
  fin_cases position <;> rfl

/-- 否定分支的对象公式精确等价于元层的一步否定规则。 -/
theorem satisfies_textbookLevyNegationRuleFormula_iff_l
    (trace : List TextbookLevyJudgment) (index : Fin trace.length)
    (entry : TextbookLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyNegationRuleFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookLevyTraceGraphZF_l trace,
        natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        entry = child.negate := by
  rw [textbookLevyNegationRuleFormula_l, satisfies_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 7 :=
    ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
      natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  change (∃ witnesses : Tuple ZFSet.{u} 7,
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyNegationRuleBody_l
      (Fin.append base witnesses)) ↔ _
  simp only [textbookLevyNegationRuleAssignment_l]
  constructor
  · rintro ⟨w, hBody⟩
    simp only [textbookLevyNegationRuleBody_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename, FOFormula.satisfies_disj,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt] at hBody
    have hEarlier : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookLevyEarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1, w 0, w 1, w 2, w 3, w 4] := by
      have hAssignment :
          (fun i : Fin 8 =>
            ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
              w 0, w 1, w 2, w 3, w 4, w 5, w 6]
              (![0, 1, 2, 7, 8, 9, 10, 11] i)) =
            ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
              natCode index.1, w 0, w 1, w 2, w 3, w 4] := by
        funext i
        fin_cases i <;> rfl
      simpa only [hAssignment] using hBody.1
    obtain ⟨child, hPrior, hRecord, hPolarity, hLevel, hArity, hCode⟩ :=
      (satisfies_textbookLevyEarlierRecordFormula_iff_l
        trace index (w 0) (w 1) (w 2) (w 3) (w 4)).mp hEarlier
    have hRest := hBody.2
    have hToggle := hRest.1
    have hLevelEq := hRest.2.1
    have hArityEq := hRest.2.2.1
    have hZero := hRest.2.2.2.1
    have hTag := hRest.2.2.2.2.1
    have hECode := hRest.2.2.2.2.2
    change w 5 = natCode 0 at hZero
    change w 6 = natCode 2 at hTag
    rw [hCode, hZero, hTag] at hECode
    have hECode' : (natCode entry.code : ZFSet.{u}) =
        natCode (textbookECode child.code 0 2) := by
      apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
        child.code 0 2 (natCode entry.code)).mp
      simpa [base] using hECode
    have hCodeEq : entry.code = textbookECode child.code 0 2 :=
      (@natCode_injective.{u}) hECode'
    have hLevelEq' : entry.level = child.level := by
      apply @natCode_injective.{u}
      simpa [base, hLevel] using hLevelEq
    have hArityEq' : entry.arity = child.arity := by
      apply @natCode_injective.{u}
      simpa [base, hArity] using hArityEq
    have hToggle' :
        (entry.isSigma = false ∧ child.isSigma = true) ∨
          (entry.isSigma = true ∧ child.isSigma = false) := by
      simpa [base, hPolarity, textbookLevyPolarityCode_l] using hToggle
    have hPolarityEq : entry.isSigma = !child.isSigma := by
      rcases hToggle' with ⟨hEntry, hChild⟩ | ⟨hEntry, hChild⟩
      · rw [hEntry, hChild]
        rfl
      · rw [hEntry, hChild]
        rfl
    apply Exists.intro child
    refine ⟨hPrior, ?_⟩
    cases entry
    cases child
    simp_all [TextbookLevyJudgment.negate]
  · rintro ⟨child, hPrior, rfl⟩
    let witnesses : Tuple ZFSet.{u} 7 :=
      ![textbookLevyRecordZF_l child,
        natCode (textbookLevyPolarityCode_l child.isSigma),
        natCode child.level, natCode child.arity, natCode child.code,
        natCode 0, natCode 2]
    refine ⟨witnesses, ?_⟩
    simp only [textbookLevyNegationRuleBody_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename, FOFormula.satisfies_disj,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt]
    have hEarlier := (satisfies_textbookLevyEarlierRecordFormula_iff_l
      trace index (textbookLevyRecordZF_l child)
      (natCode (textbookLevyPolarityCode_l child.isSigma))
      (natCode child.level) (natCode child.arity) (natCode child.code)).mpr
        ⟨child, hPrior, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hAssignment :
          (fun i : Fin 8 =>
            ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
              witnesses 0, witnesses 1, witnesses 2, witnesses 3,
              witnesses 4, witnesses 5, witnesses 6]
              (![0, 1, 2, 7, 8, 9, 10, 11] i)) =
            ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
              natCode index.1, textbookLevyRecordZF_l child,
              natCode (textbookLevyPolarityCode_l child.isSigma),
              natCode child.level, natCode child.arity, natCode child.code] := by
          funext i
          fin_cases i <;> rfl
      simpa only [hAssignment] using hEarlier
    · cases child.isSigma <;> simp [TextbookLevyJudgment.negate,
        textbookLevyPolarityCode_l, base, witnesses]
    · simp [TextbookLevyJudgment.negate, base, witnesses]
    · simp [TextbookLevyJudgment.negate, base, witnesses]
    · simp [witnesses]
    · simp [witnesses]
    · simpa [TextbookLevyJudgment.negate, base, witnesses] using
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          child.code 0 2 (natCode (textbookECode child.code 0 2))).mpr rfl

end YesMetaZFC.BMS.ConstructibleBridge
