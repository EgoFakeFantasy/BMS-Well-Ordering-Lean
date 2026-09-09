import BMSConstructibleBridge.TextbookBoundedLevyExistentialRule

/-!
# 合取分类规则的成员语言公式

合取分支读取两条严格先前记录，检查它们同极性、同层级、同元数，并令当前
记录继承这些字段。最后以标签三的 E 构造器合成两个子公式码。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 前七字段后依次放置左、右子记录的五字段和标签三。 -/
def textbookBoundedLevyConjunctionRuleBody_l : FOFormula 18 :=
  .conj
    (FOFormula.rename ![0, 1, 2, 7, 8, 9, 10, 11]
      textbookBoundedLevyEarlierRecordFormula_l) <|
  .conj
    (FOFormula.rename ![0, 1, 2, 12, 13, 14, 15, 16]
      textbookBoundedLevyEarlierRecordFormula_l) <|
  .conj (.eq 8 13) <|
  .conj (.eq 9 14) <|
  .conj (.eq 10 15) <|
  .conj (.eq 3 8) <|
  .conj (.eq 4 9) <|
  .conj (.eq 5 10) <|
  .conj (Delta0Formula.natLiteralDeltaAt 3 (17 : Fin 18)).toFO
    (TextbookNatFormula.textbookECodeFormulaAt 0 11 16 17 6)

def textbookBoundedLevyConjunctionRuleFormula_l : FOFormula 7 :=
  externalExistentialClosure_l 11 textbookBoundedLevyConjunctionRuleBody_l

/-- 十一个内部字段的追加布局。 -/
theorem textbookBoundedLevyConjunctionRuleAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 7) (w : Tuple Carrier 11) :
    Fin.append base w =
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10] := by
  funext position
  fin_cases position <;> rfl

/-- 左子记录重命名后的赋值。 -/
theorem textbookBoundedLevyConjunctionLeftAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 7) (w : Tuple Carrier 11) :
    (fun i : Fin 8 =>
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10]
        (![0, 1, 2, 7, 8, 9, 10, 11] i)) =
      ![base 0, base 1, base 2, w 0, w 1, w 2, w 3, w 4] := by
  funext i
  fin_cases i <;> rfl

/-- 右子记录重命名后的赋值。 -/
theorem textbookBoundedLevyConjunctionRightAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 7) (w : Tuple Carrier 11) :
    (fun i : Fin 8 =>
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10]
        (![0, 1, 2, 12, 13, 14, 15, 16] i)) =
      ![base 0, base 1, base 2, w 5, w 6, w 7, w 8, w 9] := by
  funext i
  fin_cases i <;> rfl

/-- 合取分支精确等价于两条先前记录上的元层合取规则。 -/
theorem satisfies_textbookBoundedLevyConjunctionRuleFormula_iff_l
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (entry : TextbookBoundedLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyConjunctionRuleFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookBoundedLevyTraceGraphZF_l trace,
        natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ left, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = left) ∧
      ∃ right, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = right) ∧
        left.isSigma = right.isSigma ∧ left.level = right.level ∧
        left.arity = right.arity ∧ entry = left.conjoin right := by
  rw [textbookBoundedLevyConjunctionRuleFormula_l, satisfies_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 7 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookBoundedLevyTraceGraphZF_l trace,
      natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  change (∃ w : Tuple ZFSet.{u} 11,
    FOFormula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyConjunctionRuleBody_l
      (Fin.append base w)) ↔ _
  simp only [textbookBoundedLevyConjunctionRuleAssignment_l]
  constructor
  · rintro ⟨w, hBody⟩
    simp only [textbookBoundedLevyConjunctionRuleBody_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename, Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt] at hBody
    obtain ⟨hLeftRaw, hRightRaw, hChildrenPolarity, hChildrenLevel,
      hChildrenArity, hEntryPolarity, hEntryLevel, hEntryArity, hTag, hECode⟩ := hBody
    have hLeft : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyEarlierRecordFormula_l
        ![base 0, base 1, base 2, w 0, w 1, w 2, w 3, w 4] := by
      simpa only [textbookBoundedLevyConjunctionLeftAssignment_l] using hLeftRaw
    have hRight : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyEarlierRecordFormula_l
        ![base 0, base 1, base 2, w 5, w 6, w 7, w 8, w 9] := by
      simpa only [textbookBoundedLevyConjunctionRightAssignment_l] using hRightRaw
    obtain ⟨left, hLeftPrior, _, hLeftPolarity, hLeftLevel,
      hLeftArity, hLeftCode⟩ :=
      (satisfies_textbookBoundedLevyEarlierRecordFormula_iff_l trace index
        (w 0) (w 1) (w 2) (w 3) (w 4)).mp (by simpa [base] using hLeft)
    obtain ⟨right, hRightPrior, _, hRightPolarity, hRightLevel,
      hRightArity, hRightCode⟩ :=
      (satisfies_textbookBoundedLevyEarlierRecordFormula_iff_l trace index
        (w 5) (w 6) (w 7) (w 8) (w 9)).mp (by simpa [base] using hRight)
    have hPolarity : left.isSigma = right.isSigma := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply (@natCode_injective.{u})
      simpa [hLeftPolarity, hRightPolarity] using hChildrenPolarity
    have hLevel : left.level = right.level := by
      apply (@natCode_injective.{u})
      simpa [hLeftLevel, hRightLevel] using hChildrenLevel
    have hArity : left.arity = right.arity := by
      apply (@natCode_injective.{u})
      simpa [hLeftArity, hRightArity] using hChildrenArity
    have hEntryPolarity' : entry.isSigma = left.isSigma := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply (@natCode_injective.{u})
      simpa [base, hLeftPolarity] using hEntryPolarity
    have hEntryLevel' : entry.level = left.level := by
      apply (@natCode_injective.{u})
      simpa [base, hLeftLevel] using hEntryLevel
    have hEntryArity' : entry.arity = left.arity := by
      apply (@natCode_injective.{u})
      simpa [base, hLeftArity] using hEntryArity
    change w 10 = natCode 3 at hTag
    rw [hLeftCode, hRightCode, hTag] at hECode
    have hEntryCode : entry.code = textbookECode left.code right.code 3 := by
      apply (@natCode_injective.{u})
      apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
        left.code right.code 3 (natCode entry.code)).mp
      simpa [base] using hECode
    refine ⟨left, hLeftPrior, right, hRightPrior,
      hPolarity, hLevel, hArity, ?_⟩
    cases entry
    cases left
    cases right
    simp_all [TextbookBoundedLevyJudgment.conjoin]
  · rintro ⟨left, hLeftPrior, right, hRightPrior,
      hPolarity, hLevel, hArity, hEntry⟩
    have hEntryPolarity : entry.isSigma = left.isSigma := by
      simpa [TextbookBoundedLevyJudgment.conjoin] using
        congrArg TextbookBoundedLevyJudgment.isSigma hEntry
    have hEntryLevel : entry.level = left.level := by
      simpa [TextbookBoundedLevyJudgment.conjoin] using
        congrArg TextbookBoundedLevyJudgment.level hEntry
    have hEntryArity : entry.arity = left.arity := by
      simpa [TextbookBoundedLevyJudgment.conjoin] using
        congrArg TextbookBoundedLevyJudgment.arity hEntry
    have hEntryCode : entry.code = textbookECode left.code right.code 3 := by
      simpa [TextbookBoundedLevyJudgment.conjoin] using
        congrArg TextbookBoundedLevyJudgment.code hEntry
    let w : Tuple ZFSet.{u} 11 :=
      ![textbookBoundedLevyRecordZF_l left,
        natCode (textbookBoundedLevyPolarityCode_l left.isSigma),
        natCode left.level, natCode left.arity, natCode left.code,
        textbookBoundedLevyRecordZF_l right,
        natCode (textbookBoundedLevyPolarityCode_l right.isSigma),
        natCode right.level, natCode right.arity, natCode right.code,
        natCode 3]
    refine ⟨w, ?_⟩
    simp only [textbookBoundedLevyConjunctionRuleBody_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename, Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt]
    have hLeft := (satisfies_textbookBoundedLevyEarlierRecordFormula_iff_l trace index
      (textbookBoundedLevyRecordZF_l left)
      (natCode (textbookBoundedLevyPolarityCode_l left.isSigma))
      (natCode left.level) (natCode left.arity) (natCode left.code)).mpr
        ⟨left, hLeftPrior, rfl, rfl, rfl, rfl, rfl⟩
    have hRight := (satisfies_textbookBoundedLevyEarlierRecordFormula_iff_l trace index
      (textbookBoundedLevyRecordZF_l right)
      (natCode (textbookBoundedLevyPolarityCode_l right.isSigma))
      (natCode right.level) (natCode right.arity) (natCode right.code)).mpr
        ⟨right, hRightPrior, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hLeft using 1 <;> ext i <;> fin_cases i <;> rfl
    · convert hRight using 1 <;> ext i <;> fin_cases i <;> rfl
    · simp [w, hPolarity]
    · simp [w, hLevel]
    · simp [w, hArity]
    · simp [base, w, hEntryPolarity]
    · simp [base, w, hEntryLevel]
    · simp [base, w, hEntryArity]
    · simp [w]
    · simpa [base, w, hEntryCode] using
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          left.code right.code 3
          (natCode (textbookECode left.code right.code 3))).mpr rfl

end YesMetaZFC.BMS.ConstructibleBridge
