import BMSConstructibleBridge.TextbookBoundedLevyRaiseRule

/-!
# 存在量词分类规则的成员语言公式

该规则要求当前记录与子记录均为 Sigma，层级不变，子元数是当前元数的后继，
并检查输出码为 `E(childCode, 0, 4)`。后继条件同时排除了零元子公式。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 当前七字段后追加子记录五字段、零和标签四。 -/
def textbookBoundedLevyExistentialRuleBody_l : FOFormula 14 :=
  .conj
    (FOFormula.rename ![0, 1, 2, 7, 8, 9, 10, 11]
      textbookBoundedLevyEarlierRecordFormula_l) <|
  .conj (Delta0Formula.natLiteralDeltaAt 1 (3 : Fin 14)).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt 1 (8 : Fin 14)).toFO <|
  .conj (.eq 4 9) <|
  .conj (Delta0Formula.successorAt 10 5).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt 0 (12 : Fin 14)).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt 4 (13 : Fin 14)).toFO
    (TextbookNatFormula.textbookECodeFormulaAt 0 11 12 13 6)

def textbookBoundedLevyExistentialRuleFormula_l : FOFormula 7 :=
  externalExistentialClosure_l 7 textbookBoundedLevyExistentialRuleBody_l

/-- 存在量词分支精确等价于有限索引证书中的量化规则。 -/
theorem satisfies_textbookBoundedLevyExistentialRuleFormula_iff_l
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (entry : TextbookBoundedLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyExistentialRuleFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookBoundedLevyTraceGraphZF_l trace,
        natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        child.isSigma = true ∧ 0 < child.arity ∧ entry = child.quantify := by
  rw [textbookBoundedLevyExistentialRuleFormula_l, satisfies_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 7 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookBoundedLevyTraceGraphZF_l trace,
      natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  change (∃ witnesses : Tuple ZFSet.{u} 7,
    FOFormula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyExistentialRuleBody_l
      (Fin.append base witnesses)) ↔ _
  simp only [textbookBoundedLevyNegationRuleAssignment_l]
  constructor
  · rintro ⟨w, hBody⟩
    simp only [textbookBoundedLevyExistentialRuleBody_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename,
      Delta0Formula.satisfies_natLiteralDeltaAt,
      Delta0Formula.satisfies_toFO, Delta0Formula.satisfies_successorAt,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt] at hBody
    have hEarlier : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyEarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, w 0, w 1, w 2, w 3, w 4] := by
      have hAssignment :
          (fun i : Fin 8 =>
            ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
              w 0, w 1, w 2, w 3, w 4, w 5, w 6]
              (![0, 1, 2, 7, 8, 9, 10, 11] i)) =
            ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
              natCode index.1, w 0, w 1, w 2, w 3, w 4] := by
        funext i
        fin_cases i <;> rfl
      simpa only [hAssignment] using hBody.1
    obtain ⟨child, hPrior, _, hChildPolarity, hLevel, hArity, hCode⟩ :=
      (satisfies_textbookBoundedLevyEarlierRecordFormula_iff_l
        trace index (w 0) (w 1) (w 2) (w 3) (w 4)).mp hEarlier
    have hEntryPolarityCode : textbookBoundedLevyPolarityCode_l entry.isSigma = 1 := by
      apply (@natCode_injective.{u})
      simpa [base] using hBody.2.1
    have hEntryPolarity : entry.isSigma = true :=
      (textbookBoundedLevyPolarityCode_eq_one_iff_l _).mp hEntryPolarityCode
    have hChildPolarityCode : textbookBoundedLevyPolarityCode_l child.isSigma = 1 := by
      apply (@natCode_injective.{u})
      simpa [hChildPolarity] using hBody.2.2.1
    have hChildPolarity' : child.isSigma = true :=
      (textbookBoundedLevyPolarityCode_eq_one_iff_l _).mp hChildPolarityCode
    have hLevelEq : entry.level = child.level := by
      apply (@natCode_injective.{u})
      simpa [base, hLevel] using hBody.2.2.2.1
    have hAritySucc : child.arity = entry.arity + 1 := by
      apply (@natCode_injective.{u})
      have hSucc : (natCode child.arity : ZFSet.{u}) =
          insert (natCode entry.arity) (natCode entry.arity) := by
        simpa [base, hArity] using hBody.2.2.2.2.1
      rw [hSucc, ← natCode_succ_eq_insert]
    have hZero := hBody.2.2.2.2.2.1
    have hTag := hBody.2.2.2.2.2.2.1
    change w 5 = natCode 0 at hZero
    change w 6 = natCode 4 at hTag
    have hECode := hBody.2.2.2.2.2.2.2
    rw [hCode, hZero, hTag] at hECode
    have hCodeEq : entry.code = textbookECode child.code 0 4 := by
      apply (@natCode_injective.{u})
      apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
        child.code 0 4 (natCode entry.code)).mp
      simpa [base] using hECode
    refine ⟨child, hPrior, hChildPolarity', ?_, ?_⟩
    · omega
    · cases entry
      cases child
      simp_all [TextbookBoundedLevyJudgment.quantify]
  · rintro ⟨child, hPrior, hChildPolarity, hPositive, hEntry⟩
    have hEntryPolarity : entry.isSigma = true := by
      simpa [TextbookBoundedLevyJudgment.quantify, hChildPolarity] using
        congrArg TextbookBoundedLevyJudgment.isSigma hEntry
    have hLevel : entry.level = child.level := by
      simpa [TextbookBoundedLevyJudgment.quantify] using
        congrArg TextbookBoundedLevyJudgment.level hEntry
    have hArity : child.arity = entry.arity + 1 := by
      have h := congrArg TextbookBoundedLevyJudgment.arity hEntry
      simp only [TextbookBoundedLevyJudgment.quantify] at h
      omega
    have hCode : entry.code = textbookECode child.code 0 4 := by
      simpa [TextbookBoundedLevyJudgment.quantify] using
        congrArg TextbookBoundedLevyJudgment.code hEntry
    let witnesses : Tuple ZFSet.{u} 7 :=
      ![textbookBoundedLevyRecordZF_l child,
        natCode (textbookBoundedLevyPolarityCode_l child.isSigma),
        natCode child.level, natCode child.arity, natCode child.code,
        natCode 0, natCode 4]
    refine ⟨witnesses, ?_⟩
    simp only [textbookBoundedLevyExistentialRuleBody_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename,
      Delta0Formula.satisfies_natLiteralDeltaAt,
      Delta0Formula.satisfies_toFO, Delta0Formula.satisfies_successorAt,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt]
    have hEarlier := (satisfies_textbookBoundedLevyEarlierRecordFormula_iff_l
      trace index (textbookBoundedLevyRecordZF_l child)
      (natCode (textbookBoundedLevyPolarityCode_l child.isSigma))
      (natCode child.level) (natCode child.arity) (natCode child.code)).mpr
        ⟨child, hPrior, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hAssignment :
          (fun i : Fin 8 =>
            ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
              witnesses 0, witnesses 1, witnesses 2, witnesses 3,
              witnesses 4, witnesses 5, witnesses 6]
              (![0, 1, 2, 7, 8, 9, 10, 11] i)) =
            ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
              natCode index.1, textbookBoundedLevyRecordZF_l child,
              natCode (textbookBoundedLevyPolarityCode_l child.isSigma),
              natCode child.level, natCode child.arity, natCode child.code] := by
          funext i
          fin_cases i <;> rfl
      simpa only [hAssignment] using hEarlier
    · simp [base, hEntryPolarity]
    · simp [witnesses, hChildPolarity]
    · simp [base, witnesses, hLevel]
    · rw [show base 5 = natCode entry.arity by rfl,
        show witnesses 3 = natCode child.arity by rfl, hArity]
      exact (@natCode_succ_eq_insert.{u}) entry.arity
    · simp [witnesses]
    · simp [witnesses]
    · simpa [base, witnesses, hCode] using
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          child.code 0 4 (natCode (textbookECode child.code 0 4))).mpr rfl

end YesMetaZFC.BMS.ConstructibleBridge
