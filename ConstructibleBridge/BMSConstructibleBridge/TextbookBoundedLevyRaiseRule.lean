import BMSConstructibleBridge.TextbookBoundedLevyNegationRule
import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteOrdinalSuccessorFormula

/-!
# 有限层级提升规则的成员语言公式

提升规则保留元数和公式码，把层级加一；目标极性可任取。这一个分支同时表示
原归纳定义中的 `lift` 与 `ofPi`/`ofSigma`。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 当前七字段后追加一条子记录的五个字段。 -/
def textbookBoundedLevyRaiseRuleBody_l : FOFormula 12 :=
  .conj
    (FOFormula.rename ![0, 1, 2, 7, 8, 9, 10, 11]
      textbookBoundedLevyEarlierRecordFormula_l) <|
  .conj (Delta0Formula.successorAt 4 9).toFO <|
  .conj (.eq 5 10) (.eq 6 11)

/-- 关闭子记录的五个内部字段。 -/
def textbookBoundedLevyRaiseRuleFormula_l : FOFormula 7 :=
  externalExistentialClosure_l 5 textbookBoundedLevyRaiseRuleBody_l

/-- 五个内部字段的追加布局。 -/
theorem textbookBoundedLevyRaiseRuleAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 7) (witnesses : Tuple Carrier 5) :
    Fin.append base witnesses =
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        witnesses 0, witnesses 1, witnesses 2, witnesses 3, witnesses 4] := by
  funext position
  fin_cases position <;> rfl

/-- 提升分支的对象公式精确等价于元层提升规则。 -/
theorem satisfies_textbookBoundedLevyRaiseRuleFormula_iff_l
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (entry : TextbookBoundedLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyRaiseRuleFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookBoundedLevyTraceGraphZF_l trace,
        natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        entry = child.raise entry.isSigma := by
  rw [textbookBoundedLevyRaiseRuleFormula_l, satisfies_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 7 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookBoundedLevyTraceGraphZF_l trace,
      natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  change (∃ witnesses : Tuple ZFSet.{u} 5,
    FOFormula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyRaiseRuleBody_l
      (Fin.append base witnesses)) ↔ _
  simp only [textbookBoundedLevyRaiseRuleAssignment_l]
  constructor
  · rintro ⟨w, hBody⟩
    simp only [textbookBoundedLevyRaiseRuleBody_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename, Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt] at hBody
    have hEarlier : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyEarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, w 0, w 1, w 2, w 3, w 4] := by
      have hAssignment :
          (fun i : Fin 8 =>
            ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
              w 0, w 1, w 2, w 3, w 4] (![0, 1, 2, 7, 8, 9, 10, 11] i)) =
            ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
              natCode index.1, w 0, w 1, w 2, w 3, w 4] := by
        funext i
        fin_cases i <;> rfl
      simpa only [hAssignment] using hBody.1
    obtain ⟨child, hPrior, _, _, hLevel, hArity, hCode⟩ :=
      (satisfies_textbookBoundedLevyEarlierRecordFormula_iff_l
        trace index (w 0) (w 1) (w 2) (w 3) (w 4)).mp hEarlier
    have hSuccessor : (natCode entry.level : ZFSet.{u}) =
        insert (natCode child.level) (natCode child.level) := by
      simpa [base, hLevel] using hBody.2.1
    have hLevelEq : entry.level = child.level + 1 := by
      apply (@natCode_injective.{u})
      rw [hSuccessor, ← natCode_succ_eq_insert]
    have hArityEq : entry.arity = child.arity := by
      apply (@natCode_injective.{u})
      simpa [base, hArity] using hBody.2.2.1
    have hCodeEq : entry.code = child.code := by
      apply (@natCode_injective.{u})
      simpa [base, hCode] using hBody.2.2.2
    refine ⟨child, hPrior, ?_⟩
    cases entry
    cases child
    simp_all [TextbookBoundedLevyJudgment.raise]
  · rintro ⟨child, hPrior, hEntry⟩
    have hLevel : entry.level = child.level + 1 := by
      simpa [TextbookBoundedLevyJudgment.raise] using
        congrArg TextbookBoundedLevyJudgment.level hEntry
    have hArity : entry.arity = child.arity := by
      simpa [TextbookBoundedLevyJudgment.raise] using
        congrArg TextbookBoundedLevyJudgment.arity hEntry
    have hCode : entry.code = child.code := by
      simpa [TextbookBoundedLevyJudgment.raise] using
        congrArg TextbookBoundedLevyJudgment.code hEntry
    let witnesses : Tuple ZFSet.{u} 5 :=
      ![textbookBoundedLevyRecordZF_l child,
        natCode (textbookBoundedLevyPolarityCode_l child.isSigma),
        natCode child.level, natCode child.arity, natCode child.code]
    refine ⟨witnesses, ?_⟩
    simp only [textbookBoundedLevyRaiseRuleBody_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename, Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt]
    have hEarlier := (satisfies_textbookBoundedLevyEarlierRecordFormula_iff_l
      trace index (textbookBoundedLevyRecordZF_l child)
      (natCode (textbookBoundedLevyPolarityCode_l child.isSigma))
      (natCode child.level) (natCode child.arity) (natCode child.code)).mpr
        ⟨child, hPrior, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hAssignment :
          (fun i : Fin 8 =>
            ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
              witnesses 0, witnesses 1, witnesses 2, witnesses 3, witnesses 4]
              (![0, 1, 2, 7, 8, 9, 10, 11] i)) =
            ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
              natCode index.1, textbookBoundedLevyRecordZF_l child,
              natCode (textbookBoundedLevyPolarityCode_l child.isSigma),
              natCode child.level, natCode child.arity, natCode child.code] := by
          funext i
          fin_cases i <;> rfl
      simpa only [hAssignment] using hEarlier
    · simpa [base, witnesses, hLevel] using
        ((@satisfies_successorAt_natCode.{u}) child.level)
    · simp [base, witnesses, hArity]
    · simp [base, witnesses, hCode]

end YesMetaZFC.BMS.ConstructibleBridge
