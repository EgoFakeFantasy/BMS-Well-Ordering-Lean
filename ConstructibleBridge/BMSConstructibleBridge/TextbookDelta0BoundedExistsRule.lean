import BMSConstructibleBridge.TextbookDelta0ConjunctionRule

/-!
# `Delta0` 有界存在量词规则的成员语言公式

子公式必须多一个自由变量；界变量是当前元数以内的旧变量。公式同时逐层检查
`E(E(E(arity, bound, 0), childCode, 3), 0, 4)` 的规范编码。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 有界存在量词规则矩阵。前五坐标为当前环境，随后为
`childRecord, childArity, childCode, bound, zero, innerMem,
tagThree, innerConj, tagFour`。 -/
def textbookDelta0BoundedExistsRuleBody_l : FOFormula 14 :=
  .conj
    (FOFormula.rename ![0, 1, 2, 5, 6, 7]
      textbookDelta0EarlierRecordFormula_l) <|
  .conj (Delta0Formula.successorAt 6 3).toFO <|
  .conj (.mem 8 0) <|
  .conj (.mem 8 3) <|
  .conj (Delta0Formula.natLiteralDeltaAt 0 (9 : Fin 14)).toFO <|
  .conj (TextbookNatFormula.textbookECodeFormulaAt 0 3 8 9 10) <|
  .conj (Delta0Formula.natLiteralDeltaAt 3 (11 : Fin 14)).toFO <|
  .conj (TextbookNatFormula.textbookECodeFormulaAt 0 10 7 11 12) <|
  .conj (Delta0Formula.natLiteralDeltaAt 4 (13 : Fin 14)).toFO
    (TextbookNatFormula.textbookECodeFormulaAt 0 12 9 13 4)

/-- 关闭九个内部见证。 -/
def textbookDelta0BoundedExistsRuleFormula_l : FOFormula 5 :=
  externalExistentialClosure_l 9 textbookDelta0BoundedExistsRuleBody_l

/-- 九个隐藏坐标追加后的显式布局。 -/
theorem textbookDelta0BoundedExistsRuleAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 5) (witnesses : Tuple Carrier 9) :
    Fin.append base witnesses =
      ![base 0, base 1, base 2, base 3, base 4,
        witnesses 0, witnesses 1, witnesses 2, witnesses 3,
        witnesses 4, witnesses 5, witnesses 6, witnesses 7,
        witnesses 8] := by
  funext position
  fin_cases position <;> rfl

/-- 有界存在量词公式精确等价于元层的一步有界量化规则。 -/
theorem satisfies_textbookDelta0BoundedExistsRuleFormula_iff_l
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (entry : TextbookDelta0Judgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0BoundedExistsRuleFormula_l
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
          textbookDelta0TraceGraphZF_l trace, natCode index.1,
          natCode entry.arity, natCode entry.code] ↔
      ∃ child,
        (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = child) ∧
        0 < child.arity ∧
        ∃ bound : Fin (child.arity - 1),
          entry = child.boundedExists bound.1 := by
  rw [textbookDelta0BoundedExistsRuleFormula_l,
    satisfies_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 5 :=
    ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
      natCode index.1, natCode entry.arity, natCode entry.code]
  change (∃ witnesses : Tuple ZFSet.{u} 9,
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookDelta0BoundedExistsRuleBody_l
      (Fin.append base witnesses)) ↔ _
  simp only [textbookDelta0BoundedExistsRuleAssignment_l]
  constructor
  · rintro ⟨w, hBody⟩
    simp only [textbookDelta0BoundedExistsRuleBody_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename, Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt,
      Delta0Formula.satisfies_natLiteralDeltaAt,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt] at hBody
    obtain ⟨hEarlierRaw, hSuccessor, hBoundOmega, hBoundArity,
      hZero, hInnerMem, hTagThree, hInnerConj, hTagFour, hOuter⟩ := hBody
    have hEarlier : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0EarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, w 0, w 1, w 2] := by
      have hAssignment :
          (fun i : Fin 6 =>
            ![base 0, base 1, base 2, base 3, base 4,
              w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8]
              (![0, 1, 2, 5, 6, 7] i)) =
            ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
              natCode index.1, w 0, w 1, w 2] := by
        funext i
        fin_cases i <;> rfl
      simpa only [hAssignment] using hEarlierRaw
    obtain ⟨child, hPrior, _hRecord, hChildArity, hChildCode⟩ :=
      (satisfies_textbookDelta0EarlierRecordFormula_iff_l
        trace index (w 0) (w 1) (w 2)).mp hEarlier
    have hAritySucc : child.arity = entry.arity + 1 := by
      apply @natCode_injective.{u}
      have hSucc : (natCode child.arity : ZFSet.{u}) =
          insert (natCode entry.arity) (natCode entry.arity) := by
        simpa [base, hChildArity] using hSuccessor
      rw [hSucc, ← natCode_succ_eq_insert]
    obtain ⟨bound, hBoundCode⟩ :=
      (IndexedSequenceZF.mem_omega_iff_exists_natCode (w 3)).mp hBoundOmega
    have hBound : bound < entry.arity :=
      (@natCode_mem_natCode_iff.{u} bound entry.arity).mp (by
        rw [hBoundCode] at hBoundArity
        simpa [base] using hBoundArity)
    change w 4 = natCode 0 at hZero
    change w 6 = natCode 3 at hTagThree
    change w 8 = natCode 4 at hTagFour
    rw [hBoundCode, hZero] at hInnerMem
    rw [hTagThree] at hInnerConj
    rw [hZero, hTagFour] at hOuter
    have hInnerMemCode : (w 5 : ZFSet.{u}) =
        natCode (textbookECode entry.arity bound 0) := by
      apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
        entry.arity bound 0 (w 5)).mp
      simpa [base] using hInnerMem
    have hInnerConjCode : (w 7 : ZFSet.{u}) =
        natCode (textbookECode
          (textbookECode entry.arity bound 0) child.code 3) := by
      rw [hInnerMemCode, hChildCode] at hInnerConj
      apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
        (textbookECode entry.arity bound 0) child.code 3 (w 7)).mp
      exact hInnerConj
    rw [hInnerConjCode] at hOuter
    have hEntryCode : entry.code = textbookECode
        (textbookECode
          (textbookECode entry.arity bound 0) child.code 3) 0 4 := by
      apply @natCode_injective.{u}
      apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
        (textbookECode
          (textbookECode entry.arity bound 0) child.code 3)
        0 4 (natCode entry.code)).mp
      simpa [base] using hOuter
    have hPositive : 0 < child.arity := by omega
    have hArityPred : entry.arity = child.arity - 1 := by omega
    let boundIndex : Fin (child.arity - 1) := by
      refine ⟨bound, ?_⟩
      omega
    refine ⟨child, hPrior, hPositive, boundIndex, ?_⟩
    cases entry with
    | mk entryArity entryCode =>
      cases child with
      | mk childArity childCode =>
        simp only [TextbookDelta0Judgment.arity,
          TextbookDelta0Judgment.code,
          TextbookDelta0Judgment.boundedExists] at hArityPred hEntryCode ⊢
        subst entryArity
        subst entryCode
        rfl
  · rintro ⟨child, hPrior, hPositive, bound, rfl⟩
    have hAritySucc : child.arity =
        (child.boundedExists bound.1).arity + 1 := by
      simp only [TextbookDelta0Judgment.boundedExists]
      omega
    let innerMem := textbookECode
      (child.boundedExists bound.1).arity bound.1 0
    let innerConj := textbookECode innerMem child.code 3
    let witnesses : Tuple ZFSet.{u} 9 :=
      ![textbookDelta0RecordZF_l child, natCode child.arity,
        natCode child.code, natCode bound.1, natCode 0,
        natCode innerMem, natCode 3, natCode innerConj, natCode 4]
    refine ⟨witnesses, ?_⟩
    simp only [textbookDelta0BoundedExistsRuleBody_l,
      FOFormula.Satisfies, FOFormula.satisfies_rename,
      Delta0Formula.satisfies_toFO, Delta0Formula.satisfies_successorAt,
      Delta0Formula.satisfies_natLiteralDeltaAt,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt]
    have hEarlier :=
      (satisfies_textbookDelta0EarlierRecordFormula_iff_l
        trace index (textbookDelta0RecordZF_l child)
        (natCode child.arity) (natCode child.code)).mpr
        ⟨child, hPrior, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hEarlier using 1 <;> ext i <;> fin_cases i <;> rfl
    · change (natCode child.arity : ZFSet.{u}) =
        insert (natCode (child.boundedExists bound.1).arity)
          (natCode (child.boundedExists bound.1).arity)
      have hCodeSucc := congrArg
        (fun arity => (natCode arity : ZFSet.{u})) hAritySucc
      simpa only [natCode_succ_eq_insert] using hCodeSucc
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
        ⟨bound.1, rfl⟩
    · exact (@natCode_mem_natCode_iff.{u} bound.1
        (child.boundedExists bound.1).arity).mpr (by
        simpa only [TextbookDelta0Judgment.boundedExists] using bound.2)
    · simp [witnesses]
    · have hCode :=
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          (child.boundedExists bound.1).arity bound.1 0
          (natCode innerMem)).mpr (by rfl)
      convert hCode using 1 <;> simp [base, witnesses, innerMem]
    · simp [witnesses]
    · have hCode :=
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          innerMem child.code 3 (natCode innerConj)).mpr (by rfl)
      convert hCode using 1 <;> simp [base, witnesses, innerMem, innerConj]
    · simp [witnesses]
    · have hCode :=
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          innerConj 0 4 (natCode (textbookECode innerConj 0 4))).mpr rfl
      convert hCode using 1 <;>
        simp [TextbookDelta0Judgment.boundedExists, base, witnesses,
          innerMem, innerConj]

end YesMetaZFC.BMS.ConstructibleBridge
