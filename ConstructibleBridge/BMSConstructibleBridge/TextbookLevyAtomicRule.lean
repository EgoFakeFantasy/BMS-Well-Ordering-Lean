import BMSConstructibleBridge.TextbookLevyTraceBounds

/-!
# 原子分类规则的成员语言公式

有限分类器的第一条规则允许成员和等号原子。公式显式要求两个变量索引属于
记录元数，并以规范 E 构造器码检查标签零或一。记录的极性和层级不受限制，
这与两类原子均属于每个累积有限层完全一致。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF
open Logic FirstOrder StabilityFrame

/--
原子规则矩阵。坐标布局为
`[omega, graph, position, polarity, level, arity, code, left, right, tag]`。
图和位置由其他四条规则共用，在本分支中不读取。
-/
def textbookLevyAtomicRuleBody_l : FOFormula 10 :=
  .conj (.mem 7 0) <|
  .conj (.mem 8 0) <|
  .conj
    (FOFormula.disj
      (Delta0Formula.natLiteralDeltaAt 0 (9 : Fin 10)).toFO
      (Delta0Formula.natLiteralDeltaAt 1 (9 : Fin 10)).toFO) <|
  .conj
    (TextbookNatFormula.textbookECodeFormulaAt 0 7 8 9 6) <|
  .conj (.mem 7 5) (.mem 8 5)

/-- 关闭 `left`、`right`、`tag` 三个内部见证。 -/
def textbookLevyAtomicRuleFormula_l : FOFormula 7 :=
  .ex (.ex (.ex textbookLevyAtomicRuleBody_l))

/-- 三个见证追加后的赋值坐标。 -/
theorem textbookLevyAtomicRuleAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 7) (left right tag : Carrier) :
    snoc (snoc (snoc base left) right) tag =
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        left, right, tag] := by
  funext index
  fin_cases index <;> rfl

/-- 在规范自然数字段上，原子规则公式精确对应元层局部规则的原子分支。 -/
theorem satisfies_textbookLevyAtomicRuleFormula_iff_l
    (graph position : ZFSet.{u}) (entry : TextbookLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyAtomicRuleFormula_l
      ![Ordinal.omega0.toZFSet, graph, position,
        natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ left right : Fin entry.arity,
        entry.code = textbookECode left.1 right.1 0 ∨
          entry.code = textbookECode left.1 right.1 1 := by
  simp only [textbookLevyAtomicRuleFormula_l, FOFormula.Satisfies]
  let base : Tuple ZFSet.{u} 7 :=
    ![Ordinal.omega0.toZFSet, graph, position,
      natCode (textbookLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  change (∃ left right tag,
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyAtomicRuleBody_l
      (snoc (snoc (snoc base left) right) tag)) ↔ _
  simp only [textbookLevyAtomicRuleAssignment_l]
  simp only [textbookLevyAtomicRuleBody_l, FOFormula.Satisfies,
    FOFormula.satisfies_disj,
    Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
    TextbookNatFormula.satisfies_textbookECodeFormulaAt]
  constructor
  · rintro ⟨leftSet, rightSet, tagSet,
      hLeftOmega, hRightOmega, hTag, hCode, hLeft, hRight⟩
    obtain ⟨left, rfl⟩ :=
      (IndexedSequenceZF.mem_omega_iff_exists_natCode leftSet).mp hLeftOmega
    obtain ⟨right, rfl⟩ :=
      (IndexedSequenceZF.mem_omega_iff_exists_natCode rightSet).mp hRightOmega
    have hLeftBound : left < entry.arity := (natCode_mem_natCode_iff _ _).mp hLeft
    have hRightBound : right < entry.arity := (natCode_mem_natCode_iff _ _).mp hRight
    let leftIndex : Fin entry.arity := ⟨left, hLeftBound⟩
    let rightIndex : Fin entry.arity := ⟨right, hRightBound⟩
    rcases hTag with hTag | hTag
    · change tagSet = natCode 0 at hTag
      subst tagSet
      have hCodeCanonical :
          FOFormula.Satisfies Delta0Formula.ZFMem
            TextbookNatFormula.textbookECodeFormula
            ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode left, natCode right,
              natCode 0, natCode entry.code] := by
        simpa [base] using hCode
      have hCode' : (natCode entry.code : ZFSet.{u}) =
          natCode (textbookECode left right 0) :=
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          left right 0 (natCode entry.code)).mp hCodeCanonical
      exact ⟨leftIndex, rightIndex, Or.inl (natCode_injective hCode')⟩
    · change tagSet = natCode 1 at hTag
      subst tagSet
      have hCodeCanonical :
          FOFormula.Satisfies Delta0Formula.ZFMem
            TextbookNatFormula.textbookECodeFormula
            ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode left, natCode right,
              natCode 1, natCode entry.code] := by
        simpa [base] using hCode
      have hCode' : (natCode entry.code : ZFSet.{u}) =
          natCode (textbookECode left right 1) :=
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          left right 1 (natCode entry.code)).mp hCodeCanonical
      exact ⟨leftIndex, rightIndex, Or.inr (natCode_injective hCode')⟩
  · rintro ⟨left, right, hCode | hCode⟩
    · refine ⟨natCode left.1, natCode right.1, natCode 0,
        ?_, ?_, Or.inl rfl, ?_, ?_, ?_⟩
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨left.1, rfl⟩
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨right.1, rfl⟩
      · apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          left.1 right.1 0 (natCode entry.code)).mpr
        rw [hCode]
      · exact (natCode_mem_natCode_iff _ _).mpr left.2
      · exact (natCode_mem_natCode_iff _ _).mpr right.2
    · refine ⟨natCode left.1, natCode right.1, natCode 1,
        ?_, ?_, Or.inr rfl, ?_, ?_, ?_⟩
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨left.1, rfl⟩
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr ⟨right.1, rfl⟩
      · apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          left.1 right.1 1 (natCode entry.code)).mpr
        rw [hCode]
      · exact (natCode_mem_natCode_iff _ _).mpr left.2
      · exact (natCode_mem_natCode_iff _ _).mpr right.2

end YesMetaZFC.BMS.ConstructibleBridge
