import BMSConstructibleBridge.TextbookDelta0TraceGraph

/-!
# `Delta0` 原子分类规则的成员语言公式

公式检查两个变量索引属于记录元数，并验证规范 E 构造器标签为成员或等号。
图和当前位置参数由其他局部规则共用，本分支不读取它们。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF
open Logic FirstOrder StabilityFrame

/--
原子规则矩阵。坐标为
`[omega, graph, position, arity, code, left, right, tag]`。
-/
def textbookDelta0AtomicRuleBody_l : FOFormula 8 :=
  .conj (.mem 5 0) <|
  .conj (.mem 6 0) <|
  .conj
    (FOFormula.disj
      (Delta0Formula.natLiteralDeltaAt 0 (7 : Fin 8)).toFO
      (Delta0Formula.natLiteralDeltaAt 1 (7 : Fin 8)).toFO) <|
  .conj
    (TextbookNatFormula.textbookECodeFormulaAt 0 5 6 7 4) <|
  .conj (.mem 5 3) (.mem 6 3)

/-- 关闭三个内部自然数见证。 -/
def textbookDelta0AtomicRuleFormula_l : FOFormula 5 :=
  .ex (.ex (.ex textbookDelta0AtomicRuleBody_l))

/-- 三次追加后的赋值坐标。 -/
theorem textbookDelta0AtomicRuleAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 5) (left right tag : Carrier) :
    snoc (snoc (snoc base left) right) tag =
      ![base 0, base 1, base 2, base 3, base 4, left, right, tag] := by
  funext index
  fin_cases index <;> rfl

/-- 在规范自然数字段上，原子公式精确对应元层原子规则。 -/
theorem satisfies_textbookDelta0AtomicRuleFormula_iff_l
    (graph position : ZFSet.{u}) (entry : TextbookDelta0Judgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0AtomicRuleFormula_l
        ![Ordinal.omega0.toZFSet, graph, position,
          natCode entry.arity, natCode entry.code] ↔
      ∃ left right : Fin entry.arity,
        entry.code = textbookECode left.1 right.1 0 ∨
          entry.code = textbookECode left.1 right.1 1 := by
  simp only [textbookDelta0AtomicRuleFormula_l, FOFormula.Satisfies]
  let base : Tuple ZFSet.{u} 5 :=
    ![Ordinal.omega0.toZFSet, graph, position,
      natCode entry.arity, natCode entry.code]
  change (∃ left right tag,
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookDelta0AtomicRuleBody_l
      (snoc (snoc (snoc base left) right) tag)) ↔ _
  simp only [textbookDelta0AtomicRuleAssignment_l]
  simp only [textbookDelta0AtomicRuleBody_l, FOFormula.Satisfies,
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
    have hLeftBound : left < entry.arity :=
      (natCode_mem_natCode_iff _ _).mp hLeft
    have hRightBound : right < entry.arity :=
      (natCode_mem_natCode_iff _ _).mp hRight
    let leftIndex : Fin entry.arity := ⟨left, hLeftBound⟩
    let rightIndex : Fin entry.arity := ⟨right, hRightBound⟩
    rcases hTag with hTag | hTag
    · change tagSet = natCode 0 at hTag
      subst tagSet
      have hCodeCanonical :
          FOFormula.Satisfies Delta0Formula.ZFMem
            TextbookNatFormula.textbookECodeFormula
            ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
              natCode left, natCode right, natCode 0,
              natCode entry.code] := by
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
            ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
              natCode left, natCode right, natCode 1,
              natCode entry.code] := by
        simpa [base] using hCode
      have hCode' : (natCode entry.code : ZFSet.{u}) =
          natCode (textbookECode left right 1) :=
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          left right 1 (natCode entry.code)).mp hCodeCanonical
      exact ⟨leftIndex, rightIndex, Or.inr (natCode_injective hCode')⟩
  · rintro ⟨left, right, hCode | hCode⟩
    · refine ⟨natCode left.1, natCode right.1, natCode 0,
        ?_, ?_, Or.inl rfl, ?_, ?_, ?_⟩
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
          ⟨left.1, rfl⟩
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
          ⟨right.1, rfl⟩
      · apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          left.1 right.1 0 (natCode entry.code)).mpr
        rw [hCode]
      · exact (natCode_mem_natCode_iff _ _).mpr left.2
      · exact (natCode_mem_natCode_iff _ _).mpr right.2
    · refine ⟨natCode left.1, natCode right.1, natCode 1,
        ?_, ?_, Or.inr rfl, ?_, ?_, ?_⟩
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
          ⟨left.1, rfl⟩
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
          ⟨right.1, rfl⟩
      · apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          left.1 right.1 1 (natCode entry.code)).mpr
        rw [hCode]
      · exact (natCode_mem_natCode_iff _ _).mpr left.2
      · exact (natCode_mem_natCode_iff _ _).mpr right.2

end YesMetaZFC.BMS.ConstructibleBridge
