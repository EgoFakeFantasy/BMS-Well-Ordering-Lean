import BMSConstructibleBridge.TextbookDelta0IndexedTrace
import BMSConstructibleBridge.ExternalExistentialClosure
import ConstructibleUniverse.SetTheory.ZFC.Constructible.IndexedSequenceValidity
import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookNaturalArithmeticLCarrier

/-!
# `Delta0` 痕迹记录的集合编码

一行记录编码为 `⟨元数, 公式码⟩`。格式公式只识别两个标准自然数字段；推导
有效性仍由后续严格前驱图公式检查。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF
open Logic FirstOrder StabilityFrame

/-- 一条 `Delta0` 分类记录的规范集合编码。 -/
noncomputable def textbookDelta0RecordZF_l
    (entry : TextbookDelta0Judgment) : ZFSet.{u} :=
  ZFSet.pair (natCode entry.arity) (natCode entry.code)

/-- 不同记录具有不同集合编码。 -/
theorem textbookDelta0RecordZF_injective_l :
    Function.Injective
      (textbookDelta0RecordZF_l : TextbookDelta0Judgment → ZFSet.{u}) := by
  rintro ⟨leftArity, leftCode⟩ ⟨rightArity, rightCode⟩ hEqual
  obtain ⟨hArity, hCode⟩ := ZFSet.pair_inj.mp hEqual
  have hArity' := natCode_injective hArity
  have hCode' := natCode_injective hCode
  cases hArity'
  cases hCode'
  rfl

/-- 每条规范记录都属于可构造宇宙。 -/
theorem textbookDelta0RecordZF_mem_L_l (entry : TextbookDelta0Judgment) :
    textbookDelta0RecordZF_l entry ∈ L :=
  orderedPair_mem_L (natCode_mem_L _) (natCode_mem_L _)

/-- 整份有限痕迹使用规范有限索引图编码。 -/
noncomputable def textbookDelta0TraceZF_l
    (trace : List TextbookDelta0Judgment) : ZFSet.{u} :=
  IndexedSequenceZF.sequenceCode (trace.map textbookDelta0RecordZF_l)

/-- 有限痕迹图的集合编码是单射。 -/
theorem textbookDelta0TraceZF_injective_l :
    Function.Injective
      (textbookDelta0TraceZF_l : List TextbookDelta0Judgment → ZFSet.{u}) := by
  intro left right hEqual
  apply List.map_injective_iff.mpr textbookDelta0RecordZF_injective_l
  exact IndexedSequenceZF.sequenceCode_injective hEqual

/-- 每份规范有限痕迹图都属于可构造宇宙。 -/
theorem textbookDelta0TraceZF_mem_L_l
    (trace : List TextbookDelta0Judgment) :
    textbookDelta0TraceZF_l trace ∈ L := by
  apply IndexedSequenceZF.sequenceCode_mem_L
  intro value hValue
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hValue
  exact textbookDelta0RecordZF_mem_L_l entry

/-- 记录分解的有界矩阵；坐标为 `[记录, 元数, 码]`。 -/
def textbookDelta0RecordMatrix_l : Delta0Formula 3 :=
  Delta0Formula.kuratowskiPairEqAt 0 1 2

/-- 字段域与记录格式；坐标为 `[omega, 记录, 元数, 码]`。 -/
def textbookDelta0RecordComponents_l : Delta0Formula 4 :=
  .conj (.mem 2 0) <|
    .conj (.mem 3 0) <|
      Delta0Formula.kuratowskiPairEqAt 1 2 3

/-- 两个字段为标准自然数时，格式公式精确识别规范记录。 -/
theorem satisfies_textbookDelta0RecordComponents_iff_l
    (value arity code : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        textbookDelta0RecordComponents_l
        ![Ordinal.omega0.toZFSet, value, arity, code] ↔
      ∃ entry : TextbookDelta0Judgment,
        arity = natCode entry.arity ∧ code = natCode entry.code ∧
          value = textbookDelta0RecordZF_l entry := by
  simp only [textbookDelta0RecordComponents_l,
    Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  change (arity ∈ Ordinal.omega0.toZFSet ∧
      code ∈ Ordinal.omega0.toZFSet ∧
      value = ZFSet.pair arity code) ↔ _
  simp only [IndexedSequenceZF.mem_omega_iff_exists_natCode]
  constructor
  · rintro ⟨⟨arityCode, rfl⟩, ⟨codeCode, rfl⟩, hValue⟩
    exact ⟨⟨arityCode, codeCode⟩, rfl, rfl, hValue⟩
  · rintro ⟨entry, rfl, rfl, rfl⟩
    exact ⟨⟨entry.arity, rfl⟩, ⟨entry.code, rfl⟩, rfl⟩

/-- 识别一条记录的二元公式；元数和码在内部存在量化。 -/
def textbookDelta0RecordValidityFormula_l : FOFormula 2 :=
  .ex (.ex textbookDelta0RecordComponents_l.toFO)

/-- 两次追加后的赋值坐标。 -/
theorem textbookDelta0RecordAssignment_l {Carrier : Type u}
    (omega value arity code : Carrier) :
    snoc (snoc ![omega, value] arity) code =
      ![omega, value, arity, code] := by
  funext index
  fin_cases index <;> rfl

/-- 格式公式恰好识别规范 `Delta0` 记录。 -/
theorem satisfies_textbookDelta0RecordValidityFormula_iff_l
    (value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0RecordValidityFormula_l
        ![Ordinal.omega0.toZFSet, value] ↔
      ∃ entry : TextbookDelta0Judgment,
        value = textbookDelta0RecordZF_l entry := by
  simp only [textbookDelta0RecordValidityFormula_l, FOFormula.Satisfies]
  change (∃ arity code,
    Delta0Formula.Satisfies Delta0Formula.ZFMem
      textbookDelta0RecordComponents_l
      (snoc (snoc ![Ordinal.omega0.toZFSet, value] arity) code)) ↔ _
  simp only [textbookDelta0RecordAssignment_l,
    satisfies_textbookDelta0RecordComponents_iff_l]
  constructor
  · rintro ⟨arity, code, entry, _, _, hValue⟩
    exact ⟨entry, hValue⟩
  · rintro ⟨entry, rfl⟩
    exact ⟨natCode entry.arity, natCode entry.code,
      entry, rfl, rfl, rfl⟩

/-- 记录格式公式属于最低有限 `Sigma` 层。 -/
theorem textbookDelta0RecordValidityFormula_isSigmaFinite_l
    (level : Nat) :
    FirstOrder.Formula.IsSigmaFinite membershipLevyBound level
      (translateExternalFormula textbookDelta0RecordValidityFormula_l) := by
  exact .existsE _ (.existsE _ (.delta0
    (translateExternalDelta0_isDelta0_l textbookDelta0RecordComponents_l)))

/-- 格式正确的集合码具有唯一解码记录。 -/
theorem textbookDelta0RecordValidity_unique_l (value : ZFSet.{u})
    (hValue : FOFormula.Satisfies Delta0Formula.ZFMem
      textbookDelta0RecordValidityFormula_l
      ![Ordinal.omega0.toZFSet, value]) :
    ∃! entry : TextbookDelta0Judgment,
      value = textbookDelta0RecordZF_l entry := by
  obtain ⟨entry, hEntry⟩ :=
    (satisfies_textbookDelta0RecordValidityFormula_iff_l value).mp hValue
  refine ⟨entry, hEntry, ?_⟩
  intro other hOther
  exact textbookDelta0RecordZF_injective_l (hOther.symm.trans hEntry)

end YesMetaZFC.BMS.ConstructibleBridge
