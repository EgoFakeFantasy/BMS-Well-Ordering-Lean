import BMSConstructibleBridge.TextbookLevyIndexedTrace
import BMSConstructibleBridge.ExternalDelta0Translation
import BMSConstructibleBridge.ExternalExistentialClosure
import ConstructibleUniverse.SetTheory.ZFC.Constructible.IndexedSequenceValidity
import ConstructibleUniverse.SetTheory.ZFC.Constructible.TextbookNaturalArithmeticLCarrier

/-!
# 分类记录的集合编码与成员语言识别

一条记录编码为 `⟨⟨极性, 层级⟩, ⟨元数, 公式码⟩⟩`，四个分量均为有限
von Neumann 序数。此处只识别记录的格式，不把格式正确冒充为推导有效。
推导规则还须使用前序模块中的严格前驱索引条件。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open FiniteSequenceZF
open Logic FirstOrder StabilityFrame

/-- 极性以零和一编码，不接受其他自然数。 -/
def textbookLevyPolarityCode_l (isSigma : Bool) : Nat :=
  if isSigma then 1 else 0

/-- 极性自然数编码是单射。 -/
theorem textbookLevyPolarityCode_injective_l :
    Function.Injective textbookLevyPolarityCode_l := by
  intro left right hEqual
  cases left <;> cases right <;> simp_all [textbookLevyPolarityCode_l]

@[simp] theorem textbookLevyPolarityCode_eq_zero_iff_l (isSigma : Bool) :
    textbookLevyPolarityCode_l isSigma = 0 ↔ isSigma = false := by
  cases isSigma <;> simp [textbookLevyPolarityCode_l]

@[simp] theorem textbookLevyPolarityCode_eq_one_iff_l (isSigma : Bool) :
    textbookLevyPolarityCode_l isSigma = 1 ↔ isSigma = true := by
  cases isSigma <;> simp [textbookLevyPolarityCode_l]

/-- 一条分类记录的规范集合编码。 -/
noncomputable def textbookLevyRecordZF_l (entry : TextbookLevyJudgment) : ZFSet.{u} :=
  ZFSet.pair
    (ZFSet.pair (natCode (textbookLevyPolarityCode_l entry.isSigma))
      (natCode entry.level))
    (ZFSet.pair (natCode entry.arity) (natCode entry.code))

/-- 集合编码没有把不同记录合并。 -/
theorem textbookLevyRecordZF_injective_l :
    Function.Injective (textbookLevyRecordZF_l : TextbookLevyJudgment → ZFSet.{u}) := by
  rintro ⟨leftPolarity, leftLevel, leftArity, leftCode⟩
    ⟨rightPolarity, rightLevel, rightArity, rightCode⟩ hEqual
  obtain ⟨hLeft, hRight⟩ := ZFSet.pair_inj.mp hEqual
  obtain ⟨hPolarity, hLevel⟩ := ZFSet.pair_inj.mp hLeft
  obtain ⟨hArity, hCode⟩ := ZFSet.pair_inj.mp hRight
  have hPolarity' := textbookLevyPolarityCode_injective_l (natCode_injective hPolarity)
  have hLevel' := natCode_injective hLevel
  have hArity' := natCode_injective hArity
  have hCode' := natCode_injective hCode
  cases hPolarity'
  cases hLevel'
  cases hArity'
  cases hCode'
  rfl

/-- 每条规范记录都属于可构造宇宙。 -/
theorem textbookLevyRecordZF_mem_L_l (entry : TextbookLevyJudgment) :
    textbookLevyRecordZF_l entry ∈ L :=
  orderedPair_mem_L
    (orderedPair_mem_L (natCode_mem_L _) (natCode_mem_L _))
    (orderedPair_mem_L (natCode_mem_L _) (natCode_mem_L _))

/-- 整份有限记录使用既有的有限索引图编码。 -/
noncomputable def textbookLevyTraceZF_l (trace : List TextbookLevyJudgment) : ZFSet.{u} :=
  IndexedSequenceZF.sequenceCode (trace.map textbookLevyRecordZF_l)

/-- 有限记录图同样具有无歧义的编码。 -/
theorem textbookLevyTraceZF_injective_l :
    Function.Injective (textbookLevyTraceZF_l : List TextbookLevyJudgment → ZFSet.{u}) := by
  intro left right hEqual
  apply List.map_injective_iff.mpr textbookLevyRecordZF_injective_l
  exact IndexedSequenceZF.sequenceCode_injective hEqual

/-- 规范的有限记录图本身属于 L。 -/
theorem textbookLevyTraceZF_mem_L_l (trace : List TextbookLevyJudgment) :
    textbookLevyTraceZF_l trace ∈ L := by
  apply IndexedSequenceZF.sequenceCode_mem_L
  intro value hValue
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hValue
  exact textbookLevyRecordZF_mem_L_l entry

/-- 记录分解的有界矩阵；坐标为 `[记录, 极性, 层级, 元数, 码, 左对, 右对]`。 -/
def textbookLevyRecordMatrix_l : Delta0Formula 7 :=
  .conj (Delta0Formula.kuratowskiPairEqAt 0 5 6)
    (.conj (Delta0Formula.kuratowskiPairEqAt 5 1 2)
      (Delta0Formula.kuratowskiPairEqAt 6 3 4))

/-- 记录的五元分解公式，仅存在量化两个中间有序对。 -/
def textbookLevyRecordFormula_l : FOFormula 5 :=
  .ex (.ex textbookLevyRecordMatrix_l.toFO)

/-- 记录分解公式在任意原始集合赋值上的精确语义。 -/
theorem satisfies_textbookLevyRecordFormula_iff_l (s : Tuple ZFSet.{u} 5) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyRecordFormula_l s ↔
      s 0 = ZFSet.pair (ZFSet.pair (s 1) (s 2))
        (ZFSet.pair (s 3) (s 4)) := by
  simp only [textbookLevyRecordFormula_l, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO, textbookLevyRecordMatrix_l,
    Delta0Formula.Satisfies, Delta0Formula.satisfies_kuratowskiPairEqAt,
    externalSnoc_eq_finSnoc_l]
  change (∃ left right, s 0 = ZFSet.pair left right ∧
    left = ZFSet.pair (s 1) (s 2) ∧ right = ZFSet.pair (s 3) (s 4)) ↔ _
  constructor
  · rintro ⟨left, right, hRecord, hLeft, hRight⟩
    simpa only [hLeft, hRight] using hRecord
  · intro hRecord
    exact ⟨ZFSet.pair (s 1) (s 2), ZFSet.pair (s 3) (s 4), hRecord, rfl, rfl⟩

/-- 分解公式具有显式的最低有限 Sigma 证书。 -/
theorem textbookLevyRecordFormula_isSigmaFinite_l (level : Nat) :
    FirstOrder.Formula.IsSigmaFinite membershipLevyBound level
      (translateExternalFormula textbookLevyRecordFormula_l) :=
  .existsE _ (.existsE _ (.delta0
    (translateExternalDelta0_isDelta0_l textbookLevyRecordMatrix_l)))

/-- 记录分量的合法域；坐标为 `[omega, 记录, 极性, 层级, 元数, 码]`。 -/
def textbookLevyRecordDomain_l : Delta0Formula 6 :=
  .conj
    (Delta0Formula.disj (Delta0Formula.natLiteralDeltaAt 0 2)
      (Delta0Formula.natLiteralDeltaAt 1 2))
    (.conj (.mem 3 0) (.conj (.mem 4 0) (.mem 5 0)))

/-- 同时要求规范字段域和有序对格式，不判断公式的分类是否有效。 -/
def textbookLevyRecordComponentsFormula_l : FOFormula 6 :=
  .conj textbookLevyRecordDomain_l.toFO
    (FOFormula.rename (fun index : Fin 5 => index.succ) textbookLevyRecordFormula_l)

/-- 四字段都有规范自然数含义时，格式公式与集合编码精确一致。 -/
theorem satisfies_textbookLevyRecordComponentsFormula_iff_l
    (value polarity level arity code : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyRecordComponentsFormula_l
      ![Ordinal.omega0.toZFSet, value, polarity, level, arity, code] ↔
      ∃ entry : TextbookLevyJudgment,
        polarity = natCode (textbookLevyPolarityCode_l entry.isSigma) ∧
        level = natCode entry.level ∧ arity = natCode entry.arity ∧
        code = natCode entry.code ∧ value = textbookLevyRecordZF_l entry := by
  simp only [textbookLevyRecordComponentsFormula_l, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO, textbookLevyRecordDomain_l,
    Delta0Formula.Satisfies, Delta0Formula.satisfies_disj,
    Delta0Formula.satisfies_natLiteralDeltaAt, FOFormula.satisfies_rename,
    satisfies_textbookLevyRecordFormula_iff_l]
  change ((polarity = natCode 0 ∨ polarity = natCode 1) ∧
      level ∈ Ordinal.omega0.toZFSet ∧ arity ∈ Ordinal.omega0.toZFSet ∧
      code ∈ Ordinal.omega0.toZFSet) ∧
    value = ZFSet.pair (ZFSet.pair polarity level) (ZFSet.pair arity code) ↔ _
  simp only [IndexedSequenceZF.mem_omega_iff_exists_natCode]
  constructor
  · rintro ⟨⟨hPolarity, ⟨n, rfl⟩, ⟨a, rfl⟩, ⟨c, rfl⟩⟩, hValue⟩
    rcases hPolarity with rfl | rfl
    · exact ⟨⟨false, n, a, c⟩, rfl, rfl, rfl, rfl, hValue⟩
    · exact ⟨⟨true, n, a, c⟩, rfl, rfl, rfl, rfl, hValue⟩
  · rintro ⟨entry, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨⟨?_, ⟨entry.level, rfl⟩, ⟨entry.arity, rfl⟩,
      ⟨entry.code, rfl⟩⟩, rfl⟩
    cases entry.isSigma
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- 识别一条记录的二元公式；四个字段均在内部存在量化。 -/
def textbookLevyRecordValidityFormula_l : FOFormula 2 :=
  externalExistentialClosure_l 4 textbookLevyRecordComponentsFormula_l

/-- 追加四字段后的赋值与显式六元赋值相同。 -/
theorem textbookLevyRecordAssignment_l {Carrier : Type u}
    (omega value : Carrier) (fields : Tuple Carrier 4) :
    Fin.append ![omega, value] fields =
      ![omega, value, fields 0, fields 1, fields 2, fields 3] := by
  funext index
  fin_cases index <;> rfl

/-- 格式公式恰好识别规范记录，任意接受值都可解码。 -/
theorem satisfies_textbookLevyRecordValidityFormula_iff_l (value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyRecordValidityFormula_l
      ![Ordinal.omega0.toZFSet, value] ↔
      ∃ entry : TextbookLevyJudgment, value = textbookLevyRecordZF_l entry := by
  rw [textbookLevyRecordValidityFormula_l, satisfies_externalExistentialClosure_l]
  simp only [textbookLevyRecordAssignment_l,
    satisfies_textbookLevyRecordComponentsFormula_iff_l]
  constructor
  · rintro ⟨fields, entry, _, _, _, _, hValue⟩
    exact ⟨entry, hValue⟩
  · rintro ⟨entry, rfl⟩
    exact ⟨![natCode (textbookLevyPolarityCode_l entry.isSigma), natCode entry.level,
      natCode entry.arity, natCode entry.code], entry, rfl, rfl, rfl, rfl, rfl⟩

/-- 四字段格式公式的最低有限 Sigma 复杂度。 -/
theorem textbookLevyRecordComponentsFormula_isSigmaFinite_l (level : Nat) :
    FirstOrder.Formula.IsSigmaFinite membershipLevyBound level
      (translateExternalFormula textbookLevyRecordComponentsFormula_l) := by
  apply FirstOrder.Formula.IsSigmaFinite.conj
  · exact .delta0 (translateExternalDelta0_isDelta0_l _)
  · change FirstOrder.Formula.IsSigmaFinite membershipLevyBound level
      (.existsE _ (.existsE _ (translateExternalFormula
        (FOFormula.rename (FOFormula.liftRename (FOFormula.liftRename Fin.succ))
          textbookLevyRecordMatrix_l.toFO))))
    apply FirstOrder.Formula.IsSigmaFinite.existsE
    apply FirstOrder.Formula.IsSigmaFinite.existsE
    rw [← externalDelta0_toFO_rename_l]
    exact .delta0 (translateExternalDelta0_isDelta0_l _)

/-- 记录格式的存在闭包仍保持最低有限 Sigma 复杂度。 -/
theorem textbookLevyRecordValidityFormula_isSigmaFinite_l (level : Nat) :
    FirstOrder.Formula.IsSigmaFinite membershipLevyBound level
      (translateExternalFormula textbookLevyRecordValidityFormula_l) :=
  translateExternalExistentialClosure_isSigmaFinite_l 4 _
    (textbookLevyRecordComponentsFormula_isSigmaFinite_l level)

/-- 格式正确的集合码有且只有一个解码记录。 -/
theorem textbookLevyRecordValidity_unique_l (value : ZFSet.{u})
    (hValue : FOFormula.Satisfies Delta0Formula.ZFMem
      textbookLevyRecordValidityFormula_l ![Ordinal.omega0.toZFSet, value]) :
    ∃! entry : TextbookLevyJudgment, value = textbookLevyRecordZF_l entry := by
  obtain ⟨entry, hEntry⟩ := (satisfies_textbookLevyRecordValidityFormula_iff_l value).mp hValue
  refine ⟨entry, hEntry, ?_⟩
  intro other hOther
  exact textbookLevyRecordZF_injective_l (hOther.symm.trans hEntry)

end YesMetaZFC.BMS.ConstructibleBridge
