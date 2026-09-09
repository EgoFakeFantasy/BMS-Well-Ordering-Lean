import BMSConstructibleBridge.TextbookLevyTraceGraph
import ConstructibleUniverse.SetTheory.ZFC.Constructible.BareStageHistoryBounds

/-!
# 记录分解的局部正确性

记录包含其两个中间有序对；传递载体因此已经包含格式公式所需的两个见证。
这给出真正的局部正确性，而不是从全宇宙语义直接假定小层语义。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 传递集合包含一个 Kuratowski 有序对时，也包含它的两个分量。 -/
theorem pair_components_mem_of_transitive_l {M left right : ZFSet.{u}}
    (hM : M.IsTransitive) (hPair : ZFSet.pair left right ∈ M) :
    left ∈ M ∧ right ∈ M := by
  have hUnordered : ({left, right} : ZFSet.{u}) ∈ ZFSet.pair left right := by
    simp [ZFSet.pair]
  have hUnorderedM := hM.mem_trans hUnordered hPair
  exact ⟨hM.mem_trans (by simp) hUnorderedM,
    hM.mem_trans (by simp) hUnorderedM⟩

/-- 任意传递载体中的记录分解与外部集合语义完全一致。 -/
theorem satisfiesIn_textbookLevyRecordFormula_iff_l
    {M : ZFSet.{u}} (hM : M.IsTransitive) (s : Tuple ZFSet.{u} 5)
    (hs : ∀ index, s index ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) textbookLevyRecordFormula_l s ↔
      s 0 = ZFSet.pair (ZFSet.pair (s 1) (s 2))
        (ZFSet.pair (s 3) (s 4)) := by
  change (∃ left, left ∈ M ∧ ∃ right, right ∈ M ∧
    Model.SatisfiesIn (M : Set ZFSet.{u}) textbookLevyRecordMatrix_l.toFO
      (snoc (snoc s left) right)) ↔ _
  have hMatrix (left right : ZFSet.{u}) (hLeft : left ∈ M) (hRight : right ∈ M) :
      Model.SatisfiesIn (M : Set ZFSet.{u}) textbookLevyRecordMatrix_l.toFO
        (snoc (snoc s left) right) ↔
        s 0 = ZFSet.pair left right ∧
          left = ZFSet.pair (s 1) (s 2) ∧ right = ZFSet.pair (s 3) (s 4) := by
    rw [Model.satisfiesIn_delta0_iff hM textbookLevyRecordMatrix_l _ (by
      intro index
      refine Fin.lastCases ?_ (fun prior => ?_) index
      · simpa only [snoc_last] using hRight
      · simp only [snoc_castSucc]
        refine Fin.lastCases ?_ (fun original => ?_) prior
        · simpa only [snoc_last] using hLeft
        · simpa only [snoc_castSucc] using hs original)]
    simp only [Delta0Formula.satisfies_toFO, textbookLevyRecordMatrix_l,
      Delta0Formula.Satisfies, Delta0Formula.satisfies_kuratowskiPairEqAt,
      externalSnoc_eq_finSnoc_l]
    rfl
  constructor
  · rintro ⟨left, hLeft, right, hRight, hφ⟩
    obtain ⟨hValue, hLeftValue, hRightValue⟩ := (hMatrix left right hLeft hRight).mp hφ
    simpa only [hLeftValue, hRightValue] using hValue
  · intro hValue
    have hValueM :
        ZFSet.pair (ZFSet.pair (s 1) (s 2)) (ZFSet.pair (s 3) (s 4)) ∈ M :=
      hValue ▸ hs 0
    obtain ⟨hLeft, hRight⟩ := pair_components_mem_of_transitive_l hM hValueM
    exact ⟨_, hLeft, _, hRight,
      (hMatrix _ _ hLeft hRight).mpr ⟨hValue, rfl, rfl⟩⟩

/-- 记录分解的绝对性只需要传递性，不需要该载体满足 ZF。 -/
theorem textbookLevyRecordFormula_absolute_l
    {M : ZFSet.{u}} (hM : M.IsTransitive) (s : Tuple ZFSet.{u} 5)
    (hs : ∀ index, s index ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) textbookLevyRecordFormula_l s ↔
      FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyRecordFormula_l s := by
  rw [satisfiesIn_textbookLevyRecordFormula_iff_l hM s hs,
    satisfies_textbookLevyRecordFormula_iff_l]

/-- 分量域和记录分解的合取也在每个传递载体中绝对。 -/
theorem textbookLevyRecordComponentsFormula_absolute_l
    {M : ZFSet.{u}} (hM : M.IsTransitive) (s : Tuple ZFSet.{u} 6)
    (hs : ∀ index, s index ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) textbookLevyRecordComponentsFormula_l s ↔
      FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyRecordComponentsFormula_l s := by
  simp only [textbookLevyRecordComponentsFormula_l, Model.SatisfiesIn, FOFormula.Satisfies]
  rw [Model.satisfiesIn_delta0_iff hM textbookLevyRecordDomain_l s hs,
    Model.satisfiesIn_rename, FOFormula.satisfies_rename]
  exact and_congr Iff.rfl (textbookLevyRecordFormula_absolute_l hM _
    (fun index => hs index.succ))

/-- 任意传递载体中的规范记录自动带有全部四个字段。 -/
theorem textbookLevyRecord_fields_mem_l {M : ZFSet.{u}} (hM : M.IsTransitive)
    (entry : TextbookLevyJudgment) (hEntry : textbookLevyRecordZF_l entry ∈ M) :
    natCode (textbookLevyPolarityCode_l entry.isSigma) ∈ M ∧
      natCode entry.level ∈ M ∧ natCode entry.arity ∈ M ∧ natCode entry.code ∈ M := by
  obtain ⟨hLeft, hRight⟩ := pair_components_mem_of_transitive_l hM hEntry
  obtain ⟨hPolarity, hLevel⟩ := pair_components_mem_of_transitive_l hM hLeft
  obtain ⟨hArity, hCode⟩ := pair_components_mem_of_transitive_l hM hRight
  exact ⟨hPolarity, hLevel, hArity, hCode⟩

/--
只要载体传递且含标准 omega，完整记录格式公式就具有精确的局部解码语义。
这里不要求全公式初等性，也不要求集合论 Replacement。
-/
theorem satisfiesIn_textbookLevyRecordValidityFormula_iff_l
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hω : Ordinal.omega0.toZFSet ∈ M) (value : ZFSet.{u}) (hValue : value ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) textbookLevyRecordValidityFormula_l
      ![Ordinal.omega0.toZFSet, value] ↔
      ∃ entry : TextbookLevyJudgment, value = textbookLevyRecordZF_l entry := by
  rw [textbookLevyRecordValidityFormula_l, satisfiesIn_externalExistentialClosure_l]
  have hAssignment (fields : Tuple ZFSet.{u} 4) (hFields : ∀ index, fields index ∈ M) :
      ∀ index : Fin 6, (Fin.append ![Ordinal.omega0.toZFSet, value] fields) index ∈ M := by
    intro index
    refine Fin.addCases (m := 2) (n := 4) ?_ (fun prior => ?_) index
    · intro prior
      fin_cases prior
      · exact hω
      · exact hValue
    · simpa using hFields prior
  constructor
  · rintro ⟨fields, hFields, hφ⟩
    have hAmbient := (textbookLevyRecordComponentsFormula_absolute_l hM _
      (hAssignment fields hFields)).mp hφ
    rw [textbookLevyRecordAssignment_l,
      satisfies_textbookLevyRecordComponentsFormula_iff_l] at hAmbient
    obtain ⟨entry, _, _, _, _, hEntry⟩ := hAmbient
    exact ⟨entry, hEntry⟩
  · rintro ⟨entry, hEntry⟩
    have hEntryM : textbookLevyRecordZF_l entry ∈ M := hEntry ▸ hValue
    obtain ⟨hPolarity, hLevel, hArity, hCode⟩ :=
      textbookLevyRecord_fields_mem_l hM entry hEntryM
    let fields : Tuple ZFSet.{u} 4 :=
      ![natCode (textbookLevyPolarityCode_l entry.isSigma), natCode entry.level,
        natCode entry.arity, natCode entry.code]
    have hFields : ∀ index, fields index ∈ M := by
      intro index
      fin_cases index
      · exact hPolarity
      · exact hLevel
      · exact hArity
      · exact hCode
    refine ⟨fields, hFields, ?_⟩
    apply (textbookLevyRecordComponentsFormula_absolute_l hM _
      (hAssignment fields hFields)).mpr
    rw [textbookLevyRecordAssignment_l,
      satisfies_textbookLevyRecordComponentsFormula_iff_l]
    exact ⟨entry, rfl, rfl, rfl, rfl, hEntry⟩

/-- 特别地，每个越过 omega 的可构造层都正确识别记录格式。 -/
theorem satisfiesIn_textbookLevyRecordValidityFormula_stage_iff_l
    {θ : Ordinal.{u}} (hθ : Ordinal.omega0 < θ) (value : StageCarrier θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u}) textbookLevyRecordValidityFormula_l
      ![Ordinal.omega0.toZFSet, value.1] ↔
      ∃ entry : TextbookLevyJudgment, value.1 = textbookLevyRecordZF_l entry :=
  satisfiesIn_textbookLevyRecordValidityFormula_iff_l (LStageZF_isTransitive θ)
    (ordinal_toZFSet_mem_LStageZF_of_lt hθ) value.1 value.2

end YesMetaZFC.BMS.ConstructibleBridge
