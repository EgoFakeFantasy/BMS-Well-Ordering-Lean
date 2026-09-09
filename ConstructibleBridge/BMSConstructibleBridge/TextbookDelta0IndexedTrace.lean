import BMSConstructibleBridge.TextbookDelta0Trace

/-!
# `Delta0` 痕迹的有限索引图形式

对象语言不解释 Lean 的列表递归。这里把检查器等价展开为：每个有限索引处的
一行只引用严格更小索引处的行。随后可以把有限函数编码成集合图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

/-- 从任意前序开始，检查成功等价于剩余部分的逐索引局部规则。 -/
theorem checkTextbookDelta0TraceFrom_iff_indexed_l
    (previous remaining : List TextbookDelta0Judgment) :
    checkTextbookDelta0TraceFrom_l previous remaining = true ↔
      ∀ index : Fin remaining.length,
        textbookDelta0LocalRule_l (previous ++ remaining.take index.1)
          (remaining.get index) := by
  induction remaining generalizing previous with
  | nil => simp [checkTextbookDelta0TraceFrom_l]
  | cons entry remaining ih =>
      rw [checkTextbookDelta0TraceFrom_l, Bool.and_eq_true,
        decide_eq_true_eq, ih]
      constructor
      · rintro ⟨hEntry, hRemaining⟩ index
        refine Fin.cases ?_ (fun prior => ?_) index
        · simpa using hEntry
        · simpa only [Fin.val_succ, List.take_succ_cons,
            List.get_eq_getElem, List.getElem_cons_succ,
            List.append_assoc, List.singleton_append] using hRemaining prior
      · intro hRows
        refine ⟨?_, ?_⟩
        · simpa using hRows 0
        · intro index
          simpa only [Fin.val_succ, List.take_succ_cons,
            List.get_eq_getElem, List.getElem_cons_succ,
            List.append_assoc, List.singleton_append] using hRows index.succ

/-- 痕迹有效性是逐索引、只检查先前行的非递归条件。 -/
theorem textbookDelta0TraceValid_iff_indexed_l
    (trace : List TextbookDelta0Judgment) :
    TextbookDelta0TraceValid trace ↔
      ∀ index : Fin trace.length,
        textbookDelta0LocalRule_l (trace.take index.1) (trace.get index) := by
  rw [← checkTextbookDelta0Trace_iff_valid_l]
  simpa only [checkTextbookDelta0Trace_l, List.nil_append] using
    checkTextbookDelta0TraceFrom_iff_indexed_l [] trace

/-- 同一个可引用记录集合给出同一个局部规则。 -/
theorem textbookDelta0RuleOver_congr_l
    {available available' : TextbookDelta0Judgment → Prop}
    (hAvailable : ∀ entry, available entry ↔ available' entry)
    (entry : TextbookDelta0Judgment) :
    textbookDelta0RuleOver_l available entry ↔
      textbookDelta0RuleOver_l available' entry := by
  simp only [textbookDelta0RuleOver_l, hAvailable]

/-- 前缀成员恰好是在严格更小索引处出现的记录。 -/
theorem textbookDelta0Entry_mem_take_iff_l
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (entry : TextbookDelta0Judgment) :
    entry ∈ trace.take index.1 ↔
      ∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = entry := by
  constructor
  · intro hEntry
    obtain ⟨prior, hPrior⟩ := List.mem_iff_get.mp hEntry
    have hPriorIndex : prior.1 < index.1 := by
      have hBound := prior.2
      simp only [List.length_take] at hBound
      omega
    let position : Fin trace.length :=
      ⟨prior.1, hPriorIndex.trans index.2⟩
    refine ⟨position, hPriorIndex, ?_⟩
    simpa only [List.get_eq_getElem, List.getElem_take, position] using hPrior
  · rintro ⟨prior, hPrior, rfl⟩
    apply List.mem_iff_get.mpr
    refine ⟨⟨prior.1, ?_⟩, ?_⟩
    · simp only [List.length_take]
      exact lt_min hPrior prior.2
    · simp only [List.get_eq_getElem, List.getElem_take]

/-- 每一行只使用有限图中严格位于它之前的记录。 -/
def textbookDelta0IndexedRule_l {length : Nat}
    (trace : Fin length → TextbookDelta0Judgment)
    (index : Fin length) : Prop :=
  textbookDelta0RuleOver_l
    (fun entry => ∃ prior : Fin length,
      prior.1 < index.1 ∧ trace prior = entry)
    (trace index)

/-- 列表痕迹和有限图痕迹具有同一有效性。 -/
theorem textbookDelta0TraceValid_iff_indexedRule_l
    (trace : List TextbookDelta0Judgment) :
    TextbookDelta0TraceValid trace ↔
      ∀ index : Fin trace.length,
        textbookDelta0IndexedRule_l trace.get index := by
  rw [textbookDelta0TraceValid_iff_indexed_l]
  apply forall_congr'
  intro index
  exact textbookDelta0RuleOver_congr_l
    (textbookDelta0Entry_mem_take_iff_l trace index) (trace.get index)

/-- 有限图上的逐行规则推出每条记录的原始 `Delta0` 证书。 -/
theorem textbookDelta0IndexedRule_certified_l {length : Nat}
    (trace : Fin length → TextbookDelta0Judgment)
    (hTrace : ∀ index, textbookDelta0IndexedRule_l trace index)
    (index : Fin length) : (trace index).Certified := by
  have hAll : ∀ position (hPosition : position < length),
      (trace ⟨position, hPosition⟩).Certified := by
    intro position
    induction position using Nat.strong_induction_on with
    | h position ih =>
        intro hPosition
        apply textbookDelta0RuleOver_sound_l ?_
          (hTrace ⟨position, hPosition⟩)
        rintro entry ⟨prior, hPrior, rfl⟩
        exact ih prior.1 hPrior prior.2
  exact hAll index.1 index.2

/-- 原始 `Delta0` 分类等价于一份有限索引图证书。 -/
theorem textbookDelta0Judgment_certified_iff_indexedTrace_l
    (entry : TextbookDelta0Judgment) :
    entry.Certified ↔
      ∃ length, ∃ trace : Fin length → TextbookDelta0Judgment,
        (∀ index, textbookDelta0IndexedRule_l trace index) ∧
          ∃ index, trace index = entry := by
  constructor
  · intro hEntry
    obtain ⟨rows, hRows, hMember⟩ :=
      (textbookDelta0Judgment_hasTrace_iff_certified_l entry).mpr hEntry
    refine ⟨rows.length, rows.get,
      (textbookDelta0TraceValid_iff_indexedRule_l rows).mp hRows, ?_⟩
    exact List.mem_iff_get.mp hMember
  · rintro ⟨length, trace, hTrace, index, rfl⟩
    exact textbookDelta0IndexedRule_certified_l trace hTrace index

end YesMetaZFC.BMS.ConstructibleBridge
