import BMSConstructibleBridge.TextbookBoundedLevyTrace

/-!
# 用有限索引代替递归检查

对象语言不能直接调用 Lean 的列表检查器。本模块把整个检查等价地展开为
“每个有限索引处的一行，只引用严格更小的索引”。后续集合编码只需实现这个
有界索引条件，不再内部化 Lean 的递归求值过程。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

/-- 从给定前序开始，检查成功等价于每个位置的局部规则。 -/
theorem checkTextbookBoundedLevyTraceFrom_iff_indexed_l
    (previous remaining : List TextbookBoundedLevyJudgment) :
    checkTextbookBoundedLevyTraceFrom_l previous remaining = true ↔
      ∀ index : Fin remaining.length,
        textbookBoundedLevyLocalRule_l (previous ++ remaining.take index.1)
          (remaining.get index) := by
  induction remaining generalizing previous with
  | nil => simp [checkTextbookBoundedLevyTraceFrom_l]
  | cons entry remaining ih =>
      rw [checkTextbookBoundedLevyTraceFrom_l, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ⟨hEntry, hRemaining⟩ index
        refine Fin.cases ?_ (fun prior => ?_) index
        · simpa using hEntry
        · simpa only [Fin.val_succ, List.take_succ_cons, List.get_eq_getElem,
            List.getElem_cons_succ,
            List.append_assoc, List.singleton_append] using hRemaining prior
      · intro hRows
        refine ⟨?_, ?_⟩
        · simpa using hRows 0
        · intro index
          simpa only [Fin.val_succ, List.take_succ_cons, List.get_eq_getElem,
            List.getElem_cons_succ,
            List.append_assoc, List.singleton_append] using hRows index.succ

/-- 整份证书的有效性是逐索引、只检查先前行的非递归条件。 -/
theorem textbookBoundedLevyTraceValid_iff_indexed_l
    (trace : List TextbookBoundedLevyJudgment) :
    TextbookBoundedLevyTraceValid trace ↔
      ∀ index : Fin trace.length,
        textbookBoundedLevyLocalRule_l (trace.take index.1) (trace.get index) := by
  rw [← checkTextbookBoundedLevyTrace_iff_valid_l]
  simpa only [checkTextbookBoundedLevyTrace_l, List.nil_append] using
    checkTextbookBoundedLevyTraceFrom_iff_indexed_l [] trace

/-- 同一个可引用记录集合给出完全相同的局部规则。 -/
theorem textbookBoundedLevyRuleOver_congr_l
    {available available' : TextbookBoundedLevyJudgment → Prop}
    (hAvailable : ∀ entry, available entry ↔ available' entry)
    (entry : TextbookBoundedLevyJudgment) :
    textbookBoundedLevyRuleOver_l available entry ↔
      textbookBoundedLevyRuleOver_l available' entry := by
  simp only [textbookBoundedLevyRuleOver_l, hAvailable]

/-- 前缀中的记录恰好是在严格更小索引处出现的记录。 -/
theorem textbookBoundedLevyEntry_mem_take_iff_l
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (entry : TextbookBoundedLevyJudgment) :
    entry ∈ trace.take index.1 ↔
      ∃ prior : Fin trace.length, prior.1 < index.1 ∧ trace.get prior = entry := by
  constructor
  · intro hEntry
    obtain ⟨prior, hPrior⟩ := List.mem_iff_get.mp hEntry
    have hPriorIndex : prior.1 < index.1 := by
      have hBound := prior.2
      simp only [List.length_take] at hBound
      omega
    let position : Fin trace.length := ⟨prior.1, hPriorIndex.trans index.2⟩
    refine ⟨position, hPriorIndex, ?_⟩
    simpa only [List.get_eq_getElem, List.getElem_take, position] using hPrior
  · rintro ⟨prior, hPrior, rfl⟩
    apply List.mem_iff_get.mpr
    refine ⟨⟨prior.1, ?_⟩, ?_⟩
    · simp only [List.length_take]
      exact lt_min hPrior prior.2
    · simp only [List.get_eq_getElem, List.getElem_take]

/-- 每一行只使用有限图中严格位于它之前的记录。 -/
def textbookBoundedLevyIndexedRule_l {length : Nat}
    (trace : Fin length → TextbookBoundedLevyJudgment) (index : Fin length) : Prop :=
  textbookBoundedLevyRuleOver_l
    (fun entry => ∃ prior : Fin length,
      prior.1 < index.1 ∧ trace prior = entry)
    (trace index)

/-- 列表证书与有限图证书具有同一有效性条件。 -/
theorem textbookBoundedLevyTraceValid_iff_indexedRule_l
    (trace : List TextbookBoundedLevyJudgment) :
    TextbookBoundedLevyTraceValid trace ↔
      ∀ index : Fin trace.length, textbookBoundedLevyIndexedRule_l trace.get index := by
  rw [textbookBoundedLevyTraceValid_iff_indexed_l]
  apply forall_congr'
  intro index
  exact textbookBoundedLevyRuleOver_congr_l
    (textbookBoundedLevyEntry_mem_take_iff_l trace index) (trace.get index)

/-- 有限图上的逐行规则推出每条记录具有原始分类证书。 -/
theorem textbookBoundedLevyIndexedRule_certified_l {length : Nat}
    (trace : Fin length → TextbookBoundedLevyJudgment)
    (hTrace : ∀ index, textbookBoundedLevyIndexedRule_l trace index)
    (index : Fin length) : (trace index).Certified := by
  have hAll : ∀ position (hPosition : position < length),
      (trace ⟨position, hPosition⟩).Certified := by
    intro position
    induction position using Nat.strong_induction_on with
    | h position ih =>
        intro hPosition
        apply textbookBoundedLevyRuleOver_sound_l ?_ (hTrace ⟨position, hPosition⟩)
        rintro entry ⟨prior, hPrior, rfl⟩
        exact ih prior.1 hPrior prior.2
  exact hAll index.1 index.2

/-- 原始分类证书恰好意味着存在一份有限索引证书。 -/
theorem textbookBoundedLevyJudgment_certified_iff_indexedTrace_l
    (entry : TextbookBoundedLevyJudgment) :
    entry.Certified ↔ ∃ length, ∃ trace : Fin length → TextbookBoundedLevyJudgment,
      (∀ index, textbookBoundedLevyIndexedRule_l trace index) ∧
        ∃ index, trace index = entry := by
  constructor
  · intro hEntry
    obtain ⟨rows, hRows, hMember⟩ :=
      (textbookBoundedLevyJudgment_hasTrace_iff_certified_l entry).mpr hEntry
    refine ⟨rows.length, rows.get,
      (textbookBoundedLevyTraceValid_iff_indexedRule_l rows).mp hRows, ?_⟩
    exact List.mem_iff_get.mp hMember
  · rintro ⟨length, trace, hTrace, index, rfl⟩
    exact textbookBoundedLevyIndexedRule_certified_l trace hTrace index

end YesMetaZFC.BMS.ConstructibleBridge
