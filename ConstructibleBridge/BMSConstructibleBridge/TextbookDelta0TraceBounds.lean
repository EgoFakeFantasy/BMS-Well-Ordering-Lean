import BMSConstructibleBridge.TextbookDelta0TraceGraph

/-!
# 有限分类证书的局部存在界

记录的所有字段都是自然数，索引图也只有有限多行。通过 `L_omega` 的有限
有序对、单点和并集闭包，直接证明整个规范证书已经属于 `L_omega`。
这个界仅针对有限语法证书，不推广为跨越任意序数的阶段求值历史界。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 每条有限分类记录都已出现在 L 的第 omega 层。 -/
theorem textbookDelta0RecordZF_mem_LStageOmega_l (entry : TextbookDelta0Judgment) :
    textbookDelta0RecordZF_l entry ∈ LStageZF Ordinal.omega0 := by
  have hNat (n : Nat) : natCode n ∈ LStageZF Ordinal.omega0 :=
    ordinal_toZFSet_mem_LStageZF_of_lt (Ordinal.natCast_lt_omega0 n)
  exact orderedPair_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0
    (hNat _) (hNat _)

/-- 有限索引图保留第 omega 层的成员资格。 -/
theorem finiteIndexedGraphFrom_mem_LStageOmega_l
    (values : List ZFSet.{u}) (hValues : ∀ value ∈ values, value ∈ LStageZF Ordinal.omega0)
    (start : Nat) : IndexedSequenceZF.graphFrom start values ∈ LStageZF Ordinal.omega0 := by
  induction values generalizing start with
  | nil => exact empty_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0
  | cons value values ih =>
      rw [IndexedSequenceZF.graphFrom_cons, ZFSet.insert_eq]
      apply union_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0
      · apply singleton_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0
        exact orderedPair_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0
          (hValues value (by simp))
          (ordinal_toZFSet_mem_LStageZF_of_lt (Ordinal.natCast_lt_omega0 start))
      · exact ih (fun current hCurrent => hValues current (by simp [hCurrent])) (start + 1)

/-- 每份规范分类证书的完整索引图已经属于 L_omega。 -/
theorem textbookDelta0TraceGraphZF_mem_LStageOmega_l (trace : List TextbookDelta0Judgment) :
    textbookDelta0TraceGraphZF_l trace ∈ LStageZF Ordinal.omega0 := by
  apply finiteIndexedGraphFrom_mem_LStageOmega_l
  intro value hValue
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hValue
  exact textbookDelta0RecordZF_mem_LStageOmega_l entry

/-- 长度标签和有限图组成的完整证书码属于 L_omega。 -/
theorem textbookDelta0TraceZF_mem_LStageOmega_l (trace : List TextbookDelta0Judgment) :
    textbookDelta0TraceZF_l trace ∈ LStageZF Ordinal.omega0 :=
  orderedPair_mem_LStageZF_of_isSuccLimit Ordinal.isSuccLimit_omega0
    (ordinal_toZFSet_mem_LStageZF_of_lt (Ordinal.natCast_lt_omega0 _))
    (textbookDelta0TraceGraphZF_mem_LStageOmega_l trace)

/-- 越过 omega 的任何层均已包含每份规范有限证书。 -/
theorem textbookDelta0TraceZF_mem_stage_l {θ : Ordinal.{u}}
    (hθ : Ordinal.omega0 ≤ θ) (trace : List TextbookDelta0Judgment) :
    textbookDelta0TraceZF_l trace ∈ LStageZF θ :=
  LStageZF_mono hθ (textbookDelta0TraceZF_mem_LStageOmega_l trace)

/-- 已分类记录总有一份检查成功、且编码位于指定小层中的有限证书。 -/
theorem textbookDelta0Judgment_exists_checkedTrace_in_stage_l
    {θ : Ordinal.{u}} (hθ : Ordinal.omega0 ≤ θ)
    {entry : TextbookDelta0Judgment} (hEntry : entry.Certified) :
    ∃ trace, checkTextbookDelta0Trace_l trace = true ∧ entry ∈ trace ∧
      textbookDelta0TraceZF_l trace ∈ LStageZF θ := by
  obtain ⟨trace, hTrace, hMember⟩ :=
    (textbookDelta0Judgment_certified_iff_checkedTrace_l entry).mp hEntry
  exact ⟨trace, hTrace, hMember, textbookDelta0TraceZF_mem_stage_l hθ trace⟩

end YesMetaZFC.BMS.ConstructibleBridge
