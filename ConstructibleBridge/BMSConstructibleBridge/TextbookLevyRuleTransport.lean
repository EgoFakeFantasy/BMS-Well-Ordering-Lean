import BMSConstructibleBridge.TextbookLevyEarlierRecord
import BMSConstructibleBridge.TextbookBoundedLevyEarlierRecord

/-!
# 两种分类记录之间的规则传输

这里只识别两种记录的四个原始字段，不识别其 `Certified` 命题。
普通与有界分类的基底规则不同；否定、合取、量化和提升的记录操作及集合编码相同。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

/-- 保留全部字段的记录等价；不包含分类证书的转换。 -/
def textbookLevyJudgmentEquiv_l :
    TextbookLevyJudgment ≃ TextbookBoundedLevyJudgment where
  toFun entry := ⟨entry.isSigma, entry.level, entry.arity, entry.code⟩
  invFun entry := ⟨entry.isSigma, entry.level, entry.arity, entry.code⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace TextbookLevyJudgment

@[simp] theorem equiv_isSigma_l (entry : TextbookLevyJudgment) :
    (textbookLevyJudgmentEquiv_l entry).isSigma = entry.isSigma := rfl

@[simp] theorem equiv_level_l (entry : TextbookLevyJudgment) :
    (textbookLevyJudgmentEquiv_l entry).level = entry.level := rfl

@[simp] theorem equiv_arity_l (entry : TextbookLevyJudgment) :
    (textbookLevyJudgmentEquiv_l entry).arity = entry.arity := rfl

@[simp] theorem equiv_code_l (entry : TextbookLevyJudgment) :
    (textbookLevyJudgmentEquiv_l entry).code = entry.code := rfl

@[simp] theorem equiv_negate_l (entry : TextbookLevyJudgment) :
    (textbookLevyJudgmentEquiv_l entry).negate =
      textbookLevyJudgmentEquiv_l entry.negate := rfl

@[simp] theorem equiv_conjoin_l (left right : TextbookLevyJudgment) :
    (textbookLevyJudgmentEquiv_l left).conjoin (textbookLevyJudgmentEquiv_l right) =
      textbookLevyJudgmentEquiv_l (left.conjoin right) := rfl

@[simp] theorem equiv_quantify_l (entry : TextbookLevyJudgment) :
    (textbookLevyJudgmentEquiv_l entry).quantify =
      textbookLevyJudgmentEquiv_l entry.quantify := rfl

@[simp] theorem equiv_raise_l (entry : TextbookLevyJudgment) (isSigma : Bool) :
    (textbookLevyJudgmentEquiv_l entry).raise isSigma =
      textbookLevyJudgmentEquiv_l (entry.raise isSigma) := rfl

end TextbookLevyJudgment

/-- 字段转换不改变任何记录的集合编码。 -/
@[simp] theorem textbookLevyRecordZF_equiv_l (entry : TextbookLevyJudgment) :
    textbookBoundedLevyRecordZF_l (textbookLevyJudgmentEquiv_l entry) =
      (textbookLevyRecordZF_l entry : ZFSet.{u}) := rfl

/-- 逐行转换保持索引图，特别是严格前驱关系。 -/
@[simp] theorem textbookLevyTraceGraphZF_equiv_l (trace : List TextbookLevyJudgment) :
    textbookBoundedLevyTraceGraphZF_l (trace.map textbookLevyJudgmentEquiv_l) =
      (textbookLevyTraceGraphZF_l trace : ZFSet.{u}) := by
  simp only [textbookBoundedLevyTraceGraphZF_l, textbookLevyTraceGraphZF_l, List.map_map]
  rfl

/-- 先前记录的存在量词可等价地由其实际位置承载。 -/
theorem exists_textbookPriorRecord_iff_l {Carrier : Type u} (trace : List Carrier)
    (index : Nat) (property : Carrier → Prop) :
    (∃ entry, (∃ prior : Fin trace.length,
      prior.1 < index ∧ trace.get prior = entry) ∧ property entry) ↔
      ∃ prior : Fin trace.length, prior.1 < index ∧ property (trace.get prior) := by
  constructor
  · rintro ⟨entry, ⟨prior, hPrior, rfl⟩, hProperty⟩
    exact ⟨prior, hPrior, hProperty⟩
  · rintro ⟨prior, hPrior, hProperty⟩
    exact ⟨trace.get prior, ⟨prior, hPrior, rfl⟩, hProperty⟩

end YesMetaZFC.BMS.ConstructibleBridge
