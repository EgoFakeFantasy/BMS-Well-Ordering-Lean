import BMSConstructibleBridge.TextbookEStageLevelAgreementFormula
import BMSConstructibleBridge.ECodeElementarity

/-!
# textbook E 一致性与可构造层初等性

统一对比公式使用全体 `L` 中的元组图，而 `ECodeSigmaElementaryAt_l`
使用层载体上的元组。本文件证明两种表述对真正的可构造层完全相同。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible
open Constructible.FiniteSequenceZF

/-- 层包含只替换元素所带的属于性证明，不改变 textbook 元组图。 -/
theorem textbookTupleGraph_externalStageTuple_l
    {α β : Ordinal.{u}} (hαβ : α ≤ β) {arity : Nat}
    (assignment : Tuple (StageCarrier α) arity) :
    textbookTupleGraph (externalStageTuple_l hαβ assignment) =
      textbookTupleGraph assignment := by
  rfl

/-- E 码初等性推出两个层集合上的统一正元真值一致性。 -/
theorem textbookELevelAgreement_of_eCode_l
    {level : Nat} {α β : Ordinal.{u}}
    (hElementary : ECodeSigmaElementaryAt_l level α β) :
    TextbookELevelAgreement_l level
      (Constructible.Model.stageLCarrier α)
      (Constructible.Model.stageLCarrier β) := by
  rcases hElementary with
    ⟨_sourceNonempty, _targetNonempty, hαβ, hElementary⟩
  intro positiveArity code hCode tuple hTuple
  have hFunction : ZFSet.IsFunc (natCode (positiveArity + 1))
      (LStageZF α) tuple.1 :=
    (mem_textbookTupleSpace_iff.mp (by
      simpa only [Constructible.Model.stageLCarrier_val] using hTuple))
  rcases exists_textbookTupleGraph_eq_of_isFunc hFunction with
    ⟨assignment, hAssignment⟩
  have hAgreement := hElementary hCode assignment
  rw [textbookTupleGraph_externalStageTuple_l hαβ assignment] at hAgreement
  simpa only [Constructible.Model.stageLCarrier_val, hAssignment] using hAgreement

/-- 统一正元 E 真值一致性在给定层包含数据后恢复 E 码初等性。 -/
theorem eCodeSigmaElementaryAt_of_textbookELevelAgreement_l
    {level : Nat} {α β : Ordinal.{u}}
    (sourceNonempty : Nonempty (StageCarrier α))
    (targetNonempty : Nonempty (StageCarrier β))
    (hαβ : α ≤ β)
    (hAgreement : TextbookELevelAgreement_l level
      (Constructible.Model.stageLCarrier α)
      (Constructible.Model.stageLCarrier β)) :
    ECodeSigmaElementaryAt_l level α β := by
  refine ⟨sourceNonempty, targetNonempty, hαβ, ?_⟩
  intro positiveArity code hCode assignment
  let tuple : Constructible.Model.LCarrier.{u} :=
    ⟨textbookTupleGraph assignment,
      textbookTupleGraph_mem_L (LStageZF_mem_L α) assignment⟩
  have hTuple : tuple.1 ∈ textbookTupleSpace
      (Constructible.Model.stageLCarrier α).1 (positiveArity + 1) := by
    exact textbookTupleGraph_mem_tupleSpace assignment
  have hCompared := hAgreement positiveArity code hCode tuple hTuple
  rw [textbookTupleGraph_externalStageTuple_l hαβ assignment]
  simpa only [tuple, Constructible.Model.stageLCarrier_val] using hCompared

/-- 在显式非空性与层包含下，两种有限层初等性表述完全等价。 -/
theorem textbookELevelAgreement_iff_eCode_l
    {level : Nat} {α β : Ordinal.{u}}
    (sourceNonempty : Nonempty (StageCarrier α))
    (targetNonempty : Nonempty (StageCarrier β))
    (hαβ : α ≤ β) :
    TextbookELevelAgreement_l level
        (Constructible.Model.stageLCarrier α)
        (Constructible.Model.stageLCarrier β) ↔
      ECodeSigmaElementaryAt_l level α β :=
  ⟨eCodeSigmaElementaryAt_of_textbookELevelAgreement_l
      sourceNonempty targetNonempty hαβ,
    textbookELevelAgreement_of_eCode_l⟩

/-- 公开二元一致性公式在两个真实层参数上精确表达 E 码初等性。 -/
theorem satisfies_textbookELevelAgreementFormula_stage_iff_eCode_l
    {level : Nat} {α β : Ordinal.{u}}
    (sourceNonempty : Nonempty (StageCarrier α))
    (targetNonempty : Nonempty (StageCarrier β))
    (hαβ : α ≤ β) (hβ : Order.IsSuccLimit β)
    (hω : Ordinal.omega0 < β) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
        (textbookELevelAgreementFormula_l level)
        ![Constructible.Model.stageLCarrier α,
          Constructible.Model.stageLCarrier β] ↔
      ECodeSigmaElementaryAt_l level α β := by
  rw [satisfies_textbookELevelAgreementFormula_iff_l level
    (Constructible.Model.stageLCarrier α)
    (Constructible.Model.stageLCarrier β) β
    (Constructible.Model.stageLCarrier_val β) hβ hω]
  exact textbookELevelAgreement_iff_eCode_l
    sourceNonempty targetNonempty hαβ

/-- 同一公式精确表达真正有界外部有限 `Sigma` 层的初等性。 -/
theorem satisfies_textbookELevelAgreementFormula_stage_iff_boundedExternal_l
    {level : Nat} {α β : Ordinal.{u}}
    (sourceNonempty : Nonempty (StageCarrier α))
    (targetNonempty : Nonempty (StageCarrier β))
    (hαβ : α ≤ β) (hβ : Order.IsSuccLimit β)
    (hω : Ordinal.omega0 < β) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
        (textbookELevelAgreementFormula_l level)
        ![Constructible.Model.stageLCarrier α,
          Constructible.Model.stageLCarrier β] ↔
      BoundedExternalStageSigmaElementaryAt_l level α β :=
  (satisfies_textbookELevelAgreementFormula_stage_iff_eCode_l
      sourceNonempty targetNonempty hαβ hβ hω).trans
    eCodeSigmaElementaryAt_iff_external_l

/--
在共同后继极限层 `L_top` 中，新闭句以两个真实层集合为参数时，精确表达
`L_α ≺_{Σ_level} L_β`。这里 `top` 只负责承载统一分类器与 E 求值历史；结论
不依赖 `top`，因此这是 Hunter 的二层关系 `φ₁` 所需的规范桥接定理。
-/
theorem satisfiesIn_textbookEStageLevelAgreementFormula_stage_iff_boundedExternal_l
    {top α β : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hωTop : Ordinal.omega0 < top) (hαtop : α < top)
    (hβtop : β < top) (hαβ : α ≤ β)
    (hα : Order.IsSuccLimit α) (hβ : Order.IsSuccLimit β)
    (hωα : Ordinal.omega0 < α) (hωβ : Ordinal.omega0 < β)
    (level : Nat) :
    Constructible.Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookEStageLevelAgreementFormula_l level)
        ![LStageZF α, LStageZF β] ↔
      BoundedExternalStageSigmaElementaryAt_l level α β := by
  have hA : LStageZF α ∈ LStageZF top := LStageZF_mem_of_lt hαtop
  have hB : LStageZF β ∈ LStageZF top := LStageZF_mem_of_lt hβtop
  have sourceNonempty : Nonempty (StageCarrier α) :=
    ⟨⟨natCode 0, natCode_mem_stage_l hωα 0⟩⟩
  have targetNonempty : Nonempty (StageCarrier β) :=
    ⟨⟨natCode 0, natCode_mem_stage_l hωβ 0⟩⟩
  rw [satisfiesIn_textbookEStageLevelAgreementFormula_iff_l
    hTop hωTop hβtop hβ hωβ level hA hB rfl]
  change TextbookELevelAgreement_l level
      (Constructible.Model.stageLCarrier α)
      (Constructible.Model.stageLCarrier β) ↔ _
  exact (textbookELevelAgreement_iff_eCode_l
    sourceNonempty targetNonempty hαβ).trans
      eCodeSigmaElementaryAt_iff_external_l

end YesMetaZFC.BMS.ConstructibleBridge
