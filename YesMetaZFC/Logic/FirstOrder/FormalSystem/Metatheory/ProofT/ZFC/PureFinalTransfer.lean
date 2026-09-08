import YesMetaZFC.Automation.RelationalTransfer
import YesMetaZFC.Automation.ModelClosure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureCompletedStage

/-! # 旧阶段规格到最终纯扩张的统一传输

每个接口只核验原公式依赖的逐符号图相等，不展开整份嵌套不动点解释。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalTransfer
open PureModel Nonlogical.BasicSetTheory
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}
noncomputable abbrev E (hℳ : Theory.Models ℳ theory) := PureCompletedStage.expansion hℳ

theorem fromRoundTwo (hℳ : Theory.Models ℳ theory) {free : SortContext S}
    (body : Formula S [] free)
    (hCovered : formulaCovered PureRoundTwoStage.functionCovered PureRoundTwoStage.relationCovered body = true)
    (args : Values (E hℳ).model.Carrier free) :
    body.satisfies (templateEnv args : Env (PureRoundTwoStage.expansion hℳ).model [] free) ↔
      body.satisfies (templateEnv args : Env (E hℳ).model [] free) :=
  transfer_covered PureRoundTwoStage.interpretation
    PureCompletedStage.interpretation.function PureCompletedStage.interpretation.relation
    (PureRoundTwoStage.expansion hℳ) (PureRoundTwoStage.realizes hℳ) (E hℳ) (PureCompletedStage.realizes hℳ)
    PureRoundTwoStage.functionCovered PureRoundTwoStage.relationCovered
    (by intro symbol h; cases symbol <;> first | rfl | contradiction)
    (by intro symbol h; cases symbol <;> first | rfl | contradiction) body hCovered args

theorem fromRelated (hℳ : Theory.Models ℳ theory) {free : SortContext S}
    (body : Formula S [] free)
    (hCovered : formulaCovered PureRelatedStage.functionCovered PureRelatedStage.relationCovered body = true)
    (args : Values (E hℳ).model.Carrier free) :
    body.satisfies (templateEnv args : Env (PureRelatedStage.expansion hℳ).model [] free) ↔
      body.satisfies (templateEnv args : Env (E hℳ).model [] free) :=
  transfer_covered PureRelatedStage.interpretation
    PureCompletedStage.interpretation.function PureCompletedStage.interpretation.relation
    (PureRelatedStage.expansion hℳ) (PureRelatedStage.realizes hℳ) (E hℳ) (PureCompletedStage.realizes hℳ)
    PureRelatedStage.functionCovered PureRelatedStage.relationCovered
    (by intro symbol h; cases symbol <;> first | rfl | contradiction)
    (by intro symbol h; cases symbol <;> first | rfl | contradiction) body hCovered args

theorem fromTransform (hℳ : Theory.Models ℳ theory) {free : SortContext S}
    (body : Formula S [] free)
    (hCovered : formulaCovered PureTransformStage.functionCovered PureTransformStage.relationCovered body = true)
    (args : Values (E hℳ).model.Carrier free) :
    body.satisfies (templateEnv args : Env (PureTransformStage.expansion hℳ).model [] free) ↔
      body.satisfies (templateEnv args : Env (E hℳ).model [] free) :=
  transfer_covered PureTransformStage.interpretation
    PureCompletedStage.interpretation.function PureCompletedStage.interpretation.relation
    (PureTransformStage.expansion hℳ) (PureTransformStage.realizes hℳ) (E hℳ) (PureCompletedStage.realizes hℳ)
    PureTransformStage.functionCovered PureTransformStage.relationCovered
    (by intro symbol h; cases symbol <;> first | rfl | contradiction)
    (by intro symbol h; cases symbol <;> first | rfl | contradiction) body hCovered args

theorem fromStructure (hℳ : Theory.Models ℳ theory) {free : SortContext S}
    (body : Formula S [] free)
    (hCovered : formulaCovered PureStructureStage.functionCovered PureStructureStage.relationCovered body = true)
    (args : Values (E hℳ).model.Carrier free) :
    body.satisfies (templateEnv args : Env (PureStructureStage.expansion hℳ).model [] free) ↔
      body.satisfies (templateEnv args : Env (E hℳ).model [] free) :=
  transfer_covered PureStructureStage.interpretation
    PureCompletedStage.interpretation.function PureCompletedStage.interpretation.relation
    (PureStructureStage.expansion hℳ) (PureStructureStage.realizes hℳ) (E hℳ) (PureCompletedStage.realizes hℳ)
    PureStructureStage.functionCovered PureStructureStage.relationCovered
    (by intro symbol h; cases symbol <;> first | rfl | contradiction)
    (by intro symbol h; cases symbol <;> first | rfl | contradiction) body hCovered args

theorem fromRoundTwoSentence (hℳ : Theory.Models ℳ theory) (body : Sentence S)
    (hCovered : formulaCovered PureRoundTwoStage.functionCovered PureRoundTwoStage.relationCovered body = true) :
    body.satisfies (Env.empty : Env (PureRoundTwoStage.expansion hℳ).model [] []) ↔
      body.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  have hOldEnv : (templateEnv .nil : Env (PureRoundTwoStage.expansion hℳ).model [] []) = Env.empty := by
    apply Env.ext <;> intro sort entry <;> cases entry
  have hNewEnv : (templateEnv .nil : Env (E hℳ).model [] []) = Env.empty := by
    apply Env.ext <;> intro sort entry <;> cases entry
  rw [← hOldEnv, ← hNewEnv]
  exact fromRoundTwo hℳ body hCovered .nil

theorem fromRelatedSentence (hℳ : Theory.Models ℳ theory) (body : Sentence S)
    (hCovered : formulaCovered PureRelatedStage.functionCovered PureRelatedStage.relationCovered body = true) :
    body.satisfies (Env.empty : Env (PureRelatedStage.expansion hℳ).model [] []) ↔
      body.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  have hOldEnv : (templateEnv .nil : Env (PureRelatedStage.expansion hℳ).model [] []) = Env.empty := by
    apply Env.ext <;> intro sort entry <;> cases entry
  have hNewEnv : (templateEnv .nil : Env (E hℳ).model [] []) = Env.empty := by
    apply Env.ext <;> intro sort entry <;> cases entry
  rw [← hOldEnv, ← hNewEnv]
  exact fromRelated hℳ body hCovered .nil

theorem fromTransformSentence (hℳ : Theory.Models ℳ theory) (body : Sentence S)
    (hCovered : formulaCovered PureTransformStage.functionCovered PureTransformStage.relationCovered body = true) :
    body.satisfies (Env.empty : Env (PureTransformStage.expansion hℳ).model [] []) ↔
      body.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  have hOldEnv : (templateEnv .nil : Env (PureTransformStage.expansion hℳ).model [] []) = Env.empty := by
    apply Env.ext <;> intro sort entry <;> cases entry
  have hNewEnv : (templateEnv .nil : Env (E hℳ).model [] []) = Env.empty := by
    apply Env.ext <;> intro sort entry <;> cases entry
  rw [← hOldEnv, ← hNewEnv]
  exact fromTransform hℳ body hCovered .nil

theorem fromStructureSentence (hℳ : Theory.Models ℳ theory) (body : Sentence S)
    (hCovered : formulaCovered PureStructureStage.functionCovered PureStructureStage.relationCovered body = true) :
    body.satisfies (Env.empty : Env (PureStructureStage.expansion hℳ).model [] []) ↔
      body.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  have hOldEnv : (templateEnv .nil : Env (PureStructureStage.expansion hℳ).model [] []) = Env.empty := by
    apply Env.ext <;> intro sort entry <;> cases entry
  have hNewEnv : (templateEnv .nil : Env (E hℳ).model [] []) = Env.empty := by
    apply Env.ext <;> intro sort entry <;> cases entry
  rw [← hOldEnv, ← hNewEnv]
  exact fromStructure hℳ body hCovered .nil

theorem functionFromArithmetic (hℳ : Theory.Models ℳ theory) (symbol : FunctionSymbol)
    (hGraph : PureCompletedStage.interpretation.function symbol = PureArithmeticStage.interpretation.function symbol)
    (args : Values (E hℳ).model.Carrier (S.funcDomain symbol)) :
    (E hℳ).function symbol args = (PureArithmeticStage.expansion hℳ).function symbol args :=
  function_regraph PureArithmeticStage.interpretation
    PureCompletedStage.interpretation.function PureCompletedStage.interpretation.relation
    (PureArithmeticStage.expansion hℳ) (PureArithmeticStage.realizes hℳ) (E hℳ) (PureCompletedStage.realizes hℳ)
    symbol hGraph args

theorem functionFromDifference (hℳ : Theory.Models ℳ theory) (symbol : FunctionSymbol)
    (hGraph : PureCompletedStage.interpretation.function symbol = PureDifferenceStage.interpretation.function symbol)
    (args : Values (E hℳ).model.Carrier (S.funcDomain symbol)) :
    (E hℳ).function symbol args = (PureDifferenceStage.expansion hℳ).function symbol args :=
  function_regraph PureDifferenceStage.interpretation
    PureCompletedStage.interpretation.function PureCompletedStage.interpretation.relation
    (PureDifferenceStage.expansion hℳ) (PureDifferenceStage.realizes hℳ) (E hℳ) (PureCompletedStage.realizes hℳ)
    symbol hGraph args

theorem functionFromRoundTwo (hℳ : Theory.Models ℳ theory) (symbol : FunctionSymbol)
    (hGraph : PureCompletedStage.interpretation.function symbol = PureRoundTwoStage.interpretation.function symbol)
    (args : Values (E hℳ).model.Carrier (S.funcDomain symbol)) :
    (E hℳ).function symbol args = (PureRoundTwoStage.expansion hℳ).function symbol args :=
  function_regraph PureRoundTwoStage.interpretation
    PureCompletedStage.interpretation.function PureCompletedStage.interpretation.relation
    (PureRoundTwoStage.expansion hℳ) (PureRoundTwoStage.realizes hℳ) (E hℳ) (PureCompletedStage.realizes hℳ)
    symbol hGraph args

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalTransfer
