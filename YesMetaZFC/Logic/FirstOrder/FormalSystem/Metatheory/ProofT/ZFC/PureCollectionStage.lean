import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFiniteSequenceSpace

/-! # 第二轮集合收集阶段的统一模型

四个新集合图在同一扩张中取值，已有极值和关系定义继续使用原纯图。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureCollectionStage
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x

def functionGraph (symbol : Nonlogical.BasicSetTheory.FunctionSymbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match symbol with
  | .finiteSubsetCollection => PureBoundedDefinitions.graph .finiteSubsetCollection
  | .powerSetBijection => PureBoundedDefinitions.graph .powerSetBijection
  | .indexOrder => PureBoundedDefinitions.graph .indexOrder
  | .finiteSequenceSpace => PureFiniteSequenceSpace.graph
  | symbol => PureStageTwoBase.functionGraph symbol

def functionCovered : Nonlogical.BasicSetTheory.FunctionSymbol → Bool
  | .finiteSubsetCollection | .powerSetBijection | .indexOrder | .finiteSequenceSpace => true
  | symbol => PureStageTwoBase.functionCovered symbol

def interpretation : Interpretation Nonlogical.BasicSetTheory.signature ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation := PureNaturalRelations.interpretation.relation

theorem map_values {ℳ : Structure.{0,0,0,x} ℒ} {sorts : SortContext Nonlogical.BasicSetTheory.signature}
    (args : Values (fun _ => Carrier ℳ) sorts) :
    mapValues interpretation args = mapValues PureNaturalRelations.interpretation args := by
  induction args with
  | nil => rfl
  | cons head tail ih => simp only [mapValues]; rw [ih]; rfl

theorem functional {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory) :
    Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  all_goals simp only [map_values]
  case finiteSubsetCollection => exact PureBoundedDefinitions.functional hℳ .finiteSubsetCollection args
  case powerSetBijection => exact PureBoundedDefinitions.functional hℳ .powerSetBijection args
  case indexOrder => exact PureBoundedDefinitions.functional hℳ .indexOrder args
  case finiteSequenceSpace =>
    cases args with | cons source tail =>
    cases tail
    exact PureFiniteSequenceSpace.functional hℳ source
  all_goals exact PureNaturalRelations.functional hℳ _ args

noncomputable def expansion {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)

theorem realizes {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) :=
  expansion_realizes (functional hℳ)

theorem inherited_round_one {symbol : Nonlogical.BasicSetTheory.RelationSymbol}
    (primitive : PureRoundOneRelations.Primitive symbol) :
    interpretation.relation symbol = openFormula interpretation (PureRoundOneRelations.condition primitive) := by
  cases primitive <;> rfl

theorem inherited_natural {symbol : Nonlogical.BasicSetTheory.RelationSymbol}
    (primitive : PureNaturalRelations.Primitive symbol) :
    interpretation.relation symbol = openFormula interpretation (PureNaturalRelations.condition primitive) := by
  cases primitive <;> rfl

/-- 通过纯翻译相同来传输满足关系，避免展开模型取值的选择证明。 -/
theorem specification_transfer {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {parameters : SortContext Nonlogical.BasicSetTheory.signature}
    (spec : Formula Nonlogical.BasicSetTheory.signature [] parameters)
    (hTranslate : openFormula interpretation spec = openFormula PureNaturalRelations.interpretation spec)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    spec.satisfies (templateEnv args : Env (PureStageTwoSemantics.expansion hℳ).model [] parameters) ↔
      spec.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  have hNew := openFormula_correct (expansion hℳ) (realizes hℳ) spec args
  rw [hTranslate, map_values] at hNew
  exact (openFormula_correct (PureStageTwoSemantics.expansion hℳ) (PureStageTwoSemantics.realizes hℳ) spec args).symm.trans hNew

theorem bounded_graph_equation {symbol : Nonlogical.BasicSetTheory.FunctionSymbol}
    (primitive : PureBoundedDefinitions.Primitive symbol) :
    interpretation.function symbol = PureBoundedDefinitions.graph primitive := by
  cases primitive <;> rfl

theorem bounded_translation {symbol : Nonlogical.BasicSetTheory.FunctionSymbol}
    (primitive : PureBoundedDefinitions.Primitive symbol) :
    openFormula interpretation (PureBoundedDefinitions.specification primitive) =
      openFormula PureNaturalRelations.interpretation (PureBoundedDefinitions.specification primitive) := by
  cases primitive <;> rfl

/-- 新函数的原成员规格在同一模型中成立，且无需强化原 guard。 -/
theorem bounded_specification {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : PureBoundedDefinitions.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (Nonlogical.BasicSetTheory.signature.funcDomain symbol)) (output : Carrier ℳ) :
    output = (expansion hℳ).function symbol args ↔
      (PureBoundedDefinitions.specification primitive).satisfies
        (templateEnv (.cons output args) : Env (expansion hℳ).model []
          (Nonlogical.BasicSetTheory.SetSort.set :: Nonlogical.BasicSetTheory.signature.funcDomain symbol)) := by
  apply ((realizes hℳ).function symbol args output).symm.trans
  rw [bounded_graph_equation primitive, map_values]
  exact (PureBoundedDefinitions.graph_correct hℳ primitive args output).trans
    (specification_transfer hℳ _ (bounded_translation primitive) (.cons output args))

theorem finite_sequence_specification {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    (source output : Carrier ℳ) :
    output = (expansion hℳ).function .finiteSequenceSpace (.cons source .nil) ↔
      (Nonlogical.BasicSetTheory.finite_sequence_space_spec (.fvar (.there .here)) (.fvar .here)).satisfies
        (templateEnv (.cons output (.cons source .nil)) : Env (expansion hℳ).model []
          [Nonlogical.BasicSetTheory.SetSort.set,Nonlogical.BasicSetTheory.SetSort.set]) := by
  apply ((realizes hℳ).function .finiteSequenceSpace (.cons source .nil) output).symm.trans
  exact (PureFiniteSequenceSpace.graph_correct hℳ output source).trans
    (specification_transfer hℳ _ rfl (.cons output (.cons source .nil)))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureCollectionStage
