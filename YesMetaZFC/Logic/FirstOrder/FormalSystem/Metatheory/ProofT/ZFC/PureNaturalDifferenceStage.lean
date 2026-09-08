import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureNaturalDifference

/-! # 本轮算术与集合构造的统一扩张

实际替换截断减法，并在同一扩张中保持加乘幂、配对、闭包、有限层级、有限宇宙
和已有收集、序列及关系规格。跨阶段传输比较纯图，不展开模型选择项。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalDifferenceStage
open PureModel PureNaturalInduction
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model PureFunctionDefinitions.parameterSorts
universe x
abbrev s := Nonlogical.BasicSetTheory.SetSort.set
abbrev S := Nonlogical.BasicSetTheory.signature
variable {ℳ : Structure.{0,0,0,x} ℒ}

def functionGraph (symbol : Nonlogical.BasicSetTheory.FunctionSymbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match symbol with
  | .naturalDifference => PureNaturalDifference.graph
  | symbol => PureFiniteUniverseStage.functionGraph symbol
def functionCovered : Nonlogical.BasicSetTheory.FunctionSymbol → Bool
  | .naturalDifference => true
  | symbol => PureFiniteUniverseStage.functionCovered symbol
def relationCovered := PureFiniteUniverseStage.relationCovered
def interpretation : Interpretation S ℒ where
  sort := fun _ => setSort
  function := functionGraph
  relation := PureFiniteUniverseStage.interpretation.relation

theorem map_values {sorts : SortContext S} (args : Values (fun _ => Carrier ℳ) sorts) :
    mapValues interpretation args = mapValues PureFiniteUniverseStage.interpretation args := by
  induction args with
  | nil => rfl
  | cons head tail ih => simp only [mapValues]; rw [ih]; rfl
theorem functional (hℳ : Theory.Models ℳ theory) : Functional interpretation ℳ := by
  intro symbol args
  cases symbol
  all_goals simp only [map_values]
  case naturalDifference =>
    cases args with | cons left tail =>
    cases tail with | cons right tail =>
    cases tail
    exact PureNaturalDifference.functional hℳ left right
  all_goals exact PureFiniteUniverseStage.functional hℳ _ args
noncomputable def expansion (hℳ : Theory.Models ℳ theory) : Expansion interpretation ℳ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.expansion (functional hℳ)
theorem realizes (hℳ : Theory.Models ℳ theory) : Realizes (expansion hℳ) := expansion_realizes (functional hℳ)

theorem function_preserved (hℳ : Theory.Models ℳ theory) (symbol : Nonlogical.BasicSetTheory.FunctionSymbol)
    (hGraph : interpretation.function symbol = PureFiniteUniverseStage.interpretation.function symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) :
    (expansion hℳ).function symbol args = (PureFiniteUniverseStage.expansion hℳ).function symbol args := by
  have hNew := ((realizes hℳ).function symbol args _).mpr rfl
  rw [hGraph,map_values] at hNew
  exact ((PureFiniteUniverseStage.realizes hℳ).function symbol args _).mp hNew
theorem transfer (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureFiniteUniverseStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureFiniteUniverseStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  have hNew := openFormula_correct (expansion hℳ) (realizes hℳ) body args
  rw [hTranslate,map_values] at hNew
  exact (openFormula_correct (PureFiniteUniverseStage.expansion hℳ) (PureFiniteUniverseStage.realizes hℳ) body args).symm.trans hNew

theorem map_arithmetic {sorts : SortContext S} (args : Values (fun _ => Carrier ℳ) sorts) :
    mapValues interpretation args = mapValues PureArithmeticStage.interpretation args :=
  (map_values args).trans ((PureFiniteUniverseStage.map_values args).trans (PureSetStage.map_values args))
theorem function_from_arithmetic (hℳ : Theory.Models ℳ theory) (symbol : Nonlogical.BasicSetTheory.FunctionSymbol)
    (hGraph : interpretation.function symbol = PureArithmeticStage.interpretation.function symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) :
    (expansion hℳ).function symbol args = (PureArithmeticStage.expansion hℳ).function symbol args := by
  have hNew := ((realizes hℳ).function symbol args _).mpr rfl
  rw [hGraph,map_arithmetic] at hNew
  exact ((PureArithmeticStage.realizes hℳ).function symbol args _).mp hNew
theorem transfer_arithmetic (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureArithmeticStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureArithmeticStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  have hNew := openFormula_correct (expansion hℳ) (realizes hℳ) body args
  rw [hTranslate,map_arithmetic] at hNew
  exact (openFormula_correct (PureArithmeticStage.expansion hℳ) (PureArithmeticStage.realizes hℳ) body args).symm.trans hNew

theorem difference_specification (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) (output : Carrier ℳ) :
    output = (expansion hℳ).function .naturalDifference (.cons left (.cons right .nil)) ↔
      PureNaturalDifference.specification.satisfies (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (expansion hℳ).model [] [s,s,s]) :=
  ((realizes hℳ).function .naturalDifference (.cons left (.cons right .nil)) output).symm.trans
    ((PureNaturalDifference.agrees hℳ hLeft hRight output).trans
      (transfer_arithmetic hℳ _ rfl (.cons output (.cons left (.cons right .nil)))))

noncomputable def arithmetic (hℳ : Theory.Models ℳ theory) (operation : PureArithmeticRecurrence.Operation) (left right : Carrier ℳ) : Carrier ℳ :=
  match operation with
  | .addition => (expansion hℳ).function .naturalAddition (.cons left (.cons right .nil))
  | .multiplication => (expansion hℳ).function .naturalMultiplication (.cons left (.cons right .nil))
  | .exponentiation => (expansion hℳ).function .naturalExponentiation (.cons left (.cons right .nil))

theorem arithmetic_specification (hℳ : Theory.Models ℳ theory) (operation : PureArithmeticRecurrence.Operation)
    {left right : Carrier ℳ} (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) (output : Carrier ℳ) :
    output = arithmetic hℳ operation left right ↔
      (PureArithmeticRecurrence.specification operation).satisfies (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (expansion hℳ).model [] [s,s,s]) := by
  have hSpec := PureArithmeticSpecifications.specification_correct hℳ operation hLeft hRight output
  have hTransfer := transfer_arithmetic hℳ (PureArithmeticRecurrence.specification operation) (by cases operation <;> rfl) (.cons output (.cons left (.cons right .nil)))
  cases operation <;> simp only [arithmetic] <;> rw [function_from_arithmetic hℳ _ rfl] <;> exact hSpec.trans hTransfer

theorem godel_specification (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) (output : Carrier ℳ) :
    output = (expansion hℳ).function .godelPairing (.cons left (.cons right .nil)) ↔
      PureGodelPairing.specification.satisfies (templateEnv (.cons output (.cons left (.cons right .nil))) : Env (expansion hℳ).model [] [s,s,s]) :=
  ((realizes hℳ).function .godelPairing (.cons left (.cons right .nil)) output).symm.trans
    ((PureGodelPairing.agrees hℳ hLeft hRight output).trans (transfer_arithmetic hℳ _ rfl (.cons output (.cons left (.cons right .nil)))))
theorem closure_specification (hℳ : Theory.Models ℳ theory) (source output : Carrier ℳ) :
    output = (expansion hℳ).function .transitiveClosure (.cons source .nil) ↔
      PureTransitiveClosure.specification.satisfies (templateEnv (.cons output (.cons source .nil)) : Env (expansion hℳ).model [] [s,s]) :=
  ((realizes hℳ).function .transitiveClosure (.cons source .nil) output).symm.trans
    ((openFormula_correct (PureArithmeticStage.expansion hℳ) (PureArithmeticStage.realizes hℳ)
      PureTransitiveClosure.specification (.cons output (.cons source .nil))).trans (transfer_arithmetic hℳ _ rfl (.cons output (.cons source .nil))))

theorem hierarchy_specification (hℳ : Theory.Models ℳ theory) :
    PureSetStage.hierarchySpec.satisfies (templateEnv (.cons ((expansion hℳ).function .finiteHierarchy .nil) .nil) : Env (expansion hℳ).model [] [s]) := by
  have hEqual := (function_preserved hℳ .finiteHierarchy rfl .nil).trans
    (PureFiniteUniverseStage.function_preserved hℳ .finiteHierarchy rfl .nil)
  rw [hEqual]
  exact (transfer hℳ _ rfl _).mp ((PureFiniteUniverseStage.transfer hℳ _ rfl _).mp (PureSetStage.hierarchy_specification hℳ))
theorem universe_specification (hℳ : Theory.Models ℳ theory) (output : Carrier ℳ) :
    output = (expansion hℳ).function .finiteUniverse .nil ↔
      PureFiniteUniverseStage.universeSpec.satisfies (templateEnv (.cons output .nil) : Env (expansion hℳ).model [] [s]) := by
  rw [function_preserved hℳ .finiteUniverse rfl .nil]
  exact (PureFiniteUniverseStage.universe_specification hℳ output).trans (transfer hℳ _ rfl (.cons output .nil))
theorem hereditary_definition (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (expansion hℳ).model bound free) (input : Term S bound free s) :
    (Nonlogical.BasicSetTheory.hereditarily_finite_definition_instance input).satisfies env :=
  realizes_definition (expansion hℳ) (realizes hℳ) .isHereditarilyFinite PureFiniteUniverseStage.hereditaryCondition rfl (.cons (input.eval env) .nil)

theorem inherited_round_one {symbol : Nonlogical.BasicSetTheory.RelationSymbol}
    (primitive : PureRoundOneRelations.Primitive symbol) :
    interpretation.relation symbol = openFormula interpretation (PureRoundOneRelations.condition primitive) := by cases primitive <;> rfl
theorem inherited_natural {symbol : Nonlogical.BasicSetTheory.RelationSymbol}
    (primitive : PureNaturalRelations.Primitive symbol) :
    interpretation.relation symbol = openFormula interpretation (PureNaturalRelations.condition primitive) := by cases primitive <;> rfl
theorem round_one_definition_correct (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : PureRoundOneRelations.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (S.relDomain symbol)) :
    (expansion hℳ).relation symbol args ↔ (PureRoundOneRelations.condition primitive).satisfies (templateEnv args) :=
  realizes_definition (expansion hℳ) (realizes hℳ) symbol (PureRoundOneRelations.condition primitive) (inherited_round_one primitive) args
theorem natural_definition_correct (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : PureNaturalRelations.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (S.relDomain symbol)) :
    (expansion hℳ).relation symbol args ↔ (PureNaturalRelations.condition primitive).satisfies (templateEnv args) :=
  realizes_definition (expansion hℳ) (realizes hℳ) symbol (PureNaturalRelations.condition primitive) (inherited_natural primitive) args

/-- 已完成的旧函数通过同一纯图保持所选值。 -/
theorem function_from_difference (hℳ : Theory.Models ℳ theory) (symbol : Nonlogical.BasicSetTheory.FunctionSymbol)
    (hGraph : interpretation.function symbol = PureDifferenceStage.interpretation.function symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) :
    (expansion hℳ).function symbol args = (PureDifferenceStage.expansion hℳ).function symbol args := by
  have hNew := ((realizes hℳ).function symbol args _).mpr rfl
  rw [hGraph,map_arithmetic,PureArithmeticStage.map_values] at hNew
  exact ((PureDifferenceStage.realizes hℳ).function symbol args _).mp hNew

theorem transfer_difference (hℳ : Theory.Models ℳ theory) {parameters : SortContext S} (body : Formula S [] parameters)
    (hTranslate : openFormula interpretation body = openFormula PureDifferenceStage.interpretation body)
    (args : Values (expansion hℳ).model.Carrier parameters) :
    body.satisfies (templateEnv args : Env (PureDifferenceStage.expansion hℳ).model [] parameters) ↔
      body.satisfies (templateEnv args : Env (expansion hℳ).model [] parameters) := by
  have hNew := openFormula_correct (expansion hℳ) (realizes hℳ) body args
  rw [hTranslate,map_arithmetic,PureArithmeticStage.map_values] at hNew
  exact (openFormula_correct (PureDifferenceStage.expansion hℳ) (PureDifferenceStage.realizes hℳ) body args).symm.trans hNew

/-- 前三项有界收集规格在新模型中保持。 -/
theorem bounded_specification {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : PureBoundedDefinitions.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) (output : Carrier ℳ) :
    output = (expansion hℳ).function symbol args ↔
      (PureBoundedDefinitions.specification primitive).satisfies
        (templateEnv (.cons output args) : Env (expansion hℳ).model [] (s :: S.funcDomain symbol)) := by
  have hGraph : interpretation.function symbol = PureDifferenceStage.interpretation.function symbol := by cases primitive <;> rfl
  rw [function_from_difference hℳ symbol hGraph args]
  apply (PureDifferenceStage.bounded_specification hℳ primitive args output).trans
  apply transfer_difference hℳ
  cases primitive <;> rfl

theorem finite_sequence_specification {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    (source output : Carrier ℳ) :
    output = (expansion hℳ).function .finiteSequenceSpace (.cons source .nil) ↔
      (Nonlogical.BasicSetTheory.finite_sequence_space_spec (.fvar (.there .here)) (.fvar .here)).satisfies
        (templateEnv (.cons output (.cons source .nil)) : Env (expansion hℳ).model [] [s,s]) := by
  rw [function_from_difference hℳ .finiteSequenceSpace rfl]
  exact (PureDifferenceStage.finite_sequence_specification hℳ source output).trans
    (transfer_difference hℳ _ rfl (.cons output (.cons source .nil)))

theorem filter_specification {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : PureSequenceFilters.Primitive symbol)
    (args : Values (expansion hℳ).model.Carrier (S.funcDomain symbol)) (output : Carrier ℳ) :
    output = (expansion hℳ).function symbol args ↔
      (PureSequenceFilters.specification primitive).satisfies
        (templateEnv (.cons output args) : Env (expansion hℳ).model [] (s :: S.funcDomain symbol)) := by
  have hGraph : interpretation.function symbol = PureDifferenceStage.interpretation.function symbol := by cases primitive <;> rfl
  rw [function_from_difference hℳ symbol hGraph args]
  apply (PureDifferenceStage.filter_specification hℳ primitive args output).trans
  apply transfer_difference hℳ
  cases primitive <;> rfl

theorem omega_specification {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ theory)
    (source seed recursion output : Carrier ℳ) :
    output = (expansion hℳ).function .omegaRecursiveSequence (.cons source (.cons seed (.cons recursion .nil))) ↔
      PureSequenceStage.omegaSpec.satisfies
        (templateEnv (.cons output (.cons source (.cons seed (.cons recursion .nil)))) : Env (expansion hℳ).model [] [s,s,s,s]) := by
  rw [function_from_difference hℳ .omegaRecursiveSequence rfl]
  exact (PureDifferenceStage.omega_specification hℳ source seed recursion output).trans
    (transfer_difference hℳ _ rfl (.cons output (.cons source (.cons seed (.cons recursion .nil)))))

/-- 最小差异点的整个定义实例也在最后扩张中保持。 -/
theorem minimum_definition (hℳ : Theory.Models ℳ theory)
    (args : Values (expansion hℳ).model.Carrier [s,s,s,s,s,s]) :
    (Nonlogical.BasicSetTheory.minimum_difference_definition_instance
      (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar .here)).satisfies (templateEnv args) := by
  apply (transfer_difference hℳ _ rfl args).mp
  exact PureDifferenceStage.definition_instance_correct hℳ (templateEnv args) _ _ _ _ _ _

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalDifferenceStage
