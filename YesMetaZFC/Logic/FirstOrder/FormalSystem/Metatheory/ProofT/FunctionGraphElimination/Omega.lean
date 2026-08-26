import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Hilbert
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Infinity

/-!
# `ω` 常元的函数图消去实例

`ω` 的图是无常元规格 `omega_spec`。图的全体性与单值性只消费外延、无穷、
归纳集谓词定义和归纳核定义四条对象公理；源理论在此最小背景上额外加入一条
`ω` 定义公理。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace Omega

open Nonlogical.BasicSetTheory
open scoped Symbols

set_option autoImplicit false

/-- 零元 `ω` 常元的无常元函数图；错误元数落到不可达的假分支。 -/
def graph (arguments : List SetTerm) (result : SetTerm) : SetFormula :=
  match arguments with
  | [] =>
      omega_spec result
  | _ =>
      .falsum

private theorem core_well_sorted
    {set : SetTerm}
    (hSet : TermWellSorted set SetSort.set) :
    TermWellSorted (coreₘ(set)) SetSort.set := by
  simpa [inductive_core_term, signature] using
    (TermWellSorted.app
      (σ := signature)
      FunctionSymbol.inductiveCore
      (ArgsWellSorted.cons hSet
        ArgsWellSorted.nil))

private theorem core_scoped
    {scope : Scope signature} {set : SetTerm}
    (hSet : TermScoped scope set) :
    TermScoped scope (coreₘ(set)) := by
  simpa [inductive_core_term] using
    (TermScoped.app
      (σ := signature) (ctx := scope)
      FunctionSymbol.inductiveCore [set] <| by
        intro term hTerm
        rw [List.mem_singleton.mp hTerm]
        exact hSet)

private theorem graph_well_formed
    {arguments : List SetTerm} {result : SetTerm}
    (hArguments :
      ArgsWellSorted arguments
        (signature.funcDomain FunctionSymbol.omega))
    (hResult :
      TermWellSorted result SetSort.set) :
    FormulaWellFormed (graph arguments result) := by
  change ArgsWellSorted arguments [] at hArguments
  cases arguments with
  | nil =>
      unfold graph omega_spec
      apply FormulaWellFormed.conj
      · apply FormulaWellFormed.rel
        simpa [signature] using
          ArgsWellSorted.cons hResult
            ArgsWellSorted.nil
      · exact FormulaWellFormed.equal
          (core_well_sorted hResult) hResult
  | cons head tail =>
      cases hArguments

private theorem graph_scoped
    {scope : Scope signature}
    {arguments : List SetTerm} {result : SetTerm}
    (hArguments :
      ∀ argument, argument ∈ arguments →
        TermScoped scope argument)
    (hResult : TermScoped scope result) :
    FormulaScoped scope (graph arguments result) := by
  cases arguments with
  | nil =>
      unfold graph omega_spec
      apply FormulaScoped.conj
      · apply FormulaScoped.rel
        intro term hTerm
        rw [List.mem_singleton.mp hTerm]
        exact hResult
      · exact FormulaScoped.equal
          (core_scoped hResult) hResult
  | cons head tail =>
      simpa [graph] using
        (FormulaScoped.falsum :
          FormulaScoped scope
            (Formula.falsum : SetFormula))

private theorem graph_freeSupport
    {arguments : List SetTerm} {result : SetTerm}
    {freeVariable : FreeVariable signature}
    (hMember :
      freeVariable ∈
        Formula.freeSupport
          (graph arguments result)) :
    freeVariable ∈
        Term.freeSupportList arguments ∨
      freeVariable ∈
        Term.freeSupport result := by
  cases arguments with
  | nil =>
      right
      simpa [graph, omega_spec,
        inductive_core_term,
        Formula.freeSupport,
        Term.freeSupport,
        Term.freeSupportList] using hMember
  | cons head tail =>
      simp [graph, Formula.freeSupport] at hMember

private theorem graph_substituteFree
    (target : SetSort) (id : FreeVarId)
    (replacement : SetTerm)
    (arguments : List SetTerm) (result : SetTerm) :
    graph
        (arguments.map
          (Term.substituteFree target id replacement))
        (Term.substituteFree target id replacement result) =
      Formula.substituteFree target id replacement
        (graph arguments result) := by
  cases arguments with
  | nil =>
      cases target
      simp [graph, omega_spec,
        inductive_core_term,
        Formula.substituteFree,
        Term.substituteFree]
  | cons head tail =>
      simp [graph, Formula.substituteFree]

private theorem graph_avoids
    {arguments : List SetTerm} {result : SetTerm}
    (hArguments :
      TermsAvoid FunctionSymbol.omega arguments)
    (hResult :
      TermAvoids FunctionSymbol.omega result) :
    FormulaAvoids FunctionSymbol.omega
      (graph arguments result) := by
  cases arguments with
  | nil =>
      simpa [graph, omega_spec,
        inductive_core_term,
        FormulaAvoids, TermsAvoid, TermAvoids] using
          hResult
  | cons head tail =>
      change True
      trivial

/-- `ω` 常元的已实现函数图编译数据。 -/
def data : Data signature where
  symbol := FunctionSymbol.omega
  sort := SetSort.set
  codomain_eq := rfl
  graph := Omega.graph
  graph_well_formed := graph_well_formed
  graph_scoped := graph_scoped
  graph_freeSupport := graph_freeSupport
  graph_substituteFree := graph_substituteFree
  graph_avoids := graph_avoids

private theorem arguments_nil
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments []) :
    arguments = [] := by
  cases hArguments.1
  rfl

private theorem total
    {arguments : List SetTerm}
    (resultId : FreeVarId)
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain FunctionSymbol.omega))
    (_hFresh :
      (SetSort.set, resultId) ∉
        Term.freeSupportList arguments) :
    Derives omega_base_theory [] <|
      Formula.existsE SetSort.set <|
        Formula.closeFreeAt SetSort.set resultId 0 <|
          graph arguments <|
            .var (.fvar SetSort.set resultId) := by
  change ArgsAdmissible arguments [] at hArguments
  rw [arguments_nil hArguments]
  simpa [graph, omega_spec,
    inductive_core_term,
    Formula.closeFreeAt,
    Term.closeFreeAt] using
      omega_spec_exists_derives

private theorem functional
    {arguments : List SetTerm}
    {left right : SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain FunctionSymbol.omega))
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Derives omega_base_theory [] <|
      Formula.imp (graph arguments left) <|
        Formula.imp (graph arguments right) <|
          Formula.equal left right := by
  change ArgsAdmissible arguments [] at hArguments
  rw [arguments_nil hArguments]
  simpa [graph] using
    omega_spec_unique left right hLeft hRight

/-- 四公理最小背景给出的 `ω` 全体、单值图表示。 -/
def graph_presentation : GraphPresentation data where
  theory := omega_base_theory
  theory_sentence := omega_base_theory_sentence
  total := total
  functional := functional

/-- 四公理最小背景嵌入现有的无穷理论。 -/
theorem omega_base_subset_infinity_theory
    {source : SetFormula}
    (hSource : omega_base_theory source) :
    infinity_theory source := by
  rcases hSource with rfl | hSource
  · exact inductive_core_theory_subset_infinity_theory
      (Or.inl rfl)
  · rcases hSource with rfl | hSource
    · exact
        Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rcases hSource with rfl | hSource
      · exact
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · change source = extensionality_axiom
          at hSource
        subst source
        have hFunction :
            function_application_theory
              extensionality_axiom :=
          extensionality_theory_subset_function_application_theory
            rfl
        have hInjective :=
          function_application_theory_subset_injective_predicate_theory
            hFunction
        have hSurjective :=
          injective_predicate_theory_subset_surjective_predicate_theory
            hInjective
        have hBijection :=
          surjective_predicate_theory_subset_bijection_predicate_theory
            hSurjective
        have hIdentity :=
          bijection_predicate_theory_subset_identity_operator_theory
            hBijection
        have hCollection :=
          identity_operator_theory_subset_mapping_collection_operator_theory
            hIdentity
        have hTransitive :=
          mapping_collection_operator_theory_subset_transitive_set_theory
            hCollection
        have hMembership :=
          transitive_set_theory_subset_membership_relation_operator_theory
            hTransitive
        have hLinear :=
          membership_relation_operator_theory_subset_linear_order_theory
            hMembership
        have hIsomorphism :=
          linear_order_theory_subset_order_isomorphism_theory
            hLinear
        have hIsomorphic :=
          order_isomorphism_theory_subset_order_isomorphic_theory
            hIsomorphism
        have hEmbedding :=
          order_isomorphic_theory_subset_order_embedding_theory
            hIsomorphic
        have hEmbeddable :=
          order_embedding_theory_subset_order_embeddable_theory
            hEmbedding
        have hDiscrete :=
          order_embeddable_theory_subset_natural_discrete_linear_order_theory
            hEmbeddable
        have hWellOrder :=
          natural_discrete_linear_order_theory_subset_well_order_theory
            hDiscrete
        have hFiniteNatural :=
          well_order_theory_subset_finite_natural_theory
            hWellOrder
        have hFiniteOrdinal :=
          finite_natural_theory_subset_finite_ordinal_theory
            hFiniteNatural
        have hImageSeparation :=
          finite_ordinal_theory_subset_relation_image_separation_theory
            hFiniteOrdinal
        have hImage :=
          relation_image_separation_theory_subset_image_operator_theory
            hImageSeparation
        have hRestriction :=
          image_operator_theory_subset_restriction_operator_theory
            hImage
        have hMinimumLinear :=
          restriction_operator_theory_subset_minimum_linear_order_theory
            hRestriction
        have hMinimumNatural :=
          minimum_linear_order_theory_subset_minimum_natural_order_theory
            hMinimumLinear
        have hOrder :=
          minimum_natural_order_theory_subset_order_operator_theory
            hMinimumNatural
        have hDifference :=
          order_operator_theory_subset_minimum_difference_theory
            hOrder
        have hIndexSeparation :=
          minimum_difference_theory_subset_index_order_separation_theory
            hDifference
        have hIndex :=
          index_order_separation_theory_subset_index_order_theory
            hIndexSeparation
        have hPowerSeparation :=
          index_order_theory_subset_power_set_bijection_separation_theory
            hIndex
        have hPowerBijection :=
          power_set_bijection_separation_theory_subset_power_set_bijection_theory
            hPowerSeparation
        have hDifferenceSeparation :=
          power_set_bijection_theory_subset_symmetric_difference_separation_theory
            hPowerBijection
        have hSymmetricDifference :=
          symmetric_difference_separation_theory_subset_symmetric_difference_theory
            hDifferenceSeparation
        have hFinite :=
          symmetric_difference_theory_subset_finite_predicate_theory
            hSymmetricDifference
        have hEquinumerous :=
          finite_predicate_theory_subset_equinumerous_predicate_theory
            hFinite
        have hCardinalityLeq :=
          equinumerous_predicate_theory_subset_cardinality_leq_predicate_theory
            hEquinumerous
        have hCardinalityLt :=
          cardinality_leq_predicate_theory_subset_cardinality_strict_less_predicate_theory
            hCardinalityLeq
        have hDedekind :=
          cardinality_strict_less_predicate_theory_subset_dedekind_finite_predicate_theory
            hCardinalityLt
        have hBasic :=
          dedekind_finite_predicate_theory_subset_basic_finite_theory
            hDedekind
        exact inductive_core_theory_subset_infinity_theory <|
          inductive_core_separation_theory_subset_inductive_core_theory <|
            inductive_set_theory_subset_inductive_core_separation_theory <|
              infinity_axiom_theory_subset_inductive_set_theory <|
                basic_finite_theory_subset_infinity_axiom_theory
                  hBasic

/-- 最小 `ω` 背景中的固定公理均不含 `ω` 常元。 -/
private theorem base_formula_avoids
    {source : SetFormula}
    (hSource : omega_base_theory source) :
    FormulaAvoids FunctionSymbol.omega source := by
  simp only [omega_base_theory,
    extensionality_theory,
    Theory.insert,
    Theory.singleton] at hSource
  repeat'
    first
    | obtain hSource | hSource := hSource
    | subst source
  all_goals
    apply checkFormulaAvoids_sound
    native_decide

/-- 最小背景公理在 `ω` 编译下严格保持原式。 -/
private theorem formula_base_eq
    {source : SetFormula}
    (hSource : omega_base_theory source) :
    FunctionGraphElimination.formula data source =
      source := by
  apply formula_eq_of_sentence_avoids data source
  · exact base_formula_avoids hSource
  · exact omega_base_theory_sentence hSource

/-- 打开定义公理唯一 binder 后的源公式。 -/
private def definition_point : SetFormula :=
  omega_definition_instance (x#0)

/-- `ω` 定义实例消去常元后的标准存在等式图。 -/
private def compiled_definition_point : SetFormula :=
  ((∃ₘ[SetSort.set, 0],
      omega_spec (x#0) ∧ₘ
        ((x#1) ≐ₘ (x#0))) ↔ₘ
    omega_spec (x#1))

/-- 开放 `ω` 定义实例的编译恰为标准存在等式图。 -/
private theorem formula_definition_point :
    FunctionGraphElimination.formula
        data definition_point =
      compiled_definition_point := by
  unfold definition_point omega_definition_instance
  rw [FunctionGraphElimination.formula]
  have hSpecAvoid :
      FormulaAvoids FunctionSymbol.omega
        (omega_spec (x#0)) := by
    apply checkFormulaAvoids_sound
    native_decide
  rw [formula_eq_source_of_avoids
    data (omega_spec (x#0)) hSpecAvoid]
  simp [compiled_definition_point,
    omega_spec, inductive_core_term,
    FunctionGraphElimination.formula,
    FunctionGraphElimination.equality,
    FunctionGraphElimination.terms,
    FunctionGraphElimination.term,
    close_witnesses, condition_conjunction,
    data, graph, source_formula, source_term,
    source_id, witness_id]

private theorem definition_point_admissible :
    Formula.Admissible definition_point := by
  unfold definition_point
    omega_definition_instance
  exact Formula.Admissible.iff
    (Formula.Admissible.equal
      (set_variable_admissible 0)
      omega_term_admissible)
    (omega_spec_admissible
      (set_variable_admissible 0))

/-- 最小背景逐点证明编译后的 `ω` 定义实例。 -/
private theorem compiled_definition_point_derives :
    Derives omega_base_theory []
      compiled_definition_point := by
  have hBridge :=
    graph_presentation.exists_graph_eq_iff
      (arguments := [])
      (result := x#1)
      0 ArgsAdmissible.nil
      (set_variable_admissible 1)
      (by native_decide)
      (by native_decide)
  change Derives omega_base_theory []
    (Formula.iff
      (Formula.existsE SetSort.set
        (Formula.closeFreeAt SetSort.set 0 0
          (Formula.conj
            (graph [] (x#0))
            ((x#1) ≐ₘ (x#0)))))
      (graph [] (x#1))) at hBridge
  simpa [compiled_definition_point,
    graph, omega_spec,
    inductive_core_term,
    Formula.closeFreeAt,
    Term.closeFreeAt] using hBridge

/-- 最小背景证明整个 `ω` 定义公理的函数图编译。 -/
private theorem formula_definition_axiom_derives :
    Derives omega_base_theory []
      (FunctionGraphElimination.formula
        data omega_definition_axiom) := by
  have hPoint :
      Derives omega_base_theory []
        (FunctionGraphElimination.formula
          data definition_point) := by
    rw [formula_definition_point]
    exact compiled_definition_point_derives
  have hClosed :=
    graph_presentation.formula_forall_close_derives
      SetSort.set 0 definition_point
      definition_point_admissible hPoint
  simpa [omega_definition_axiom,
    definition_point] using hClosed

private theorem compile_axiom
    {source : SetFormula}
    (hSource : omega_operator_theory source) :
    Derives omega_base_theory []
      (FunctionGraphElimination.formula
        data source) := by
  rcases hSource with rfl | hSource
  · exact formula_definition_axiom_derives
  · rw [formula_base_eq hSource]
    exact Derives.theory_mem hSource
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          (omega_base_theory_admissible
            source hSource))

/-- `ω` 定义扩张的理论级函数图消去表示。 -/
def theory_presentation :
    TheoryPresentation data where
  graph := graph_presentation
  source := omega_operator_theory
  compile_axiom := compile_axiom

theorem hilbert
    {source : SetFormula}
    (hSource :
      HilbertDerives omega_operator_theory source) :
    Derives omega_base_theory []
      (FunctionGraphElimination.formula
        data source) :=
  theory_presentation.hilbert hSource

/-- `ω` 扩张的 checked 自然演绎证明可整体翻译到四公理最小背景。 -/
theorem derives
    {source : SetFormula}
    (hSource :
      Derives omega_operator_theory [] source) :
    Derives omega_base_theory []
      (FunctionGraphElimination.formula
        data source) :=
  theory_presentation.derives SetSort.set hSource

theorem hilbert_falsum
    (hSource :
      HilbertDerives omega_operator_theory
        Formula.falsum) :
    Derives omega_base_theory [] Formula.falsum :=
  theory_presentation.hilbert_falsum hSource

theorem derives_falsum
    (hSource :
      Derives omega_operator_theory []
        Formula.falsum) :
    Derives omega_base_theory [] Formula.falsum :=
  theory_presentation.derives_falsum
    SetSort.set hSource

theorem consistent
    (hBase :
      Derives.Consistent omega_base_theory []) :
    Derives.Consistent omega_operator_theory [] :=
  theory_presentation.consistent SetSort.set hBase

theorem hilbert_consistent
    (hBase :
      Derives.Consistent omega_base_theory []) :
    ¬ HilbertDerives omega_operator_theory
        Formula.falsum :=
  theory_presentation.hilbert_consistent hBase

/-- `ω` 定义公理直接证明规范常元满足无常元图。 -/
private theorem omega_term_spec_derives :
    Derives omega_operator_theory []
      (omega_spec ωₘ) := by
  have hAxiom :
      Derives omega_operator_theory []
        omega_definition_axiom :=
    Derives.theory_mem (Or.inl rfl)
  have hInstance :=
    Derives.forall_elim
      (term := ωₘ) hAxiom
  have hDefinition :
      Derives omega_operator_theory []
        ((ωₘ ≐ₘ ωₘ) ↔ₘ omega_spec ωₘ) := by
    simpa [omega_definition_axiom,
      omega_definition_instance,
      omega_term,
      omega_spec,
      inductive_core_term,
      Formula.openAt,
      Formula.closeFreeAt,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree,
      set_variable, set_bound_variable] using
        hInstance
  exact Derives.iff_elim_right hDefinition <|
    Derives.eq_refl_m
      (T := omega_operator_theory)
      (Γ := []) (sort := SetSort.set)
      ωₘ

private theorem realizes
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain FunctionSymbol.omega)) :
    Derives omega_operator_theory [] <|
      graph arguments
        (.app FunctionSymbol.omega arguments) := by
  change ArgsAdmissible arguments [] at hArguments
  rw [arguments_nil hArguments]
  simpa [graph, omega_term] using
    omega_term_spec_derives

/-- `ω` 常元定义扩张的完整函数图表示。 -/
def presentation : DefinitionPresentation data where
  toGraphPresentation := graph_presentation
  extension := omega_operator_theory
  extension_sentence := omega_operator_theory_sentence
  base_subset := by
    intro formula hFormula
    exact Or.inr hFormula
  realizes := realizes

/-- `ω` 编译与原闭句在定义扩张中可证明等价。 -/
theorem sentence_iff
    {source : SetFormula}
    (hSource : Formula.Sentence source) :
    Derives omega_operator_theory []
      (Formula.iff
        (FunctionGraphElimination.formula
          data source)
        source) :=
  presentation.sentence_iff hSource

/-- 最小 `ω` 定义扩张嵌入现有的宽无穷理论。 -/
theorem omega_operator_subset_infinity_theory
    {source : SetFormula}
    (hSource : omega_operator_theory source) :
    infinity_theory source := by
  rcases hSource with rfl | hSource
  · exact Or.inl rfl
  · exact omega_base_subset_infinity_theory
      hSource

/--
现有宽无穷理论上的 `ω` 图表示。

该层只服务旧章节迁移；真正把 `ω` 公理消去到无常元背景的接口仍是
`graph_presentation` 与 `theory_presentation`。
-/
def infinity_graph_presentation :
    GraphPresentation data :=
  graph_presentation.theory_weaken
    infinity_theory
    (fun _ hSource =>
      omega_base_subset_infinity_theory hSource)
    infinity_theory_sentence

private theorem infinity_realizes
    {arguments : List SetTerm}
    (hArguments :
      ArgsAdmissible arguments
        (signature.funcDomain FunctionSymbol.omega)) :
    Derives infinity_theory [] <|
      graph arguments
        (.app FunctionSymbol.omega arguments) :=
  (realizes hArguments).theory_weaken
    (fun _ hSource =>
      omega_operator_subset_infinity_theory hSource)

/-- 旧宽无穷理论经新 `ω` 图接口得到的完整定义表示。 -/
def infinity_presentation :
    DefinitionPresentation data where
  toGraphPresentation := infinity_graph_presentation
  extension := infinity_theory
  extension_sentence := infinity_theory_sentence
  base_subset := by
    intro formula hFormula
    exact hFormula
  realizes := infinity_realizes

/-- 旧无穷理论中的闭句与其 `ω` 图编译像可证明等价。 -/
theorem infinity_sentence_iff
    {source : SetFormula}
    (hSource : Formula.Sentence source) :
    Derives infinity_theory []
      (Formula.iff
        (FunctionGraphElimination.formula
          data source)
        source) :=
  infinity_presentation.sentence_iff hSource

end Omega
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
